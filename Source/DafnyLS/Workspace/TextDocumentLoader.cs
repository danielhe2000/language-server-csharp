using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Linq;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class TextDocumentLoader : ITextDocumentLoader {
    private readonly IDafnyParser _parser;
    private readonly ISymbolResolver _symbolResolver;
    private readonly IProgramVerifier _verifier;
    private readonly ISymbolTableFactory _symbolTableFactory;
    private readonly IVerificationNotificationPublisher _notificationPublisher;

    public TextDocumentLoader(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IVerificationNotificationPublisher notificationPublisher
    ) {
      _parser = parser;
      _symbolResolver = symbolResolver;
      _verifier = verifier;
      _symbolTableFactory = symbolTableFactory;
      _notificationPublisher = notificationPublisher;
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, bool verify, CancellationToken cancellationToken) {
      if(verify){
        return await GenerateProgramRecordInfo(textDocument ,cancellationToken);
      }
      else{
        return await GenerateProgramWithoutVerify(textDocument, cancellationToken);
      }
    }
    /****************** ORIGINAL METHODS **************/
    private async Task<DafnyDocument> GenerateProgram(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      _notificationPublisher.Started(textDocument);
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }

    private async Task<DafnyDocument> GenerateProgramWithoutVerify(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      // int StatementCount = DocumentPrinter.GetStatementCount(program, "module1", "foo");
      // Console.WriteLine(">>>>>>>>>>>>>>>>>> # Statement: " + StatementCount + " <<<<<<<<<<<<<<<<<<");
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, null);
    }

    /****************** USED FOR ASSERTION TEST **************/
    private async Task<DafnyDocument> GenerateProgramWithSmallTweak(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // Verify 
      _notificationPublisher.Started(textDocument);
      DocumentModifier.RemoveLemmaLinesFlattened(program, "foo", "module1", 2);
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      DocumentPrinter.OutputErrorInfo(errorReporter);

      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      var Stm = DocumentPrinter.GetStatement(program, "module1", "foo", 2);
      if(Stm == null){
        Console.WriteLine("????????? Can't be null?!");
      }
      else{
        Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> " + Stm.Tok.GetLspRange().Start + " to " + Stm.Tok.GetLspRange().End);
      }
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      // DocumentPrinter.OutputProgramInfo(program);
      DocumentPrinter.OutputErrorInfo(errorReporter);

      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
    private async Task<DafnyDocument> GenerateProgramAssertionTestBasic(TextDocumentItem textDocument, CancellationToken cancellationToken){
      int begin = 0;    // Beginning of the target search range
      int end = 0;      // End of the target search range
      string ModuleName = "module1";
      string LemmaName = "foo";
      
      _notificationPublisher.Started(textDocument);

      // Initial run, to record program info
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // Record the program info
      foreach(ModuleDefinition module in program.ModuleSigs.Keys){
          if(module.FullName != ModuleName) continue;
          foreach(ICallable callable in module.CallGraph.vertices.Keys){
              var corresVertex = module.CallGraph.vertices[callable];
              if(callable.WhatKind != "lemma" || callable.NameRelativeToModule != LemmaName) continue;
              var LemmaCallable = (Lemma)callable;
              end = LemmaCallable.methodBody.Body.Count;
          }
      }
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }
      if(errorReporter.AllMessages[ErrorLevel.Error].Count != 0 && end == 0){
        Console.WriteLine("The error is not in the designated lemma or module");
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }

      // Start binary search
      while(begin < end){
        int middle = (begin + end) / 2;
        Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Current middle: " + middle + "<<<<<<<<<<<<<<<<<<<<<<<<");
        errorReporter = new BuildErrorReporter();
        program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
        compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
        symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
        DocumentModifier.RemoveLemmaLines(program, "foo", "module1", middle);
        serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
        if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
          begin = middle + 1;
        }
        else{
          end = middle;
        }
      }
      Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Final conclusion: assertion failure on line " + (begin - 1) + "<<<<<<<<<<<<<<<<<<<<<<<<");
      int TargetLine = begin - 1;

      // Perform the final pass, and record the lsp location of assertion failure
      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);

      foreach(ModuleDefinition module in program.ModuleSigs.Keys){
          if(module.FullName != ModuleName) continue;
          foreach(ICallable callable in module.CallGraph.vertices.Keys){
              var corresVertex = module.CallGraph.vertices[callable];
              if(callable.WhatKind != "lemma" || callable.NameRelativeToModule != LemmaName) continue;
              var LemmaCallable = (Lemma)callable;
              var Location = LemmaCallable.methodBody.Body[TargetLine].Tok.GetLspPosition();
              var Range = LemmaCallable.methodBody.Body[TargetLine].Tok.GetLspRange();
              Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> " + Location);
              Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> " + Range.Start + " to " + Range.End);
          }
      }

      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
      private async Task<DafnyDocument> GenerateProgramAssertionTestAdvanced(TextDocumentItem textDocument, CancellationToken cancellationToken){
      int begin = 0;    // Beginning of the target search range
      int end = 0;      // End of the target search range
      string ModuleName = "module1";
      string LemmaName = "foo";
      
      _notificationPublisher.Started(textDocument);

      // Initial run, to record program info
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // Record the program info
      end = DocumentPrinter.GetStatementCount(program, ModuleName, LemmaName);

      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }
      if(errorReporter.AllMessages[ErrorLevel.Error].Count != 0 && end == 0){
        Console.WriteLine("The error is not in the designated lemma or module");
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }

      // Start binary search
      while(begin < end){
        int middle = (begin + end) / 2;
        Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Current middle: " + middle + "<<<<<<<<<<<<<<<<<<<<<<<<");
        errorReporter = new BuildErrorReporter();
        program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
        compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
        symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
        DocumentModifier.RemoveLemmaLinesFlattened(program, LemmaName, ModuleName, middle);
        serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
        if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
          begin = middle + 1;
        }
        else{
          end = middle;
        }
      }
      Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Final conclusion: assertion failure of statement #" + (begin - 1) + "<<<<<<<<<<<<<<<<<<<<<<<<");
      int TargetLine = begin - 1;

      // Perform the final pass, and record the lsp location of assertion failure
      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);

      var Target = DocumentPrinter.GetStatement(program,ModuleName,LemmaName,TargetLine);
      Position Location;
      OmniSharp.Extensions.LanguageServer.Protocol.Models.Range Range;
      if(Target != null){
        Location = Target.Tok.GetLspPosition();
        Range = Target.Tok.GetLspRange();
      }else{
        var TargetLemma = DocumentPrinter.GetCallable(program,ModuleName, LemmaName);
        Location = TargetLemma.Tok.GetLspPosition();
        Range = TargetLemma.Tok.GetLspRange();
      }
      Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Final conclusion: assertion failure of statement #" + (begin - 1) + "<<<<<<<<<<<<<<<<<<<<<<<<");
      Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Assertion failure Location: " + Location);
      Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Assertion failure Range: " + Range.Start + " to " + Range.End);

      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }  

    /***************   TIME OUT METHODS: *************/

    private async Task<DafnyDocument> GenerateProgramRecordInfo(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      _notificationPublisher.Started(textDocument);
      List<Tuple<string, string> > callableName = new List<Tuple<string, string> >();
      List<string> callableInfo = new List<string>();
      List<int> timeoutLines = new List<int>();
      var serializedCounterExamples = await _verifier.VerifyAsyncRecordInfo(program, cancellationToken, callableName, callableInfo);
      Console.WriteLine(">>>>>>>>>>>>>> Timeout Callable Name Count: " + callableName.Count + "<<<<<<<<<<<<<<");
      Console.WriteLine(">>>>>>>>>>>>>> Timeout Callable Info Count: " + callableInfo.Count + "<<<<<<<<<<<<<<");
      for(int i = 0; i < callableName.Count; ++i){
        string ModuleName = callableName[i].Item1;
        string LemmaName = callableName[i].Item2;
        int begin = 0;    // Beginning of the target search range
        int end = DocumentPrinter.GetStatementCount(program, ModuleName, LemmaName);      // End of the target search range
        if(end == 0){
          Console.WriteLine("The timeout lemma has no body / the timeout callable is not a lemma");
          continue;
        }
        Console.WriteLine(">>>>>>>>>>> Current Lemma "+LemmaName + " has #statement " + end);
        while(begin < end){
          int middle = (begin + end) / 2;
          Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Current middle: " + middle + "<<<<<<<<<<<<<<<<<<<<<<<<");
          List<Tuple<string, string> > TempCallableName = new List<Tuple<string, string> >();
          List<string> TempCallableInfo = new List<string>();
          var TempErrorReporter = new BuildErrorReporter();
          var TempProgram = await _parser.ParseAsync(textDocument, TempErrorReporter, cancellationToken);
          var TempCompilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, TempProgram, cancellationToken);
          DocumentModifier.RemoveLemmaLinesFlattened(TempProgram,LemmaName,ModuleName,middle);
          Console.WriteLine(">>>>>>>>>>> After truncating, current lemma "+LemmaName + " has #statement " + DocumentPrinter.GetStatementCount(TempProgram, ModuleName, LemmaName));
          var temp = _verifier.VerifyAsyncRecordInfoSpecifyName(TempProgram, cancellationToken, TempCallableName, TempCallableInfo, callableName[i].Item1, callableName[i].Item2);
          if(TempCallableInfo.Count == 0){
            begin = middle + 1;
          }
          else{
            end = middle;
          }
        }
        int TargetLine = begin - 1;
        var Target = DocumentPrinter.GetStatement(program, ModuleName, LemmaName,TargetLine);
        OmniSharp.Extensions.LanguageServer.Protocol.Models.Range Range;
        if(Target != null){
          Range = Target.Tok.GetLspRange();
          
        }
        else{
          var TargetLemma = DocumentPrinter.GetCallable(program, ModuleName, LemmaName);
          Range = TargetLemma.Tok.GetLspRange();
        }
        Console.WriteLine("~~~~~~~~~~~~~ Module " + ModuleName + ", Lemma: " + LemmaName + " timeout range: " + Range.Start + " to " + Range.End + " ~~~~~~~~~~");
      }
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
  }
}
