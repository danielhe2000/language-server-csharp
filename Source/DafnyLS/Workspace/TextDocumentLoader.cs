using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.IO; 
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
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
      // Console.WriteLine(">>>>>>>>> Time out: " + DafnyOptions.O.TimeLimit);
      // Console.WriteLine(">>>>>>>>> Arith Mode: " + DafnyOptions.O.ArithMode);
      // Console.WriteLine(">>>>>>>>> Disable NLarith: " + DafnyOptions.O.DisableNLarith);
      if(verify){
        return await GenerateProgramZ3Timeout(textDocument ,cancellationToken);
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
      DocumentModifier.RemoveLemmaLinesFlattened(program, "foo", "", "module1", 2);
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      // DocumentPrinter.OutputErrorInfo(errorReporter);

      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      var Stm = DocumentPrinter.GetStatement(program, "module1", "", "foo", 2);
      if(Stm == null){
        // Console.WriteLine("????????? Can't be null?!");
      }
      else{
        // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> " + Stm.Tok.GetLspRange().Start + " to " + Stm.Tok.GetLspRange().End);
      }
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      // DocumentPrinter.OutputProgramInfo(program);
      // DocumentPrinter.OutputErrorInfo(errorReporter);

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
        // Console.WriteLine("The error is not in the designated lemma or module");
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }

      // Start binary search
      while(begin < end){
        int middle = (begin + end) / 2;
        // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Current middle: " + middle + "<<<<<<<<<<<<<<<<<<<<<<<<");
        errorReporter = new BuildErrorReporter();
        program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
        compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
        symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
        DocumentModifier.RemoveLemmaLines(program, "foo", "","module1", middle);
        serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
        if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
          begin = middle + 1;
        }
        else{
          end = middle;
        }
      }
      // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Final conclusion: assertion failure on line " + (begin - 1) + "<<<<<<<<<<<<<<<<<<<<<<<<");
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
              // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> " + Location);
              // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> " + Range.Start + " to " + Range.End);
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
      string ClassName = "";
      string LemmaName = "foo";
      
      _notificationPublisher.Started(textDocument);

      // Initial run, to record program info
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // Record the program info
      end = DocumentPrinter.GetStatementCount(program, ModuleName, ClassName,LemmaName);

      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }
      if(errorReporter.AllMessages[ErrorLevel.Error].Count != 0 && end == 0){
        // Console.WriteLine("The error is not in the designated lemma or module");
        _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
        return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      }

      // Start binary search
      while(begin < end){
        int middle = (begin + end) / 2;
        // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Current middle: " + middle + "<<<<<<<<<<<<<<<<<<<<<<<<");
        errorReporter = new BuildErrorReporter();
        program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
        compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
        symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
        DocumentModifier.RemoveLemmaLinesFlattened(program, LemmaName, ClassName, ModuleName, middle);
        serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
        if(errorReporter.AllMessages[ErrorLevel.Error].Count == 0){
          begin = middle + 1;
        }
        else{
          end = middle;
        }
      }
      // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Final conclusion: assertion failure of statement #" + (begin - 1) + "<<<<<<<<<<<<<<<<<<<<<<<<");
      int TargetLine = begin - 1;

      // Perform the final pass, and record the lsp location of assertion failure
      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);

      var Target = DocumentPrinter.GetStatement(program,ModuleName,ClassName,LemmaName,TargetLine);
      Position Location;
      OmniSharp.Extensions.LanguageServer.Protocol.Models.Range Range;
      if(Target != null){
        Location = Target.Tok.GetLspPosition();
        Range = Target.Tok.GetLspRange();
      }else{
        var TargetLemma = DocumentPrinter.GetCallable(program,ModuleName, ClassName, LemmaName);
        Location = TargetLemma.Tok.GetLspPosition();
        Range = TargetLemma.Tok.GetLspRange();
      }
      // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Final conclusion: assertion failure of statement #" + (begin - 1) + "<<<<<<<<<<<<<<<<<<<<<<<<");
      // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Assertion failure Location: " + Location);
      // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Assertion failure Range: " + Range.Start + " to " + Range.End);

      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }  

    /***************   TIME OUT METHODS: *************/

    private async Task<DafnyDocument> GenerateProgramWithTimeout(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      _notificationPublisher.Started(textDocument);
      List<Tuple<string, string, string> > callableName = new List<Tuple<string, string, string> >();
      List<long> callableTime = new List<long>();
      Dictionary<ICallable, long> callableTotalTime = new Dictionary<ICallable, long>();
      // List<int> timeoutLines = new List<int>();
      var serializedCounterExamples = await _verifier.VerifyAsyncRecordInfo(program, cancellationToken, callableName, callableTime);
      
      /*
      Console.WriteLine(">>>>>>>>>>>>>> Timeout Callable Name Count: " + callableName.Count + "<<<<<<<<<<<<<<");
      Console.WriteLine(">>>>>>>>>>>>>> Timeout Callable Info Count: " + callableTime.Count + "<<<<<<<<<<<<<<");
      for(int i = 0; i < callableName.Count; ++i){
        string ModuleName = callableName[i].Item1;
        string ClassName = callableName[i].Item2;
        string LemmaName = callableName[i].Item3;
        Console.WriteLine(">>>>>>>>>>" + ModuleName + "." + ClassName + "." + LemmaName + ": " + callableTime[i] + "ms");
      }*/
      
      var TimeoutFound = false;
      for(int i = 0; i < callableName.Count; ++i){
        string ModuleName = callableName[i].Item1;
        string ClassName = callableName[i].Item2;
        string LemmaName = callableName[i].Item3;
        var TargetCallable = DocumentPrinter.GetCallable(program, ModuleName, ClassName, LemmaName);
        if(TargetCallable == null) continue;
        if(callableTime[i] > 0){
          // Console.WriteLine(">>>>>>>>>>" + ModuleName + "." + ClassName + "." + LemmaName + ": " + callableTime[i] + "ms");
          if(callableTotalTime.ContainsKey(TargetCallable)){
            callableTotalTime[TargetCallable] += callableTime[i];
          }
          else{
            callableTotalTime.Add(TargetCallable, callableTime[i]);
          }
          continue;
        }
        else if(callableTotalTime.ContainsKey(TargetCallable)){
          callableTotalTime.Remove(TargetCallable);
        }
        TimeoutFound = true;
        int begin = 0;    // Beginning of the target search range
        int end = DocumentPrinter.GetStatementCount(program, ModuleName, ClassName, LemmaName);      // End of the target search range
        if(end == 0){
          // Console.WriteLine("The timeout lemma has no body / the timeout callable is not a lemma");
          // var CallableRange = TargetCallable.Tok.GetLspRange();
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(TargetCallable.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "This callable causes a time-out", source = MessageSource.Other});
          continue;
        }
        // Console.WriteLine(">>>>>>>>>>> Current Lemma "+LemmaName + " has #statement " + end);
        while(begin < end){
          int middle = (begin + end) / 2;
          var TimeoutResultTask = TruncateAndCheckTimeOut(textDocument, middle, ModuleName, LemmaName, ClassName, cancellationToken);
          bool NoTimeout = await TimeoutResultTask;
          /*
          // Console.WriteLine(">>>>>>>>>>>>>>>>>>>>>>>>>>> Current middle: " + middle + "<<<<<<<<<<<<<<<<<<<<<<<<");
          List<Tuple<string, string, string> > TempCallableName = new List<Tuple<string, string, string> >();
          List<long> TempCallableInfo = new List<long>();
          var TempErrorReporter = new BuildErrorReporter();
          var TempProgram = await _parser.ParseAsync(textDocument, TempErrorReporter, cancellationToken);
          var TempCompilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, TempProgram, cancellationToken);
          DocumentModifier.RemoveLemmaLinesFlattened(TempProgram,LemmaName,ClassName,ModuleName,middle);
          // Console.WriteLine(">>>>>>>>>>> After truncating, current lemma "+LemmaName + " has #statement " + DocumentPrinter.GetStatementCount(TempProgram, ModuleName, ClassName, LemmaName));
          var temp = await _verifier.VerifyAsyncRecordInfoSpecifyName(TempProgram, cancellationToken, TempCallableName, TempCallableInfo, ModuleName,ClassName,LemmaName);
          // Console.WriteLine(">>>>>>>>>>> TempCallableInfo Size" + TempCallableInfo.Count);*/
          if(NoTimeout){
            begin = middle + 1;
          }
          else{
            end = middle;
          }
        }
        int TargetLine = begin - 1;
        var Target = DocumentPrinter.GetStatement(program, ModuleName, ClassName, LemmaName,TargetLine);
        // OmniSharp.Extensions.LanguageServer.Protocol.Models.Range Range;
        if(Target != null){
          // Range = Target.Tok.GetLspRange();
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(Target.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "This line causes a time-out", source = MessageSource.Other});
        }
        else{
          var TargetLemma = DocumentPrinter.GetCallable(program, ModuleName, ClassName, LemmaName);
          // Range = TargetLemma.Tok.GetLspRange();
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(TargetLemma.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "The post-condition of this lemma causes a time-out", source = MessageSource.Other});
        }
        // Console.WriteLine("~~~~~~~~~~~~~ Module " + ModuleName + ", Lemma: " + LemmaName + " timeout range: " + Range.Start + " to " + Range.End + " ~~~~~~~~~~");
      }

      // DocumentPrinter.OutputErrorInfo(errorReporter);
      foreach(var item in callableTotalTime){
        var TargetCallable = item.Key;
        var Time = item.Value;
        Token TimeoutToken = new Token();
        DocumentModifier.CopyToken(TargetCallable.Tok, TimeoutToken);
        errorReporter.AllMessages[ErrorLevel.Info].Add(new ErrorMessage {token = TimeoutToken, message = Time + " ms spent on verifying this callable", source = MessageSource.Other});
      }
      _notificationPublisher.Completed(textDocument, (serializedCounterExamples == null) && (!TimeoutFound));
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
    /**/
    private async Task<DafnyDocument> GenerateProgramWithTimeoutMultiThread(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      _notificationPublisher.Started(textDocument);
      List<Tuple<string, string, string> > callableName = new List<Tuple<string, string, string> >();
      List<long> callableTime = new List<long>();
      Dictionary<ICallable, long> callableTotalTime = new Dictionary<ICallable, long>();
      // List<int> timeoutLines = new List<int>();
      var serializedCounterExamples = await _verifier.VerifyAsyncRecordInfo(program, cancellationToken, callableName, callableTime);
      
      var TimeoutFound = false;
      for(int i = 0; i < callableName.Count; ++i){
        string ModuleName = callableName[i].Item1;
        string ClassName = callableName[i].Item2;
        string LemmaName = callableName[i].Item3;
        var TargetCallable = DocumentPrinter.GetCallable(program, ModuleName, ClassName, LemmaName);
        if(callableTime[i] > 0){
          // Console.WriteLine(">>>>>>>>>>" + ModuleName + "." + ClassName + "." + LemmaName + ": " + callableTime[i] + "ms");
          if(callableTotalTime.ContainsKey(TargetCallable)){
            callableTotalTime[TargetCallable] += callableTime[i];
          }
          else{
            callableTotalTime.Add(TargetCallable, callableTime[i]);
          }
          continue;
        }
        else if(callableTotalTime.ContainsKey(TargetCallable)){
          callableTotalTime.Remove(TargetCallable);
        }
        TimeoutFound = true;
        int begin = 0;    // Beginning of the target search range
        int end = DocumentPrinter.GetStatementCount(program, ModuleName, ClassName, LemmaName);      // End of the target search range
        if(end == 0){
          // Console.WriteLine("The timeout lemma has no body / the timeout callable is not a lemma");
          // var CallableRange = TargetCallable.Tok.GetLspRange();
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(TargetCallable.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "This callable causes a time-out", source = MessageSource.Other});
          continue;
        }
        // Console.WriteLine(">>>>>>>>>>> Current Lemma "+LemmaName + " has #statement " + end);
        while(begin < end){
          int middle1 = begin + (end-begin)/3;
          int middle2 = begin + (end-begin)*2/3;
          Console.WriteLine(">>>>>>>>>>> Current Lemma "+LemmaName);
          // Console.WriteLine(">>>>>>>>>>> Current Begin "+begin);
          // Console.WriteLine(">>>>>>>>>>> Current End "+end);
          // Console.WriteLine(">>>>>>>>>>> Current Middle1 "+middle1);
          // Console.WriteLine(">>>>>>>>>>> Current Middle2 "+middle2);
          Stopwatch sw = new Stopwatch();
          sw.Start();
          /*Console.WriteLine("============= Main thread ID is :" + Thread.CurrentThread.ManagedThreadId);
          var TimeoutResultTask1 = TruncateAndCheckTimeOut(textDocument, middle1, ModuleName, LemmaName, ClassName, cancellationToken);
          var TimeoutResultTask2 = TruncateAndCheckTimeOut(textDocument, middle2, ModuleName, LemmaName, ClassName, cancellationToken);
          // TimeoutResultTask1.Start();
          // TimeoutResultTask2.Start();
          bool NoTimeout1 = TimeoutResultTask1.Result;
          bool NoTimeout2 = TimeoutResultTask2.Result;*/

          MultiTreadHelper mth = new MultiTreadHelper(_parser, _symbolResolver, _verifier, textDocument, ModuleName, ClassName, LemmaName, middle1, middle2, cancellationToken);
          Thread t1 = new Thread(new ThreadStart(mth.TruncateAndCheckFirstHalf));
          Thread t2 = new Thread(new ThreadStart(mth.TruncateAndCheckSecondHalf));
          t1.IsBackground = true;
          t2.IsBackground = true;
          t1.Start();
          t2.Start();
          t1.Join();
          t2.Join();
          Console.WriteLine(">>>>>>> After verifying, elapsed time is: " + sw.ElapsedMilliseconds);
          /*
          if(NoTimeout2){
            begin = middle2 + 1;
          }
          else if(NoTimeout1){
            begin = middle1 + 1;
            end = middle2;
          }
          else{
            end = middle1;
          }*/
          if(mth.result2){
            begin = middle2 + 1;
          }
          else if(mth.result1){
            begin = middle1 + 1;
            end = middle2;
          }
          else{
            end = middle1;
          }
        }
        int TargetLine = begin - 1;
        var Target = DocumentPrinter.GetStatement(program, ModuleName, ClassName, LemmaName,TargetLine);
        // OmniSharp.Extensions.LanguageServer.Protocol.Models.Range Range;
        if(Target != null){
          var Range = Target.Tok.GetLspRange();
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(Target.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "This line causes a time-out", source = MessageSource.Other});
          Console.WriteLine("~~~~~~~~~~~~~ Module " + ModuleName + ", Lemma: " + LemmaName + " timeout range: " + Range.Start + " to " + Range.End + " ~~~~~~~~~~");
        }
        else{
          var TargetLemma = DocumentPrinter.GetCallable(program, ModuleName, ClassName, LemmaName);
          var Range = TargetLemma.Tok.GetLspRange();
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(TargetLemma.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "The post-condition of this lemma causes a time-out", source = MessageSource.Other});
          Console.WriteLine("~~~~~~~~~~~~~ Module " + ModuleName + ", Lemma: " + LemmaName + " timeout range: " + Range.Start + " to " + Range.End + " ~~~~~~~~~~");
        }
        
      }

      // DocumentPrinter.OutputErrorInfo(errorReporter);
      foreach(var item in callableTotalTime){
        var TargetCallable = item.Key;
        var Time = item.Value;
        Token TimeoutToken = new Token();
        DocumentModifier.CopyToken(TargetCallable.Tok, TimeoutToken);
        errorReporter.AllMessages[ErrorLevel.Info].Add(new ErrorMessage {token = TimeoutToken, message = Time + " ms spent on verifying this callable", source = MessageSource.Other});
      }
      _notificationPublisher.Completed(textDocument, (serializedCounterExamples == null) && (!TimeoutFound));
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
    // Return true if there is no time-out
    private async Task<bool> TruncateAndCheckTimeOut(TextDocumentItem textDocument, int Start, string ModuleName, string LemmaName, string ClassName, CancellationToken cancellationToken){
      List<Tuple<string, string, string> > TempCallableName = new List<Tuple<string, string, string> >();
      List<long> TempCallableInfo = new List<long>();
      var TempErrorReporter = new BuildErrorReporter();
      // Console.WriteLine("============= Start " + Start + " thread ID is :" + Thread.CurrentThread.ManagedThreadId);
      var TempProgram = await _parser.ParseAsync(textDocument, TempErrorReporter, cancellationToken);
      // Console.WriteLine(">>>>> Parse Start: " + Start);
      var TempCompilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, TempProgram, cancellationToken);
      // Console.WriteLine(">>>>> Resolve Start: " + Start);
      DocumentModifier.RemoveLemmaLinesFlattened(TempProgram,LemmaName,ClassName,ModuleName,Start);
      // Console.WriteLine(">>>>>>>>>>> After truncating, current lemma "+LemmaName + " has #statement " + DocumentPrinter.GetStatementCount(TempProgram, ModuleName, ClassName, LemmaName));
      var temp = await _verifier.VerifyAsyncRecordInfoSpecifyName(TempProgram, cancellationToken, TempCallableName, TempCallableInfo, ModuleName,ClassName,LemmaName);
      // Console.WriteLine(">>>>>>>>>>> TempCallableInfo Size" + TempCallableInfo.Count);
      return (TempCallableInfo.Count == 0) || (TempCallableInfo.Count == 1 && TempCallableInfo[0] > 0) || (TempCallableInfo.Count == 2 && TempCallableInfo[1] > 0);
    }
  
    /******************** Z3 METHODS: ***********************/

    private async Task<DafnyDocument> GenerateProgramZ3OutputTest(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      _notificationPublisher.Started(textDocument);
      TextWriter originalOut = Console.Out;
      StringWriter stringw = new StringWriter();
      Console.SetOut(stringw);
      _verifier.SetZ3OutputOption("RefinementProof", "", "RefinementNext");
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      Console.SetOut(originalOut);
      Console.WriteLine(">>>>>>>>>>>>>>>> Now we print the stream writer: <<<<<<<<<<<<<<");
      Console.WriteLine(stringw.ToString());
      Console.WriteLine(">>>>>>>>>>>>>>>> Stream writer printed: <<<<<<<<<<<<<<");
      string pattern = @"\[quantifier_instances\] (?<FileName>\w+)dfy(?<CallableName>\w*)\.(?<Line>\d+):\d+ : *(?<Count>\d+) :";
      SortedDictionary<Tuple<string, string>, int> Z3Information = new SortedDictionary<Tuple<string, string>, int>();
      foreach (Match match in Regex.Matches(stringw.ToString(), pattern)){ 
          GroupCollection groups = match.Groups;
          Console.WriteLine("Filename: " + groups["FileName"].ToString()+" has count " + groups["Count"].ToString() + " at line" + groups["Line"].ToString() + " (Callable is " + groups["CallableName"].ToString() + ")");
          var info = Tuple.Create<string, string>(groups["FileName"].ToString(), groups["Line"].ToString());
          if(Z3Information.ContainsKey(info)){
            Z3Information[info] += int.Parse(groups["Count"].ToString());
          }
          else{
            Z3Information.Add(info, int.Parse(groups["Count"].ToString()));
          }
      }
      
      if(Z3Information.Count == 0) return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
      
      int MaxCount = Z3Information.Values.Max();
      var KeyOfMax = Z3Information.FirstOrDefault(x => x.Value == MaxCount).Key;
      Console.WriteLine("****************Time out detected!*******************");
      Console.WriteLine("Line " + KeyOfMax.Item2 + " of file " + KeyOfMax.Item1 + ".dfy might be the cause of timeout: it's been called " + MaxCount + " times");
      _verifier.ReleaseZ3Option();
      /*
      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      foreach(var o in DafnyOptions.O.ProverOptions){
        Console.WriteLine("~~~~~~~~~~~~~~" + o);
      }
      _verifier.SetZ3OutputOption("RefinementProof", "Test", "TimeoutTestMethod");
      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      foreach(var o in DafnyOptions.O.ProverOptions){
        Console.WriteLine("~~~~~~~~~~~~~~" + o);
      }
      _verifier.ReleaseZ3Option();*/
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
  
    private async Task<DafnyDocument> GenerateProgramZ3Timeout(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      _notificationPublisher.Started(textDocument);
      List<Tuple<string, string, string> > callableName = new List<Tuple<string, string, string> >();
      List<long> callableTime = new List<long>();
      Dictionary<ICallable, long> callableTotalTime = new Dictionary<ICallable, long>();
      // List<int> timeoutLines = new List<int>();
      var serializedCounterExamples = await _verifier.VerifyAsyncRecordInfo(program, cancellationToken, callableName, callableTime);
      
      var TimeoutFound = false;
      for(int i = 0; i < callableName.Count; ++i){
        string ModuleName = callableName[i].Item1;
        string ClassName = callableName[i].Item2;
        string LemmaName = callableName[i].Item3;
        var TargetCallable = DocumentPrinter.GetCallable(program, ModuleName, ClassName, LemmaName);
        if(TargetCallable == null) continue;
        // If there is no timeout, we store its verification time in a dictionary for publication
        if(callableTime[i] > 0){
          if(callableTotalTime.ContainsKey(TargetCallable)){
            callableTotalTime[TargetCallable] += callableTime[i];
          }
          else{
            callableTotalTime.Add(TargetCallable, callableTime[i]);
          }
          continue;
        }
        // The dictionary only stores time for none-time-out callable, so if there is a timeout, remove it from the dictionary
        else if(callableTotalTime.ContainsKey(TargetCallable)){
          callableTotalTime.Remove(TargetCallable);
        }
        TimeoutFound = true;
        Token CallableTimeoutToken = new Token();
        DocumentModifier.CopyToken(TargetCallable.Tok, CallableTimeoutToken);
        errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = CallableTimeoutToken, message = "This callable causes a time-out", source = MessageSource.Other});
        
        // First, perform search on Z3
        TextWriter originalOut = Console.Out;
        StringWriter stringw = new StringWriter();
        Console.SetOut(stringw);
        var TempErrorReporter = new BuildErrorReporter();
        var TempProgram = await _parser.ParseAsync(textDocument, TempErrorReporter, cancellationToken);
        var TempCompilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, TempProgram, cancellationToken);
        _verifier.SetZ3OutputOption(ModuleName, ClassName, LemmaName);
        var TempSerializedCounterExamples = await _verifier.VerifyAsync(TempProgram, cancellationToken);
        _verifier.ReleaseZ3Option();
        Console.SetOut(originalOut);
        // Console.WriteLine(stringw.ToString());
        string pattern = @"\[quantifier_instances\] (?<FileName>\w+)dfy(?<CallableName>\w*)\.(?<Line>\d+):\d+ : *(?<Count>\d+) :";
        string patternPrelude = @"\[quantifier_instances\] DafnyPreludebpl\.(?<Line>\d+):\d+ : *(?<Count>\d+) :";
        Dictionary<Tuple<string, string>, long> Z3Information = new Dictionary<Tuple<string, string>, long>();
        Dictionary<int, long> PreludeInformation = new Dictionary<int, long>();
        foreach (Match match in Regex.Matches(stringw.ToString(), pattern)){ 
          GroupCollection groups = match.Groups;
          // Console.WriteLine("Filename: " + groups["FileName"].ToString()+" has count " + groups["Count"].ToString() + " at line" + groups["Line"].ToString() + " (Callable is " + groups["CallableName"].ToString() + ")");
          var info = Tuple.Create<string, string>(groups["FileName"].ToString(), groups["Line"].ToString());
          if(Z3Information.ContainsKey(info)){
            Z3Information[info] += long.Parse(groups["Count"].ToString());
          }
          else{
            Z3Information.Add(info, long.Parse(groups["Count"].ToString()));
          }
        }
        foreach (Match match in Regex.Matches(stringw.ToString(), patternPrelude)){
          GroupCollection groups = match.Groups;
          int lineNum = int.Parse(groups["Line"].ToString());
          long count = long.Parse(groups["Count"].ToString());
          if(PreludeInformation.ContainsKey(lineNum)){
            PreludeInformation[lineNum] += count;
          }
          else{
            PreludeInformation.Add(lineNum, count);
          }
        }
        bool Z3InformationUseful = false;
        if(Z3Information.Count != 0){
          long MaxCount = Z3Information.Values.Max();
          var KeyOfMax = Z3Information.FirstOrDefault(x => x.Value == MaxCount).Key;
          string m = "Line " + KeyOfMax.Item2 + " of file " + KeyOfMax.Item1 + ".dfy might be the cause of timeout: it's been called " + MaxCount + " times";
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = CallableTimeoutToken, message = m, source = MessageSource.Other});
          if(MaxCount > 10000) Z3InformationUseful = true;
        }
        if(PreludeInformation.Count != 0){
          long MaxCount = PreludeInformation.Values.Max();
          int KeyOfMax = PreludeInformation.FirstOrDefault(x => x.Value == MaxCount).Key;
          string m = "Line " + KeyOfMax + " of DafnyPrelude.bpl might be the cause of timeout: it's been called " + MaxCount + " times";
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = CallableTimeoutToken, message = m, source = MessageSource.Other});
          if(MaxCount > 10000) Z3InformationUseful = true;
        }
        if(Z3InformationUseful) continue;
        // If Z3 cannot provide useful information, we then perform binary search
        if((TargetCallable.WhatKind != "lemma")) continue;
        int begin = 0;    // Beginning of the target search range
        int end = DocumentPrinter.GetStatementCount(program, ModuleName, ClassName, LemmaName);      // End of the target search range
        if(end == 0){
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = CallableTimeoutToken, message = "The post-condition of this lemma causes a time-out", source = MessageSource.Other});
          continue;
        }
        while(begin < end){
          int middle = (begin + end) / 2;
          var TimeoutResultTask = TruncateAndCheckTimeOut(textDocument, middle, ModuleName, LemmaName, ClassName, cancellationToken);
          bool NoTimeout = await TimeoutResultTask;
          if(NoTimeout){
            begin = middle + 1;
          }
          else{
            end = middle;
          }
        }
        int TargetLine = begin - 1;
        var Target = DocumentPrinter.GetStatement(program, ModuleName, ClassName, LemmaName,TargetLine);
        if(Target != null){
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(Target.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "This line causes a time-out", source = MessageSource.Other});
        }
        else{
          // var TargetLemma = DocumentPrinter.GetCallable(program, ModuleName, ClassName, LemmaName);
          Token TimeoutToken = new Token();
          DocumentModifier.CopyToken(TargetCallable.Tok, TimeoutToken);
          errorReporter.AllMessages[ErrorLevel.Error].Add(new ErrorMessage {token = TimeoutToken, message = "The post-condition of this lemma causes a time-out", source = MessageSource.Other});
        }
      }

      // Now, we report verification time of each callable
      foreach(var item in callableTotalTime){
        var TargetCallable = item.Key;
        var Time = item.Value;
        Token TimeoutToken = new Token();
        DocumentModifier.CopyToken(TargetCallable.Tok, TimeoutToken);
        errorReporter.AllMessages[ErrorLevel.Info].Add(new ErrorMessage {token = TimeoutToken, message = Time + " ms spent on verifying this callable", source = MessageSource.Other});
      }
      _notificationPublisher.Completed(textDocument, (serializedCounterExamples == null) && (!TimeoutFound));
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }
    /**/
  
  
  
  
  }

  public class MultiTreadHelper{
    private readonly IDafnyParser _parser;
    private readonly ISymbolResolver _symbolResolver;
    private readonly IProgramVerifier _verifier;
    private TextDocumentItem _textDocument;
    private string _ModuleName;
    private string _ClassName;
    private string _LemmaName;
    private int _middle1;
    private int _middle2;
    private CancellationToken _cancellationToken;
    public bool result1 = false;
    public bool result2 = false;

    public MultiTreadHelper(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      TextDocumentItem textDocument,
      string ModuleName,
      string ClassName,
      string LemmaName,
      int middle1,
      int middle2,
      CancellationToken cancellationToken
    ) {
      _parser = parser;
      _symbolResolver = symbolResolver;
      _verifier = verifier;
      _textDocument = textDocument;
      _ModuleName = ModuleName;
      _ClassName = ClassName;
      _LemmaName = LemmaName;
      _middle1 = middle1;
      _middle2 = middle2;
      _cancellationToken = cancellationToken;
    }

    public void TruncateAndCheckFirstHalf(){
      List<Tuple<string, string, string> > TempCallableName = new List<Tuple<string, string, string> >();
      List<long> TempCallableInfo = new List<long>();
      var TempErrorReporter = new BuildErrorReporter();
      Console.WriteLine("============= Start " + _middle1 + " thread ID is :" + Thread.CurrentThread.ManagedThreadId);
      var TempProgram =  _parser.ParseAsync(_textDocument, TempErrorReporter, _cancellationToken).Result;
      Console.WriteLine(">>>>> Parse Start: " + _middle1);
      var TempCompilationUnit = _symbolResolver.ResolveSymbolsAsync(_textDocument, TempProgram, _cancellationToken).Result;
      Console.WriteLine(">>>>> Resolve Start: " + _middle1);
      DocumentModifier.RemoveLemmaLinesFlattened(TempProgram,_LemmaName,_ClassName,_ModuleName,_middle1);
      // Console.WriteLine(">>>>>>>>>>> After truncating, current lemma "+LemmaName + " has #statement " + DocumentPrinter.GetStatementCount(TempProgram, ModuleName, ClassName, LemmaName));
      var temp = _verifier.VerifyAsyncRecordInfoSpecifyName(TempProgram, _cancellationToken, TempCallableName, TempCallableInfo, _ModuleName,_ClassName,_LemmaName).Result;
      result1 = (TempCallableInfo.Count == 0 || TempCallableInfo[0] > 0);
    }
    
    public void TruncateAndCheckSecondHalf(){
      List<Tuple<string, string, string> > TempCallableName = new List<Tuple<string, string, string> >();
      List<long> TempCallableInfo = new List<long>();
      var TempErrorReporter = new BuildErrorReporter();
      Console.WriteLine("============= Start " + _middle2 + " thread ID is :" + Thread.CurrentThread.ManagedThreadId);
      var TempProgram =  _parser.ParseAsync(_textDocument, TempErrorReporter, _cancellationToken).Result;
      Console.WriteLine(">>>>> Parse Start: " + _middle2);
      var TempCompilationUnit = _symbolResolver.ResolveSymbolsAsync(_textDocument, TempProgram, _cancellationToken).Result;
      Console.WriteLine(">>>>> Resolve Start: " + _middle2);
      DocumentModifier.RemoveLemmaLinesFlattened(TempProgram,_LemmaName,_ClassName,_ModuleName,_middle2);
      // Console.WriteLine(">>>>>>>>>>> After truncating, current lemma "+LemmaName + " has #statement " + DocumentPrinter.GetStatementCount(TempProgram, ModuleName, ClassName, LemmaName));
      var temp = _verifier.VerifyAsyncRecordInfoSpecifyName(TempProgram, _cancellationToken, TempCallableName, TempCallableInfo, _ModuleName,_ClassName,_LemmaName).Result;
      result2 = (TempCallableInfo.Count == 0 || TempCallableInfo[0] > 0);
    }
  }
}
