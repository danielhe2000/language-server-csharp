﻿using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
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
      /*
      Console.WriteLine("************** Start loading the target file asynchronously!!! **************");
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      // DocumentModifier.RemoveLastLineOfFOO(program);
      
      var serializedCounterExamples = await VerifyIfEnabled(textDocument, program, verify, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      // DocumentPrinter.OutputErrorInfo(errorReporter);
      // var serializedCounterExamples = await VerifyTwiceWithModificationFirst(textDocument, program, verify, cancellationToken);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);*/
      if(verify){
        return await GenerateProgramAssertionTestBasic(textDocument ,cancellationToken);
      }
      else{
        return await GenerateProgramWithoutVerify(textDocument, cancellationToken);
      }
    }
    /*
    private async Task<string?> VerifyIfEnabled(TextDocumentItem textDocument, Dafny.Program program, bool verify, CancellationToken cancellationToken) {
      if(!verify) {
        Console.WriteLine("*************** Not verifying this time ****************");
        return null;
      }
      _notificationPublisher.Started(textDocument);
      Console.WriteLine("*************** Verify started ****************");
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      Console.WriteLine("*************** Verify Complete ****************");
      return serializedCounterExamples;
    }*/

    private async Task<DafnyDocument> GenerateProgramWithSmallTweak(TextDocumentItem textDocument, CancellationToken cancellationToken){
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      // Verify 
      _notificationPublisher.Started(textDocument);
      DocumentModifier.RemoveLemmaLines(program, "foo", "module1", 3);
      var serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      DocumentPrinter.OutputProgramInfo(program);
      DocumentPrinter.OutputErrorInfo(errorReporter);

      errorReporter = new BuildErrorReporter();
      program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      serializedCounterExamples = await _verifier.VerifyAsync(program, cancellationToken);
      _notificationPublisher.Completed(textDocument, serializedCounterExamples == null);
      DocumentPrinter.OutputProgramInfo(program);
      DocumentPrinter.OutputErrorInfo(errorReporter);

      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }

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
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, null);
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
  }
}
