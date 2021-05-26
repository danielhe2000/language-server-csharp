using Microsoft.Dafny.LanguageServer.Language;
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
      Console.WriteLine("************** Start loading the target file asynchronously!!! **************");
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      // OutputProgramInfo(program);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      OutputProgramInfo(program);
      var serializedCounterExamples = await VerifyIfEnabled(textDocument, program, verify, cancellationToken);
      // OutputProgramInfo(program);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }

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
    }

    private void OutputProgramInfo(Dafny.Program program){
      Console.WriteLine("*************** Print Program Info ****************");
      Console.WriteLine("Program name: " + program.FullName);

      Console.WriteLine("Program module signature size: " + program.ModuleSigs.Count);
      int module_count = 0;
      foreach(ModuleDefinition module in program.ModuleSigs.Keys){
        Console.WriteLine("   Module "+module_count+" full name: " + module.FullName);
        Console.WriteLine("   Module "+module_count+" include size: " + module.Includes.Count);
        Console.WriteLine("   Module "+module_count+" TopLevelDecls size: " + module.TopLevelDecls.Count);

        Console.WriteLine("   Module "+module_count+" call graph size: " + module.CallGraph.vertices.Count);
        int callable_count = 0;
        foreach(ICallable callable in module.CallGraph.vertices.Keys){
          var corresVertex = module.CallGraph.vertices[callable];
          Console.WriteLine("     Callable "+callable_count+" kind: " + callable.WhatKind);
          Console.WriteLine("     Callable "+callable_count+" name: " + callable.NameRelativeToModule);
          Console.WriteLine("     Callable "+callable_count+" #succesor: " + corresVertex.Successors.Count);
          if(callable.WhatKind == "method"){
            var MethodCallable = (Method)callable;
            var Body = MethodCallable.methodBody;
            Console.WriteLine("     Callable "+callable_count+" #statement " + Body.Body.Count);
            // Try to remove the last assertion of foo
            /*
            if(callable.NameRelativeToModule == "foo"){
              Body.Body.Remove(Body.Body.Last());
              Console.WriteLine("     Callable "+callable_count+" #statement after deletion " + Body.Body.Count);
            }*/
            /*
            if(callable.NameRelativeToModule == "foo"){
              Body.Body.Remove(Body.Body[Body.Body.Count - 2]);
              Console.WriteLine("     Callable "+callable_count+" #statement after deletion " + Body.Body.Count);
            }*/
            /*
            for(int i = 0; i < Body.Body.Count; ++ i){
              var Stm = Body.Body[i];
              var Lbls = Stm.Labels;
              bool not_null = Lbls != null;
              Console.WriteLine("       Callable "+callable_count+" statement " + i + " label count " + LList<Label>.Count(Lbls));
              if(not_null){
                Console.Write("       ");
              }
              while(Lbls != null){
                Console.Write(Lbls.Data.Name);
                Lbls = Lbls.Next;
              }
              if(not_null){
                Console.WriteLine();
              }
            }*/
          }
          ++ callable_count;
        }
        

        if(module.EnclosingModule != null){
          Console.WriteLine("   Module "+module_count+" has an enclosing module with name: " + module.EnclosingModule.FullName);
        }
       
        ++module_count;
      }
      
      Console.WriteLine("Program compile module size: " + program.CompileModules.Count);
      for(int i = 0; i < program.CompileModules.Count; ++ i){
        ModuleDefinition module = program.CompileModules[i];
        Console.WriteLine("   Compile module "+i+" full name: " + module.FullName);

      }
    }
  }
}
