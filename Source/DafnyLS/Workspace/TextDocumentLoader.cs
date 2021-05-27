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
      // DocumentPrinter.OutputProgramInfo(program);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      DocumentPrinter.OutputProgramInfo(program);
      var serializedCounterExamples = await VerifyIfEnabled(textDocument, program, verify, cancellationToken);
      // DocumentPrinter.OutputProgramInfo(program);
      DocumentPrinter.OutputErrorInfo(errorReporter);
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
  }
}
