﻿using MediatR;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server.Capabilities;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP Synchronization handler for document based events, such as change, open, close and save.
  /// The documents are managed using an implementaiton of <see cref="IDocumentDatabase"/>.
  /// </summary>
  public class DafnyTextDocumentHandler : TextDocumentSyncHandler {
    private const string LanguageId = "dafny";

    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;
    private readonly IDiagnosticPublisher _diagnosticPublisher;

    public DafnyTextDocumentHandler(
        ILogger<DafnyTextDocumentHandler> logger, IDocumentDatabase documents, IDiagnosticPublisher diagnosticPublisher
    ) : base(TextDocumentSyncKind.Incremental, CreateRegistrationOptions()) {
      _logger = logger;
      _documents = documents;
      _diagnosticPublisher = diagnosticPublisher;
    }

    private static TextDocumentSaveRegistrationOptions CreateRegistrationOptions() {
      return new TextDocumentSaveRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage(LanguageId)
      };
    }

    public override TextDocumentAttributes GetTextDocumentAttributes(DocumentUri uri) {
      return new TextDocumentAttributes(uri, LanguageId);
    }

    public override async Task<Unit> Handle(DidOpenTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received open notification {}", notification.TextDocument.Uri);
      var document = await _documents.LoadDocumentAsync(notification.TextDocument, cancellationToken);
      _diagnosticPublisher.PublishDiagnostics(document, cancellationToken);
      return Unit.Value;
    }

    public override Task<Unit> Handle(DidCloseTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received close notification {}", notification.TextDocument.Uri);
      var document = _documents.CloseDocument(notification.TextDocument);
      if(document != null) {
        _diagnosticPublisher.HideDiagnostics(document);
      }
      return Unit.Task;
    }

    public override async Task<Unit> Handle(DidChangeTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received change notification {}", notification.TextDocument.Uri);
      // notification is the change of the document
      var document = await _documents.UpdateDocumentAsync(notification, cancellationToken);
      if(document != null) {
        _diagnosticPublisher.PublishDiagnostics(document, cancellationToken);
      }
      return Unit.Value;
    }

    public override async Task<Unit> Handle(DidSaveTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received save notification {}", notification.TextDocument.Uri);
      var document = await _documents.SaveDocumentAsync(notification.TextDocument, cancellationToken);
      if(document != null) {
        _diagnosticPublisher.PublishDiagnostics(document, cancellationToken);
      }
      return Unit.Value;
    }
  }
}
