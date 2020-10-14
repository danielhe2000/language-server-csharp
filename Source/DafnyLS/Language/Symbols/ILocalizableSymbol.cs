﻿using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using AstNode = System.Object;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents a symbol that can be localized within the document.
  /// </summary>
  internal interface ILocalizableSymbol : ISymbol {
    /// <summary>
    /// Gets the syntax node of the AST> that declared this symbol.
    /// </summary>
    AstNode Node { get; }

    /// <summary>
    /// Gets the text representation of the symbol.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The detail text of the symbol.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    string GetDetailText(CancellationToken cancellationToken);

    /// <summary>
    /// Gets the range that should be respected for hovering over the symbol.
    /// </summary>
    /// <returns>A range representing the hoverable region (i.e. the identifier of a method).</returns>
    Range GetHoverRange();
  }
}
