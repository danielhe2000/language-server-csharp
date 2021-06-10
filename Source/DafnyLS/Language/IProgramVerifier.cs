using System;
using System.Threading;
using System.Threading.Tasks;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Implementations of this interface are responsible to verify the correctness of a program.
  /// </summary>
  public interface IProgramVerifier {
    /// <summary>
    /// Applies the program verification to the specified dafny program.
    /// </summary>
    /// <param name="program">The dafny program to verify.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>A string containing the counter-example if the verification failed, <c>null</c> if the program is correct.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    void SetZ3OutputOption(string ModuleName, string ClassName, string LemmaName);
    void ReleaseZ3Option();
    Task<string?> VerifyAsync(Dafny.Program program, CancellationToken cancellationToken);
    Task<string?> VerifyAsyncRecordInfo(Dafny.Program program, CancellationToken cancellationToken);
    Task<string?> VerifyAsyncRecordInfo(Dafny.Program program, CancellationToken cancellationToken, List<Tuple<string, string, string> > callableName, List<long> callableTime);
    Task<string?> VerifyAsyncRecordInfoSpecifyName(Dafny.Program program, CancellationToken cancellationToken, 
                                                                List<Tuple<string, string, string> > callableName, List<long> callableTime,
                                                                string ModuleName, String ClassName, string LemmaName);
  }
}
