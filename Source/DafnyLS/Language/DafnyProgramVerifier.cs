using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using System;
using System.Diagnostics.CodeAnalysis;
using System.Collections.Generic;
using System.IO;
using System.Text;
using System.Threading;
using System.Diagnostics;
using System.Threading.Tasks;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// dafny-lang based implementation of the program verifier. Since it makes use of static members,
  /// any access is synchronized. Moreover, it ensures that exactly one instance exists over the whole
  /// application lifetime.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this verifier serializes all invocations.
  /// </remarks>
  public class DafnyProgramVerifier : IProgramVerifier {
    private static readonly object _initializationSyncObject = new object();
    private static readonly MessageSource VerifierMessageSource = MessageSource.Other;
    private static bool _initialized;

    private readonly ILogger _logger;
    private readonly SemaphoreSlim _mutex = new SemaphoreSlim(1);

    private DafnyProgramVerifier(ILogger<DafnyProgramVerifier> logger) {
      _logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the verifier. It ensures that global/static
    /// settings are set exactly ones.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this verifier instance.</param>
    /// <returns>A safely created dafny verifier instance.</returns>
    public static DafnyProgramVerifier Create(ILogger<DafnyProgramVerifier> logger) {
      lock(_initializationSyncObject) {
        if(!_initialized) {
          // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
          //      A dash means write to the textwriter instead of a file.
          // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
          DafnyOptions.O.ModelViewFile = "-";
          DafnyOptions.O.TimeLimit = 2;
          DafnyOptions.O.ArithMode = 5;
          DafnyOptions.O.DisableNLarith = true;
          // DafnyOptions.O.SetZ3Option("smt.qi.profile","true");
          // DafnyOptions.O.SetZ3Option("smt.qi.profile_freq","1000");
          // DafnyOptions.O.procsToCheck.Add("*RefinementNext");
          
          _initialized = true;
          logger.LogTrace("initialized the boogie verifier...");
        }
        return new DafnyProgramVerifier(logger);
      }
    }

    
    public async Task<string?> VerifyAsync(Dafny.Program program, CancellationToken cancellationToken) {
      if(program.reporter.AllMessages[ErrorLevel.Error].Count > 0) {
        // TODO Change logic so that the loader is responsible to ensure that the previous steps were sucessful.
        _logger.LogDebug("skipping program verification since the parser or resolvers already reported errors");
        return null;
      }
      await _mutex.WaitAsync(cancellationToken);
      try {
        // The printer is responsible for two things: It logs boogie errors and captures the counter example model.
        var errorReporter = program.reporter;
        var printer = new ModelCapturingOutputPrinter(_logger, errorReporter);
        ExecutionEngine.printer = printer;
        var translated = Translator.Translate(program, errorReporter, new Translator.TranslatorFlags { InsertChecksums = true });
        foreach(var (CompileName, boogieProgram) in translated) {
          cancellationToken.ThrowIfCancellationRequested();
          VerifyWithBoogie(boogieProgram, cancellationToken);
        }
        return printer.SerializedCounterExamples;
      } finally {
        _mutex.Release();
      }
    }


    public async Task<string?> VerifyAsyncRecordInfo(Dafny.Program program, CancellationToken cancellationToken) {
      if(program.reporter.AllMessages[ErrorLevel.Error].Count > 0) {
        // TODO Change logic so that the loader is responsible to ensure that the previous steps were sucessful.
        _logger.LogDebug("skipping program verification since the parser or resolvers already reported errors");
        return null;
      }
      await _mutex.WaitAsync(cancellationToken);
      try {
        // The printer is responsible for two things: It logs boogie errors and captures the counter example model.
        var errorReporter = program.reporter;
        List<Tuple<string, string, string> > callableName = new List<Tuple<string, string, string> >();
        List<long> callableInfo = new List<long>();
        var printer = new ModelCapturingOutputPrinter(_logger, errorReporter,callableName, callableInfo);
        ExecutionEngine.printer = printer;
        var translated = Translator.Translate(program, errorReporter, new Translator.TranslatorFlags { InsertChecksums = true });
        foreach(var (CompileName, boogieProgram) in translated) {
          // Console.WriteLine("------------------ Compile name of current boogie program is: " + CompileName  + "---------");
          cancellationToken.ThrowIfCancellationRequested();
          VerifyWithBoogie(boogieProgram, cancellationToken);
        }
        /*
        Console.WriteLine(">>>>>>>>>>>>>> Callable Name Count: " + callableName.Count + "<<<<<<<<<<<<<<");
        Console.WriteLine(">>>>>>>>>>>>>> Callable Info Count: " + callableInfo.Count + "<<<<<<<<<<<<<<");
        
        for(int i = 0; i < callableName.Count; ++i){
          Console.WriteLine(">>>>>>>>>>> Callable #"+i+": " + callableName[i].Item1 + "." + callableName[i].Item2 + "." + callableName[i].Item3 + ", Status: " + callableInfo[i]);
        }*/
        return printer.SerializedCounterExamples;
      } finally {
        _mutex.Release();
      }
    }
    
    public async Task<string?> VerifyAsyncRecordInfo(Dafny.Program program, CancellationToken cancellationToken, 
                                                    List<Tuple<string, string, string> > callableName, List<long> callableTime) {
      if(program.reporter.AllMessages[ErrorLevel.Error].Count > 0) {
        // TODO Change logic so that the loader is responsible to ensure that the previous steps were sucessful.
        _logger.LogDebug("skipping program verification since the parser or resolvers already reported errors");
        return null;
      }
      await _mutex.WaitAsync(cancellationToken);
      try {
        // The printer is responsible for two things: It logs boogie errors and captures the counter example model.
        var errorReporter = program.reporter;
        var printer = new ModelCapturingOutputPrinter(_logger, errorReporter, callableName, callableTime);
        ExecutionEngine.printer = printer;
        var translated = Translator.Translate(program, errorReporter, new Translator.TranslatorFlags { InsertChecksums = true });
        foreach(var (CompileName, boogieProgram) in translated) {
          cancellationToken.ThrowIfCancellationRequested();
          VerifyWithBoogie(boogieProgram, cancellationToken);
        }
        return printer.SerializedCounterExamples;
      } finally {
        _mutex.Release();
      }
      
    }

    public async Task<string?> VerifyAsyncRecordInfoSpecifyName(Dafny.Program program, CancellationToken cancellationToken, 
                                                                List<Tuple<string, string, string> > callableName, List<long> callableTime,
                                                                string ModuleName, string ClassName, string LemmaName) {
      if(program.reporter.AllMessages[ErrorLevel.Error].Count > 0) {
        // TODO Change logic so that the loader is responsible to ensure that the previous steps were sucessful.
        _logger.LogDebug("skipping program verification since the parser or resolvers already reported errors");
        return null;
      }
      await _mutex.WaitAsync(cancellationToken);
      try {
        string toBeChecked = "*" + ModuleName + "." + ClassName + "." + LemmaName;
        DafnyOptions.O.procsToCheck.Add(toBeChecked);
        // Console.WriteLine(">>>>>>>>>>>> Specify: " + toBeChecked);
        // Console.WriteLine("User Constrained Procs To Check?" + DafnyOptions.O.UserConstrainedProcsToCheck);
        
        // The printer is responsible for two things: It logs boogie errors and captures the counter example model.
        var errorReporter = program.reporter;
        var printer = new ModelCapturingOutputPrinter(_logger, errorReporter,callableName, callableTime);
        ExecutionEngine.printer = printer;
        var translated = Translator.Translate(program, errorReporter, new Translator.TranslatorFlags { InsertChecksums = true });
        foreach(var (CompileName, boogieProgram) in translated) {
          cancellationToken.ThrowIfCancellationRequested();
          VerifyWithBoogie(boogieProgram, cancellationToken);
        }
        if(DafnyOptions.O.procsToCheck.Count > 0) DafnyOptions.O.procsToCheck.RemoveAt(DafnyOptions.O.procsToCheck.Count - 1);
        return printer.SerializedCounterExamples;
      } finally {
        _mutex.Release();
      }
    }
    
    private void VerifyWithBoogie(Boogie.Program program, CancellationToken cancellationToken) {
      program.Resolve();
      program.Typecheck();
      
      ExecutionEngine.EliminateDeadVariables(program);
      ExecutionEngine.CollectModSets(program);
      ExecutionEngine.CoalesceBlocks(program);
      ExecutionEngine.Inline(program);
      // TODO Is the programId of any relevance? The requestId is used to cancel a verification.
      //      However, the cancelling a verification is currently not possible since it blocks a text document
      //      synchronization event which are serialized. Thus, no event is processed until the pending
      //      synchronization is completed.
      var uniqueId = Guid.NewGuid().ToString();
      using(cancellationToken.Register(() => CancelVerification(uniqueId))) {
        // TODO any use of the verification state?
        ExecutionEngine.InferAndVerify(program, new PipelineStatistics(), uniqueId, error => { }, uniqueId);
      }
    }

    private void CancelVerification(string requestId) {
      _logger.LogDebug("requesting verification cancellation of {}", requestId);
      ExecutionEngine.CancelRequest(requestId);
    }

    private class ModelCapturingOutputPrinter : OutputPrinter {
      private readonly ILogger _logger;
      private readonly ErrorReporter _errorReporter;
      private StringBuilder? _serializedCounterExamples;
      private List<Tuple<string, string, string> > _CallableName = new List<Tuple<string, string, string> >();
      private List<long> _CallableTime = new List<long>();
      private Stopwatch sw = new Stopwatch();

      public string? SerializedCounterExamples => _serializedCounterExamples?.ToString();

      public ModelCapturingOutputPrinter(ILogger logger, ErrorReporter errorReporter) {
        _logger = logger;
        _errorReporter = errorReporter;
      }

      public ModelCapturingOutputPrinter(ILogger logger, ErrorReporter errorReporter, 
                                         List<Tuple<string, string, string> > CallableName, List<long> CallableTime) {
        _logger = logger;
        _errorReporter = errorReporter;
        _CallableName = CallableName;
        _CallableTime = CallableTime;
      }

      public void AdvisoryWriteLine(string format, params object[] args) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> ErrorWriteLine <<<<<<<<<<<<<<<<<");
        // Console.WriteLine(format);
      }

      public void ErrorWriteLine(TextWriter tw, string s) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> ErrorWriteLine <<<<<<<<<<<<<<<<<");
        _logger.LogError(s);
      }

      public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> ErrorWriteLine <<<<<<<<<<<<<<<<<");
        _logger.LogError(format, args);
      }

      public void Inform(string s, TextWriter tw) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> Inform: \"" +s+"\" <<<<<<<<<<<<<<<<<");
        // _mutex.Wait();
        _logger.LogInformation(s);
        string pattern = @"^Verifying (?<TaskName>\w+)\$\$(?<ModuleName>\w+)\.(?<ClassName>\w+)\.(?<CallableName>\w+) \.\.\.$";
        foreach (Match match in Regex.Matches(s, pattern)){
            // Console.WriteLine(match.Value);
            GroupCollection groups = match.Groups;
            // if(groups["TaskName"].ToString() == "CheckWellformed") return;
            sw.Start();
            _CallableName.Add(Tuple.Create<string, string, string>(groups["ModuleName"].ToString(), groups["ClassName"].ToString(), groups["CallableName"].ToString()));
            // Console.WriteLine(">>>>>>>>>>>>>>>> Module name: " + groups["ModuleName"]);
            // Console.WriteLine(">>>>>>>>>>>>>>>> Callable name: " + groups["CallableName"]);
        }
        if((s == "verified" || s == "timed out" || s == "error") && _CallableName.Count - _CallableTime.Count == 1){
          if(sw.IsRunning){
            sw.Stop();
          }
          if(s == "timed out"){
            _CallableTime.Add(-1);
          }
          else{
            _CallableTime.Add(sw.ElapsedMilliseconds);
          }
          sw.Reset();
        }
      }

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> Report BPL Error <<<<<<<<<<<<<<<<<");
        // Console.WriteLine(message);
        _logger.LogError(message);
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> WriteErrorInformation <<<<<<<<<<<<<<<<<");
        CaptureCounterExamples(errorInfo);
        CaptureViolatedPostconditions(errorInfo);
      }

      private void CaptureCounterExamples(ErrorInformation errorInfo) {
        if(errorInfo.Model is StringWriter modelString) {
          // We do not know a-priori how many errors we'll receive. Therefore we capture all models
          // in a custom stringbuilder and reset the original one to not duplicate the outputs.
          _serializedCounterExamples ??= new StringBuilder();
          _serializedCounterExamples.Append(modelString.ToString());
          modelString.GetStringBuilder().Clear();
        }
      }

      private void CaptureViolatedPostconditions(ErrorInformation errorInfo) {
        _errorReporter.Error(VerifierMessageSource, errorInfo.Tok, errorInfo.Msg);
        foreach(var auxiliaryErrorInfo in errorInfo.Aux) {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if(auxiliaryErrorInfo.Tok.line > 0) {
            _errorReporter.Info(VerifierMessageSource, auxiliaryErrorInfo.Tok, auxiliaryErrorInfo.Msg);
          }
        }
      }

      public void WriteTrailer(PipelineStatistics stats) {
        // Console.WriteLine(">>>>>>>>>>>>>>>> WriteTrailer <<<<<<<<<<<<<<<<<");
      }
    }
  }
}
