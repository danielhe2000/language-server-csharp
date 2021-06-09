using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.IO;
using System.Linq;
using System.Threading;
using System;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;


namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class TimeoutTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;
    private const int MaxTestExecutionTimeMs = 120000;
    private TestDiagnosticReceiver _diagnosticReceiver;
    private IDictionary<string, string> _configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      _configuration = configuration;
      _diagnosticReceiver = new TestDiagnosticReceiver();
      _client = await InitializeClient(options => options.OnPublishDiagnostics(_diagnosticReceiver.DiagnosticReceived));
    }

    protected override IConfiguration CreateConfiguration() {
      return _configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(_configuration).Build();
    }

    [TestMethod]
    [Timeout(MaxTestExecutionTimeMs)]
    public async Task VerySimpleCloningTest() {
      var source = @"
module module1 {
    lemma foo() {
        assert false;
        assert 1 == 1;
        assert true;
        assert 2 == 2;
        assert true;
        assert 3 == 3;
    }
}".Trim();
    //var documentItem = await CreateTextDocumentFromFileAsync("GenericSort.dfy");
      var documentItem = CreateTestDocument(source);
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      
      _client.OpenDocument(documentItem);
      var changeReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var changeDiagnostics = changeReport.Diagnostics.ToArray();
      Assert.AreEqual(0, changeDiagnostics.Length);
      _client.SaveDocument(documentItem);
      var saveReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Console.WriteLine("Number of errors: " + saveDiagnostics.Length);
      for(int i = 0; i < saveDiagnostics.Length; ++i){
        var Diagnostic = saveDiagnostics[i];
        Assert.AreEqual("Other", Diagnostic.Source);
        Assert.AreEqual(DiagnosticSeverity.Error, Diagnostic.Severity);
        Console.WriteLine(Diagnostic.Message);
        Console.WriteLine(Diagnostic.Range.Start);
        Console.WriteLine(Diagnostic.Range.End);
      }
    }

    [TestMethod]
    [Timeout(MaxTestExecutionTimeMs)]
    public async Task TimeoutWithBoogieTest() {
      var filePath = Path.Combine("MyTest", "TestFiles", "TimeoutsModified.dfy");
      var source = await File.ReadAllTextAsync(filePath, CancellationToken);
      var documentItem = CreateTestDocument(source);
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      _client.OpenDocument(documentItem);
      var changeReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      _client.SaveDocument(documentItem);
      var saveReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Console.WriteLine("Number of errors: " + saveDiagnostics.Length);
      for(int i = 0; i < saveDiagnostics.Length; ++i){
        var Diagnostic = saveDiagnostics[i];
        if(Diagnostic.Severity != DiagnosticSeverity.Error) continue;
        Console.WriteLine(Diagnostic.Message);
        Console.WriteLine(Diagnostic.Range.Start);
        Console.WriteLine(Diagnostic.Range.End);
      }
    }

    [TestMethod]
    [Timeout(MaxTestExecutionTimeMs)]
    public async Task ClassTest() {
      var filePath = Path.Combine("MyTest", "TestFiles", "ClassTest.dfy");
      var source = await File.ReadAllTextAsync(filePath, CancellationToken);
      var documentItem = CreateTestDocument(source);
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      _client.OpenDocument(documentItem);
      var changeReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      _client.SaveDocument(documentItem);
      var saveReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Console.WriteLine("Number of errors: " + saveDiagnostics.Length);
      for(int i = 0; i < saveDiagnostics.Length; ++i){
        var Diagnostic = saveDiagnostics[i];
        if(Diagnostic.Severity != DiagnosticSeverity.Error) continue;
        Console.WriteLine(Diagnostic.Message);
        Console.WriteLine(Diagnostic.Range.Start);
        Console.WriteLine(Diagnostic.Range.End);
      }
    }

    public class TestDiagnosticReceiver {
      private readonly SemaphoreSlim _availableDiagnostics = new SemaphoreSlim(0);
      private readonly ConcurrentQueue<PublishDiagnosticsParams> _diagnostics = new ConcurrentQueue<PublishDiagnosticsParams>();

      public void DiagnosticReceived(PublishDiagnosticsParams request) {
        _diagnostics.Enqueue(request);
        _availableDiagnostics.Release();
      }

      public async Task<PublishDiagnosticsParams> AwaitNextPublishDiagnostics(CancellationToken cancellationToken) {
        await _availableDiagnostics.WaitAsync(cancellationToken);
        if(_diagnostics.TryDequeue(out var diagnostics)) {
          return diagnostics;
        }
        throw new System.InvalidOperationException("got a signal for a received diagnostic but it was not present in the queue");
      }
    }

  }
}
