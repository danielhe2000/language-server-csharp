using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using System.Linq;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace{
    public class DocumentPrinter{
        public static void PrintStatementInfo(Statement Stm, string Parent, int StmtCount, int IndentLvl){
            var SubExps = Stm.SubExpressions;
            var SubStms = Stm.SubStatements;
            string Indent = "";
            for(int i = 0; i < IndentLvl; ++i){
                Indent += "  ";
            }
            Console.WriteLine("       " + Indent + Parent + ", statement " + StmtCount + " #expression " + SubExps.Count());
            if(SubExps.Count() > 0){
                var ExpsCount = 0;
                foreach(var Sub in SubExps){
                    Console.WriteLine("       " + Indent + Parent + ", statement " + StmtCount + " expression" + ExpsCount + " is " + Sub.Type.AsText());
                    ++ExpsCount;
                }
            }
            Console.WriteLine("       " + Indent + Parent + ", statement " + StmtCount + " #substatements " + SubStms.Count());
            
            if(SubStms.Count() > 0){
                var SubStmtCount = 0;
                foreach(var Sub in SubStms){
                    PrintStatementInfo(Sub, Parent + " statement" + StmtCount, SubStmtCount, IndentLvl + 1);
                }
                ++ SubStmtCount;
            }

        }

        private static void PrintModuleInfo(ModuleDefinition module, int module_count){
            Console.WriteLine("   Module "+module_count+" full name: " + module.FullName);
            Console.WriteLine("   Module "+module_count+" include size: " + module.Includes.Count);
            Console.WriteLine("   Module "+module_count+" TopLevelDecls size: " + module.TopLevelDecls.Count);

            Console.WriteLine("   Module "+module_count+" call graph size: " + module.CallGraph.vertices.Count);
            int CallableCount = 0;
            foreach(ICallable callable in module.CallGraph.vertices.Keys){
                var corresVertex = module.CallGraph.vertices[callable];
                Console.WriteLine("     Callable "+CallableCount+" kind: " + callable.WhatKind);
                Console.WriteLine("     Callable "+CallableCount+" name: " + callable.NameRelativeToModule);
                Console.WriteLine("     Callable "+CallableCount+" #succesor: " + corresVertex.Successors.Count);
                if(callable.WhatKind == "lemma"){
                    var LemmaCallable = (Lemma)callable;
                    var Body = LemmaCallable.methodBody;
                    Console.WriteLine("     Callable "+CallableCount+" #statement " + Body.Body.Count);
                    for(int i = 0; i < Body.Body.Count; ++ i){
                        PrintStatementInfo(Body.Body[i], "Callable "+CallableCount, i, 0);
                    }
                }
                ++ CallableCount;
            }
            if(module.EnclosingModule != null){
                Console.WriteLine("   Module "+module_count+" has an enclosing module with name: " + module.EnclosingModule.FullName);
            }
        }

        public static void OutputProgramInfo(Dafny.Program program){
            Console.WriteLine("*************** Print Program Info ****************");
            Console.WriteLine("Program name: " + program.FullName);

            Console.WriteLine("Program module signature size: " + program.ModuleSigs.Count);
            int ModuleCount = 0;
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                PrintModuleInfo(module,ModuleCount);
                ++ModuleCount;
            }
        }
    
        public static void OutputErrorInfo(ErrorReporter errorReporter){
            int errorCount = 0;
            Console.WriteLine("************** Print error message!!! **************");
            foreach(var message in errorReporter.AllMessages[ErrorLevel.Error]){
                Console.WriteLine("Error Message" + errorCount + " message: " + message.message);
                Console.WriteLine("Error Message" + errorCount + " location: " + message.token.GetLspRange().Start + " to " + message.token.GetLspRange().End);
                Console.WriteLine("Error Message" + errorCount + " source: " + message.source.ToString());
                ++errorCount;
            }
            Console.WriteLine("************** Error message printed!!! **************");
        }

        public static string GetStatementType(Statement stmt){
            if (stmt is AssertStmt) {
                return "Assert Statement";
            } else if (stmt is ExpectStmt) {
                return "Expect Statement";
            } else if (stmt is AssumeStmt) {
                return "Assume Statement";
            } else if (stmt is PrintStmt) {
                return "Print Statement";
            } else if (stmt is RevealStmt) {
                return "Reveal Statement";
            } else if (stmt is BreakStmt) {
                return "Break Statement";
            } else if (stmt is ReturnStmt) {
                return "Return Statement";
            } else if (stmt is YieldStmt) {
                return "Yield Statement";
            } else if (stmt is AssignStmt) {
                return "Assign Statement";
            } else if (stmt is DividedBlockStmt) {
                return "Divided Block Statement";
            } else if (stmt is BlockStmt) {
                return "Block Statement";
            } else if (stmt is IfStmt) {
                return "If Statement";
            } else if (stmt is AlternativeStmt) {
                return "Alternative Statement";
            } else if (stmt is WhileStmt) {
                return "While Statement";
            } else if (stmt is AlternativeLoopStmt) {
                return "Alternative Loop Statement";
            } else if (stmt is ForallStmt) {
                return "Forall Statement";
            } else if (stmt is CalcStmt) {
                return "Calc Statement";
                // calc statements have the unusual property that the last line is duplicated.  If that is the case (which
                // we expect it to be here), we share the clone of that line as well.
            } else if (stmt is NestedMatchStmt) {
                return "Nested Match Statement";
            } else if (stmt is MatchStmt) {
                return "Match Statement";
            } else if (stmt is AssignSuchThatStmt) {
                return "Assugn Such-that Statement";
            } else if (stmt is UpdateStmt) {
                return "Update Statement";
            } else if (stmt is AssignOrReturnStmt) {
                return "Assign or Return Statement";
            } else if (stmt is VarDeclStmt) {
                return "Variable Declaration Statement";
            } else if (stmt is VarDeclPattern) {
                return "Variable Declaration Pattern";
            } else if (stmt is ModifyStmt) {
                return "Modify Statement";
            } else {
                return "Unexpected Statement";
            }
        }
    }
}