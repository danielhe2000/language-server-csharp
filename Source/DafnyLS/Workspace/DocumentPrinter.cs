using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
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
            Console.WriteLine("       " + Indent + Parent + ", statement " + StmtCount + " type " + GetStatementType(Stm));
            // Console.WriteLine("       " + Indent + Parent + ", statement " + StmtCount + " #expression " + SubExps.Count());
            /*
            if(SubExps.Count() > 0){
                var ExpsCount = 0;
                foreach(var Sub in SubExps){
                    Console.WriteLine("       " + Indent + Parent + ", statement " + StmtCount + " expression" + ExpsCount + " is " + Sub.Type.AsText());
                    ++ExpsCount;
                }
            }*/
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
                    if(Body == null) return;
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
            Console.WriteLine(">>>>>>>>>>>>>>>>> Print error message!!! <<<<<<<<<<<<<<<<<<<<");
            foreach(var message in errorReporter.AllMessages[ErrorLevel.Error]){
                Console.WriteLine("Error Message" + errorCount + " message: " + message.message);
                Console.WriteLine("Error Message" + errorCount + " location: " + message.token.GetLspRange().Start + " to " + message.token.GetLspRange().End);
                Console.WriteLine("Error Message" + errorCount + " source: " + message.source.ToString());
                ++errorCount;
            }
            Console.WriteLine(">>>>>>>>>>>>>>>>> Error message printed!!! <<<<<<<<<<<<<<<<<");
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
                return "Block Statement";           // Can be continued
            } else if (stmt is IfStmt) {
                return "If Statement";              // Can be continued (if has a block)
            } else if (stmt is AlternativeStmt) {
                return "Alternative Statement";
            } else if (stmt is WhileStmt) {
                return "While Statement";           // Can be continued (if has a block)
            } else if (stmt is AlternativeLoopStmt) {
                return "Alternative Loop Statement";
            } else if (stmt is ForallStmt) {
                return "Forall Statement";          // Can be continued (if has a block)
            } else if (stmt is CalcStmt) {
                return "Calc Statement";
                // calc statements have the unusual property that the last line is duplicated.  If that is the case (which
                // we expect it to be here), we share the clone of that line as well.
            } else if (stmt is NestedMatchStmt) {   // In fact, the match statements are interpreted as this, so this will count
                return "Nested Match Statement";
            } else if (stmt is MatchStmt) {         // Need to double check on this. Must check if this can continue
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
    
        public static int GetStatementCount(Dafny.Program program, string ModuleName, string LemmaName){
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != ModuleName) continue;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    if(callable.WhatKind != "lemma" || callable.NameRelativeToModule != LemmaName) continue;
                    var LemmaCallable = (Lemma)callable;
                    var Body = LemmaCallable.Body.Body;
                    if(Body == null) return 0;
                    return GetStatementCountHelper(Body);
                }
            }
            return 0;
        }

        private static int GetStatementCountHelper(IEnumerable<Statement> Body){
            int result = 0;
            foreach(var Stm in Body){
                if(Stm is VarDeclPattern) continue;
                if(Stm is ForallStmt){
                    result += 1;
                    result += GetStatementCountHelper(Stm.SubStatements);
                }
                else if(Stm is BlockStmt || Stm is IfStmt || Stm is WhileStmt || Stm is NestedMatchStmt || Stm is MatchStmt){
                    result += GetStatementCountHelper(Stm.SubStatements);
                }
                else{
                    result += 1;
                }
            }
            return result;
        }

        public static Statement GetStatement(Dafny.Program program, string ModuleName, string LemmaName, int Location){
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != ModuleName) continue;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    if(callable.WhatKind != "lemma" || callable.NameRelativeToModule != LemmaName) continue;
                    var LemmaCallable = (Lemma)callable;
                    var Body = LemmaCallable.Body.Body;
                    var End = GetStatementHelper(Body, Location, out var Result);
                    return Result;
                }
            }
            return null;
        }

        public static ICallable GetCallable(Dafny.Program program, string ModuleName, string LemmaName){
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != ModuleName) continue;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    if(callable.WhatKind != "lemma" || callable.NameRelativeToModule != LemmaName) continue;
                    return callable;
                }
            }
            return null;
        }
        
        private static int GetStatementHelper(IEnumerable<Statement> Body, int Location, out Statement Result){
            Result = null;
            foreach(var Stm in Body){
                if(Stm is VarDeclPattern) continue;
                if(Location == 0) {
                    if(Stm is BlockStmt || Stm is IfStmt || Stm is WhileStmt || Stm is NestedMatchStmt || Stm is MatchStmt){
                        Location = GetStatementHelper(Stm.SubStatements, Location, out Result);
                        if(Result != null){
                            return 0;
                        }
                    }
                    else{
                        Result = Stm;
                        return 0;
                    }
                }
                if(Stm is BlockStmt || Stm is IfStmt || Stm is WhileStmt || Stm is ForallStmt || Stm is NestedMatchStmt || Stm is MatchStmt){
                    if(Stm is ForallStmt){
                        --Location;
                    }
                    Location = GetStatementHelper(Stm.SubStatements, Location, out Result);
                    if(Location == 0 && Result != null){
                        return 0;
                    }
                }
                else{
                    -- Location;
                }
            }
            return Location;
        }

    }
}