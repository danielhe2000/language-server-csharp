using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using System.Linq;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace{
    public class DocumentModifier{

        // private BlockStmt ClonedStmt;
        // private Cloner cloner = new Cloner();
        // private string _moduleName;
        // private string _callableName;
        /*
        public DocumentModifier(Dafny.Program program, string ModuleName, string CallableName){
            _moduleName = ModuleName;
            _callableName = CallableName;
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != _moduleName) continue;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    if(callable.NameRelativeToModule != _callableName) continue;
                    var LemmaCallable = (Lemma)callable;
                    var Body = LemmaCallable.methodBody;
                    // Console.WriteLine("********** Print Original Statement Info ************");
                    // Console.WriteLine("Cloned Statement count: " + Body.Body.Count);
                    for(int i = 0; i < Body.Body.Count; ++ i){
                        DocumentPrinter.PrintStatementInfo(Body.Body[i], "Test ", i, 0);
                    }
                    ClonedStmt = cloner.CloneBlockStmt(Body);
                    // Console.WriteLine("********** Print Cloned Statement Info ************");
                    // Console.WriteLine("Cloned Statement count: " + ClonedStmt.Body.Count);
                    for(int i = 0; i < ClonedStmt.Body.Count; ++ i){
                        DocumentPrinter.PrintStatementInfo(ClonedStmt.Body[i], "Test ", i, 0);
                    }
                    break;
                }
            }
        }*/
        /*
        public void RestoreProgram(Dafny.Program program){
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != _moduleName) continue;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    if(callable.NameRelativeToModule != _callableName) continue;
                    var LemmaCallable = (Lemma)callable;
                    LemmaCallable.methodBody = cloner.CloneBlockStmt(ClonedStmt);
                }
            }
        }*/

        public static void RemoveLastLineOfFOO(Dafny.Program program){
            Console.WriteLine("Program module signature size: " + program.ModuleSigs.Count);
            int module_count = 0;
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                Console.WriteLine("   Module "+module_count+" full name: " + module.FullName);
                int callable_count = 0;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    var corresVertex = module.CallGraph.vertices[callable];
                    Console.WriteLine("     Callable "+callable_count+" name: " + callable.NameRelativeToModule);
                    if(callable.WhatKind == "lemma"){
                        var LemmaCallable = (Lemma)callable;
                        var Body = LemmaCallable.methodBody;
                        Console.WriteLine("     Callable "+callable_count+" #statement " + Body.Body.Count);
                        // Try to remove the last assertion of foo
                        if(callable.NameRelativeToModule == "foo"){
                            Body.Body.Remove(Body.Body.Last());
                            Console.WriteLine("     Callable "+callable_count+" #statement after deletion " + Body.Body.Count);
                        }
                    }
                    ++ callable_count;
                }
                ++module_count;
            }
        }
        public static void RemoveLemmaLines(Dafny.Program program, string LemmaName, string ModuleName, int Start){
            // Console.WriteLine("Program module signature size: " + program.ModuleSigs.Count);
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != ModuleName) continue;
                //Console.WriteLine("   Module "+module_count+" full name: " + module.FullName);
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    var corresVertex = module.CallGraph.vertices[callable];
                    // Console.WriteLine("     Callable "+callable_count+" name: " + callable.NameRelativeToModule);
                    if(callable.WhatKind != "lemma") continue;
                    if(callable.NameRelativeToModule != LemmaName) continue;
                    var LemmaCallable = (Lemma)callable;
                    var Body = LemmaCallable.methodBody;
                    // Console.WriteLine("     Callable "+callable_count+" #statement " + Body.Body.Count);
                    /*
                    if(Start >= Body.Body.Count){
                        Console.WriteLine("Cannot starting position longer than list size!");
                        return;
                    }*/
                    Body.Body.RemoveRange(Start, Body.Body.Count - Start);
                }
            }
        }

        public static void RemoveLemmaLinesFlattened(Dafny.Program program, string LemmaName, string ModuleName, int Start){
            // Console.WriteLine("Program module signature size: " + program.ModuleSigs.Count);
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                if(module.FullName != ModuleName) continue;
                //Console.WriteLine("   Module "+module_count+" full name: " + module.FullName);
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                    var corresVertex = module.CallGraph.vertices[callable];
                    // Console.WriteLine("     Callable "+callable_count+" name: " + callable.NameRelativeToModule);
                    if(callable.WhatKind != "lemma") continue;
                    if(callable.NameRelativeToModule != LemmaName) continue;
                    var LemmaCallable = (Lemma)callable;
                    var Body = LemmaCallable.methodBody;
                    int result = RemoveLemmaLinesFlattenedHelper(Body.Body, Start);
                }
            }
        }

        private static int RemoveLemmaLinesFlattenedHelper(List<Statement> Body, int Start){
            if(Body == null) return Start;
            int Count = 0;
            foreach(var Stm in Body){
                if(Stm is VarDeclPattern) continue;
                if(Start == 0){
                    Body.RemoveRange(Count, Body.Count - Count);
                    return 0;
                }
                Start = RemoveLemmaLinesFlattenedStmtHelper(Stm, Start);
                ++Count;
            }
            return Start;
        }
        
        private static int RemoveLemmaLinesFlattenedStmtHelper(Statement Stm, int Start){
            if(Stm is VarDeclPattern) return Start;
            var Type = DocumentPrinter.GetStatementType(Stm);
            if(Stm is BlockStmt){
                var BlockStm = (BlockStmt) Stm;
                if(BlockStm.Body == null) return Start;
                return RemoveLemmaLinesFlattenedHelper(BlockStm.Body, Start);
            }
            else if(Stm is WhileStmt){
                var WhileStm = (WhileStmt) Stm;
                if(WhileStm.Body == null || WhileStm.Body.Body == null) return Start;
                return RemoveLemmaLinesFlattenedHelper(WhileStm.Body.Body, Start);
            }
            else if(Stm is ForallStmt){
                var ForallStm = (ForallStmt) Stm;
                --Start;
                if(ForallStm.Body == null) return Start;
                // Forall statement body must be a block statement, so it can safely handle 0 situation
                return RemoveLemmaLinesFlattenedStmtHelper(ForallStm.Body, Start);   
            }
            else if(Stm is NestedMatchStmt){
                var NestedMatchStm = (NestedMatchStmt) Stm;
                if(NestedMatchStm.ResolvedStatement == null) return Start;
                return RemoveLemmaLinesFlattenedStmtHelper(NestedMatchStm.ResolvedStatement, Start);
            }
            else if(Stm is IfStmt){
                return RemoveLemmaLinesIfHelper((IfStmt) Stm, Start);
            }
            else if(Stm is MatchStmt){
                return RemoveLemmaLinesMatchHelper((MatchStmt)Stm, Start);
            }
            else{
                return Start - 1;
            }
        }   
        private static int RemoveLemmaLinesIfHelper(IfStmt Stm, int Start){
            if(Stm.Thn == null || Stm.Thn.Body == null) return Start;
            Start = RemoveLemmaLinesFlattenedHelper(Stm.Thn.Body, Start);
            if(Start == 0){
                Stm.Els = null;
                return 0;
            }
            else if(Stm.Els == null){
                return Start;
            }
            else{
                return RemoveLemmaLinesFlattenedStmtHelper(Stm.Els, Start);
            }
        }

        private static int RemoveLemmaLinesMatchHelper(MatchStmt Stm, int Start){
            foreach(var Case in Stm.Cases){
                if(Case.Body == null) continue;
                Start = RemoveLemmaLinesFlattenedHelper(Case.Body, Start);
            }
            return Start;
        }


    }
}