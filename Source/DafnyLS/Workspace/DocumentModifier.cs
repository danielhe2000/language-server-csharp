using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
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
    }
}