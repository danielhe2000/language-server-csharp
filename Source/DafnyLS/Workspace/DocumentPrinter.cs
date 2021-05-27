using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using System.Linq;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace{
    public class DocumentPrinter{
        private static void PrintStatementInfo(Statement Stm, string Parent, int StmtCount, int IndentLvl){
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
                    var MethodCallable = (Method)callable;
                    var Body = MethodCallable.methodBody;
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
        }
    }
}