using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using System.Linq;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace{
    public class DocumentModifier{
        private void ModifyProgram(Dafny.Program program){
            Console.WriteLine("*************** Print Program Info ****************");
            Console.WriteLine("Program name: " + program.FullName);

            Console.WriteLine("Program module signature size: " + program.ModuleSigs.Count);
            int module_count = 0;
            foreach(ModuleDefinition module in program.ModuleSigs.Keys){
                Console.WriteLine("   Module "+module_count+" full name: " + module.FullName);
                Console.WriteLine("   Module "+module_count+" include size: " + module.Includes.Count);
                Console.WriteLine("   Module "+module_count+" TopLevelDecls size: " + module.TopLevelDecls.Count);

                Console.WriteLine("   Module "+module_count+" call graph size: " + module.CallGraph.vertices.Count);
                int callable_count = 0;
                foreach(ICallable callable in module.CallGraph.vertices.Keys){
                var corresVertex = module.CallGraph.vertices[callable];
                Console.WriteLine("     Callable "+callable_count+" kind: " + callable.WhatKind);
                Console.WriteLine("     Callable "+callable_count+" name: " + callable.NameRelativeToModule);
                Console.WriteLine("     Callable "+callable_count+" #succesor: " + corresVertex.Successors.Count);
                if(callable.WhatKind == "lemma"){
                    var MethodCallable = (Method)callable;
                    var Body = MethodCallable.methodBody;
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
    }
}