module module1 {
    datatype Step = GetStep(key:int, value:int) | PutStep(key:int, value:int) | OtherStep(key:int, value: int)
    
    lemma onlydeclair(){
        var a := 1;
        var b := 2;
    }

    lemma foo() 
    {
        var a := PutStep(2,3);
        assert true;
        match a{
            case GetStep(key, value) =>{
                assert key == 2;
                assert value == 3;
            }
            case PutStep(key, value) =>{
                assert key == 2;
                if(value != 3){
                    assert true;
                    assert true;
                }
                else{
                    assert value != 3;
                }
            }
            case OtherStep(key, value) =>{
                assert key == 2;
                assert value == 3;
            }
        }
        assert true;
    }

    lemma Lemma_LEnvironmentInitEstablishesInvariant<K, V>(a:map<K,V>, b:map<K,V>)
        requires a == b
        requires a == b
        ensures  a == b
    {
    }
}
