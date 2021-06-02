module module1 {
    datatype Step = GetStep(key:int, value:int) | PutStep(key:int, value:int) | OtherStep(key:int, value: int)
    
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
}
