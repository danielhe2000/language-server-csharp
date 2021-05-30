module module1 {
    lemma foo() 
    {
        var a := 1;
        if(a == 1){
            assert true;
        }
        else if(a == 2){
            assert false;
        }
    }
}




/*module module1 {
    lemma bar(){
        assert true;
    }

    lemma foo() 
    {
        bar();
        if(1==1){
            if(2==2){
                assert true;
                if(3!=3){
                    assert false;
                }
            }
            assert true;
            assert false;
        }
        assert true;
        while(false){
            assert true;
            assert false;
        }
        assert true;
        {
            assert true;
            assert false;
        }
        forall a | a == 1 ensures a == 1{
            assert true;
            assert false;
            while(false){
                assert true;
                assert false;
            }
        }
    }
}*/