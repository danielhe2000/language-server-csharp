module module1 {
    lemma bar(){
        assert true;
    }

    lemma foo() 
    {
        var a := 1;
        if(a==1){
            assert true;
        }
        else if(a==2){
            assert false;
        }
        else{
            assert false;
        }
    }
}