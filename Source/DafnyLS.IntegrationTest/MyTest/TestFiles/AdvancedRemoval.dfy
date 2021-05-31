module module1 {
    lemma foo() 
    {
        var a := 1;
        match a{
            case 0 => assert true;
            case 2 => assert true;
            case 1 => assert false;
        }
        assert true;
        a := 2;
        
    }

    lemma bar(){
        assert true;
    }

}
