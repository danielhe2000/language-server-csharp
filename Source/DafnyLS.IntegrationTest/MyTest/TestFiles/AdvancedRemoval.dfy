module module1 {
    lemma foo() 
    {
        assert true;
        assert true;
        {
            assert true;
            assert false;
        }
        assert true;
    }

}
