module module1 {
    method foo() {
        assert 1 == 1;
        assert true;
        assert false;
    }

    method bar() {
        assert 1 == 1;
        assert true;
        foo();
    }
}

module module2 {
    method foo() {
        assert 1 == 1;
        assert true;
        assert false;
    }

    method bar() {
        assert 1 == 1;
        assert true;
        foo();
    }
}