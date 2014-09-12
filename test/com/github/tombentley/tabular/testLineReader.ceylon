import ceylon.test {
    test,
    assertTrue
}

shared test
void testLineReader() {
    variable value lr = LineReader("line1\nline2\nline3".iterator().next);
    assert (exists l1 = lr.readLine(),
        l1 == "line1");
    assert (exists l2 = lr.readLine(),
        l2 == "line2");
    assert (exists l3 = lr.readLine(),
        l3 == "line3");
    assert (!lr.readLine() exists);
    
    lr = LineReader("line1\n\rline2\r\nline3".iterator().next);
    assert (exists l4 = lr.readLine(),
        l4 == "line1");
    assert (exists l5 = lr.readLine(),
        l5 == "line2");
    assert (exists l6 = lr.readLine(),
        l6 == "line3");
    assert (!lr.readLine() exists);
    
    lr = LineReader("line1\nline2\rline3".iterator().next);
    assert (exists l7 = lr.readLine(),
        l7 == "line1");
    assert (exists l8 = lr.readLine(),
        l8 == "line2");
    assert (exists l9 = lr.readLine(),
        l9 == "line3");
    assert (!lr.readLine() exists);
    
    lr = LineReader("line1\nline2\nline3".iterator().next);
    assert (exists l10 = lr.readLine(),
        l10 == "line1");
    lr.unread();
    assert (exists l11 = lr.readLine(),
        l11 == "line1");
    assert (exists l12 = lr.readLine(),
        l12 == "line2");
    assert (exists l13 = lr.readLine(),
        l13 == "line3");
    assert (!lr.readLine() exists);
}
