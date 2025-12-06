package br.ufrn.library.exception;

public class UserNotFoundException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /*@ pure @*/
    public UserNotFoundException(String message) {
        super(message);
    }
}