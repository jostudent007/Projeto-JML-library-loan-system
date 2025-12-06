package br.ufrn.library.model;

public abstract class Book {
    
    /*@ spec_public @*/ protected String title;
    /*@ spec_public @*/ protected String author;
    /*@ spec_public @*/ protected String isbn;
    /*@ spec_public @*/ protected boolean available;

    public Book(String title, String author, String isbn) {
        this.title = title;
        this.author = author;
        this.isbn = isbn;
        this.available = true;
    }

    public String getTitle() { return title; }

    public String getAuthor() { return author; }

    public String getIsbn() { return isbn; }

    public boolean isAvailable() { return available; }
    
    public abstract boolean isAvailableForLoan();

    public void setAvailable(boolean available) {
        this.available = available;
    }
    
    // Métodos de estado para o empréstimo
    public void registerLoan() {
        this.available = false;
    }

    public void registerReturn() {
        this.available = true;
    }

}