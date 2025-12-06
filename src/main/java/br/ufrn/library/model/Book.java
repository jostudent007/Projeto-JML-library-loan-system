package br.ufrn.library.model;

public abstract class Book {

    /*@ public invariant title != null && title.length() > 0; @*/
    /*@ public invariant author != null && author.length() > 0; @*/
    /*@ public invariant isbn != null && isbn.length() > 0; @*/
    
    /*@ spec_public @*/ protected String title;
    /*@ spec_public @*/ protected String author;
    /*@ spec_public @*/ protected String isbn;
    /*@ spec_public @*/ protected boolean available;

    /*@ public normal_behavior
      @   requires title != null && title.length() > 0;
      @   requires author != null && author.length() > 0;
      @   requires isbn != null && isbn.length() > 0;
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   ensures this.isbn == isbn;
      @   ensures this.available == true;
      @*/
    public Book(String title, String author, String isbn) {
        this.title = title;
        this.author = author;
        this.isbn = isbn;
        this.available = true;
    }

    // --- MÉTODOS PUROS ESSENCIAIS ---

    /*@ pure @*/
    public String getTitle() { return title; }

    /*@ pure @*/
    public String getAuthor() { return author; }

    /*@ pure @*/
    public String getIsbn() { return isbn; }

    /*@ pure @*/
    public boolean isAvailable() { return available; }
    
    /*@ pure @*/
    public abstract boolean isAvailableForLoan();

    public void setAvailable(boolean available) {
        this.available = available;
    }
    
    public void registerLoan() {
        this.available = false;
    }

    public void registerReturn() {
        this.available = true;
    }
}