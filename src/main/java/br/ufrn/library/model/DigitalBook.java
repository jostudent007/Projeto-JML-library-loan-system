package br.ufrn.library.model;

public class DigitalBook extends Book {
    
    /*@ public normal_behavior
      @   requires title != null && title.length() > 0;
      @   requires author != null && author.length() > 0;
      @   requires isbn != null && isbn.length() > 0;
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   ensures this.isbn == isbn;
      @*/
    public DigitalBook(String title, String author, String isbn) {
        super(title, author, isbn);
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public void download() {
        // COMENTADO PARA VERIFICAÇÃO JML:
        // System.out.println("Downloading digital book: " + getTitle());
    }

    /*@ also
      @   ensures \result == true;
      @*/
    @Override
    public /*@ pure @*/ boolean isAvailableForLoan() {
        return true;
    }

    /*@ also
      @   assignable \nothing;
      @*/
    @Override
    public void registerLoan() {
        // Implementação vazia intencional
    }

    /*@ also
      @   assignable \nothing;
      @*/
    @Override
    public void registerReturn() {
        // Implementação vazia intencional
    }
}