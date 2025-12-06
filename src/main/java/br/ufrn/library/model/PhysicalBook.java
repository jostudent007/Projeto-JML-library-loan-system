package br.ufrn.library.model;

public class PhysicalBook extends Book {
    
    /*@ public invariant totalCopies >= 0; @*/
    /*@ public invariant availableCopies >= 0; @*/
    /*@ public invariant availableCopies <= totalCopies; @*/
    
    /*@ spec_public @*/ private int totalCopies;
    /*@ spec_public @*/ private int availableCopies;

    /*@ public normal_behavior
      @   requires title != null && title.length() > 0;
      @   requires author != null && author.length() > 0;
      @   requires isbn != null && isbn.length() > 0;
      @   requires totalCopies >= 0;
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   ensures this.isbn == isbn;
      @   ensures this.totalCopies == totalCopies;
      @   ensures this.availableCopies == totalCopies;
      @*/
    public PhysicalBook(String title, String author, String isbn, int totalCopies) {
        super(title, author, isbn);
        
        if (totalCopies < 0) {
            throw new IllegalArgumentException("Total copies cannot be negative.");
        }
        
        this.totalCopies = totalCopies;
        this.availableCopies = totalCopies;
    }

    /*@ also
      @   ensures \result == (availableCopies > 0);
      @*/
    @Override
    public /*@ pure @*/ boolean isAvailableForLoan() {
        return availableCopies > 0;
    }

    /*@ also
      @   requires availableCopies > 0;
      @   assignable availableCopies;
      @   ensures availableCopies == \old(availableCopies) - 1;
      @   ensures totalCopies == \old(totalCopies);
      @*/
    @Override
    public void registerLoan() {
        if (availableCopies > 0) {
            this.availableCopies--;
        } else {
            throw new IllegalStateException("No copies available");
        }
    }

    /*@ also
      @   assignable availableCopies;
      @   ensures \old(availableCopies) < totalCopies ==> availableCopies == \old(availableCopies) + 1;
      @   ensures \old(availableCopies) == totalCopies ==> availableCopies == \old(availableCopies);
      @*/
    @Override
    public void registerReturn() {
        if (this.availableCopies < this.totalCopies) {
            this.availableCopies++;
        }
    }

    /*@ public normal_behavior
      @   ensures \result == totalCopies;
      @*/
    public /*@ pure @*/ int getTotalCopies() {
        return totalCopies;
    }

    /*@ public normal_behavior
      @   ensures \result == availableCopies;
      @*/
    public /*@ pure @*/ int getAvailableCopies() {
        return availableCopies;
    }

    /*@ public normal_behavior
      @   requires newTotalCopies >= 0;
      @   requires newTotalCopies >= (totalCopies - availableCopies);
      @   assignable totalCopies, availableCopies;
      @   ensures totalCopies == newTotalCopies;
      @   ensures availableCopies == newTotalCopies - (\old(totalCopies) - \old(availableCopies));
      @*/
    public void setTotalCopies(int newTotalCopies) {
        if (newTotalCopies < 0) {
            throw new IllegalArgumentException("Total copies cannot be negative.");
        }

        int loanedCopies = this.totalCopies - this.availableCopies;

        if (newTotalCopies < loanedCopies) {
            throw new IllegalStateException("Cannot reduce total below loaned count.");
        }

        this.totalCopies = newTotalCopies;
        this.availableCopies = newTotalCopies - loanedCopies;
    }
}