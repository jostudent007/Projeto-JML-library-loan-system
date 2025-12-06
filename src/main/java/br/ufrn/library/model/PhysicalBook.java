package br.ufrn.library.model;

public class PhysicalBook extends Book {
    
    /*@ spec_public @*/ private int totalCopies;
    /*@ spec_public @*/ private int availableCopies;

    public PhysicalBook(String title, String author, String isbn, int totalCopies) {
        super(title, author, isbn);
        
        if (totalCopies < 0) {
            throw new IllegalArgumentException("Total copies cannot be negative.");
        }
        
        this.totalCopies = totalCopies;
        this.availableCopies = totalCopies;
    }

    @Override
    public boolean isAvailableForLoan() {
        return availableCopies > 0;
    }

    @Override
    public void registerLoan() {
        if (availableCopies > 0) {
            this.availableCopies--;
        } else {
            throw new IllegalStateException("No copies available");
        }
    }

    @Override
    public void registerReturn() {
        if (this.availableCopies < this.totalCopies) {
            this.availableCopies++;
        }
    }

    public int getTotalCopies() {
        return totalCopies;
    }

    public int getAvailableCopies() {
        return availableCopies;
    }

    public void setTotalCopies(int newTotalCopies) {
        if (newTotalCopies < 0) {
            throw new IllegalArgumentException("Total copies cannot be negative.");
        }

        //@ assume this.totalCopies >= 0 && this.availableCopies >= 0;
        int loanedCopies = this.totalCopies - this.availableCopies;

        if (newTotalCopies < loanedCopies) {
            throw new IllegalStateException("Cannot reduce total below loaned count.");
        }

        this.totalCopies = newTotalCopies;
        //@ assume loanedCopies >= 0;
        this.availableCopies = newTotalCopies - loanedCopies;
    }
}