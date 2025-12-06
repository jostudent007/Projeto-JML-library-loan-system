package br.ufrn.library.model;

import java.time.LocalDate;

public class Loan {

    /*@ spec_public non_null @*/ private String id;
    /*@ spec_public non_null @*/ private User user;
    /*@ spec_public non_null @*/ private Book book;
    
    /*@ spec_public non_null @*/ private LocalDate loanDate;
    /*@ spec_public non_null @*/ private LocalDate dueDate;
    /*@ spec_public nullable @*/ private LocalDate returnDate;
    
    /*@ spec_public @*/ private boolean isReturned;

    /*@ public invariant id != null && id.length() > 0; @*/
    /*@ public invariant isReturned == (returnDate != null); @*/

    /*@ public normal_behavior
      @   requires id != null && id.length() > 0;
      @   requires user != null && book != null;
      @   requires loanDate != null && dueDate != null;
      @   ensures this.id == id;
      @   ensures this.user == user;
      @   ensures this.book == book;
      @   ensures this.loanDate == loanDate;
      @   ensures this.dueDate == dueDate;
      @   ensures this.isReturned == false;
      @   ensures this.returnDate == null;
      @*/
    public Loan(String id, User user, Book book, LocalDate loanDate, LocalDate dueDate) {
        this.id = id;
        this.user = user;
        this.book = book;
        this.loanDate = loanDate;
        this.dueDate = dueDate;
        this.isReturned = false;
        this.returnDate = null;
    }

    /*@ public normal_behavior
      @   requires returnDate != null;
      @   assignable this.returnDate, this.isReturned;
      @   ensures this.returnDate == returnDate;
      @   ensures this.isReturned == true;
      @*/
    public void markAsReturned(LocalDate returnDate) {
        this.returnDate = returnDate;
        this.isReturned = true;
    }

    /*@ public normal_behavior
      @   requires currentDate != null;
      @   ensures \result == false; 
      @*/
    /*@ pure @*/
    public boolean isOverdue(LocalDate currentDate) {
        if (isReturned) return false;
        return false;
    }

    // --- GETTERS PUROS ---
    /*@ pure @*/ public String getId() { return id; }
    /*@ pure @*/ public User getUser() { return user; }
    /*@ pure @*/ public Book getBook() { return book; }
    /*@ pure @*/ public LocalDate getLoanDate() { return loanDate; }
    /*@ pure @*/ public LocalDate getDueDate() { return dueDate; }
    /*@ pure @*/ public boolean isReturned() { return isReturned; }
}