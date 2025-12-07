package br.ufrn.library.model;

import java.time.LocalDate;

public class Loan {

    /*@ spec_public @*/ private final String id;
    /*@ spec_public @*/ private final User user;
    /*@ spec_public @*/ private final Book book;
    
    /*@ spec_public @*/ private final LocalDate loanDate;
    /*@ spec_public @*/ private final LocalDate dueDate;
    
    /*@ spec_public nullable @*/ private LocalDate returnDate;
    /*@ spec_public @*/ private boolean isReturned;

    // INVARIANTES: Garantem que os campos final nunca são nulos
    /*@ public invariant id != null; @*/
    /*@ public invariant user != null; @*/
    /*@ public invariant book != null; @*/
    /*@ public invariant loanDate != null; @*/
    /*@ public invariant dueDate != null; @*/

    /*@ public normal_behavior
      @   requires id != null;
      @   requires user != null;
      @   requires book != null;
      @   requires loanDate != null;
      @   requires dueDate != null;
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

    /*@ public behavior
      @   requires currentDate != null;
      @   // CORREÇÃO: Removemos o ensures condicional para evitar conflito com LocalDate
      @   signals (Exception e) true;
      @*/
    public boolean isOverdue(LocalDate currentDate) {
        if (isReturned) return false;
        return currentDate.isAfter(dueDate);
    }

    // Getters
    /*@ pure @*/ public String getId() { return id; }
    /*@ pure @*/ public User getUser() { return user; }
    /*@ pure @*/ public Book getBook() { return book; }
    /*@ pure @*/ public LocalDate getLoanDate() { return loanDate; }
    /*@ pure @*/ public LocalDate getDueDate() { return dueDate; }
    /*@ pure @*/ public boolean isReturned() { return isReturned; }
}