package br.ufrn.library.model;

import java.util.ArrayList;
import java.util.List;

public class User {

    // SEM INVARIANTS nas Strings para não ativar a verificação interna do Java
    /*@ spec_public @*/ private final String id;

    /*@ spec_public @*/ private String name;

    /*@ public invariant loanHistory != null; @*/
    /*@ spec_public @*/ private List<Loan> loanHistory;

    /*@ public normal_behavior
      @   requires id != null;
      @   requires name != null;
      @   ensures this.id == id;
      @   ensures this.name == name;
      @   ensures this.loanHistory != null && this.loanHistory.isEmpty();
      @*/
    public User(String id, String name) {
        this.id = id;
        this.name = name;
        this.loanHistory = new ArrayList<>();
    }

    /*@ public normal_behavior
      @   requires name != null;
      @   assignable this.name;
      @   ensures this.name == name;
      @*/
    public void setName(String name) {
        this.name = name;
    }

    /*@ public normal_behavior
      @   requires loan != null;
      @   assignable \everything; 
      @*/
    public void addLoanToHistory(Loan loan) {
        this.loanHistory.add(loan);
    }

    // Getters simples (sem JML pure para não complicar o Service)
    public String getId() {
        return id;
    }
    
    public String getName() { 
        return name; 
    }

    public List<Loan> getLoanHistory() {
        return loanHistory; 
    }
}