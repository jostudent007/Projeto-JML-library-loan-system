package br.ufrn.library.model;

import java.util.ArrayList;
import java.util.List;

public class User {

    /*@ public invariant id != null && id.length() > 0; @*/
    /*@ spec_public non_null @*/ 
    private final String id;
    
    /*@ spec_public non_null @*/ 
    private String name;
    
    /*@ spec_public non_null @*/ 
    private List<Loan> loanHistory;

    /*@ public normal_behavior
      @   requires id != null && id.length() > 0;
      @   requires name != null && name.length() > 0;
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
      @   requires name != null && name.length() > 0;
      @   assignable this.name;
      @   ensures this.name == name;
      @*/
    public void setName(String name) {
        this.name = name;
    }

    /*@ public normal_behavior
      @   requires loan != null;
      @   assignable \everything; // Permite alteração do estado interno da lista
      @   ensures loanHistory.contains(loan);
      @*/
    public void addLoanToHistory(Loan loan) {
        this.loanHistory.add(loan);
    }

    /*@ pure @*/
    public String getId() { return id; }

    /*@ pure @*/
    public String getName() { return name; }

    public void setLoanHistory(List<Loan> history) {
        this.loanHistory = history;
    }
}