package br.ufrn.library.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class User {

    /*@ public invariant id != null && id.length() > 0; @*/
    /*@ spec_public @*/ private final String id;

    /*@ public invariant name != null && name.length() > 0; @*/
    /*@ spec_public @*/ private String name;

    /*@ public invariant loanHistory != null; @*/
    /*@ spec_public @*/ private List<Loan> loanHistory;

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
      @   // CORREÇÃO: \everything permite que o método altere o conteúdo interno da lista
      @   assignable \everything; 
      @   ensures loanHistory.contains(loan);
      @*/
    public void addLoanToHistory(Loan loan) {
        this.loanHistory.add(loan);
    }

    // --- GETTERS PUROS ---

    /*@ public normal_behavior
      @   ensures \result == this.id;
      @*/
    /*@ pure @*/
    public String getId() {
        return id;
    }
    
    /*@ public normal_behavior
      @   ensures \result == this.name;
      @*/
    /*@ pure @*/
    public String getName() { 
        return name; 
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @*/
    /*@ pure @*/
    public List<Loan> getLoanHistory() {
        return Collections.unmodifiableList(loanHistory);
    }
}