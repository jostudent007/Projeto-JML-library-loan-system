package br.ufrn.library.model;

import java.time.LocalDate;

public class Loan {

    // --- INVARIANTES DE ESTADO ---

    /*@ public invariant id != null && id.length() > 0; @*/
    /*@ spec_public @*/
    private String id;

    /*@ public invariant user != null; @*/
    /*@ spec_public @*/
    private User user;

    /*@ public invariant book != null; @*/
    /*@ spec_public @*/
    private Book book;

    /*@ public invariant loanDate != null; @*/
    /*@ spec_public @*/
    private LocalDate loanDate;

    /*@ public invariant dueDate != null; @*/
    /*@ spec_public @*/
    private LocalDate dueDate;

    // A data de devolução pode ser nula (enquanto o empréstimo está ativo)
    /*@ spec_public nullable @*/
    private LocalDate returnDate;

    /*@ spec_public @*/
    private boolean isReturned;

    // --- INVARIANTES LÓGICOS E TEMPORAIS ---

    // 1. A data de vencimento nunca pode ser antes da data de empréstimo.
    /*@ public invariant !dueDate.isBefore(loanDate); @*/

    // 2. CONSISTÊNCIA: A flag isReturned deve estar sincronizada com a existência de returnDate.
    // (isReturned é verdadeiro SE E SOMENTE SE returnDate não for nulo)
    /*@ public invariant isReturned <==> returnDate != null; @*/

    // 3. Se houver uma data de devolução, ela não pode ser antes da data de empréstimo.
    /*@ public invariant returnDate != null ==> !returnDate.isBefore(loanDate); @*/

    
    /*@ public normal_behavior
      @   requires id != null && id.trim().length() > 0;
      @   requires user != null;
      @   requires book != null;
      @   requires loanDate != null;
      @   requires dueDate != null;
      @   // Validação temporal na entrada
      @   requires !dueDate.isBefore(loanDate);
      @
      @   ensures this.id == id;
      @   ensures this.user == user;
      @   ensures this.book == book;
      @   ensures this.loanDate == loanDate;
      @   ensures this.dueDate == dueDate;
      @   // Garante o estado inicial do empréstimo (ativo)
      @   ensures this.returnDate == null;
      @   ensures this.isReturned == false;
      @*/
    public Loan(String id, User user, Book book, LocalDate loanDate, LocalDate dueDate) {
        if (id == null || id.trim().isEmpty()) {
            throw new IllegalArgumentException("Loan ID cannot be null or empty.");
        }
        if (user == null) {
            throw new IllegalArgumentException("User cannot be null.");
        }
        if (book == null) {
            throw new IllegalArgumentException("Book cannot be null.");
        }
        if (loanDate == null) {
            throw new IllegalArgumentException("Loan date cannot be null.");
        }
        if (dueDate == null) {
            throw new IllegalArgumentException("Due date cannot be null.");
        }
        if (dueDate.isBefore(loanDate)) {
            throw new IllegalArgumentException("Due date cannot be before loan date.");
        }

        this.id = id;
        this.user = user;
        this.book = book;
        this.loanDate = loanDate;
        this.dueDate = dueDate;
        this.returnDate = null;
        this.isReturned = false;
    }

    /*@ public normal_behavior
      @   requires returnDate != null;
      @   // A devolução não pode ser no passado (antes de ter pego o livro)
      @   requires !returnDate.isBefore(this.loanDate);
      @   // Só pode devolver se AINDA NÃO tiver sido devolvido
      @   requires !this.isReturned;
      @
      @   assignable this.returnDate, this.isReturned;
      @
      @   ensures this.returnDate == returnDate;
      @   ensures this.isReturned == true;
      @*/
    public void markAsReturned(LocalDate returnDate) {
        if (returnDate == null) {
            throw new IllegalArgumentException("Return date cannot be null.");
        }
        if (returnDate.isBefore(loanDate)) {
            throw new IllegalArgumentException("Return date cannot be before loan date.");
        }
        if (this.isReturned) {
            throw new IllegalStateException("Loan has already been returned.");
        }

        this.returnDate = returnDate;
        this.isReturned = true;
    }

    /*@ public normal_behavior
      @   requires currentDate != null;
      @   // O método é puro (apenas leitura)
      @   assignable \nothing; 
      @
      @   // Definição lógica de atraso:
      @   // Verdadeiro SE (não devolvido E data atual depois do vencimento)
      @   ensures \result == (!isReturned && currentDate.isAfter(dueDate));
      @*/
    public /*@ pure @*/ boolean isOverdue(LocalDate currentDate) {
        if (currentDate == null) {
            throw new IllegalArgumentException("Current date cannot be null.");
        }
        return !isReturned && currentDate.isAfter(dueDate);
    }

    /*@ public normal_behavior
      @   ensures \result == this.id;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getId() { // <--- Assegure-se que este está presente
        return id;
    }

    /*@ public normal_behavior
      @   ensures \result == this.user;
      @*/
    public /*@ pure @*/ User getUser() {
        return user;
    }

    /*@ public normal_behavior
      @   ensures \result == this.book;
      @*/
    public /*@ pure @*/ Book getBook() {
        return book;
    }

    /*@ public normal_behavior
      @   ensures \result == this.loanDate;
      @*/
    public /*@ pure @*/ LocalDate getLoanDate() {
        return loanDate;
    }

    /*@ public normal_behavior
      @   ensures \result == this.dueDate;
      @*/
    public /*@ pure @*/ LocalDate getDueDate() {
        return dueDate;
    }

    /*@ public normal_behavior
      @   ensures \result == this.returnDate;
      @*/
    public /*@ pure nullable @*/ LocalDate getReturnDate() {
        return returnDate;
    }

    /*@ public normal_behavior
      @   ensures \result == this.isReturned;
      @*/
    public /*@ pure @*/ boolean isReturned() {
        return isReturned;
    }

    // --- ESPECIFICAÇÕES DE OBJETOS COMUNS ---

    // toString geralmente é 'assignable \nothing' e garante resultado não nulo
    /*@ also
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    @Override
    public String toString() {
        return "Loan{" +
                "id='" + id + '\'' +
                ", userId='" + (user != null ? user.getId() : "null") + '\'' +
                ", bookIsbn='" + (book != null ? book.getIsbn() : "null") + '\'' +
                ", loanDate=" + loanDate +
                ", dueDate=" + dueDate +
                ", returnDate=" + returnDate +
                ", isReturned=" + isReturned +
                '}';
    }

    /*@ also
      @   ensures (o == null) ==> (\result == false);
      @   ensures (this == o) ==> (\result == true);
      @   ensures (o instanceof Loan) && ((Loan)o).id.equals(this.id) ==> \result == true;
      @*/
    @Override
    public /*@ pure @*/ boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Loan loan = (Loan) o;
        return id.equals(loan.id);
    }

    /*@ also
      @   ensures \result == id.hashCode();
      @*/
    @Override
    public /*@ pure @*/ int hashCode() {
        return id.hashCode();
    }
}