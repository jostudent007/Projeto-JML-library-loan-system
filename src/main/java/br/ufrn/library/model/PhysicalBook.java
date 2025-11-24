package br.ufrn.library.model;

public class PhysicalBook extends Book {
    
    // --- INVARIANTES DE CLASSE ---
    
    // 1. O número total de cópias não pode ser negativo.
    /*@ public invariant totalCopies >= 0; @*/
    
    // 2. As cópias disponíveis não podem ser negativas.
    /*@ public invariant availableCopies >= 0; @*/
    
    // 3. As cópias disponíveis nunca podem exceder o total de cópias.
    /*@ public invariant availableCopies <= totalCopies; @*/
    
    // Tornamos os campos visíveis para a especificação (spec_public)
    /*@ spec_public @*/
    private int totalCopies;
    /*@ spec_public @*/
    private int availableCopies;

    /*@ public normal_behavior
      @   requires title != null && title.trim().length() > 0;
      @   requires author != null && author.trim().length() > 0;
      @   requires isbn != null && isbn.trim().length() > 0;
      @   // Pré-condição específica desta classe:
      @   requires totalCopies >= 0;
      @
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   ensures this.isbn == isbn;
      @   ensures this.totalCopies == totalCopies;
      @   // Inicialmente, todas as cópias estão disponíveis
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
      @   // Refinamento: aqui sabemos exatamente a regra de disponibilidade
      @   ensures \result == (availableCopies > 0);
      @*/
    @Override
    public /*@ pure @*/ boolean isAvailableForLoan() {
        return availableCopies > 0;
    }

    /*@ also
      @   // A classe pai exige 'requires isAvailableForLoan()'.
      @   // Portanto, aqui exigimos que availableCopies > 0.
      @   requires availableCopies > 0;
      @
      @   assignable availableCopies;
      @
      @   // O número de cópias diminui exatamente em 1
      @   ensures availableCopies == \old(availableCopies) - 1;
      @   // O total de cópias permanece inalterado
      @   ensures totalCopies == \old(totalCopies);
      @*/
    @Override
    public void registerLoan() {
        // Nota: Com JML ativado (RAC), o erro explodiria na pré-condição antes de chegar no 'if'
        if (isAvailableForLoan()) {
            this.availableCopies--;
        } else {
            // Esse código se torna tecnicamente inalcançável se o contrato for respeitado pelo chamador
            throw new IllegalStateException("No copies available to register loan for book: " + this.isbn);
        }
    }

    /*@ also
      @   assignable availableCopies;
      @
      @   // CASO 1: Se havia cópias emprestadas (disponível < total), incrementa 1.
      @   ensures \old(availableCopies) < totalCopies ==> availableCopies == \old(availableCopies) + 1;
      @   
      @   // CASO 2: Se já estava tudo na estante (disponível == total), mantém igual.
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
      @   // 1. O novo total não pode ser negativo
      @   requires newTotalCopies >= 0;
      @   
      @   // 2. Definição auxiliar para clareza: livros emprestados
      @   // old(loaned) = old(total) - old(available)
      @   // O novo total deve ser suficiente para cobrir os livros que já estão emprestados.
      @   requires newTotalCopies >= (\old(totalCopies) - \old(availableCopies));
      @
      @   assignable totalCopies, availableCopies;
      @
      @   // O total é atualizado
      @   ensures totalCopies == newTotalCopies;
      @
      @   // As cópias disponíveis são recalculadas corretamente:
      @   // NovoDisponivel = NovoTotal - (LivrosEmprestadosAntigamente)
      @   ensures availableCopies == newTotalCopies - (\old(totalCopies) - \old(availableCopies));
      @*/
    public void setTotalCopies(int newTotalCopies) {
        if (newTotalCopies < 0) {
            throw new IllegalArgumentException("Total copies cannot be negative.");
        }

        int loanedCopies = this.totalCopies - this.availableCopies;

        if (newTotalCopies < loanedCopies) {
            throw new IllegalStateException(
                "Cannot set total copies to " + newTotalCopies + 
                ". There are currently " + loanedCopies + " copies on loan."
            );
        }

        this.totalCopies = newTotalCopies;
        this.availableCopies = newTotalCopies - loanedCopies;
    }
}