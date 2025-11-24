package br.ufrn.library.model;

public class DigitalBook extends Book {
    
    /*@ public normal_behavior
      @   // As pré-condições são as mesmas do pai (Book)
      @   requires title != null && title.trim().length() > 0;
      @   requires author != null && author.trim().length() > 0;
      @   requires isbn != null && isbn.trim().length() > 0;
      @   
      @   // Garante que o objeto foi construído corretamente
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   ensures this.isbn == isbn;
      @*/
    public DigitalBook(String title, String author, String isbn) {
        super(title, author, isbn);
    }

    /*@ public normal_behavior
      @   // Este método imprime no console, mas não altera o estado do objeto Book.
      @   // Portanto, para fins de modelo de dados, ele não atribui nada.
      @   assignable \nothing;
      @*/
    public void download() {
        System.out.println("Downloading digital book: " + getTitle());
    }

    // --- MÉTODOS SOBRESCRITOS (Override) ---

    /*@ also
      @   // REFINAMENTO: Ao contrário de um livro genérico, o digital 
      @   // garante que o resultado é SEMPRE verdadeiro.
      @   ensures \result == true;
      @*/
    @Override
    public /*@ pure @*/ boolean isAvailableForLoan() {
        return true;
    }

    /*@ also
      @   // O pai (Book) exigia 'requires isAvailableForLoan()'.
      @   // Como aqui isAvailableForLoan() é sempre true, essa pré-condição é trivialmente satisfeita.
      @
      @   // REFINAMENTO: O pai permitia alterar tudo (assignable \everything).
      @   // Nós restringimos: o empréstimo digital NÃO altera o estado do livro (cópias infinitas).
      @   assignable \nothing;
      @*/
    @Override
    public void registerLoan() {
        // Implementação vazia intencional (livro digital não tem controle de estoque)
    }

    /*@ also
      @   // Mesma lógica: devolver um arquivo digital não muda o estado do objeto original.
      @   assignable \nothing;
      @*/
    @Override
    public void registerReturn() {
        // Implementação vazia intencional
    }
}