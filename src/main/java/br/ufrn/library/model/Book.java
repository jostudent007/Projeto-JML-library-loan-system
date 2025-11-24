package br.ufrn.library.model;

public abstract class Book {
    
    // spec_public permite que o JML "enxergue" variáveis protected/private nas especificações públicas.
    // non_null garante que, uma vez criado, o campo nunca vira null.
    
    /*@ public invariant title != null && title.length() > 0; @*/
    /*@ spec_public non_null @*/
    protected String title;

    /*@ public invariant author != null && author.length() > 0; @*/
    /*@ spec_public non_null @*/
    protected String author;

    // ISBN é final, então seu invariante é garantido pelo construtor
    /*@ public invariant isbn != null && isbn.length() > 0; @*/
    /*@ spec_public non_null @*/
    protected final String isbn;

    /*@ public normal_behavior
      @   // PRE-CONDIÇÕES: O chamador não deve passar strings nulas ou vazias
      @   requires title != null && title.trim().length() > 0;
      @   requires author != null && author.trim().length() > 0;
      @   requires isbn != null && isbn.trim().length() > 0;
      @
      @   // PÓS-CONDIÇÕES: Os campos internos devem ser iguais aos argumentos
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   ensures this.isbn == isbn;
      @*/
    public Book(String title, String author, String isbn) {

        if (isbn == null || isbn.trim().isEmpty()) {
            throw new IllegalArgumentException("ISBN cannot be null or empty.");
        }
        if (title == null || title.trim().isEmpty()) {
            throw new IllegalArgumentException("Book title cannot be empty.");
        }
        if (author == null || author.trim().isEmpty()) {
            throw new IllegalArgumentException("Book author cannot be empty.");
        }

        this.title = title;
        this.author = author;
        this.isbn = isbn;
    }

    /*@ public normal_behavior
      @   requires title != null && title.trim().length() > 0;
      @   requires author != null && author.trim().length() > 0;
      @   // Assignable diz o que este método pode mudar. Note que 'isbn' não está aqui.
      @   assignable this.title, this.author;
      @   ensures this.title == title;
      @   ensures this.author == author;
      @   // Garante que o ISBN não mudou (mesmo sendo final, é bom explicitar em lógica)
      @   ensures this.isbn == \old(this.isbn);
      @*/
    public void updateDetails(String title, String author) {

        if (title == null || title.trim().isEmpty()) {
            throw new IllegalArgumentException("Book title cannot be empty.");
        }
        if (author == null || author.trim().isEmpty()) {
            throw new IllegalArgumentException("Book author cannot be empty.");
        }
        
        this.title = title;
        this.author = author;
    }

    // Métodos 'pure' não têm efeitos colaterais. São seguros para usar dentro de outras especificações JML.
    
    /*@ public normal_behavior
      @   ensures \result == this.title;
      @*/
    public /*@ pure @*/ String getTitle() { return title; }

    /*@ public normal_behavior
      @   ensures \result == this.author;
      @*/
    public /*@ pure @*/ String getAuthor() { return author; }

    /*@ public normal_behavior
      @   ensures \result == this.isbn;
      @*/
    public /*@ pure @*/ String getIsbn() { return isbn; }
    
    // --- MÉTODOS ABSTRATOS ---
    
    // Mesmo sem corpo, definimos o contrato que as subclasses DEVEM seguir.

    /*@ public normal_behavior
      @   // Este método apenas consulta o estado, não altera nada.
      @   assignable \nothing;
      @*/
    public abstract /*@ pure @*/ boolean isAvailableForLoan();

    /*@ public normal_behavior
      @   // Só podemos tentar registrar empréstimo se o livro estiver disponível.
      @   requires isAvailableForLoan();
      @   // O método vai alterar o estado do objeto (ex: diminuir contador de cópias)
      @   assignable \everything; 
      @*/
    public abstract void registerLoan();

    /*@ public normal_behavior
      @   // O método vai alterar o estado para devolver o livro
      @   assignable \everything;
      @*/
    public abstract void registerReturn();
}