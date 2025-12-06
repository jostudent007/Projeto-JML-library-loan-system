package br.ufrn.library.repository;

import br.ufrn.library.model.Book;
import java.util.List;
import java.util.Optional;

public interface BookRepository {
    
    /*@ pure @*/
    boolean existsByIsbn(String isbn);

    /*@ pure @*/
    Optional<Book> findByIsbn(String isbn);

    /*@ pure @*/
    List<Book> findAll();
    
    Book save(Book book);
    
    void deleteByIsbn(String isbn);
}