package br.ufrn.library.repository.impl;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

import br.ufrn.library.model.Book;
import br.ufrn.library.repository.BookRepository;

public class InMemoryBookRepository implements BookRepository {

    private static final Map<String, Book> database = new ConcurrentHashMap<>();

    @Override
    public Book save(Book book) {
        database.put(book.getIsbn(), book);
        return book;
    }

    @Override
    public Optional<Book> findByIsbn(String isbn) {
        return Optional.ofNullable(database.get(isbn));
    }

    @Override
    public List<Book> findAll() {
        return new ArrayList<>(database.values());
    }

    // CORREÇÃO: Alterado de boolean para void para bater com a Interface
    @Override
    public void deleteByIsbn(String isbn) {
        database.remove(isbn);
    }

    @Override
    public boolean existsByIsbn(String isbn) {
        return database.containsKey(isbn);
    }
}