package br.ufrn.library.service;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import br.ufrn.library.dto.BookAvailabilityDTO;
import br.ufrn.library.exception.BookNotFoundException;
import br.ufrn.library.model.Book;
import br.ufrn.library.model.DigitalBook;
import br.ufrn.library.model.PhysicalBook;
import br.ufrn.library.repository.BookRepository;

@SuppressWarnings("all")
public class BookService {

    private final BookRepository bookRepository;

    public BookService(BookRepository bookRepository) {
        this.bookRepository = bookRepository;
    }

    public void registerDigitalBook(String title, String author, String isbn) {
        if (bookRepository.existsByIsbn(isbn)) {
            throw new IllegalArgumentException("Book already exists");
        }
        DigitalBook digitalBook = new DigitalBook(title, author, isbn);
        bookRepository.save(digitalBook);
    }

    public void registerPhysicalBook(String title, String author, String isbn, int totalCopies) {
        if (bookRepository.existsByIsbn(isbn)) {
            throw new IllegalArgumentException("Book already exists");
        }
        PhysicalBook physicalBook = new PhysicalBook(title, author, isbn, totalCopies);
        bookRepository.save(physicalBook);
    }

    public void updateDigitalBook(String isbn, String newTitle, String newAuthor) {
        Book bookToUpdate = findBookByIsbn(isbn);

        if (bookToUpdate instanceof DigitalBook) {
            DigitalBook digitalBook = (DigitalBook) bookToUpdate;
            bookRepository.save(digitalBook);
        } else {
            throw new IllegalArgumentException("Not a digital book");
        }
    }

    public void updatePhysicalBook(String isbn, String newTitle, String newAuthor, int newTotalCopies) {
        Book bookToUpdate = findBookByIsbn(isbn);

        if (bookToUpdate instanceof PhysicalBook) {
            PhysicalBook physicalBook = (PhysicalBook) bookToUpdate;
            if (newTotalCopies >= 0) {
                physicalBook.setTotalCopies(newTotalCopies);
                bookRepository.save(physicalBook);
            }
        } else {
            throw new IllegalArgumentException("Not a physical book");
        }
    }

    public Book findBookByIsbn(String isbn) {
        Optional<Book> bookOpt = bookRepository.findByIsbn(isbn);
        if (bookOpt.isEmpty()) {
            throw new BookNotFoundException("Book not found");
        }
        return bookOpt.get();
    }

    public List<Book> listAllBooks() {
        return bookRepository.findAll();
    }

    public List<BookAvailabilityDTO> getBookAvailabilityReport() {
        List<Book> books = bookRepository.findAll();
        List<BookAvailabilityDTO> report = new ArrayList<>();
        
        for (Book book : books) {
            report.add(new BookAvailabilityDTO(book));
        }
        return report;
    }

    public void deleteBook(String isbn) {
        if (!bookRepository.existsByIsbn(isbn)) {
            throw new BookNotFoundException("Book not found");
        }
        bookRepository.deleteByIsbn(isbn);
    }
}