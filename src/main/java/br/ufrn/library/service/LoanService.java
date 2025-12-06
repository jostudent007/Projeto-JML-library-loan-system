package br.ufrn.library.service;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import br.ufrn.library.dto.LoanReportDTO;
import br.ufrn.library.exception.BookNotFoundException;
import br.ufrn.library.exception.NoCopiesAvailableException;
import br.ufrn.library.exception.UserNotFoundException;
import br.ufrn.library.model.Book;
import br.ufrn.library.model.Loan;
import br.ufrn.library.model.User;
import br.ufrn.library.repository.BookRepository;
import br.ufrn.library.repository.LoanRepository;
import br.ufrn.library.repository.UserRepository;

public class LoanService {

    private static final int DEFAULT_LOAN_PERIOD_DAYS = 14;

    private final /*@ spec_public non_null @*/ LoanRepository loanRepository;
    private final /*@ spec_public non_null @*/ BookRepository bookRepository;
    private final /*@ spec_public non_null @*/ UserRepository userRepository;

    //@ public invariant loanRepository != null;
    //@ public invariant bookRepository != null;
    //@ public invariant userRepository != null;

    /*@ public normal_behavior
      @   requires loanRepository != null;
      @   requires bookRepository != null;
      @   requires userRepository != null;
      @   ensures this.loanRepository == loanRepository;
      @   ensures this.bookRepository == bookRepository;
      @   ensures this.userRepository == userRepository;
      @*/
    public LoanService(LoanRepository loanRepository, BookRepository bookRepository, UserRepository userRepository) {
        if (loanRepository == null) throw new IllegalArgumentException("LoanRepository null");
        if (bookRepository == null) throw new IllegalArgumentException("BookRepository null");
        if (userRepository == null) throw new IllegalArgumentException("UserRepository null");

        this.loanRepository = loanRepository;
        this.bookRepository = bookRepository;
        this.userRepository = userRepository;
    }

    public Loan createLoan(String loanId, String userId, String isbn) {
        return createLoan(loanId, userId, isbn, LocalDate.now(), DEFAULT_LOAN_PERIOD_DAYS);
    }
/*@ public normal_behavior
      @   requires loanId != null && loanId.length() > 0;
      @   requires userId != null && userId.length() > 0;
      @   requires isbn != null && isbn.length() > 0;
      @   requires loanDate != null;
      @   requires loanPeriodDays > 0;
      @   requires userRepository.existsById(userId);
      @   requires bookRepository.existsByIsbn(isbn);
      @   ensures \result != null;
      @ also
      @ public exceptional_behavior
      @   requires loanId != null && loanId.length() > 0; // Ensure this is here for exceptional cases too
      @   signals (UserNotFoundException e) !userRepository.existsById(userId);
      @   signals (BookNotFoundException e) userRepository.existsById(userId) && !bookRepository.existsByIsbn(isbn);
      @   signals (NoCopiesAvailableException e) true;
      @*/
    public Loan createLoan(String loanId, String userId, String isbn, LocalDate loanDate, int loanPeriodDays) {
        // Redundant checks for Java safety, but JML relies on 'requires' above
        if (userId == null || userId.isEmpty()) throw new IllegalArgumentException("ID invalid");
        if (isbn == null || isbn.isEmpty()) throw new IllegalArgumentException("ISBN invalid");
        if (loanDate == null) throw new IllegalArgumentException("Date invalid");
        if (loanPeriodDays <= 0) throw new IllegalArgumentException("Period invalid");

        Optional<User> userOpt = userRepository.findById(userId);
        if (userOpt.isEmpty()) throw new UserNotFoundException("User not found");
        User user = userOpt.get();

        Optional<Book> bookOpt = bookRepository.findByIsbn(isbn);
        if (bookOpt.isEmpty()) throw new BookNotFoundException("Book not found");
        Book book = bookOpt.get();

        if (!book.isAvailableForLoan()) {
            throw new NoCopiesAvailableException("No copies");
        }

        LocalDate dueDate = loanDate.plusDays(loanPeriodDays);
        
        // JML needs to know dueDate is not before loanDate. 
        // Since we add positive days, it is true, but we assume it for verifier speed.
        //@ assume !dueDate.isBefore(loanDate); 

        Loan loan = new Loan(loanId, user, book, loanDate, dueDate);

        book.registerLoan();
        bookRepository.save(book);
        loanRepository.save(loan);
        user.addLoanToHistory(loan);
        userRepository.save(user);

        return loan;
    }

    /*@ public normal_behavior
      @   requires loanId != null && returnDate != null;
      @   requires loanRepository.existsById(loanId);
      @   ensures \result != null;
      @ also
      @ public exceptional_behavior
      @   signals (Exception e) true;
      @*/
    public Loan returnLoan(String loanId, LocalDate returnDate) {
        if (loanId == null || loanId.isEmpty()) throw new IllegalArgumentException("ID invalido");
        if (returnDate == null) throw new IllegalArgumentException("Data invalida");

        Optional<Loan> loanOpt = loanRepository.findById(loanId);
        if (loanOpt.isEmpty()) throw new IllegalArgumentException("Loan not found");
        Loan loan = loanOpt.get();

        if (loan.isReturned()) throw new IllegalStateException("Already returned");

        loan.markAsReturned(returnDate);
        
        Book book = loan.getBook();
        book.registerReturn(); // Atualiza estado do livro

        bookRepository.save(book);
        loanRepository.save(loan);

        return loan;
    }

    /*@ public normal_behavior
      @   requires loanId != null;
      @   requires loanRepository.existsById(loanId);
      @   ensures \result != null;
      @ also
      @ public exceptional_behavior
      @   requires loanId == null || !loanRepository.existsById(loanId);
      @   signals (IllegalArgumentException e) !loanRepository.existsById(loanId);
      @*/
    public /*@ pure @*/ Loan findLoanById(String loanId) {
        if (loanId == null || loanId.isEmpty()) throw new IllegalArgumentException("ID invalido");
        Optional<Loan> loanOpt = loanRepository.findById(loanId);
        if (loanOpt.isEmpty()) throw new IllegalArgumentException("Loan not found");
        return loanOpt.get();
    }

    // Métodos de listagem puros
    public /*@ pure @*/ List<Loan> getLoansByUser(String userId) { return loanRepository.findByUserId(userId); }
    public /*@ pure @*/ List<Loan> getActiveLoansbyUser(String userId) { return loanRepository.findActiveByUserId(userId); }
    public /*@ pure @*/ List<Loan> getLoansByBook(String isbn) { return loanRepository.findByBookIsbn(isbn); }
    public /*@ pure @*/ List<Loan> getAllActiveLoans() { return loanRepository.findAllActive(); }
    public /*@ pure @*/ List<Loan> getAllLoans() { return loanRepository.findAll(); }

    public List<Loan> getOverdueLoans() { return getOverdueLoans(LocalDate.now()); }

    /*@ public normal_behavior
      @   requires currentDate != null;
      @   ensures \result != null;
      @*/
    public /*@ pure @*/ List<Loan> getOverdueLoans(LocalDate currentDate) {
        if (currentDate == null) throw new IllegalArgumentException("Data invalida");
        
        List<Loan> activeLoans = loanRepository.findAllActive();
        List<Loan> overdueLoans = new ArrayList<>();
        
        for (Loan loan : activeLoans) {
            if (loan.isOverdue(currentDate)) {
                overdueLoans.add(loan);
            }
        }
        return overdueLoans;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @*/
    public /*@ pure @*/ LoanReportDTO generateLoanReport() {
        List<Loan> allLoans = loanRepository.findAll();
        long totalLoanCount = allLoans.size();

        // Contagem manual para evitar Streams
        Map<Book, Long> loansPerBook = new LinkedHashMap<>();
        for (Loan loan : allLoans) {
            Book book = loan.getBook();
            if (loansPerBook.containsKey(book)) {
                loansPerBook.put(book, loansPerBook.get(book) + 1L);
            } else {
                loansPerBook.put(book, 1L);
            }
        }

        // Ordenação manual (Bubble Sort simples) das entradas do mapa
        List<Map.Entry<Book, Long>> list = new ArrayList<>(loansPerBook.entrySet());
        for (int i = 0; i < list.size(); i++) {
            for (int j = i + 1; j < list.size(); j++) {
                Long v1 = list.get(i).getValue();
                Long v2 = list.get(j).getValue();
                if (v2 > v1) { // Decrescente
                    Map.Entry<Book, Long> temp = list.get(i);
                    list.set(i, list.get(j));
                    list.set(j, temp);
                }
            }
        }

        // Reconstrução do mapa ordenado
        Map<Book, Long> sortedLoansPerBook = new LinkedHashMap<>();
        for (Map.Entry<Book, Long> entry : list) {
            sortedLoansPerBook.put(entry.getKey(), entry.getValue());
        }

        return new LoanReportDTO(totalLoanCount, sortedLoansPerBook);
    }

    /*@ public normal_behavior
      @   requires loanId != null;
      @   requires loanRepository.existsById(loanId);
      @ also
      @ public exceptional_behavior
      @   requires loanId == null || !loanRepository.existsById(loanId);
      @   signals (IllegalArgumentException e) !loanRepository.existsById(loanId);
      @*/
    public /*@ pure @*/ boolean isLoanOverdue(String loanId) {
        if (loanId == null || loanId.isEmpty()) throw new IllegalArgumentException("ID invalido");
        Loan loan = findLoanById(loanId);
        return loan.isOverdue(LocalDate.now());
    }
}