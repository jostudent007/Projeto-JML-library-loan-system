package br.ufrn.library.service;

import java.time.LocalDate;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

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

    private final LoanRepository loanRepository;
    private final BookRepository bookRepository;
    private final UserRepository userRepository;

    //@ public invariant loanRepository != null;
    //@ public invariant bookRepository != null;
    //@ public invariant userRepository != null;

    /*@
      @ requires loanRepository != null;
      @ requires bookRepository != null;
      @ requires userRepository != null;
      @ ensures this.loanRepository == loanRepository;
      @ ensures this.bookRepository == bookRepository;
      @ ensures this.userRepository == userRepository;
      @*/
    public LoanService(LoanRepository loanRepository, BookRepository bookRepository, UserRepository userRepository) {
        if (loanRepository == null) {
            throw new IllegalArgumentException("LoanRepository não pode ser nulo.");
        }
        if (bookRepository == null) {
            throw new IllegalArgumentException("BookRepository não pode ser nulo.");
        }
        if (userRepository == null) {
            throw new IllegalArgumentException("UserRepository não pode ser nulo.");
        }

        this.loanRepository = loanRepository;
        this.bookRepository = bookRepository;
        this.userRepository = userRepository;
    }

    public Loan createLoan(String loanId, String userId, String isbn) {
        return createLoan(loanId, userId, isbn, LocalDate.now(), DEFAULT_LOAN_PERIOD_DAYS);
    }

    /*@
      @ requires loanId != null && userId != null && isbn != null && loanDate != null;
      @ requires !userId.isEmpty() && !isbn.isEmpty();
      @ requires loanPeriodDays > 0;
      @ ensures \result != null;
      @ ensures \result.getBook().getIsbn().equals(isbn);
      @ ensures \result.getUser().getId().equals(userId);
      @ // Se lançar UserNotFound, é porque o user não existe
      @ signals (UserNotFoundException e) !userRepository.existsById(userId);
      @ // Se lançar BookNotFound, user existe MAS livro não
      @ signals (BookNotFoundException e) userRepository.existsById(userId) && !bookRepository.existsByIsbn(isbn);
      @ // A exceção mais critica: Se lançar NoCopies, tudo existe, mas o livro não está disponível
      @ signals (NoCopiesAvailableException e) userRepository.existsById(userId) && bookRepository.existsByIsbn(isbn); 
      @*/
    public Loan createLoan(String loanId, String userId, String isbn, LocalDate loanDate, int loanPeriodDays) {
        if (userId == null || userId.trim().isEmpty()) {
            throw new IllegalArgumentException("ID do usuário não pode ser nulo ou vazio.");
        }
        if (isbn == null || isbn.trim().isEmpty()) {
            throw new IllegalArgumentException("ISBN não pode ser nulo ou vazio.");
        }
        if (loanDate == null) {
            throw new IllegalArgumentException("Data do empréstimo não pode ser nula.");
        }
        if (loanPeriodDays <= 0) {
            throw new IllegalArgumentException("Período do empréstimo deve ser positivo.");
        }

        User user = userRepository.findById(userId)
                .orElseThrow(() -> new UserNotFoundException("Usuário não encontrado com ID: " + userId));

        Book book = bookRepository.findByIsbn(isbn)
                .orElseThrow(() -> new BookNotFoundException("Livro não encontrado com ISBN: " + isbn));

        // Ponto crítico para a especificação JML:
        if (!book.isAvailableForLoan()) {
            throw new NoCopiesAvailableException("Nenhuma cópia disponível para o livro: " + book.getTitle());
        }

        LocalDate dueDate = loanDate.plusDays(loanPeriodDays);

        Loan loan = new Loan(loanId, user, book, loanDate, dueDate);

        book.registerLoan();

        bookRepository.save(book);

        loanRepository.save(loan);

        user.addLoanToHistory(loan);
        userRepository.save(user);

        return loan;
    }

    public Loan returnLoan(String loanId) {
        return returnLoan(loanId, LocalDate.now());
    }

    /*@
      @ requires loanId != null && returnDate != null;
      @ requires !loanId.isEmpty();
      @ ensures \result != null;
      @ ensures \result.getId().equals(loanId);
      @ ensures \result.isReturned() == true;
      @ signals (IllegalArgumentException e) !loanRepository.existsById(loanId); 
      @ // Garante que se der IllegalState, o empréstimo existia mas já estava devolvido
      @ signals (IllegalStateException e) loanRepository.existsById(loanId) && (\old(findLoanById(loanId)).isReturned());
      @*/
    public Loan returnLoan(String loanId, LocalDate returnDate) {
        if (loanId == null || loanId.trim().isEmpty()) {
            throw new IllegalArgumentException("ID do empréstimo não pode ser nulo ou vazio.");
        }
        if (returnDate == null) {
            throw new IllegalArgumentException("Data de devolução não pode ser nula.");
        }

        Loan loan = loanRepository.findById(loanId)
                .orElseThrow(() -> new IllegalArgumentException("Empréstimo não encontrado com ID: " + loanId));

        if (loan.isReturned()) {
            throw new IllegalStateException("O empréstimo já foi devolvido.");
        }

        loan.markAsReturned(returnDate);

        Book book = loan.getBook();
        book.registerReturn();

        bookRepository.save(book);

        loanRepository.save(loan);

        return loan;
    }

    /*@
      @ requires loanId != null;
      @ ensures \result != null;
      @ signals (IllegalArgumentException e) !loanRepository.existsById(loanId);
      @ pure
      @*/
    public Loan findLoanById(String loanId) {
        if (loanId == null || loanId.trim().isEmpty()) {
            throw new IllegalArgumentException("ID do empréstimo não pode ser nulo ou vazio.");
        }

        return loanRepository.findById(loanId)
                .orElseThrow(() -> new IllegalArgumentException("Empréstimo não encontrado com ID: " + loanId));
    }

    /*@
      @ requires userId != null;
      @ ensures \result != null;
      @ pure
      @*/
    public List<Loan> getLoansByUser(String userId) {
        if (userId == null || userId.trim().isEmpty()) {
            throw new IllegalArgumentException("ID do usuário não pode ser nulo ou vazio.");
        }

        return loanRepository.findByUserId(userId);
    }

    /*@
      @ requires userId != null;
      @ ensures \result != null;
      @ pure
      @*/
    public List<Loan> getActiveLoansbyUser(String userId) {
        if (userId == null || userId.trim().isEmpty()) {
            throw new IllegalArgumentException("ID do usuário não pode ser nulo ou vazio.");
        }

        return loanRepository.findActiveByUserId(userId);
    }

    /*@
      @ requires isbn != null;
      @ ensures \result != null;
      @ pure
      @*/
    public List<Loan> getLoansByBook(String isbn) {
        if (isbn == null || isbn.trim().isEmpty()) {
            throw new IllegalArgumentException("ISBN não pode ser nulo ou vazio.");
        }

        return loanRepository.findByBookIsbn(isbn);
    }

    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public List<Loan> getAllActiveLoans() {
        return loanRepository.findAllActive();
    }

    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public List<Loan> getAllLoans() {
        return loanRepository.findAll();
    }

    public List<Loan> getOverdueLoans() {
        return getOverdueLoans(LocalDate.now());
    }

    /*@
      @ requires currentDate != null;
      @ ensures \result != null;
      @ pure
      @*/
    public List<Loan> getOverdueLoans(LocalDate currentDate) {
        if (currentDate == null) {
            throw new IllegalArgumentException("Data atual não pode ser nula.");
        }

        List<Loan> activeLoans = loanRepository.findAllActive();
        return activeLoans.stream()
                .filter(loan -> loan.isOverdue(currentDate))
                .toList();
    }

    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public LoanReportDTO generateLoanReport() {
        
        List<Loan> allLoans = loanRepository.findAll();

        long totalLoanCount = allLoans.size();

        Map<Book, Long> loansPerBook = allLoans.stream()
                .collect(Collectors.groupingBy(
                        Loan::getBook, 
                        Collectors.counting()
                ));

        Map<Book, Long> sortedLoansPerBook = loansPerBook.entrySet().stream()
                .sorted(Map.Entry.<Book, Long>comparingByValue().reversed())
                .collect(Collectors.toMap(
                        Map.Entry::getKey, 
                        Map.Entry::getValue, 
                        (e1, e2) -> e1, 
                        LinkedHashMap::new
                ));
        
        return new LoanReportDTO(totalLoanCount, sortedLoansPerBook);
    }

    /*@
      @ requires loanId != null;
      @ signals (IllegalArgumentException e) !loanRepository.existsById(loanId);
      @ pure
      @*/
    public boolean isLoanOverdue(String loanId) {
        if (loanId == null || loanId.trim().isEmpty()) {
            throw new IllegalArgumentException("ID do empréstimo não pode ser nulo ou vazio.");
        }

        Loan loan = findLoanById(loanId);
        return loan.isOverdue(LocalDate.now());
    }
}