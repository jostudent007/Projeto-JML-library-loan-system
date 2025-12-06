package br.ufrn.library.repository;

import br.ufrn.library.model.Loan;
import java.util.List;
import java.util.Optional;

public interface LoanRepository {
    
    /*@ pure @*/
    boolean existsById(String id);

    /*@ pure @*/
    Optional<Loan> findById(String id);
    
    // Métodos de busca específicos
    /*@ pure @*/ List<Loan> findByUserId(String userId);
    /*@ pure @*/ List<Loan> findActiveByUserId(String userId);
    /*@ pure @*/ List<Loan> findByBookIsbn(String isbn);
    /*@ pure @*/ List<Loan> findAllActive();
    /*@ pure @*/ List<Loan> findAll();
    
    Loan save(Loan loan);
    
}