package br.ufrn.library.dto;

import java.util.Map;
import br.ufrn.library.model.Book;

public class LoanReportDTO {

    private final long totalLoans;
    private final Map<Book, Long> loansPerBook;

    /*@ pure @*/
    public LoanReportDTO(long totalLoans, Map<Book, Long> loansPerBook) {
        this.totalLoans = totalLoans;
        this.loansPerBook = loansPerBook;
    }
    /*@ pure @*/
    public long getTotalLoans() { return totalLoans; }
    /*@ pure @*/
    public Map<Book, Long> getLoansPerBook() { return loansPerBook; }
}