package br.ufrn.library.cli;

import java.time.LocalDate;
import java.util.Map;
import java.util.Scanner;

import br.ufrn.library.dto.LoanReportDTO;
import br.ufrn.library.model.Book;
import br.ufrn.library.model.Loan;
import br.ufrn.library.service.LoanService;

public class LoanConsoleHandler {

    private final LoanService loanService;
    private final Scanner scanner;

    public LoanConsoleHandler(LoanService loanService, Scanner scanner) {
        this.loanService = loanService;
        this.scanner = scanner;
    }

    public void handleCreateLoan() {
        try {
            System.out.println("\n--- 3. Realizar Empréstimo ---");
            
            System.out.print("ID do Empréstimo (ex: L01): ");
            String loanId = scanner.nextLine();
            
            System.out.print("ID do Usuário: ");
            String userId = scanner.nextLine();
            
            System.out.print("ISBN do Livro: ");
            String isbn = scanner.nextLine();

            // Service validado pelo JML
            loanService.createLoan(loanId, userId, isbn);
            System.out.println("Empréstimo realizado com sucesso!");

        } catch (Exception e) {
            System.err.println("Erro ao realizar empréstimo: " + e.getMessage());
        }
    }

    public void handleReturnLoan() {
        try {
            System.out.println("\n--- 4. Devolver Livro ---");
            System.out.print("ID do Empréstimo: ");
            String loanId = scanner.nextLine();

            // CORREÇÃO: Passando a data atual explicitamente para casar com o Service
            loanService.returnLoan(loanId, LocalDate.now()); 
            System.out.println("Devolução registrada com sucesso!");

        } catch (Exception e) {
            System.err.println("Erro na devolução: " + e.getMessage());
        }
    }

    public void handleListActiveLoans() {
        System.out.println("\n--- 7. Listar Empréstimos Ativos ---");
        var loans = loanService.getAllActiveLoans();

        if (loans.isEmpty()) {
            System.out.println("Nenhum empréstimo ativo.");
            return;
        }

        for (Loan loan : loans) {
            System.out.printf("  -> [LoanID: %s] User: %s | Book: %s | Due: %s\n",
                    loan.getId(),
                    loan.getUser().getName(),
                    loan.getBook().getTitle(),
                    loan.getDueDate());
        }
    }

    public void handleLoanReport() {
        System.out.println("\n--- 8. Relatório de Empréstimos (Mais Populares) ---");
        
        LoanReportDTO report = loanService.generateLoanReport();
        
        System.out.println("Total de Empréstimos Realizados: " + report.getTotalLoans());
        System.out.println("Empréstimos por Livro:");

        Map<Book, Long> map = report.getLoansPerBook();
        if (map.isEmpty()) {
            System.out.println("  (Nenhum dado)");
        } else {
            for (Map.Entry<Book, Long> entry : map.entrySet()) {
                System.out.printf("  -> %s (ISBN: %s): %d empréstimos\n",
                        entry.getKey().getTitle(),
                        entry.getKey().getIsbn(),
                        entry.getValue());
            }
        }
    }
}