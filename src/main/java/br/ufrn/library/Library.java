package br.ufrn.library;

import java.util.Scanner;

import br.ufrn.library.cli.BookConsoleHandler;
import br.ufrn.library.cli.LoanConsoleHandler;
import br.ufrn.library.cli.UserConsoleHandler;
import br.ufrn.library.repository.BookRepository;
import br.ufrn.library.repository.LoanRepository;
import br.ufrn.library.repository.UserRepository;
import br.ufrn.library.repository.impl.InMemoryBookRepository;
import br.ufrn.library.repository.impl.InMemoryLoanRepository;
import br.ufrn.library.repository.impl.InMemoryUserRepository;
import br.ufrn.library.service.BookService;
import br.ufrn.library.service.LoanService;
import br.ufrn.library.service.UserService;

public class Library {

    // --- ESPECIFICAÇÕES DE CAMPOS (State) ---

    // O scanner é final e inicializado na declaração, então nunca é nulo.
    /*@ public static invariant scanner != null; @*/
    private static final Scanner scanner = new Scanner(System.in);
    
    // spec_public torna variáveis privadas visíveis para as especificações JML públicas.
    // nullable é necessário porque elas começam como null antes do setupServices().
    /*@ public static spec_public nullable BookService bookService; @*/
    private static BookService bookService;

    /*@ public static spec_public nullable UserService userService; @*/
    private static UserService userService;

    /*@ public static spec_public nullable LoanService loanService; @*/
    private static LoanService loanService;

    /*@ public static spec_public nullable BookConsoleHandler bookHandler; @*/
    private static BookConsoleHandler bookHandler;

    /*@ public static spec_public nullable UserConsoleHandler userHandler; @*/
    private static UserConsoleHandler userHandler;

    /*@ public static spec_public nullable LoanConsoleHandler loanHandler; @*/
    private static LoanConsoleHandler loanHandler;

    // --- MÉTODOS ---

    /*@ public normal_behavior
      @   assignable bookService, userService, loanService, bookHandler, userHandler, loanHandler;
      @*/
    public static void main(String[] args) {
        setupServices();
        setupHandlers();
        runMenuLoop();
        
        scanner.close();
        System.out.println("Sistema finalizado.");
    }

    /*@ public normal_behavior
      @   // Este método pode modificar apenas os serviços
      @   assignable userService, bookService, loanService;
      @   
      @   // Após a execução, garante que os serviços não são nulos
      @   ensures userService != null;
      @   ensures bookService != null;
      @   ensures loanService != null;
      @*/
    private static void setupServices() {
        UserRepository userRepo = new InMemoryUserRepository();
        BookRepository bookRepo = new InMemoryBookRepository();
        LoanRepository loanRepo = new InMemoryLoanRepository();

        userService = new UserService(userRepo);
        bookService = new BookService(bookRepo);
        loanService = new LoanService(loanRepo, bookRepo, userRepo);
    }

    /*@ public normal_behavior
      @   // PRE-CONDIÇÃO: Os serviços JÁ devem ter sido iniciados antes de chamar os handlers
      @   requires userService != null;
      @   requires bookService != null;
      @   requires loanService != null;
      @   requires scanner != null;
      @
      @   // Este método modifica os handlers
      @   assignable bookHandler, userHandler, loanHandler;
      @
      @   // PÓS-CONDIÇÃO: Garante que os handlers estão prontos para uso
      @   ensures bookHandler != null;
      @   ensures userHandler != null;
      @   ensures loanHandler != null;
      @*/
    private static void setupHandlers() {
        bookHandler = new BookConsoleHandler(bookService, scanner);
        userHandler = new UserConsoleHandler(userService, scanner);
        loanHandler = new LoanConsoleHandler(loanService, scanner);
    }

    /*@ public normal_behavior
      @   // Requer que tudo esteja configurado para rodar o loop
      @   requires scanner != null;
      @   requires bookHandler != null && userHandler != null && loanHandler != null;
      @   // Como é um loop de UI, ele afeta "o mundo" (estado do sistema, console, etc)
      @   assignable \everything;
      @*/
    private static void runMenuLoop() {
        boolean running = true;
        while (running) {
            printMenu();
            try {
                // Check if line exists to avoid NoSuchElementException if input stream is closed unexpectedly
                if (scanner.hasNextLine()) { 
                    String line = scanner.nextLine();
                    // Basic validation before parsing
                    if (line.matches("\\d+")) {
                        int choice = Integer.parseInt(line);
                        running = dispatchMenuChoice(choice);
                    } else {
                         System.err.println("Erro: Por favor, digite um número válido.");
                    }
                } else {
                    running = false; // Exit if no input
                }
            } catch (NumberFormatException e) {
                System.err.println("Erro: Por favor, digite um número válido.");
            }
            
            if (running) {
                System.out.println("\nPressione Enter para continuar...");
                if (scanner.hasNextLine()) scanner.nextLine();
            }
        }
    }

    // Métodos void que só imprimem na tela (IO) são difíceis de especificar formalmente com JML puro,
    // então geralmente usamos "assignable \nothing" (não muda estado do objeto) 
    // ou omitimos a especificação detalhada de IO.
    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    private static void printMenu() {
        System.out.println("\n--- Sistema de Biblioteca ---");
        System.out.println("1. Cadastrar Livro");
        System.out.println("2. Cadastrar Usuário");
        System.out.println("3. Realizar Empréstimo");
        System.out.println("4. Realizar Devolução");
        System.out.println("5. Listar Livros e Disponibilidade");
        System.out.println("6. Listar Usuários Cadastrados");
        System.out.println("7. Listar Empréstimos Ativos");
        System.out.println("8. Gerar Relatório de Empréstimos");
        System.out.println("9. Carregar Dados");
        System.out.println("0. Sair");
        System.out.print("Escolha uma opção: ");
    }

    /*@ public normal_behavior
      @   requires bookHandler != null;
      @   requires userHandler != null;
      @   requires loanHandler != null;
      @   // Pode modificar o estado de todo o sistema dependendo da escolha
      @   assignable \everything; 
      @   
      @   // Exemplo de especificação por casos (opcional, mas ilustrativo):
      @   // Se a escolha for 0, o resultado deve ser false (parar o loop)
      @   ensures choice == 0 ==> \result == false;
      @   // Se a escolha não for 0, o loop continua (geralmente)
      @   ensures choice != 0 ==> \result == true;
      @*/
    private static boolean dispatchMenuChoice(int choice) {
        try {
            switch (choice) {
                case 1:
                    bookHandler.handleRegisterBook();
                    break;
                case 2:
                    userHandler.handleRegisterUser();
                    break;
                case 3:
                    loanHandler.handleCreateLoan();
                    break;
                case 4:
                    loanHandler.handleReturnLoan();
                    break;
                case 5:
                    bookHandler.handleListBookAvailability();
                    break;
                case 6:
                    userHandler.handleListAllUsers();
                    break;
                case 7:
                    loanHandler.handleListActiveLoans();
                    break;
                case 8:
                    loanHandler.handleLoanReport();
                    break;
                case 9:
                    // Verifica null pointer para os serviços aqui se necessário, 
                    // mas a precondição do main já deveria cobrir
                    if (userService != null && bookService != null && loanService != null) {
                         DataLoader.seed(userService, bookService, loanService);
                    }
                    break;
                case 0:
                    return false;
                default:
                    System.err.println("Opção inválida. Tente novamente.");
            }
        } catch (Exception e) {
            System.err.println("\n--- ERRO NA OPERAÇÃO ---\n" + e.getMessage() + "\n");
        }
        return true;
    }
    
}