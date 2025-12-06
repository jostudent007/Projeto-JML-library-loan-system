package br.ufrn.library.cli;

import java.util.Scanner;
import br.ufrn.library.model.User;
import br.ufrn.library.service.UserService;

public class UserConsoleHandler {

    private final UserService userService;
    private final Scanner scanner;

    public UserConsoleHandler(UserService userService, Scanner scanner) {
        this.userService = userService;
        this.scanner = scanner;
    }

    public void handleRegisterUser() {
        try {
            System.out.println("\n--- 2. Cadastrar Usuário ---");
            System.out.print("ID do Usuário: ");
            String id = scanner.nextLine();
            
            System.out.print("Nome do Usuário: ");
            String name = scanner.nextLine();

            userService.registerUser(id, name);
            System.out.println("Usuário cadastrado com sucesso!");
        } catch (Exception e) {
            System.err.println("Erro ao cadastrar usuário: " + e.getMessage());
        }
    }

    public void handleListAllUsers() {
        System.out.println("\n--- 6. Listar Usuários ---");
        var users = userService.listAllUsers();
        
        if (users.isEmpty()) {
            System.out.println("Nenhum usuário cadastrado.");
            return;
        }

        for (User user : users) {
            System.out.printf("  -> [%s] %s\n", user.getId(), user.getName());
        }
    }
}