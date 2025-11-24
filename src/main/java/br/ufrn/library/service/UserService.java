package br.ufrn.library.service;

import java.util.List;

import br.ufrn.library.model.User;
import br.ufrn.library.repository.UserRepository;

public class UserService {

    private final UserRepository userRepository;

    //@ public invariant userRepository != null;

    /*@
      @ requires userRepository != null;
      @ ensures this.userRepository == userRepository;
      @*/
    public UserService(UserRepository userRepository) {
        this.userRepository = userRepository;
    }

    /*@
      @ requires id != null && name != null;
      @ ensures \result != null;
      @ ensures \result.getId().equals(id);
      @ ensures \result.getName().equals(name);
      @ // Garante que o usuário foi "persistido" (conceitualmente)
      @ ensures userRepository.existsById(id); 
      @ // Se lançar exceção, é porque o usuário JÁ existia
      @ signals (IllegalArgumentException e) userRepository.existsById(id);
      @*/
    public User registerUser(String id, String name) {
        if (userRepository.existsById(id)) {
            throw new IllegalArgumentException("User with this ID already exists.");
        }
        User newUser = new User(id, name);
        return userRepository.save(newUser);
    }

    /*@
      @ requires id != null;
      @ ensures \result != null;
      @ ensures \result.getId().equals(id);
      @ // Se lançar exceção, é porque o usuário NÃO existe
      @ signals (IllegalArgumentException e) !userRepository.existsById(id);
      @ pure
      @*/
    public User findUserById(String id) {
        return userRepository.findById(id)
                .orElseThrow(() -> new IllegalArgumentException("User not found with ID: " + id));
    }

    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public List<User> listAllUsers() {
        return userRepository.findAll();
    }
    
    /*@
      @ requires id != null && newName != null;
      @ ensures \result != null;
      @ ensures \result.getId().equals(id);
      @ ensures \result.getName().equals(newName);
      @ // A exceção aqui é propagada do findUserById, então a condição é a mesma: user não existe
      @ signals (IllegalArgumentException e) !userRepository.existsById(id);
      @*/
    public User updateUser(String id, String newName) {
        User userToUpdate = findUserById(id);
        userToUpdate.setName(newName);
        
        return userRepository.save(userToUpdate);
    }
}