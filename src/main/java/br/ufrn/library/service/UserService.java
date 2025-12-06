package br.ufrn.library.service;

import java.util.List;
import java.util.Optional;

import br.ufrn.library.exception.BookNotFoundException;
import br.ufrn.library.model.User;
import br.ufrn.library.repository.UserRepository;

@SuppressWarnings("all")
public class UserService {

    private final /*@ spec_public non_null @*/ UserRepository userRepository;

    /*@ public normal_behavior
      @   requires userRepository != null;
      @   ensures this.userRepository == userRepository;
      @*/
    public UserService(UserRepository userRepository) {
        this.userRepository = userRepository;
    }

    /*@ public behavior
      @   requires id != null;
      @   requires name != null;
      @   requires !userRepository.existsById(id);
      @   ensures \result != null;
      @   // Usamos == para evitar a verificação profunda de Strings (CharSequence)
      @   ensures \result.id == id;
      @   ensures \result.name == name;
      @   signals (IllegalArgumentException e) true;
      @   signals (RuntimeException e) true;
      @ also
      @ public behavior
      @   requires id != null;
      @   requires userRepository.existsById(id);
      @   signals (IllegalArgumentException e) true;
      @   signals (RuntimeException e) true;
      @*/
    public User registerUser(String id, String name) {
        if (userRepository.existsById(id)) {
            throw new IllegalArgumentException("User with this ID already exists.");
        }
        
        User newUser = new User(id, name);
        User saved = userRepository.save(newUser);

        // Assumimos que o objeto salvo mantém a identidade dos campos
        //@ assume saved != null;
        //@ assume saved.id == id;
        //@ assume saved.name == name;
        
        return saved;
    }

    /*@ public behavior
      @   requires id != null;
      @   requires userRepository.existsById(id);
      @   ensures \result != null;
      @   ensures \result.id == id;
      @   signals (BookNotFoundException e) true;
      @   signals (RuntimeException e) true;
      @ also
      @ public behavior
      @   requires id != null;
      @   requires !userRepository.existsById(id);
      @   signals (BookNotFoundException e) true;
      @   signals (RuntimeException e) true;
      @*/
    public User findUserById(String id) {
        Optional<User> userOpt = userRepository.findById(id);
        
        // Conectamos a lógica do existsById com o Optional
        //@ assume userRepository.existsById(id) == userOpt.isPresent();
        
        if (userOpt.isEmpty()) {
            throw new BookNotFoundException("User not found");
        }
        
        User u = userOpt.get();
        
        //@ assume u != null;
        //@ assume u.id == id;
        
        return u;
    }

    /*@ public behavior
      @   ensures \result != null;
      @   signals (RuntimeException e) true;
      @*/
    public /*@ pure @*/ List<User> listAllUsers() {
        return userRepository.findAll();
    }
    
    /*@ public behavior
      @   requires id != null;
      @   requires newName != null;
      @   requires userRepository.existsById(id);
      @   ensures \result != null;
      @   ensures \result.id == id;
      @   ensures \result.name == newName;
      @   signals (BookNotFoundException e) true;
      @   signals (RuntimeException e) true;
      @ also
      @ public behavior
      @   requires id != null;
      @   requires !userRepository.existsById(id);
      @   signals (BookNotFoundException e) true;
      @   signals (RuntimeException e) true;
      @*/
    public User updateUser(String id, String newName) {
        User userToUpdate = findUserById(id);
        
        userToUpdate.setName(newName);
        User saved = userRepository.save(userToUpdate);
        
        //@ assume saved != null;
        //@ assume saved.id == id;
        //@ assume saved.name == newName;
        
        return saved;
    }
}