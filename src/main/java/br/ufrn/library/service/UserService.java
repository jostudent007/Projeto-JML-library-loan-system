package br.ufrn.library.service;

import java.util.List;
import java.util.Optional;

import br.ufrn.library.exception.BookNotFoundException;
import br.ufrn.library.model.User;
import br.ufrn.library.repository.UserRepository;

public class UserService {

    private final /*@ spec_public non_null @*/ UserRepository userRepository;

    //@ public invariant userRepository != null;

    /*@ public normal_behavior
      @   requires userRepository != null;
      @   ensures this.userRepository == userRepository;
      @*/
    public UserService(UserRepository userRepository) {
        this.userRepository = userRepository;
    }

    /*@ public normal_behavior
      @   requires id != null && id.length() > 0;
      @   requires name != null && name.length() > 0;
      @   requires !userRepository.existsById(id);
      @   ensures \result != null;
      @   ensures \result.getId().equals(id);
      @   ensures \result.getName().equals(name);
      @   ensures userRepository.existsById(id);
      @ also
      @ public exceptional_behavior
      @   requires id != null && id.length() > 0;
      @   requires userRepository.existsById(id);
      @   signals (IllegalArgumentException e) userRepository.existsById(id);
      @*/
    public User registerUser(String id, String name) {
        if (userRepository.existsById(id)) {
            throw new IllegalArgumentException("User with this ID already exists.");
        }
        User newUser = new User(id, name);
        return userRepository.save(newUser);
    }

    /*@ public normal_behavior
      @   requires id != null;
      @   requires userRepository.existsById(id);
      @   ensures \result != null;
      @   ensures \result.getId().equals(id);
      @ also
      @ public exceptional_behavior
      @   requires id != null;
      @   requires !userRepository.existsById(id);
      @   signals (IllegalArgumentException e) !userRepository.existsById(id);
      @*/
    public /*@ pure @*/ User findUserById(String id) {
        // Correção: Sem lambdas
        Optional<User> userOpt = userRepository.findById(id);
        if (userOpt.isEmpty()) {
            throw new BookNotFoundException("Book not found");
        }
        return userOpt.get();
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @*/
    public /*@ pure @*/ List<User> listAllUsers() {
        return userRepository.findAll();
    }
    
    /*@ public normal_behavior
      @   requires id != null && id.length() > 0;
      @   requires newName != null && newName.length() > 0;
      @   requires userRepository.existsById(id);
      @   ensures \result != null;
      @   ensures \result.getId().equals(id);
      @   ensures \result.getName().equals(newName);
      @ also
      @ public exceptional_behavior
      @   requires id != null;
      @   requires !userRepository.existsById(id);
      @   signals (IllegalArgumentException e) !userRepository.existsById(id);
      @*/
    public User updateUser(String id, String newName) {
        User userToUpdate = findUserById(id);
        userToUpdate.setName(newName);
        return userRepository.save(userToUpdate);
    }
}