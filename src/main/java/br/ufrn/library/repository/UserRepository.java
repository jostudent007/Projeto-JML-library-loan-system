package br.ufrn.library.repository;

import br.ufrn.library.model.User;
import java.util.List;
import java.util.Optional;

public interface UserRepository {
    
    /*@ pure @*/
    boolean existsById(String id);

    /*@ pure @*/
    Optional<User> findById(String id);

    User save(User user);
    
    /*@ pure @*/ List<User> findAll();
}