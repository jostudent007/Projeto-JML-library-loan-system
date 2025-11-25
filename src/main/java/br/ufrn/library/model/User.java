package br.ufrn.library.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class User {

    // --- INVARIANTES ---

    // O ID é a identidade do usuário, nunca muda (final) e não pode ser inválido.
    /*@ public invariant id != null && id.length() > 0; @*/
    /*@ spec_public @*/
    private final String id;

    // O nome pode mudar, mas nunca pode ficar em um estado inválido.
    /*@ public invariant name != null && name.length() > 0; @*/
    /*@ spec_public @*/
    private String name;

    // A lista em si nunca é nula (pode estar vazia, mas o objeto List existe).
    /*@ public invariant loanHistory != null; @*/
    
    // INVARIANTE AVANÇADO (Lógica de Predicados):
    // "Para todo índice i, de 0 até o tamanho da lista, o elemento na posição i não é nulo."
    /*@ public invariant (\forall int i; 0 <= i && i < loanHistory.size(); loanHistory.get(i) != null); @*/
    /*@ spec_public @*/
    private List<Loan> loanHistory;

    /*@ public normal_behavior
      @   requires id != null && id.trim().length() > 0;
      @   requires name != null && name.trim().length() > 0;
      @
      @   ensures this.id == id;
      @   ensures this.name == name;
      @   // Garante que a lista foi inicializada e está vazia
      @   ensures this.loanHistory != null && this.loanHistory.isEmpty();
      @*/
    public User(String id, String name) {
        if (id == null || id.trim().isEmpty()) {
            throw new IllegalArgumentException("User ID cannot be empty.");
        }
        if (name == null || name.trim().isEmpty()) {
            throw new IllegalArgumentException("User name cannot be empty.");
        }
        
        this.id = id;
        this.name = name;
        this.loanHistory = new ArrayList<>();
    }

    /*@ public normal_behavior
      @   requires name != null && name.trim().length() > 0;
      @   // Só permite modificar o campo 'name'
      @   assignable this.name;
      @   ensures this.name == name;
      @*/
    public void setName(String name) {
        if (name == null || name.trim().isEmpty()) {
            throw new IllegalArgumentException("User name cannot be empty.");
        }
        this.name = name;
    }

    /*@ public normal_behavior
      @   // Não aceitamos adicionar empréstimos nulos
      @   requires loan != null;
      @   
      @   // O método altera o estado interno da lista loanHistory
      @   assignable loanHistory; 
      @
      @   // O tamanho da lista aumenta em 1
      @   ensures loanHistory.size() == \old(loanHistory.size()) + 1;
      @   // O elemento adicionado está presente na lista
      @   ensures loanHistory.contains(loan);
      @*/
    public void addLoanToHistory(Loan loan) {
        this.loanHistory.add(loan);
    }

    /*@ public normal_behavior
      @   ensures \result == this.id;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getId() {
        return id;
    }
    
    /*@ public normal_behavior
      @   ensures \result == this.name;
      @*/
    public /*@ pure @*/ String getName() { return name; }

    /*@ public normal_behavior
      @   // O método é puro (não altera estado), apenas retorna uma visualização
      @   ensures \result != null;
      @   // O tamanho da lista retornada é igual ao tamanho da lista interna
      @   ensures \result.size() == loanHistory.size();
      @   // Nota: Não precisamos especificar que é "unmodifiable" aqui, 
      @   // pois isso é comportamento de runtime, mas garantimos que os dados são consistentes.
      @*/
    public /*@ pure @*/ List<Loan> getLoanHistory() {
        return Collections.unmodifiableList(loanHistory);
    }

    // --- LÓGICA DE IGUALDADE ---

    /*@ also
      @   // Contrato padrão do equals:
      @   // Se o objeto for comparado com null, retorna false
      @   ensures (o == null) ==> (\result == false);
      @   // Se for o mesmo objeto (referência), retorna true
      @   ensures (this == o) ==> (\result == true);
      @   // Se for da mesma classe e tiver o mesmo ID, retorna true
      @   ensures (o instanceof User) && ((User)o).id.equals(this.id) ==> \result == true;
      @*/
    @Override
    public /*@ pure @*/ boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        User user = (User) o;
        return id.equals(user.id);
    }

    /*@ also
      @   // O hashcode deve ser consistente com o ID.
      @   // Se dois objetos são iguais (equals), seus hashcodes devem ser iguais.
      @   ensures \result == id.hashCode();
      @*/
    @Override
    public /*@ pure @*/ int hashCode() {
        return id.hashCode();
    }
}