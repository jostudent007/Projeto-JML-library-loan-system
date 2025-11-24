# 📚 Sistema de Gerenciamento de Biblioteca (Especificação JML)

![Java](https://img.shields.io/badge/Java-21-blue?logo=java)
![Maven](https://img.shields.io/badge/Maven-3.8%2B-red?logo=apachemaven)
![JML](https://img.shields.io/badge/JML-OpenJML-orange)
![License](https://img.shields.io/badge/License-MIT-green)

Projeto desenvolvido para a disciplina de **Lógica Aplicada à Engenharia de Software**.
O objetivo principal deste repositório é aplicar **Especificação Formal** utilizando **JML (Java Modeling Language)** em um sistema de gerenciamento de biblioteca, garantindo a corretude do software através da abordagem de *Design by Contract* (Projeto por Contrato).

---

## 🧑‍💻 Autores

* **[Joadson Ferreira do Nascimento]**
* **[Paulo Sérgio da Silva Junior]**

## 🎯 Objetivo do Projeto

Diferente de implementações focadas apenas na funcionalidade, este projeto visa demonstrar o uso de lógica formal para validar o comportamento do software. O código foi anotado com especificações JML para definir rigorosamente:

* **Invariantes de Classe:** Propriedades que devem ser sempre verdadeiras para os objetos do sistema.
* **Pré-condições (`requires`):** O que deve ser verdade antes de um método ser executado.
* **Pós-condições (`ensures`):** O que o método garante que será verdade após sua execução.
* **Sinais (`signals`):** As exceções que o método pode lançar e sob quais condições.

---

## ✨ Funcionalidades do Sistema

O sistema (o "objeto de estudo") implementa as seguintes funcionalidades, sobre as quais as regras lógicas foram aplicadas:

* **Gestão de Usuários:** Cadastro e listagem.
* **Gestão de Acervo:** Cadastro de livros Físicos (com estoque) e Digitais (estoque infinito).
* **Operações de Empréstimo:** Realizar empréstimo e devolução, respeitando as regras de disponibilidade.
* **Consultas e Relatórios:** Listagem de disponibilidade e relatórios de empréstimos ativos.
* **Utilitários:** Carga de dados (seed) para testes.

---

## 🏛️ Arquitetura e Especificação Lógica

O sistema segue uma arquitetura em camadas, onde cada camada recebeu um tipo específico de atenção na especificação JML:

### 1. Model (`/model`) - Invariantes
As entidades (`User`, `Book`, `Loan`) contêm as **Invariantes de Classe**.
* *Exemplo de Lógica:* Um livro nunca pode ter um número negativo de cópias disponíveis (`invariant totalCopies >= 0;`). Um empréstimo deve ter sempre uma data de início válida.
* Essas anotações garantem a consistência dos dados em qualquer momento da execução.

### 2. Service (`/service`) - Contratos de Operação
É aqui que reside o coração do **Design by Contract**. Os serviços (`LoanService`, etc.) possuem pré e pós-condições detalhadas.
* **Pré-condições:** O método de empréstimo exige que o usuário exista e que o livro tenha cópias disponíveis (`requires book.isAvailable();`).
* **Pós-condições:** Garante que, após o empréstimo, o estoque do livro foi decrementado em 1 e o registro do empréstimo foi criado (`ensures book.getAvailableCopies() == \old(book.getAvailableCopies()) - 1;`).

### 3. Repository (`/repository`)
Define a abstração do acesso aos dados.
* As interfaces foram anotadas com especificações `model` (campos fantasmas do JML) para simular o comportamento de armazenamento e permitir a verificação estática sem precisar de um banco de dados real.

---

## 🛠️ Tecnologias Utilizadas

* **Java 21:** Linguagem base.
* **JML (Java Modeling Language):** Linguagem de especificação comportamental.
* **OpenJML:** Ferramenta utilizada para checagem de sintaxe e verificação estática das anotações (ESC - Extended Static Checking).
* **Maven:** Gerenciamento de dependências.

---

## 🚀 Compilando e Verificando

### 1. Compilação Java (Standard)
Para compilar o projeto como um software Java comum:

```bash
mvn clean package
```

2. Verificação com JML (Opcional)
Caso tenha o OpenJML configurado em sua máquina, você pode verificar as especificações lógicas (exemplo de comando genérico):

```bash
java -jar openjml.jar -rac -dirs src/main/java/br/ufrn/library
```

# Ou para verificação estática (ESC):

```bash
java -jar openjml.jar -esc -dirs src/main/java/br/ufrn/library
```

(Nota: As anotações JML estão dentro de comentários //@ ou /*@ ... @*/, portanto, não afetam a execução normal do Java se o compilador JML não for usado).

🏃‍♀️ Executando o Sistema
Para testar a aplicação rodando (Runtime):

No terminal, na raiz do projeto:

```bash
mvn exec:java -Dexec.mainClass="br.ufrn.library.Library"
```
Passo Recomendado: Ao iniciar, utilize a Opção 9 ("Carregar Dados") para popular o sistema com dados de teste e verificar se as regras de negócio (e suas especificações subjacentes) estão sendo respeitadas.
