#!/bin/bash

# ================= CONFIGURAÇÕES =================
OPENJML="$HOME/Documents/openjml/openjml"
SRC="src/main/java"
MODEL_PKG="br/ufrn/library/model"

# ================= EXECUÇÃO =================
echo "=========================================="
echo "Iniciando verificação JML..."
echo "OpenJML: $OPENJML"
echo "=========================================="

if [ ! -f "$OPENJML" ]; then
    echo "ERRO: OpenJML não encontrado em $OPENJML"
    exit 1
fi

# COMANDO EM UMA LINHA SÓ (Para evitar erros de sintaxe)
# Flags:
#   -esc: Use ESC prover
#   --purity-check=false: Desativa verificações de pureza para reduzir falsos positivos
#   -cp: Classpath
$OPENJML -esc --purity-check=false -cp $SRC $SRC/$MODEL_PKG/Loan.java #$SRC/$MODEL_PKG/Loan.java $SRC/$MODEL_PKG/User.java $SRC/$MODEL_PKG/DigitalBook.java

# Para testar manualmente usar (mudando apenas o caminho do arquivo a ser testado):
# ~/Documents/openjml/openjml -esc -cp src/main/java src/main/java/br/ufrn/library/model/PhysicalBook.java src/main/java/br/ufrn/library/model/User.java
# Ou usar para verificar uma pasta inteira: ~/Documents/openjml/openjml -esc -cp src/main/java src/main/java/br/ufrn/library/model/*.java
echo "=========================================="
echo "Verificação concluída."