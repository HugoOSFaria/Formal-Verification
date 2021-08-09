def solucaoWrite(matriz,valor):
    linhas = len(matriz)
    colunas = len(matriz[0])
    f = open("solucao.txt","w")

    for i in range(0,linhas):
        string = "Linha " + str(i) + " : "
        for j in range(0,colunas):
            string = string+str(matriz[i][j])+" | "
        string = string+str(valor[i][colunas])+"\n"
        f.write(string)
    string = "          "
    for j in range(0,colunas-1):
        string = string+str(valor[linhas][j])+" | "
    string = string+str(valor[linhas][j])+" |"
    string = string+"\n"
    f.write(string)

from z3 import *
file = input("Enter puzzle file name:\n")
matriz = []
matrizVar = []
solver = Solver()
with open(file) as fp:
    for line in fp:
        line = line.strip('\n')
        newLines = line.split(',')
        matriz.append(newLines)
linhas = len(matriz)-1
colunas = len(matriz[0])-1

#Declara todas as variáveis
for i in range(0,linhas):
    linhaVar = []
    for j in range(0,colunas):
        linhaVar.append(Int("x"+str(i)+str(j)))
    matrizVar.append(linhaVar)

#Todos distintos
dist = [ Distinct([ matrizVar[l][c] for l in range(linhas) for c in range(colunas) ]) ]
solver.add(dist)

#Tudo maior que 0
maior_zero = [matrizVar[l][c] > 0 for c in range(colunas) for l in range(linhas)]
solver.add(maior_zero)

#Soma de linhas
linhas_sum = [ And(sum([ matrizVar[l][c] for c in range(colunas) ]) == matriz[l][colunas]) for l in range(linhas)]
solver.add(linhas_sum)

#Soma de colunas
colunas_sum = [ And(sum([ matrizVar[l][c] for l in range(linhas) ]) == matriz[linhas][c]) for c in range(colunas)]
solver.add(colunas_sum)

for i in range(0, linhas):
    for j in range(0,colunas):
        if matriz[i][j] != " ":
            solver.add(matrizVar[i][j] == matriz[i][j])

print(solver.check())
if solver.check() == sat:
    m = solver.model()
    r = [ [ m.evaluate(matrizVar[i][j]) for j in range(colunas) ]
          for i in range(linhas) ]
    print_matrix(r)
    solucaoWrite(r,matriz)
else:
    print ("failed to solve")
