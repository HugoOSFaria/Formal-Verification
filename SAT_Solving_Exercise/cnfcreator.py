import os
def createDic():
    global dictionary
    counter = 1
    dictionary = {}
    for linha in range(1,5):
        for coluna in range(1,5):
            for numero in range(1,5):
                key = "x"+str(linha)+str(coluna)+str(numero)
                dictionary[key] = counter
                counter+=1
def getDictValue(number):
    actual_key = "x"+number
    return str(dictionary.get(actual_key))


f = open("dimacs.cnf","w")
N = 4
createDic()
for linha in range(1,N+1):
    for coluna in range(1,N+1):
        for numero in range(1,N+1):
            key = ""+str(linha)+str(coluna)+str(numero)
            f.write(str(getDictValue(key)))
            f.write(" ")
        f.write("0\n")
for linha in range(1,N+1):
    for coluna in range(1,N+1):
        for numero in range(1,N+1):
            for b in range(numero+1,N+1):
                key1 = str(linha)+str(coluna)+str(numero)
                key2 = str(linha)+str(coluna)+(str(b))
                insert = "-"+str(getDictValue(key1))+" -"+str(getDictValue(key2))
                f.write(insert)
                f.write(" 0\n")
for linha in range(1,N+1):
    for numero in range(1,N+1):
        for coluna in range(1,N+1):
            for b in range(coluna+1,N+1):
                key1 = str(linha)+str(coluna)+str(numero)
                key2 = str(linha)+str(b)+(str(numero))
                insert = "-"+str(getDictValue(key1))+" -"+str(getDictValue(key2))
                f.write(insert)
                f.write(" 0\n")
for coluna in range(1,N+1):
    for numero in range(1,N+1):
        for linha in range(1,N+1):
            for b in range(linha+1,N+1):
                key1 = str(linha)+str(coluna)+str(numero)
                key2 = str(b)+str(coluna)+(str(numero))
                insert = "-"+str(getDictValue(key1))+" -"+str(getDictValue(key2))
                f.write(insert)
                f.write(" 0\n")
for numero in range(1,N+1):
    texto = str("-"+getDictValue("11"+str(numero))+" -"+getDictValue("12"+str(numero))+" 0\n"+
    "-"+getDictValue("11"+str(numero))+" -"+getDictValue("21"+str(numero))+" 0\n"+
    "-"+getDictValue("11"+str(numero))+" -"+getDictValue("22"+str(numero))+" 0\n"+
    "-"+getDictValue("12"+str(numero))+" -"+getDictValue("21"+str(numero))+" 0\n"+
    "-"+getDictValue("12"+str(numero))+" -"+getDictValue("22"+str(numero))+" 0\n"+
    "-"+getDictValue("21"+str(numero))+" -"+getDictValue("22"+str(numero))+" 0\n")
    f.write(texto)
    texto = str("-"+getDictValue("13"+str(numero))+" -"+getDictValue("14"+str(numero))+" 0\n"+
    "-"+getDictValue("13"+str(numero))+" -"+getDictValue("23"+str(numero))+" 0\n"+
    "-"+getDictValue("14"+str(numero))+" -"+getDictValue("23"+str(numero))+" 0\n"+
    "-"+getDictValue("13"+str(numero))+" -"+getDictValue("23"+str(numero))+" 0\n"+
    "-"+getDictValue("14"+str(numero))+" -"+getDictValue("24"+str(numero))+" 0\n"+
    "-"+getDictValue("23"+str(numero))+" -"+getDictValue("24"+str(numero))+" 0\n")
    f.write(texto)
    texto = str("-"+getDictValue("31"+str(numero))+" -"+getDictValue("32"+str(numero))+" 0\n"
    +"-"+getDictValue("31"+str(numero))+" -"+getDictValue("41"+str(numero))+" 0\n"
    +"-"+getDictValue("31"+str(numero))+" -"+getDictValue("42"+str(numero))+" 0\n"
    +"-"+getDictValue("32"+str(numero))+" -"+getDictValue("41"+str(numero))+" 0\n"
    +"-"+getDictValue("32"+str(numero))+" -"+getDictValue("42"+str(numero))+" 0\n"
    +"-"+getDictValue("41"+str(numero))+" -"+getDictValue("42"+str(numero))+" 0\n")
    f.write(texto)
    texto = str("-"+getDictValue("33"+str(numero))+" -"+getDictValue("34"+str(numero))+" 0\n"
    +"-"+getDictValue("33"+str(numero))+" -"+getDictValue("43"+str(numero))+" 0\n"
    +"-"+getDictValue("33"+str(numero))+" -"+getDictValue("44"+str(numero))+" 0\n"
    +"-"+getDictValue("34"+str(numero))+" -"+getDictValue("44"+str(numero))+" 0\n"
    +"-"+getDictValue("34"+str(numero))+" -"+getDictValue("43"+str(numero))+" 0\n"
    +"-"+getDictValue("43"+str(numero))+" -"+getDictValue("44"+str(numero))+" 0\n")
    f.write(texto)
newline = ''
while newline != 'quit':
    newline = input("Há algum número já no sudoku? Se sim introduzir linha coluna e número, se não escrever quit\n")
    if newline != 'quit':
        f.write(str(getDictValue(newline)))
        f.write(" 0\n")
f.close()
