;Declarar as variáveis
;int M[3][3];
;    M[1][1] = 2;
;    M[1][2] = 3;
;    M[1][3] = 4;
;    M[2][1] = 3;
;    M[2][2] = 4;
;    M[2][3] = 5;
;    M[3][1] = 4;
;    M[3][2] = 5;
;    M[3][3] = 6;

;Exercicio 1.2:

(declare-const M0 (Array Int (Array Int Int)))
(declare-const M1 (Array Int (Array Int Int)))
(declare-const M2 (Array Int (Array Int Int)))
(declare-const M3 (Array Int (Array Int Int)))
(declare-const M4 (Array Int (Array Int Int)))
(declare-const M5 (Array Int (Array Int Int)))
(declare-const M6 (Array Int (Array Int Int)))
(declare-const M7 (Array Int (Array Int Int)))
(declare-const M8 (Array Int (Array Int Int)))
(declare-const M9 (Array Int (Array Int Int)))

(assert (= M1 (store M0 1 (store (select M0 1) 1 2))))
(assert (= M2 (store M1 1 (store (select M1 1) 2 3))))
(assert (= M3 (store M2 1 (store (select M2 1) 3 4))))
(assert (= M4 (store M3 2 (store (select M3 2) 1 3))))
(assert (= M5 (store M4 2 (store (select M4 2) 2 4))))
(assert (= M6 (store M5 2 (store (select M5 2) 3 5))))
(assert (= M7 (store M6 3 (store (select M6 3) 1 4))))
(assert (= M8 (store M7 3 (store (select M7 3) 2 5))))
(assert (= M9 (store M8 3 (store (select M8 3) 3 6))))

(check-sat)
(push)
(echo "--------------------")

;Exercicio 1.3

;Se i = j então M[i][j] != 3
;(i = j) -> (M[i][j] != 3)

(declare-fun i () Int)
(declare-fun j () Int)

(assert (not(=> (= i j) (not(= (select (select M9 i) j) 3)))))

(check-sat)
(echo "A)SAT logo e refutavel")
(echo "--------------------")
(pop)
(push)

;Como i e j não estão restringidos entre 1 e 3 não sabemos o que acontece com a matriz para lá dos valores de 1 a 3 então
;não podemos afirmar que a afirmação é verdadeira
;No entanto se restringirmos entre 1 e 3 verificamos que a afirmação é sempre verdadeira, como podemos ver a seguir :

(declare-fun i () Int)
(declare-fun j () Int)

(assert (and (>= i 1) (<= i 3)))
(assert (and (>= j 1) (<= j 3)))
(assert (not(=> (= i j) (not(= (select (select M9 i) j) 3)))))

(check-sat)
(echo "A.1) Exemplo e UNSAT logo nao e refutavel")
(echo "--------------------")
(pop)
(push)

;Para quaisquer i e j entre 1 e 3, M[i][j] = M[j][i]
;-(M[i][j] = M[j][i])
;M[i][j] != M[j][i]

(declare-fun i () Int)
(declare-fun j () Int)

(assert (and (>= i 1) (<= i 3)))
(assert (and (>= j 1) (<= j 3)))
(assert (not(= (select (select M9 i) j) (select (select M9 j) i))))

(check-sat)
(echo "B) UNSAT logo nao e refutavel")
(echo "--------------------")
(pop)
(push)

;Como podemos ver, o solver confirma a afirmação dentro da restrição dada

;Para quaisquer i e j entre 1 e 3, se i < j então M[i][j] < 6.
;-(i < j -> M[i][j] < 6)

(declare-fun i () Int)
(declare-fun j () Int)

(assert (and (>= i 1) (<= i 3)))
(assert (and (>= j 1) (<= j 3)))
(assert (not(=> (< i j) (< (select (select M9 i) j) 6))))

(check-sat)
(echo "D) UNSAT logo nao e refutavel")
(echo "--------------------")
(pop)
(push)

; Para quaisquer i, a e b entre 1 e 3, se a > b então M[i][a] > M[i][b].
;-(a > b -> M[i][a] > M[i][b])

(declare-fun i () Int)
(declare-fun a () Int)
(declare-fun b () Int)

(assert (and (>= i 1) (<= i 3)))
(assert (and (>= a 1) (<= a 3)))
(assert (and (>= b 1) (<= b 3)))

(assert (not(=> (> a b) (> (select (select M9 i) a) (select (select M9 i) b)))))

(check-sat)
(echo "D) UNSAT logo nao e refutavel")
(echo "--------------------")
(pop)
(push)

;Como podemos ver, o solver confirma a afirmação dentro da restrição dada

;Para quaisquer i e j entre 1 e 3, M[i][j] + M[i+1][j+1] = M[i+1][j] + M[i][j+1].
;-(M[i][j] + M[i+1][j+1] = M[i+1][j] + M[i][j+1])

(declare-fun i () Int)
(declare-fun j () Int)

(assert (and (>= i 1) (<= i 3)))
(assert (and (>= j 1) (<= j 3)))
(assert (not(=(+ (select (select M9 i) j) (select (select M9 (+ i 1)) (+ j 1))) (+ (select (select M9 (+ i 1)) j) (select (select M9 i) (+ j 1))))))

(check-sat)
(echo "E) SAT logo e refutavel")
(pop)
(push)

;Neste caso a afirmação é refutável uma vez que não conseguimos saber o que aconteceria nos casos que i ou j +1 são 4
