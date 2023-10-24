#lang eopl

; Juan Sebastian Cifuentes Vallejo - 202179800
; Maria Alejandra Carvajal Perez - 202178495
; Yissy Katherine Posso Perea - 202181910

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| GRAMATICA:
<programa> :=  <expresion>
               un-programa (exp)


<expresion> := <numero>
               numero-lit (num)

            := "\""<texto> "\""
               texto-lit (txt)

            := <identificador>
               var-exp (id)

            := (<expresion> <primitiva-binaria> <expresion>)
               primapp-bin-exp (exp1 prim-binaria exp2)

            := <primitiva-unaria> (<expresion>)
               primapp-un-exp (prim-unaria exp)

            := Si <expresion> entonces <expresion>  sino <expresion> finSI
               condicional-exp (test-exp true-exp false-exp)

            := declarar (<identificador> = <expresion> (;)) { <expresion> }
               variableLocal-exp (ids exps cuerpo)

            := procedimiento (<identificador>*',') haga <expresion> finProc
               procedimiento-ex (ids cuero)

            :=  "evaluar" expresion   (expresion ",")*  finEval
                app-exp(exp exps) 


<primitiva-binaria> :=  + (primitiva-suma)

                    :=  ~ (primitiva-resta)

                    :=  / (primitiva-div)

                    :=  * (primitiva-multi)

                    :=  concat (primitiva-concat)


<primitiva-unaria> :=  longitud (primitiva-longitud)

                   :=  add1 (primitiva-add1)

                   :=  sub1 (primitiva-sub1)


|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Especificación Léxica:

(define scanner-spec-simple-interpreter
  '(
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    (numero (digit (arbno digit) "." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)
  
    (texto ("\"" (arbno (or letter digit whitespace "?")) "\"") string)
    ;(texto (letter (arbno (or letter digit whitespace "?"))) string)
  
    (identificador ("@" letter (arbno (or letter digit))) symbol)
  
    (espacio (whitespace) skip)
    (comentario ("%" (arbno (not #\newline))) skip)
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Especificación Sintáctica (gramática):

(define grammar-simple-interpreter
  '(
    (programa (expresion) un-programa)
    
    (expresion (numero) numero-lit)
    (expresion (texto) texto-lit)
    ;(expresion ("\"" texto "\"") texto-lit)
    (expresion (identificador) var-exp)
    (expresion ("(" expresion primitiva-binaria expresion ")") primapp-bin-exp)
    (expresion (primitiva-unaria "(" expresion ")") primapp-un-exp)

    (expresion ("Si" expresion "entonces" expresion "sino" expresion "finSI") condicional-exp)

    (expresion ("declarar" "(" (arbno identificador "=" expresion ";") ")" "{" expresion "}") variableLocal-exp)

    (expresion ("procedimiento" "(" (separated-list identificador ",") ")" "haga" expresion "finProc") procedimiento-ex)

    (expresion ("evaluar" expresion "(" (separated-list expresion ",") ")"  "finEval") app-exp)
    
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("concat") primitiva-concat)
    
    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Tipos de datos para la sintaxis abstracta de la gramática:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados):

(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Analizador Léxico (Scanner):

(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Interpretador (FrontEnd + Evaluación + señal para lectura ):

(define interpretador
  (sllgen:make-rep-loop "--> "
    (lambda (pgm) (eval-program  pgm))
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)

(define eval-program
  (lambda (pgm)
    (cases programa pgm
      (un-programa (exp)
                 (eval-expression exp (init-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scheme-value? (lambda (v) #t))
;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record (syms (list-of symbol?))
                       (vals (list-of scheme-value?))
                       (env environment?)))

;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)))

;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

; Funciones auxiliar para encontrar la posición de un símboloen la lista de símbolos de unambiente
(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))
;función que busca un símbolo en un ambiente
(define buscar-variable
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'buscar-variable "Error, la variable ~s no existe" sym))
      (extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable env sym)))))))

; Ambiente inicial
(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e)
     '(1 2 3 "hola" "FLP")
     (empty-env))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evalua la expresión en el ambiente de entrada
(define eval-expression
  (lambda (exp env)
    (cases expresion exp
      (numero-lit (num) num)
      (texto-lit (txt) (substring txt 1 (- (string-length txt) 1)))
      (var-exp (id) (buscar-variable env id))
      (primapp-bin-exp (exp1 prim-binaria exp2) (aplicar-primitiva-binaria prim-binaria (eval-expression exp1 env) (eval-expression exp2 env)))
      (primapp-un-exp (prim-unaria exp) (aplicar-primitiva-unaria prim-unaria (eval-expression exp env)))
      (condicional-exp (test-exp true-exp false-exp)
        (if (valor-verdad? (eval-expression test-exp env))
          (eval-expression true-exp env)
          (eval-expression false-exp env)))
      (variableLocal-exp (ids exps cuerpo)
        (let ((args (eval-exps exps env)))
          (eval-expression cuerpo (extend-env ids args env))))
      (procedimiento-ex (ids cuerpo) (cerradura ids cuerpo env))
      (app-exp (exp exps)
        (let ((proc (eval-expression exp env)) (args (eval-exps exps env)))
          (if (procVal? proc)
              (apply-procedure proc args)
              (eopl:error 'eval-expression "Attempt to apply non-procedure ~s" proc))))
    )
  )
)

; Funciones auxiliares para evaluar variableLocal-exp's
(define eval-exps
  (lambda (exps env)
    (map (lambda (x) (eval-rand x env)) exps)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))


; Funciones auxiliares para evaluar procedimiento-ex's
(define-datatype procVal procVal?
  (cerradura
    (lista-ID (list-of symbol?))
    (exp expresion?)
    (amb environment?); <------ Cambiar nombre de enviroment a ambiente (y todos los demas)
  )
)

(define apply-procedure
  (lambda (proc args)
    (cases procVal proc
      (cerradura (ids body env)
               (eval-expression body (extend-env ids args env))))))


                                 
; Funcion que aplica las operaciones binarias (las del tipo primitiva-binaria)
(define aplicar-primitiva-binaria
  (lambda (t-primitiva-binaria exp-1 exp-2)
    (cases primitiva-binaria t-primitiva-binaria
      (primitiva-suma () (+ exp-1 exp-2))
      (primitiva-resta () (- exp-1 exp-2))
      (primitiva-div () (/ exp-1 exp-2))
      (primitiva-multi () (* exp-1 exp-2))
      (primitiva-concat () (string-append exp-1 exp-2))
    )
  )
)

; Funcion que aplica las operaciones unarias (las del tipo primitiva-unaria)
(define aplicar-primitiva-unaria
  (lambda (t-primitiva-unaria exp-1)
    (cases primitiva-unaria t-primitiva-unaria
      (primitiva-longitud () (string-length exp-1))
      (primitiva-add1 () (+ exp-1 1))
      (primitiva-sub1 () (- exp-1 1))
    )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;valor-verdad?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define valor-verdad?
  (lambda (x)
    (not (zero? x))))