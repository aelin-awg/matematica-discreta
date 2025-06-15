import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  static final String[] NOMS = {"Laia Lluch Pons", "Michael James Arias Sweeney"};

  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   */
  static class Tema1 {
    /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
     */
    static final char CONJ = '∧'; 
    static final char DISJ = '∨'; 
    static final char IMPL = '→'; 
    static final char NAND = '.'; 

    static int exercici1(char[] ops, int[] vars) {
        int numVars = 0;
        for (int v : vars) {
            numVars = Math.max(v, numVars);
        }
        numVars++; //El nombre de variables és el major+1 perquè comença per v0

        //Dos booleans per saber si l'expressió pot ser vertadera, falsa o ambdues
        boolean canBeTrue = false;
        boolean canBeFalse = false;

        //truthTable contindrà els diferents valors de veritat que aniran agafant les variables
        boolean[] truthTable = new boolean[numVars];
        //numCombinations són totes les combinacions de valors de les variables
        int numCombinations = (int) Math.pow(2, numVars);
        //Recorrem totes les combinacions i modifiquem els bits necessaris
        //per a representar i en binari a truthTable
        for (int i = 0; i < numCombinations; i++) {
            for (int j = 0; j < numVars; j++) {
                truthTable[j] = ((i >> j) & 1) == 1;
            }

            boolean op1 = truthTable[vars[0]]; //Primer operand de cada operació
            //Bucle per a fer totes les operacions de l'expressió
            for (int k = 0; k < ops.length; k++) {
                boolean op2 = truthTable[vars[k + 1]]; //Segon operand de cada operació
                switch (ops[k]) {
                    case CONJ: op1 = op1 && op2; break;
                    case DISJ: op1 = op1 || op2; break;
                    case IMPL: op1 = !op1 || op2; break;
                    case NAND: op1 = !(op1 && op2); break;
                }
            }
            //Ara op1 conté el resultat de tota l'expressió per a la 
            //combinació de valors actual. 
            if (op1) {
                canBeTrue = true;
            } else {
                canBeFalse = true;
            }
            //Si una expressió pot ser vertadera i falsa, no fa falta seguir mirant valors
            if (canBeTrue && canBeFalse) {
                return -1;
            }
        }
        //Si arriba fins aquí, és tautologia o contradicció
        return canBeTrue ? 1 : 0;
    }

    /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
        //Primer comprovam que tot P(x) és cert dins l'univers
        //Suposam que sí i comprovam si en algun cas no es compleix
        boolean pTrueForAllX = true;
        for (int x : universe) {
            if (!p.test(x)) {
                pTrueForAllX = false;
                break;
            }
        }
        //Ara comprovam que existeixi exactament una x tal que Q(x) és cert
        int count = 0;
        for (int x : universe) {
            if (q.test(x)) {
                count++;
            }
        }
        boolean qTrueOnce = count == 1;
        //Si ambdós són falsos o ambdós són vertaders, la proposició és certa
        return pTrueForAllX == qTrueOnce;
    }

    static void tests() {
      // Exercici 1
      // Taules de veritat

      // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
      test(1, 1, 1, () -> exercici1(new char[] { IMPL, DISJ, DISJ }, new int[] { 0, 2, 1, 0 }) == 1);

      // Contradicció: (p0 . p0) ∧ p0
      test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);

      // Exercici 2
      // Equivalència

      test(1, 2, 1, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x == 0, (x) -> x == 0);
      });

      test(1, 2, 2, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x >= 1, (x) -> x % 2 == 0);
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
   */
  static class Tema2 {
    /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
     */
    static int exercici1(int[] a) {
        /*
        Els nombres de Stirling de segona espècie (S(n,k)) compten les maneres de dividir un conjunt de n
        elements en k subconjunts. Llavors, el total de particions del conjunt seria la suma de
        tots aquests nombres per tots els valors de k entre 1 i n. Això dona el nombre de Bell (B(n)).
        */
        //Com que sen's indica que els valors no estaran repetits dins `a`, el total d'elements diferents és a.length.
        int numElements = a.length;
        int[][] numStirling = new int[numElements + 1][numElements + 1];
        numStirling[0][0] = 1; //S(0,0) = 1. Mai serà buit i podríem començar directament amb 1 element,
                               //però ens ha semblat més clar fer l'algoritme sencer

        //Omplim l'array segons S(n,k)=S(n-1,k-1)+kS(n-1,k) 
        for (int n = 1; n <= numElements; n++) {
            for (int k = 1; k <= numElements; k++) {
                numStirling[n][k] = numStirling[n - 1][k - 1] + k * numStirling[n - 1][k];
            }
        }

        //Per a calcular B(n), feim el sumatori de S(n,k) amb k de 1 a n (el nombre d'elements total)
        int numBellN = 0;
        for (int k = 1; k <= numElements; k++) {
            numBellN += numStirling[numElements][k];
        }

        return numBellN;
    }

    /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
     */
    static int exercici2(int[] a, int[][] rel) {
        /*
        Com que les clausures reflexiva i transitiva sempre existeixen, si no són ja dins de
        la relació rel, les hem d'afegir (a la clausura). Un cop es té això, s'ha de comprovar
        si aquesta pot ser antisimètrica: si aRb i bRa, llavors a=b. 
        */
        //Com que anirem afegint elements, convertim la relació inicial en un ArrayList per a
        //fer-la de mida dinàmica. 
        List<int[]> clausura = new ArrayList<>(Arrays.asList(rel));

        //Primer afegim la relació reflexiva (x,x) si no hi és ja a rel
        for (int x : a) {
            if (!contains(clausura, x, x)) {
                clausura.add(new int[]{x, x});
            }
        }

        //Ara afegim la relació transitiva. Com que cada cop que s'afegeix una parella d'elements
        //hi pot faltar una relació, utilitzarem el booleà added per a controlar-ho.
        boolean added = true;
        //El següent ArrayList guardarà les relacions que falten dins de la llista original
        //per a tenir la relació transitiva. 
        List<int[]> missingRels = new ArrayList<>();
        while (added) {
            added = false;
            missingRels.clear(); //Buidam la llista de relacions per afegir
            for (int[] r1 : clausura) {
                for (int[] r2 : clausura) {
                    //Compara el segon element de la primera relació amb el primer de la segona
                    if (r1[1] == r2[0]) {
                        //Si són iguals i la relació entre ells no està ni a clausura ni a les que
                        //falten per afegir en aquesta tanda, s'afegeix i es marca el canvi a added
                        if (!contains(clausura, r1[0], r2[1]) && !contains(missingRels, r1[0], r2[1])) {
                            missingRels.add(new int[]{r1[0], r2[1]});
                            added = true;
                        }
                    }
                }
            }
            //Afegim totes les faltants a clausura i, si s'han afegit relacions, tornam a executar el bucle
            clausura.addAll(missingRels);
        }

        //Només queda comprovar si la clausura resultant és antisimètrica: per cada parell d'elements, si
        //aquests són diferents i existeix la parella inversa, la clausura no serà antisimètrica. 
        for (int[] r : clausura) {
            if ((r[0] != r[1]) && contains(clausura, r[1], r[0])) {
                return -1;
            }
        }

        //Si arribam aquí, és ordre parcial. Falta calcular el cardinal, que és la mida de la llista
        return clausura.size();
    }

    /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
     */
    static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
        //Guardarem els elements que poden ser ínfims o suprems dins de la llista, és a dit
        //les fites inferiors o superiors segons el valor de op.
        List<Integer> fites = new ArrayList<>();
        if (!op) {
            //Cercam l'ínfim: el major element de a que és <= que tots els elements de x
            //Primer trobam les fites inferiors. 
            for (int b : a) {
                boolean isFitaInferior = true;
                for (int c : x) {
                    //Si b > c, llavors b no pot ser ínfim
                    if (!contains(rel, b, c)) {
                        isFitaInferior = false;
                        break;
                    }
                }
                if (isFitaInferior) {
                    fites.add(b);
                }
            }
            if (fites.isEmpty()) {
                return null; //No hi ha ínfim
            } else {
                //L'ínfim serà el valor major d'entre tots els valors de la fita inferior
                int infim = fites.get(0);
                for (int i = 1; i < fites.size(); i++) {
                    if (fites.get(i) > infim) {
                        infim = fites.get(i);
                    }
                }
                return infim;
            }

        } else {
            //Cercam el suprem: el menor element de a que és >= que tots els elements de x
            //Primer trobam les fites superiors.
            for (int b : a) {
                boolean isFitaSuperior = true;
                for (int c : x) {
                    //Si c > b, b no podrà ser suprem
                    if (!contains(rel, c, b)) {
                        isFitaSuperior = false;
                        break;
                    }
                }
                if (isFitaSuperior) {
                    fites.add(b);
                }
            }
            if (fites.isEmpty()) {
                return null; //No hi ha suprem
            } else {
                //El suprem és el menor d'entre els elements de la fita superior
                int suprem = fites.get(0);
                for (int i = 1; i < fites.size(); i++) {
                    if (fites.get(i) < suprem) {
                        suprem = fites.get(i);
                    }
                }
                return suprem;
            }
        }
    }

    /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
     */
    static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
        /*
        El graf de f és (x, f(x)). Com que hem de donar el graf de la inversa, ho feim
        directament com (f(x),x), amb x pertanyent a a.
        La mida serà la major entre el domini i el codomini de la inversa original,
        ja que la funció inversa ha d'anar de B -> A, però ha de poder contenir tots
        els elements segons la inversa que haguem de retornar i per a fer les comprovacions
        correctament (imatges repetides, etc.).
         */
        int[][] grafInversa = new int[Math.max(a.length, b.length)][2];
        //Omplim el graf de la inversa segons els valors del domini de la funció original.
        for (int i = 0; i < a.length; i++) {
            grafInversa[i] = new int[]{f.apply(a[i]), a[i]};
        }

        //Comprovam si és injectiva (no existeixen imatges repetides per a valors de a diferents)
        //Utilitzam a.length perquè això ens dona el total d'imatges que té la funcio original
        boolean isInjectiva = true;
        for (int i = 0; i < a.length; i++) {
            //Comparam cada element amb els següents. Si se'n troba un d'igual amb antiimatge
            //diferent, no és injectiva
            for (int j = i + 1; j < a.length; j++) {
                if ((grafInversa[i][0] == grafInversa[j][0]) && (grafInversa[i][1] != grafInversa[j][1])) {
                    isInjectiva = false;
                    break;
                }
            }
            if (!isInjectiva) {
                break;
            }
        }

        //Comprovam si és exhaustiva (tot element de b és imatge)
        boolean isExhaustiva = true;
        for (int y : b) {
            boolean found = false;
            for (int[] i : grafInversa) {
                if (i[0] == y) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                isExhaustiva = false;
                break;
            }
        }

        if (isInjectiva && isExhaustiva) {
            return grafInversa;
        } else if (isInjectiva) {
            //Com que no tot element de b es troba dins de la inversa que tenim (no és exhaustiva),
            //els hem d'afegir i assignar una antiimatge per a retornar la funció de b -> a
            int idx = a.length;
            for (int y : b) {
                boolean found = false;
                for (int[] i : grafInversa) {
                    if (i[0] == y) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    grafInversa[idx++] = new int[]{y, a[0]};
                }
            }
            return grafInversa;
        } else if (isExhaustiva) {
            //Cercam la inversa per la dreta
            int[][] inversaDreta = new int[b.length][2];
            for (int i = 0; i < b.length; i++) {
                for (int x : a) {
                    if (f.apply(x) == b[i]) {
                        inversaDreta[i] = new int[]{b[i], x};
                        break;
                    }
                }
            }
            return inversaDreta;
        } else {
            return null; //No existeix cap inversa
        }
    }
    
    /**
     * Mètode auxiliar per a cercar parelles ordenades dins d'una llista
     * @param list llista on cercar
     * @param a element [0]
     * @param b element [1]
     * @return true si la parella especificada es troba dins de la llista
     */
    static boolean contains(List<int[]> list, int a, int b) {
        for (int[] r : list) {
            if (r[0] == a && r[1] == b) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * Mètode exactament igual a l'anterior però adaptat a un array bidimensional
     * en vés d'una llista
     * @param array array on cercar
     * @param a element [0]
     * @param b element [1]
     * @return true si la parella especificada es troba dins de l'array
     */
    static boolean contains(int[][] array, int a, int b) {
        for (int[] r : array) {
            if (r[0] == a && r[1] == b) {
                return true;
            }
        }
        return false;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // Nombre de particions

      test(2, 1, 1, () -> exercici1(new int[] { 1 }) == 1);
      test(2, 1, 2, () -> exercici1(new int[] { 1, 2, 3 }) == 5);

      // Exercici 2
      // Clausura d'ordre parcial

      final int[] INT02 = { 0, 1, 2 };

      test(2, 2, 1, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 2} }) == 6);
      test(2, 2, 2, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 0}, {1, 2} }) == -1);

      // Exercici 3
      // Ínfims i suprems

      final int[] INT15 = { 1, 2, 3, 4, 5 };
      final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
      final Integer ONE = 1;

      test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[] { 2, 3 }, false)));
      test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[] { 2, 3 }, true) == null);

      // Exercici 4
      // Inverses

      final int[] INT05 = { 0, 1, 2, 3, 4, 5 };

      test(2, 4, 1, () -> {
        var inv = exercici4(INT05, INT02, (x) -> x/2);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT02.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1]/2 != i)
            return false;
        }

        return true;
      });

      test(2, 4, 2, () -> {
        var inv = exercici4(INT02, INT05, (x) -> x);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT05.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1] != i)
            return false;
        }

        return true;
      });
    }

    /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    // Especialització de generateRel per as = bs
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   */
  static class Tema3 {
    /*
     * Determinau si el graf `g` (no dirigit) té cicles.
     */
    static boolean exercici1(int[][] g) {
        boolean[] visited = new boolean[g.length];
        //Recorrem tots els vèrtexs no visitats i comprovam si són part d'un cicle
        for (int i = 0; i < g.length; i++) {
            if (!visited[i]) {
                if (cicleFound(g, visited, i, -1)) {
                    return true;
                }
            }
        }
        return false;
    }

    /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
     */
    static boolean exercici2(int[][] g1, int[][] g2) {
        //Per a què dos grafs siguin isomorfs, han de tenir el mateix nombre de nodes i arestes.
        //El nombre de nodes és el nombre de files del graf
        if (g1.length != g2.length) {
            return false;
        }
        //El nombre d'arestes és la suma de la longitud de cada fila del graf dividit entre 2
        //perquè no és dirigit
        if (countArestes(g1) != countArestes(g2)) {
            return false;
        }
        
        //Un altre tret dels grafs isomorfs és que tenen el mateix nombre de vèrtexs 
        //amb grau igual per a poder mantenir les adjacències entre nodes.
        int[] grausG1 = new int[g1.length];
        int[] grausG2 = new int[g1.length];
        for (int i = 0; i < g1.length; i++) {
            grausG1[i] = g1[i].length;
            grausG2[i] = g2[i].length;
        }
        Arrays.sort(grausG1);
        Arrays.sort(grausG2);
        if (!Arrays.equals(grausG1, grausG2)) {
            return false;
        }
        
        /*  
        A partir d'aquí, els dos grafs tenen el mateix ordre, la mateixa mida i el 
        mateix nombre de nodes amb grau igual. 
        Per a comprovar si són isomorfs, anam provant permutacions del graf i comprovam
        si alguna d'aquestes manté les adjacències dels nodes del primer graf
        */
        int[] perm = new int[g1.length];
        for (int i = 0; i < g1.length; i++) {
            perm[i] = i;
        }

        while (nextPerm(perm)) {
            if (isIsomorf(g1, g2, perm)) {
                //Ens basta trobar una permutació de nodes que compleixi el criteri
                return true;
            }
        }
        //Si arriba fins aquí, és perquè no són isomorfs
        return false;
    }

    /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
     */
    static int[] exercici3(int[][] g, int r) {
        //Per a comprovar que és un arbre, hem de comprovar que |E| = |V| - 1
        if (countArestes(g) != (g.length - 1)) {
            return null;
        }
        //Per a ser arbre, també ha de ser connex i no pot tenir cicles. Reutilitzarem
        //el mètode usar a l'exercici 1 per a cercar cicles a partir del node 0. 
        boolean[] visited = new boolean[g.length];
        if (cicleFound(g, visited, 0, -1)) {
            return null;
        }
        //Si no s'han visitat tots els nodes, el graf no és connex i, per tant, no és arbre
        for (boolean v : visited) {
            if (!v) {
                return null;
            }
        }

        //Per als arbres, cercam el recorregut en postordre
        Arrays.fill(visited, false); //Reiniciam les visites
        List<Integer> postordre = new ArrayList<>();
        findPostordre(g, visited, postordre, r, -1);
        //Pasam l'ArrayList a array
        int[] postordreArr = new int[postordre.size()];
        for (int i = 0; i < postordreArr.length; i++) {
            postordreArr[i] = postordre.get(i);
        }
        return postordreArr;
    }

    /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
     */
    static int exercici4(char[][] mapa) {
        int rows = mapa.length;
        int columns = mapa[0].length;

        //Començam cercant la posició de 'O'
        int posOX = 0;
        int posOY = 0;
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < columns; j++) {
                if (mapa[i][j] == 'O') {
                    posOX = i;
                    posOY = j;
                }
            }
        }

        //Utilitzarem l'algorisme de Dijkstra per a trobar el camí més curt
        //Inicialitzam les distàncies entre nodes amb el valor màxim
        int[][] distances = new int[rows][columns];
        for (int i = 0; i < rows; i++) {
            Arrays.fill(distances[i], Integer.MAX_VALUE);
        }
        //Modificam la distància del node 'O' a 0
        distances[posOX][posOY] = 0;

        //Guardarem els nodes que es poden visitar des de l'origen dins d'una llista
        List<int[]> notExplored = new ArrayList<>();
        notExplored.add(new int[]{posOX, posOY});

        //Començam el recorregut fins que no quedin pendents o trobem 'D'
        while (!notExplored.isEmpty()) {
            int minDistance = Integer.MAX_VALUE;
            int minIdx = -1;
            for (int i = 0; i < notExplored.size(); i++) {
                int[] pos = notExplored.get(i);
                if (distances[pos[0]][pos[1]] < minDistance) {
                    minDistance = distances[pos[0]][pos[1]];
                    minIdx = i;
                }
            }

            //Quan hem trobat el node amb distància mínima, hem de comprovar els adjacents
            int[] minPos = notExplored.remove(minIdx);
            int x = minPos[0];
            int y = minPos[1];

            //Si aquest node és 'D' ja, retornam la distància
            if (mapa[x][y] == 'D') {
                return distances[x][y];
            }

            //Comprovam el node superior
            if (((x - 1) >= 0) && (mapa[x - 1][y] != '#')) {
                //Comprovam que realment no és un graf amb pesos, utilitzem pes = 1. 
                //Comparam la distància fins al nou "node" amb la distància anterior
                //per a assegurar el camí més curt i l'afegim als nodes pendents d'explorar
                if ((distances[x][y] + 1) < distances[x - 1][y]) {
                    distances[x - 1][y] = distances[x][y] + 1;
                    notExplored.add(new int[]{x - 1, y});
                }
            }
            //Comprovam el node inferior
            if (((x + 1) < rows) && (mapa[x + 1][y] != '#')) {
                if ((distances[x][y] + 1) < distances[x + 1][y]) {
                    distances[x + 1][y] = distances[x][y] + 1;
                    notExplored.add(new int[]{x + 1, y});
                }
            }
            //Comprovam el node a l'esquerra
            if (((y - 1) >= 0) && (mapa[x][y - 1] != '#')) {
                if ((distances[x][y] + 1) < distances[x][y - 1]) {
                    distances[x][y - 1] = distances[x][y] + 1;
                    notExplored.add(new int[]{x, y - 1});
                }
            }
            //Comprovam el node a la dreta
            if (((y + 1) < columns) && (mapa[x][y + 1] != '#')) {
                if ((distances[x][y] + 1) < distances[x][y + 1]) {
                    distances[x][y + 1] = distances[x][y] + 1;
                    notExplored.add(new int[]{x, y + 1});
                }
            }
        }
        //Si arriba fins aquí, és perquè no s'ha trobat cap camí
        return -1;
    }
    
    /**
     * Mètode recursiu per a cercar cicles dins d'un graf.
     * @param graph graf a explorar
     * @param visited control dels nodes ja explorats
     * @param currentV node actual
     * @param parentV node pare del node actual
     * @return true si el graf conté un cicle
     */
    static boolean cicleFound(int[][] graph, boolean[] visited, int currentV, int parentV) {
        visited[currentV] = true;
        for (int adjacentV : graph[currentV]) {
            if (!visited[adjacentV]) {
                //Utilitzam el mètode recursivament passant el node actual com a node pare de l'adjacent
                if (cicleFound(graph, visited, adjacentV, currentV)) {
                    return true;
                    //Es va propagant el valor true cap amunt fins a tornar al mètode de l'exercici
                }
            } else if (adjacentV != parentV) {
                //Trobam un node adjacent ja visitat que no és el pare de l'actual,
                //significa que hi ha un altre camí que duu a un node ja visitat i, per tant,
                //el graf té cicle.
                return true;
            }
        }
        return false;
    }
    
    /**
     * Mètode per a comptar les arestes d'un graf no dirigit. Cada aresta es compta
     * dos cops, per això s'ha de dividir el resultat entre 2. 
     * @param graph 
     * @return nombre total d'arestes del graf no dirigit
     */
    static int countArestes(int[][] graph) {
        int e = 0;
        for (int[] adjacents : graph) {
            e += adjacents.length;
        }
        return e/2;
    }
    
    /**
     * Mètode per a generar la següent permutació d'un int[]. 
     * @param perm array amb la permutació actual
     * @return true si s'ha generat una nova permutació, false si l'actual és la darrera
     */
    static boolean nextPerm(int[] perm) {
        //Comprovam si ja és la darrera
        int i = 0, j = perm.length - 1;
        while ((i < perm.length) && (perm[i] == j)) {
            i++;
            j--;
        }
        if (i == perm.length) {
            return false; //És la darrera permutació
        }

        //Cercam el primer element des de la dreta que sigui menor que el següent
        i = perm.length - 2;
        while (perm[i] > perm[i + 1]) {
            i--;
        }

        //Cercam l'element més petit a la dreta de i que sigui més gran que perm[i]
        j = perm.length - 1;
        while (perm[j] < perm[i]) {
            j--;
        }

        //Intercanviam els valors i i j
        int change = perm[i];
        perm[i] = perm[j];
        perm[j] = change;

        //Reorganitzam els elements a la dreta de i en ordre ascendent
        for (i++, j = perm.length - 1; i < j; i++, j--) {
            change = perm[i];
            perm[i] = perm[j];
            perm[j] = change;
        }
        return true;
    }
    
    /**
     * Mètode per a determinar si dos grafs són isomorfs amb la permutació actual. 
     * S'aplica la permutació al g1 mitjançant un array nou per a evitar modificar
     * l'original i es comparen les adjacències de nodes amb el g2.
     * @param g1 graf al qual aplicar la permutació
     * @param g2 graf objectiu
     * @param perm permutació actual a aplicar
     * @return true si s'ha trobat una permutació tal que es mantenen les arestes
     * originals al nou graf, false si aquesta permutació de nodes no compleix la condició
     */
    static boolean isIsomorf(int[][] g1, int[][] g2, int[] perm) {
        //Hem de comprovar que els nodes adjacents es mantenen en el segon graf
        for (int i = 0; i < g1.length; i++) {
            int[] originalAjacents = g1[i];
            int[] newAdjacents = new int[originalAjacents.length];
            //Aplicam la permutació als nodes adjacents del primer graf
            for (int j = 0; j < originalAjacents.length; j++) {
                newAdjacents[j] = perm[originalAjacents[j]];
            }
            Arrays.sort(newAdjacents);

            int[] correctAdjacents = Arrays.copyOf(g2[perm[i]], g2[perm[i]].length);
            Arrays.sort(correctAdjacents);

            //Llavors, si els nodes adjacents nous no coincideixen amb els nodes adjacents
            //del graf 2, aquesta permutació no fa que els adjacents es mantinguin.
            if (!Arrays.equals(newAdjacents, correctAdjacents)) {
                return false;
            }
        }
        return true;
    }
    
    /**
     * Mètode per a recórrer un arbre en postordre. Es visiten els nodes fills per ordre
     * d'esquerra a dreta i es van afegint a la llista en postordre quan ja no tenen nodes
     * adjacents sense visitar. Llavors, el primer element afegit és el node fill més a
     * l'esquerra de l'arbre i el darrer és l'arrel per la recursivitat del mètode. 
     * @param graph graf que s'analitza
     * @param visited control dels nodes ja explorats
     * @param postordre llista amb l'ordre dels nodes demanat
     * @param currentV node actual
     * @param parentV node pare de l'actual
     */
    static void findPostordre(int[][] graph, boolean[] visited, List<Integer> postordre, int currentV, int parentV) {
        visited[currentV] = true;
        for (int adjacentV : graph[currentV]) {
            if (!visited[adjacentV]) {
                findPostordre(graph, visited, postordre, adjacentV, currentV);
            }
        }
        postordre.add(currentV);
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {

      final int[][] D2 = { {}, {} };
      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] T1 = { {1, 2}, {0}, {0} };
      final int[][] T2 = { {1}, {0, 2}, {1} };

      // Exercici 1
      // G té cicles?

      test(3, 1, 1, () -> !exercici1(D2));
      test(3, 1, 2, () -> exercici1(C3));

      // Exercici 2
      // Isomorfisme de grafs

      test(3, 2, 1, () -> exercici2(T1, T2));
      test(3, 2, 2, () -> !exercici2(T1, C3));

      // Exercici 3
      // Postordre

      test(3, 3, 1, () -> exercici3(C3, 1) == null);
      test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[] { 1, 2, 0 }));

      // Exercici 4
      // Laberint

      test(3, 4, 1, () -> {
        return -1 == exercici4(new char[][] {
            " #O".toCharArray(),
            "D# ".toCharArray(),
            " # ".toCharArray(),
        });
      });

      test(3, 4, 2, () -> {
        return 8 == exercici4(new char[][] {
            "###D".toCharArray(),
            "O # ".toCharArray(),
            " ## ".toCharArray(),
            "    ".toCharArray(),
        });
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
     */
    static int[] exercici1(String msg, int n, int e) {
        //Primer aconseguim els codis ASCII de l'String
        byte[] asciiString = msg.getBytes();
        //Com que seràn blocs de longitud 2, retornarem un array amb la meitat d'elements
        int[] encrypted = new int[msg.length() / 2];
        for (int i = 0; i < encrypted.length; i++) {
            //Agafem els bytes a encriptar
            int ascii1 = asciiString[2 * i];
            int ascii2 = asciiString[2 * i + 1];
            //Combinam els dos caràcters en un bloc. Com que els caràcters van de 32
            //a 127, multiplicam el primer per 128 (igual que a classe per *26 quan
            //utilitzàvem l'alfabet amb les lletres de 0 a 25)
            int block = (ascii1 * 128) + ascii2;
            //Encriptam el bloc
            encrypted[i] = RSA(block, n, e);
        }
        return encrypted;
    }

    /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     */
    static String exercici2(int[] m, int n, int e) {
        /*Primer desencriptam el missatge, necessitam trobar d = e^(-1) mod Φ(N)
            per a poder calcular missatge ^ d mod N.
            Sabem que N és la multiplicació de dos primers, llavors basta trobar un nombre
            primer que divideixi a N.
        */
        int p = 0;
        int q = 0;
        for (int i = 2; i <= n; i++) {
            if (n % i == 0) {
                p = i;
                q = n / i;
                break;
            }
            //Si el 2 no es factor, podemos saltarnos todos los números pares
            if (i != 2) {
                i += 1;
            }
        }
        //Φ(N) = Φ(p)*Φ(q). Com que p i q són primers, Φ(p) = p-1.
        int phiN = (p - 1) * (q - 1);

        //d = invers de e mod phiN tal que (d*e)%phiN == 1
        int d;
        for (d = 1; d < phiN; d++) {
            if ((d * e) % phiN == 1) {
                break;
            }
        }

        //Desencriptam fent el procés invers a l'exercici anterior
        byte[] decrypted = new byte[m.length * 2]; //Cada bloc té longitud 2
        for (int i = 0; i < m.length; i++) {
            int block = RSA(m[i], n, d);
            int ascii2 = block % 128;
            int ascii1 = ((block - ascii2) / 128) % 128;
            decrypted[2 * i] = (byte) ascii1;
            decrypted[2 * i + 1] = (byte) ascii2;
        }
        //Convertim l'array de bytes en String
        return new String(decrypted);
    }

    /**
     * Mètode per a aplicar el xifrat RSA a un bloc codificat en ASCII mitjançant
     * els paràmetres n i e de la clau pública o n i d de la clau privada. 
     * @param block bloc a xifrar
     * @param n mòdul aplicat
     * @param exp exponent a aplicar (e o d)
     * @return el bloc encriptat
     */
    static int RSA(int block, int n, int exp) {
        int encryptedBlock = 1;
        block = block % n;

        while (exp > 0) {
            //Si l'exponent és senar
            if ((exp % 2) != 0) {
                encryptedBlock = (encryptedBlock * block) % n;
            }
            //Si l'exponent és parell, base = (x*x) i exponent = exponent/2
            block = (block * block) % n;
            exp = exp / 2;
        }
        return encryptedBlock;
    }
    
    static void tests() {
      // Exercici 1
      // Codificar i encriptar
      test(4, 1, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = exercici1("Patata", n, e);
        return Arrays.equals(encr, new int[] { 4907, 4785, 4785 });
      });

      // Exercici 2
      // Desencriptar i decodificar
      test(4, 2, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = new int[] { 4907, 4785, 4785 };
        var decr = exercici2(encr, n, e);
        return "Patata".equals(decr);
      });
    }
  }

  /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    System.out.println("---- Tema 1 ----");
    Tema1.tests();
    System.out.println("---- Tema 2 ----");
    Tema2.tests();
    System.out.println("---- Tema 3 ----");
    Tema3.tests();
    System.out.println("---- Tema 4 ----");
    Tema4.tests();
  }

  // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
  static void test(int tema, int exercici, int test, BooleanSupplier p) {
    try {
      if (p.getAsBoolean())
        System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
      else
        System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
    } catch (Exception e) {
      if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
        System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
      } else {
        System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
        e.printStackTrace();
      }
    }
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
