
# Konstrukcja `for`

`for comprehension` to idealna abstrakcja do pisania funkcyjnych programów komunikujących się ze światem.
Ponieważ będziemy używać jej bardzo często, poświęcimy chwilę na przypomnienie sobie zasad jej działania, a
przy okazji zobaczymy, jak Scalaz może pomóc nam pisać czystszy kod.

Ten rozdział nie skupia się na programowaniu czysto funkcyjnym, a techniki w nim opisane znajdą zastosowanie
również w zwykłych aplikacjach.

## Wzbogacona składnia

Konstrukcja `for` w Scali jest prostą regułę przepisania (_rewrite rule_), zwaną również *cukrem składniowym* (_syntactic sugar_), 
i nie wnosi żadnych dodatkowych informacji do naszego programu.

Aby zobaczyć, co tak naprawdę robi `for`, użyjemy funkcji `show` i `reify` dostępnych w REPLu. Dzięki nim możemy
wypisać kod w formie, jaką przyjmuje po inferencji typów (_type inference_). 

{lang="text"}
~~~~~~~~
  scala> import scala.reflect.runtime.universe._
  scala> val a, b, c = Option(1)
  scala> show { reify {
           for { i <- a ; j <- b ; k <- c } yield (i + j + k)
         } }
  
  res:
  $read.a.flatMap(
    ((i) => $read.b.flatMap(
      ((j) => $read.c.map(
        ((k) => i.$plus(j).$plus(k)))))))
~~~~~~~~

Widzimy dużo szumu spowodowanego dodatkowymi wzbogaceniami (np. `+` jest przepisany jako `$plus` itp.). 
Dla zwiększenia zwięzłości w dalszych przykładach pominiemy wywołania `show` oraz `reify`, kiedy linia rozpoczyna się 
od `reify>`. Dodatkowo generowany kod poddamy ręcznemu oczyszczeniu, aby nie rozpraszać czytelnika.

{lang="text"}
~~~~~~~~
  reify> for { i <- a ; j <- b ; k <- c } yield (i + j + k)
  
  a.flatMap {
    i => b.flatMap {
      j => c.map {
        k => i + j + k }}}
~~~~~~~~

Zasadą kciuka jest, że każdy `<-` (zwany *generatorem*) jest równoznaczny z zagnieżdżonym wywołaniem `flatMap`,
z wyjątkiem ostatniego, który jest wywołaniem funkcji `map`, do której przekazane zostaje ciało bloku `yield`.

### Przypisania

Możemy bezpośrednio przypisywać wartości do zmiennych za pomocą wyrażeń typu `ij = i + j` (słowo kluczowe `val` nie jest wymagane).

{lang="text"}
~~~~~~~~
  reify> for {
           i <- a
           j <- b
           ij = i + j
           k <- c
         } yield (ij + k)
  
  a.flatMap {
    i => b.map { j => (j, i + j) }.flatMap {
      case (j, ij) => c.map {
        k => ij + k }}}
~~~~~~~~

Wywołanie `map` na `b` wprowadza zmienną `ij`, która jest flat-mapowana razem z `j`, a na końcu
wołane jest ostateczne `map` wykorzystujące kod z bloku `yield`.

Niestety nie możemy deklarować przypisań przed użyciem generatora. Funkcjonalność ta
została zasugerowana, ale nie została jeszcze zaimplementowana: 
<https://github.com/scala/bug/issues/907>

{lang="text"}
~~~~~~~~
  scala> for {
           initial = getDefault
           i <- a
         } yield initial + i
  <console>:1: error: '<-' expected but '=' found.
~~~~~~~~

Możemy obejść to ograniczenie poprzez zadeklarowanie zmiennej poza konstrukcją `for`

{lang="text"}
~~~~~~~~
  scala> val initial = getDefault
  scala> for { i <- a } yield initial + i
~~~~~~~~

lub poprzez stworzenie `Option` z pierwotnej wartości

{lang="text"}
~~~~~~~~
  scala> for {
           initial <- Option(getDefault)
           i <- a
         } yield initial + i
~~~~~~~~


A> Słowo kluczowe `val`, oprócz przypisywania pojedynczych wartości, wspiera także dowolne wyrażenia dopasowania.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   scala> val (first, second) = ("hello", "world")
A>   first: String = hello
A>   second: String = world
A>   
A>   scala> val list: List[Int] = ...
A>   scala> val head :: tail = list
A>   head: Int = 1
A>   tail: List[Int] = List(2, 3)
A> ~~~~~~~~
A> 
A> Tak samo działa przypisywanie wewnątrz `for`
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   scala> val maybe = Option(("hello", "world"))
A>   scala> for {
A>            entry <- maybe
A>            (first, _) = entry
A>          } yield first
A>   res: Some(hello)
A> ~~~~~~~~
A> 
A> Trzeba jednak uważać, aby nie pominąć żadnego z wariantów, gdyż skutkować to będzie wyjątkiem wyrzuconym w trakcie 
A> działania programu (a w konsekwencji zaburzeniem *totalności*).
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   scala> val a :: tail = list
A>   caught scala.MatchError: List()
A> ~~~~~~~~


### Filtrowanie

Możemy umieścić wyrażenie `if` za generatorem, aby ograniczyć wartości za pomocą predykatu

{lang="text"}
~~~~~~~~
  reify> for {
           i  <- a
           j  <- b
           if i > j
           k  <- c
         } yield (i + j + k)
  
  a.flatMap {
    i => b.withFilter {
      j => i > j }.flatMap {
        j => c.map {
          k => i + j + k }}}
~~~~~~~~

Starsze wersje Scali używały metody `filter`, ale ponieważ `Traversable.filter` tworzy nową kolekcję dla każdego predykatu,
wprowadzono metodę `withFilter` jako bardziej wydajną alternatywę. Musimy uważać, aby przypadkowo nie wywołać `withFilter`, podając informację 
co do oczekiwanego typu, którą kompilator interpretuje jako pattern matching.

{lang="text"}
~~~~~~~~
  reify> for { i: Int <- a } yield i
  
  a.withFilter {
    case i: Int => true
    case _      => false
  }.map { case i: Int => i }
~~~~~~~~

Podobnie jak w przypadku przypisywania wartości do zmiennych, generatory mogą używać pattern matchingu po swojej lewej stronie. W przeciwieństwie 
do przypisań (które rzucają `MatchError` w przypadku niepowodzenia), generatory są *filtrowane* i nie rzucają wyjątków 
w czasie wykonania. Niestety dzieje się to kosztem podwójnego zaaplikowania wzoru.

A> Plugin kompilatora [`better-monadic-for`](https://github.com/oleg-py/better-monadic-for) produkuje alternatywną, **lepszą**
A> wersję kodu niż oryginalny kompilator Scali. Poniższy przykład:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   reify> for { i: Int <- a } yield i
A> ~~~~~~~~
A>
A> jest interpretowany jako
A>
A> {lang="text"}
A> ~~~~~~~~
A>   a.map { (i: Int) => i}
A> ~~~~~~~~
A> 
A> zamiast nieefektywnego podwójnego dopasowywania (w najlepszym przypadku) i potajemnego filtrowania
A> wartości w czasie wykonania (w przypadku najgorszym). Używanie wysoce zalecane!

### For Each

Jeśli nie użyjemy słowa `yield`, kompilator użyje metody `foreach` zamiast `flatMap`, co ma sens
jedynie w obecności efektów ubocznych.

{lang="text"}
~~~~~~~~
  reify> for { i <- a ; j <- b } println(s"$i $j")
  
  a.foreach { i => b.foreach { j => println(s"$i $j") } }
~~~~~~~~


### Podsumowanie

Pełen zbiór metod używanych przez konstrukcję `for` nie ma jednego wspólnego interfejsu, a każde użycie jest 
niezależnie kompilowane. Gdyby taki interfejs istniał, wyglądałby mniej więcej tak:

{lang="text"}
~~~~~~~~
  trait ForComprehensible[C[_]] {
    def map[A, B](f: A => B): C[B]
    def flatMap[A, B](f: A => C[B]): C[B]
    def withFilter[A](p: A => Boolean): C[A]
    def foreach[A](f: A => Unit): Unit
  }
~~~~~~~~

Jeśli kontekst (`C[_]`) konstrukcji `for` nie dostarcza swoich własnych metod `map` i `flatMap` 
to nie wszystko jeszcze stracone. Jeśli dostępna jest niejawna instancja typu `scalaz.Bind[C]`
to dostarczy ona potrzebne metody `map` oraz `flatMap`.

A> Deweloperzy często zaskakiwani są faktem, że operacje oparte o typ `Future` i zdefiniowane wewnątrz konstrukcji `for`
A> nie są wykonywane równolegle:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   import scala.concurrent._
A>   import ExecutionContext.Implicits.global
A>   
A>   for {
A>     i <- Future { expensiveCalc() }
A>     j <- Future { anotherExpensiveCalc() }
A>   } yield (i + j)
A> ~~~~~~~~
A> 
A> Dzieje się tak, ponieważ funkcja przekazana do metody `flatMap`, która wywołuje `anotherExpensiveCalc`, wykonuje się wyłącznie
A> **po** zakończeniu `expensiveCalc`. Aby wymusić równoległe wykonanie tych dwóch operacji, musimy utworzyć je poza
A> konstrukcją `for`.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   val a = Future { expensiveCalc() }
A>   val b = Future { anotherExpensiveCalc() }
A>   for { i <- a ; j <- b } yield (i + j)
A> ~~~~~~~~
A> 
A> Konstrukcja `for` zaprojektowana jest wyłącznie do definiowania programów sekwencyjnych. W jednym z następnych
A> rozdziałów pokażemy o wiele lepszą metodę definiowania obliczeń równoległych. Spoiler: nie używaj typu `Future`.


## Obsługa błędów

Jak dotąd patrzyliśmy jedynie na reguły przepisywania, nie natomiast na to, co dzieje się wewnątrz metod `map` i `flatMap`.
Zastanówmy się co dzieje się, kiedy kontekst `for` zadecyduje, że nie może kontynuować działania.

W przykładzie bazującym na typie `Option` blok `yield` wywoływany jest jedynie kiedy wartości wszystkich zmiennych 
`i, j, k` są zdefiniowane.

{lang="text"}
~~~~~~~~
  for {
    i <- a
    j <- b
    k <- c
  } yield (i + j + k)
~~~~~~~~

Jeśli którakolwiek ze zmiennych `a, b, c` przyjmie wartość `None`, konstrukcja `for` zrobi zwarcie[^zwarcie] i zwróci `None`, nie mówiąc
nam co poszło nie tak.

[^zwarcie]: Z angielskiego _short-circuits_ - zakończenie przetwarzania bez wykonywania pozostałych instrukcji.

A> W praktyce możemy zobaczyć wiele funkcji z parametrami typu `Option`, które w rzeczywistości muszą być zdefiniowane,
A> aby uzyskać sensowny rezultat. Alternatywą do rzucania wyjątku jest użycie konstrukcji `for`, która zapewni nam totalność
A> naszej funkcji (zwrócenie wartości dla każdego możliwego argumentu):
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   def namedThings(
A>     someName  : Option[String],
A>     someNumber: Option[Int]
A>   ): Option[String] = for {
A>     name   <- someName
A>     number <- someNumber
A>   } yield s"$number ${name}s"
A> ~~~~~~~~
A> 
A> jest to jednak rozwiązanie rozwlekłe, niezdarne i w złym stylu. Jeśli funkcja wymaga wszystkich swoich argumentów,
A> to powinna zadeklarować takie wymaganie jawnie, spychając tym samym obowiązek obsłużenia brakujących wartości na 
A> wywołującego tę funkcję.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   def namedThings(name: String, num: Int) = s"$num ${name}s"
A> ~~~~~~~~

Jeśli użyjemy typu `Either`, wtedy `Left` powodować będzie zwarcie konstrukcji `for` z dodatkową informacją, którą niesie w sobie.
Rozwiązanie to jest zdecydowanie lepsze w przypadku raportowania błędów niż użycie typu `Option`:

{lang="text"}
~~~~~~~~
  scala> val a = Right(1)
  scala> val b = Right(2)
  scala> val c: Either[String, Int] = Left("sorry, no c")
  scala> for { i <- a ; j <- b ; k <- c } yield (i + j + k)
  
  Left(sorry, no c)
~~~~~~~~

Na koniec spójrzmy co stanie się z typem `Future`, który zawiedzie

{lang="text"}
~~~~~~~~
  scala> import scala.concurrent._
  scala> import ExecutionContext.Implicits.global
  scala> for {
           i <- Future.failed[Int](new Throwable)
           j <- Future { println("hello") ; 1 }
         } yield (i + j)
  scala> Await.result(f, duration.Duration.Inf)
  caught java.lang.Throwable
~~~~~~~~

Wartość `Future`, która wypisuje wiadomość do terminala, nie jest nigdy tworzona, ponieważ, 
tak jak w przypadku `Option` i `Either`, konstrukcja `for` zwiera obwód i zakańcza przetwarzanie.

Zwieranie obwodu w przypadku odejścia od oczekiwanej ścieżki przetwarzania jest ważnym i często spotykanym rozwiązaniem.
Pamiętajmy, że konstrukcja `for` nie jest w stanie obsłużyć uprzątnięcia zasobów (_resource cleanup_), a więc nie ma możliwości wyrażenia zachowania 
podobnego do `try`/`finally`. Rozwiązanie to jest dobre, gdyż jasno deklaruje, że to kontekst 
(który zazwyczaj jest `Monad`ą, jak zobaczymy później), a nie logika biznesowa, jest odpowiedzialny za obsługę błędów 
i uprzątnięcie zasobów.


## Sztuczki

Chociaż łatwo jest przepisać prosty kod sekwencyjny przy pomocy konstrukcji `for`,
czasami chcielibyśmy zrobić coś, co w praktyce wymaga mentalnych fikołków. Ten rozdział zbiera
niektóre praktyczne przykłady i pokazuje jak sobie z nimi radzić.


### Wyjście awaryjne

Powiedzmy, że wywołujemy metodę, która zwraca typ `Option`. Jeśli wywołanie to się nie powiedzie,
chcielibyśmy użyć innej metody (i tak dalej i tak dalej), np. gdy używamy cache'a.

{lang="text"}
~~~~~~~~
  def getFromRedis(s: String): Option[String]
  def getFromSql(s: String): Option[String]
  
  getFromRedis(key) orElse getFromSql(key)
~~~~~~~~

Jeśli chcemy zrobić to samo poprzez asynchroniczną wersję tego samego API

{lang="text"}
~~~~~~~~
  def getFromRedis(s: String): Future[Option[String]]
  def getFromSql(s: String): Future[Option[String]]
~~~~~~~~

musimy uważać, aby nie spowodować zbędnych obliczeń, ponieważ

{lang="text"}
~~~~~~~~
  for {
    cache <- getFromRedis(key)
    sql   <- getFromSql(key)
  } yield cache orElse sql
~~~~~~~~

uruchomi oba zapytania. Możemy użyć pattern matchingu na pierwszym rezultacie, ale typ się nie zgadza

{lang="text"}
~~~~~~~~
  for {
    cache <- getFromRedis(key)
    res   <- cache match {
               case Some(_) => cache !!! wrong type !!!
               case None    => getFromSql(key)
             }
  } yield res
~~~~~~~~

Musimy stworzyć `Future` ze zmiennej `cache`.

{lang="text"}
~~~~~~~~
  for {
    cache <- getFromRedis(key)
    res   <- cache match {
               case Some(_) => Future.successful(cache)
               case None    => getFromSql(key)
             }
  } yield res
~~~~~~~~

`Future.successful` tworzy nową wartość typu `Future`, podobnie jak konstruktor typu `Option` lub
`List`.


### Wczesne wyjście

Powiedzmy, że znamy warunek, który pozwala nam szybciej zakończyć obliczenia z poprawną wartością.

Jeśli chcemy zakończyć je szybciej z błędem, standardowym sposobem na zrobienie tego w OOP[^oop] jest rzucenie wyjątku

[^oop]: _Object Oriented Programming_

{lang="text"}
~~~~~~~~
  def getA: Int = ...
  
  val a = getA
  require(a > 0, s"$a must be positive")
  a * 10
~~~~~~~~

co można zapisać asynchronicznie jako

{lang="text"}
~~~~~~~~
  def getA: Future[Int] = ...
  def error(msg: String): Future[Nothing] =
    Future.failed(new RuntimeException(msg))
  
  for {
    a <- getA
    b <- if (a <= 0) error(s"$a must be positive")
         else Future.successful(a)
  } yield b * 10
~~~~~~~~

Lecz jeśli chcemy zakończyć obliczenia z poprawną wartością, prosty kod synchroniczny:

{lang="text"}
~~~~~~~~
  def getB: Int = ...
  
  val a = getA
  if (a <= 0) 0
  else a * getB
~~~~~~~~

przekłada się na zagnieżdżone konstrukcje `for`, gdy tylko nasze zależności staną się asynchroniczne:

{lang="text"}
~~~~~~~~
  def getB: Future[Int] = ...
  
  for {
    a <- getA
    c <- if (a <= 0) Future.successful(0)
         else for { b <- getB } yield a * b
  } yield c
~~~~~~~~

A> Jeśli dostępna jest domyślna instancja `Monad[T]` dla `T[_]` (co oznacza, że `T` jest monadyczne), wówczas
A> Scalaz pozwala nam tworzyć instancje `T[A]` używając wartości `a: A` poprzez wywołanie `a.pure[T]`.
A> 
A> Scalaz dostarcza instancję `Monad[Future]` a `.pure[Future]` wywołuje `Future.successful`.
A> Poza tym, że `pure` jest nieco bardziej zwięzłe, jest to pojęcie ogólne, które aplikuje się do typów innych niż `Future`,
A> a przez to jest to rozwiązanie rekomendowane.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   for {
A>     a <- getA
A>     c <- if (a <= 0) 0.pure[Future]
A>          else for { b <- getB } yield a * b
A>   } yield c
A> ~~~~~~~~


## Łączenie kontekstów

Kontekst, którego używamy wewnątrz konstrukcji `for`, musi być niezmienny: nie możemy mieszać wielu różnych typów jak 
na przykład `Future` i `Option`.

{lang="text"}
~~~~~~~~
  scala> def option: Option[Int] = ...
  scala> def future: Future[Int] = ...
  scala> for {
           a <- option
           b <- future
         } yield a * b
  <console>:23: error: type mismatch;
   found   : Future[Int]
   required: Option[?]
           b <- future
                ^
~~~~~~~~

Nie ma nic, co pozwoliłoby nam mieszać dowolne dwa konteksty wewnątrz konstrukcji `for`, ponieważ nie da się zdefiniować znaczenia takiej operacji.

Jednak gdy mamy do czynienia z konkretnymi kontekstami intencja jest zazwyczaj oczywista, tymczasem 
kompilator nadal nie przyjmuje naszego kodu.

{lang="text"}
~~~~~~~~
  scala> def getA: Future[Option[Int]] = ...
  scala> def getB: Future[Option[Int]] = ...
  scala> for {
           a <- getA
           b <- getB
         } yield a * b
                   ^
  <console>:30: error: value * is not a member of Option[Int]
~~~~~~~~

Chcielibyśmy, aby konstrukcja `for` zajęła się zewnętrznym kontekstem i pozwoliła nam
skupić się modyfikacji wartości wewnątrz instancji typu `Option`. 
Ukrywaniem zewnętrznego kontekstu zajmują się tzw. transformatory monad (_monad transformers_), 
a Scalaz dostarcza nam implementacje tychże dla typów `Option` i `Either`, nazywające się 
odpowiednio `OptionT` oraz `EitherT`.

Kontekst zewnętrzny może być dowolnym kontekstem, który sam w sobie kompatybilny jest z konstrukcją `for`,
musi jedynie pozostać niezmienny.

Tworzymy instancję `OptionT` z każdego wywołania metody, zmieniając tym samym kontekst z `Future[Option[_]]` 
na `OptionT[Future, _]`.

{lang="text"}
~~~~~~~~
  scala> val result = for {
           a <- OptionT(getA)
           b <- OptionT(getB)
         } yield a * b
  result: OptionT[Future, Int] = OptionT(Future(<not completed>))
~~~~~~~~

`.run` pozwala nam wrócić do oryginalnego kontekstu

{lang="text"}
~~~~~~~~
  scala> result.run
  res: Future[Option[Int]] = Future(<not completed>)
~~~~~~~~

Transformatory monad pozwalają nam mieszać wywołania funkcji zwracających `Future[Option[_]]` z
funkcjami zwracającymi po prostu `Future` poprzez metodę `.liftM[OptionT]` (pochodzącą ze scalaz):

{lang="text"}
~~~~~~~~
  scala> def getC: Future[Int] = ...
  scala> val result = for {
           a <- OptionT(getA)
           b <- OptionT(getB)
           c <- getC.liftM[OptionT]
         } yield a * b / c
  result: OptionT[Future, Int] = OptionT(Future(<not completed>))
~~~~~~~~

Dodatkowo możemy mieszać wartości typu `Option` poprzez wywołanie
`Future.successful` (lub `.pure[Future]`), a następnie `OptionT`.

{lang="text"}
~~~~~~~~
  scala> def getD: Option[Int] = ...
  scala> val result = for {
           a <- OptionT(getA)
           b <- OptionT(getB)
           c <- getC.liftM[OptionT]
           d <- OptionT(getD.pure[Future])
         } yield (a * b) / (c * d)
  result: OptionT[Future, Int] = OptionT(Future(<not completed>))
~~~~~~~~

Znów zrobił się mały bałagan, ale i tak jest lepiej niż gdybyśmy ręcznie pisali zagnieżdżone 
wywołania metod `flatMap` oraz `map`. Możemy nieco uprzątnąć za pomocą  DSLa który obsłuży
wszystkie wymagane konwersje

{lang="text"}
~~~~~~~~
  def liftFutureOption[A](f: Future[Option[A]]) = OptionT(f)
  def liftFuture[A](f: Future[A]) = f.liftM[OptionT]
  def liftOption[A](o: Option[A]) = OptionT(o.pure[Future])
  def lift[A](a: A)               = liftOption(Option(a))
~~~~~~~~

w połączeniu z operatorem `|>`, który aplikuje funkcje podaną po prawej stronie na argumencie 
podanym z lewej strony, możemy wizualnie oddzielić logikę od transformacji.

{lang="text"}
~~~~~~~~
  scala> val result = for {
           a <- getA       |> liftFutureOption
           b <- getB       |> liftFutureOption
           c <- getC       |> liftFuture
           d <- getD       |> liftOption
           e <- 10         |> lift
         } yield e * (a * b) / (c * d)
  result: OptionT[Future, Int] = OptionT(Future(<not completed>))
~~~~~~~~

A> `|>` jest często nazywany *operatorem drozda* z powodu jego podobieństwa do tego słodkiego ptaka.
A> Ci, który nie lubią operatorów symbolicznych, mogą użyć aliasu `.into`. 

To podejście działa również dla `Either` i innych typów danych, ale w ich przypadku metody pomocnicze są bardziej skomplikowane
i wymagają dodatkowy parametrów. Scalaz dostarcza wiele transformatorów
monad dla typów, które definiuje, więc zawsze 
warto sprawdzić, czy ten, którego potrzebujemy jest dostępny.


# Projektowanie aplikacji

W tym rozdziale napiszemy logikę biznesową oraz testy dla czysto funkcyjnej aplikacji serwerowej.
Kod źródłowy tej aplikacji dostępny jest wraz ze źródłami tej książki w katalogu `example`.
Nie mniej lepiej nie zagłębiać się w niego, zanim nie dotrzemy do ostatniego rozdziału, gdyż
wraz z poznawaniem technik FP będziemy go istotnie zmieniać.

## Specyfikacja

Nasza aplikacja będzie zarządzać farmą serwerów, tworzoną na bazie zapotrzebowania i operującą z możliwie niskim
budżetem. Będzie ona nasłuchiwać wiadomości od serwera CI [Drone](https://github.com/drone/drone) i uruchamiać
agenty (maszyny robocze) używając [Google Container Engine](https://cloud.google.com/container-engine/) (GKE), tak aby 
zaspokoić potrzeby kolejki zadań.

{width=60%}
![](images/architecture.png)

Drone otrzymuje pracę do wykonania kiedy kontrybutor zgłasza pull request w obsługiwanym projekcie na githubie.
Drone przydziela pracę swoim agentom, gdzie każdy z nich przetwarza jedno zadanie w danym momencie.

Zadaniem naszej aplikacji jest zagwarantować, że zawsze jest dość agentów, aby wykonać potrzebną pracę, 
jednocześnie dbając, aby ich liczba nie przekroczyła określonej granicy i minimalizując całkowite koszta.
Aby tego dokonać potrzebna będzie liczba elementów w *kolejce* i liczba dostępnych *agentów*.

Google potrafi tworzyć węzły (_nodes_), każdy z nich może być gospodarzem dla wielu agentów równocześnie.
Agent podczas startu rejestruje się w serwerze, który od tej pory kontroluje jego cykl życia (wliczając 
cykliczne weryfikowanie czy agent jest nadal aktywny).

GKE pobiera opłatę za każdą minutę działania węzła, zaokrąglając czas do najbliższej godziny. Aby osiągnąć maksymalną 
efektywność, nie możemy po prostu tworzyć nowych węzłów dla każdego zadania. Zamiast tego powinniśmy reużywać
wcześniej stworzone węzły i utrzymywać je do 58 minuty ich działania. 

Nasza aplikacja musi być w stanie uruchamiać i zatrzymywać węzły, sprawdzać ich status (np. czas działania, aktywność)
oraz wiedzieć, jaki jest aktualny czas wg GKE.

Dodatkowo, nie jest dostępne żadne API, które pozwoliłoby rozmawiać bezpośrednio z danym *agentem*, tak więc nie wiemy,
czy aktualnie wykonuje on jakąś pracę dla serwera. Jeśli przypadkowo zatrzymamy agenta w czasie wykonywania pracy,
jest to niewygodne, gdyż wymaga ludzkiej interakcji i ponownego rozpoczęcia zadania.

Kontrybutorzy mogą ręcznie dodawać agentów do farmy, tak więc liczba agentów i węzłów może być różna. Nie musimy
dodawać węzłów, jeśli dostępni są wolni agenci.

W przypadku awarii powinniśmy zawsze wybierać najtańszą opcję.

Zarówno Drone, jak i GKE udostępniają JSONowe REST API zabezpieczone OAuth 2.0.


## Interfejsy i algebry

Spróbujmy teraz skodyfikować diagram architektury z poprzedniego rozdziału. Po pierwsze powinniśmy zdefiniować
prosty typ danych do przechowywania znacznika czasu z dokładnością do milisekund. Niestety typ taki nie
jest dostępny ani w bibliotece standardowej Javy ani Scali.

{lang="text"}
~~~~~~~~
  import scala.concurrent.duration._
  
  final case class Epoch(millis: Long) extends AnyVal {
    def +(d: FiniteDuration): Epoch = Epoch(millis + d.toMillis)
    def -(e: Epoch): FiniteDuration = (millis - e.millis).millis
  }
~~~~~~~~

W FP *algebra* zajmuje miejsce *interfejsu* z Javy lub zbioru poprawnych wiadomości obsługiwanych
przez aktora z Akki. W tej właśnie warstwie definiujemy wszystkie operacje naszego systemu, które 
prowadzą do komunikacji ze światem zewnętrznym a tym samym do efektów ubocznych.

Istnieje ścisła więź między algebrami a logiką biznesową. Często przechodzić będziemy przez kolejne iteracje,
w których próbujemy zamodelować nasz problem, następnie implementujemy rozwiązanie, tylko po to, aby przekonać się,
że nasz model i zrozumienie problemu wcale nie było tak kompletne, jak nam się wydawało.

{lang="text"}
~~~~~~~~
  trait Drone[F[_]] {
    def getBacklog: F[Int]
    def getAgents: F[Int]
  }
  
  final case class MachineNode(id: String)
  trait Machines[F[_]] {
    def getTime: F[Epoch]
    def getManaged: F[NonEmptyList[MachineNode]]
    def getAlive: F[Map[MachineNode, Epoch]]
    def start(node: MachineNode): F[MachineNode]
    def stop(node: MachineNode): F[MachineNode]
  }
~~~~~~~~

Użyliśmy typu `NonEmptyList`, który można łatwo utworzyć, wywołując metodę `.toNel` na standardowej liście, co zwraca nam
`Option[NonEmptyList]`. Poza tym wszystko powinno być jasne.


A> Dobrą praktyką w FP jest odzwierciedlenie ograniczeń (_constraints_) zarówno w typach przyjmowanych, **jak i** zwracanych z 
A> funkcji --- oznacza to, że nigdy nie musimy obsługiwać sytuacji, które nie mają prawa się zdążyć. Jednocześnie
A> podejście to kłóci się z *prawem Postela*: "bądź liberalny względem tego, co przyjmujesz od innych"[^postel].
A>
A> I chociaż zgadzamy się, że typy parametrów powinny być tak ogólne, jak to tylko możliwe, to nie zgadzamy się,
A> że funkcja powinna przyjmować typ `Seq`, jeśli nie potrafi obsłużyć pustej kolekcji tego typu. Inaczej zmuszeni jesteśmy
A> wyrzucić wyjątek, tym samym tracąc totalność funkcji i powodując efekt uboczny. 
A>
A> Dlatego też wybieramy `NonEmptyList` nie dlatego, że jest to lista, ale dlatego, że gwarantuje ona nam obecność 
A> przynajmniej jednego elementu. Kiedy lepiej poznamy hierarchie typeclass ze Scalaz, poznamy również lepszy sposób na
A> wyrażenie tej gwarancji.

[^postel]: _Be conservative in what you do, be liberal in what you accept from others_

## Logika biznesowa

Teraz przyszedł czas na napisanie logiki biznesowej, która definiuje zachowanie naszej aplikacji.
Na razie rozpatrywać będziemy tylko szczęśliwy scenariusz (_happy path_).

Potrzebujemy klasy `WorldView`, która przechowywać będzie całość naszej wiedzy o świecie. 
Gdybyśmy projektowali naszą aplikację przy użyciu Akki, `WorldView` najprawdopodobniej
zostałby zaimplementowany jako `var` wewnątrz stanowego aktora.

`WorldView` agreguje wartości zwracane przez wszystkie metody ze wcześniej zdefiniowanych algebr
oraz dodaje pole `pending`, aby umożliwić śledzenie nieobsłużonych jeszcze żądań.

{lang="text"}
~~~~~~~~
  final case class WorldView(
    backlog: Int,
    agents: Int,
    managed: NonEmptyList[MachineNode],
    alive: Map[MachineNode, Epoch],
    pending: Map[MachineNode, Epoch],
    time: Epoch
  )
~~~~~~~~

Teraz prawie gotowi jesteśmy, aby zacząć pisać naszą logikę biznesową, ale musimy zadeklarować, że zależy ona
od algebr `Drone` in `Machines`.

Możemy zacząć od interfejsu dla naszej logiki

{lang="text"}
~~~~~~~~
  trait DynAgents[F[_]] {
    def initial: F[WorldView]
    def update(old: WorldView): F[WorldView]
    def act(world: WorldView): F[WorldView]
  }
~~~~~~~~

i zaimplementować go za pomocą *modułu*. Moduł zależy wyłącznie od innych modułów, algebr i czystych funkcji oraz 
potrafi abstrahować nad `F`. Jeśli implementacja algebraicznego interfejsu zależy od konkretnego typu, np. `IO`,
nazywamy ją *interpreterem*.

{lang="text"}
~~~~~~~~
  final class DynAgentsModule[F[_]: Monad](D: Drone[F], M: Machines[F])
    extends DynAgents[F] {
~~~~~~~~

Ograniczenie kontekstu (_context bound_) poprzez typ `Monad` oznacza, że `F` jest *monadyczne*, pozwalając nam tym samym na używanie
metod `map`, `pure`, i oczywiście, `flatmap` wewnątrz konstrukcji `for`.

Mamy dostęp do algebr `Drone` i `Machines` poprzez `D` i `M`. Używanie pojedynczych wielkich liter jest popularną konwencją
dla implementacji algebr i typeklas.

Nasza logika biznesowa działać będzie wewnątrz nieskończonej pętli, która może być zapisana jako pseudokod:

{lang="text"}
~~~~~~~~
  state = initial()
  while True:
    state = update(state)
    state = act(state)
~~~~~~~~


### `initial`

Wewnątrz metody `initial` wywołujemy wszystkie zewnętrzne serwisy, a wyniki tych wywołań zapisujemy wewnątrz
instancji `WorldView`.  Pole `pending` domyślnie pozostaje puste.

{lang="text"}
~~~~~~~~
  def initial: F[WorldView] = for {
    db <- D.getBacklog
    da <- D.getAgents
    mm <- M.getManaged
    ma <- M.getAlive
    mt <- M.getTime
  } yield WorldView(db, da, mm, ma, Map.empty, mt)
~~~~~~~~

Przypomnij sobie, jak w Rozdziale 1 mówiliśmy, że `flatMap` (używany wraz z generatorem `<-`)
pozwala nam operować na wartościach dostępnych w czasie wykonania. Kiedy zwracamy `F[_]` to tak naprawdę
zwracamy kolejny program, który zostanie zinterpretowany w czasie wykonania. Na takim programie wywołujemy `flatMap`.
Tak właśnie możemy sekwencyjnie łączyć kod, który powoduje efekty uboczne, jednocześnie mogąc używać zupełnie czystej
(pozbawionej tychże efektów) implementacji w czasie testowania. FP może być przez to widziane jako Ekstremalne Mockowanie.


### `update`

Metoda `update` powinna wywołać `initial`, aby odświeżyć nasz obraz świata, zachowując znane akcje, które oczekują na wywołanie (pole `pending`).

Jeśli węzeł zmienił swój stan, usuwamy go z listy oczekujących, a jeśli akcja trwa dłużej niż 10 minut, to zakładamy,
że zakończyła się porażką i zapominamy, że ją zainicjowaliśmy.

{lang="text"}
~~~~~~~~
  def update(old: WorldView): F[WorldView] = for {
    snap <- initial
    changed = symdiff(old.alive.keySet, snap.alive.keySet)
    pending = (old.pending -- changed).filterNot {
      case (_, started) => (snap.time - started) >= 10.minutes
    }
    update = snap.copy(pending = pending)
  } yield update
  
  private def symdiff[T](a: Set[T], b: Set[T]): Set[T] =
    (a union b) -- (a intersect b)
~~~~~~~~

Konkretne funkcje takie jak `.symdiff` nie wymagają testowych interpreterów, ponieważ mają bezpośrednio wyrażone zarówno
wejście, jak i wyjście. Możemy przenieść je do samodzielnego, bezstanowego obiektu, który można
testować w izolacji i testować jedynie publiczne metody modułu.


### `act`

Metoda `act` jest nieco bardziej skomplikowana, więc dla zwiększenia czytelności podzielimy ją na dwie części:
wykrywanie akcji, które należy wykonać oraz wykonywanie tychże akcji. To uproszczenie sprawia, że możemy wykonać tylko 
jedną akcję per wywołanie, ale jest to całkiem rozsądne, biorąc pod uwagę, że dzięki temu możemy lepiej kontrolować wykonywane akcje
oraz wywoływać `act` tak długo aż nie pozostanie żadna akcja do wykonania.


Wykrywanie konkretnych scenariuszy dzieje się poprzez ekstraktory bazujące na `WorldView`, co w praktyce jest
po prostu bardziej ekspresywną formą warunków `if` / `else`.

Musimy dodać agentów do farmy, jeśli praca gromadzi się w kolejce oraz nie ma żadnych agentów, aktywnych węzłów ani akcji oczekujących na wykonanie. 
Jako wynik zwracamy węzeł, który chcielibyśmy uruchomić.

{lang="text"}
~~~~~~~~
  private object NeedsAgent {
    def unapply(world: WorldView): Option[MachineNode] = world match {
      case WorldView(backlog, 0, managed, alive, pending, _)
           if backlog > 0 && alive.isEmpty && pending.isEmpty
             => Option(managed.head)
      case _ => None
    }
  }
~~~~~~~~

Jeśli kolejka jest pusta, powinniśmy zatrzymać wszystkie nieaktywne (niewykonujące żadnych zadań) węzły. 
Pamiętając, że Google zawsze pobiera opłatę za pełne godziny, wyłączamy węzły jedynie w 58 minucie ich działania.
Wynikiem jest lista węzłów do zatrzymania.

Jako zabezpieczenie finansowe zakładamy, że żaden węzeł nie może żyć dłużej niż 5 godzin.

{lang="text"}
~~~~~~~~
  private object Stale {
    def unapply(world: WorldView): Option[NonEmptyList[MachineNode]] = world match {
      case WorldView(backlog, _, _, alive, pending, time) if alive.nonEmpty =>
        (alive -- pending.keys).collect {
          case (n, started) if backlog == 0 && (time - started).toMinutes % 60 >= 58 => n
          case (n, started) if (time - started) >= 5.hours => n
        }.toList.toNel
  
      case _ => None
    }
  }
~~~~~~~~

Gdy już zdefiniowaliśmy scenariusze, które nas interesują, możemy przejść do implementacji metody `act`. 
Gdy chcemy aby, węzeł został uruchomiony lub zatrzymany, dodajemy go do listy `pending` wraz z zapisem
czasu, w którym tę akcję zaplanowaliśmy.

{lang="text"}
~~~~~~~~
  def act(world: WorldView): F[WorldView] = world match {
    case NeedsAgent(node) =>
      for {
        _ <- M.start(node)
        update = world.copy(pending = Map(node -> world.time))
      } yield update
  
    case Stale(nodes) =>
      nodes.foldLeftM(world) { (world, n) =>
        for {
          _ <- M.stop(n)
          update = world.copy(pending = world.pending + (n -> world.time))
        } yield update
      }
  
    case _ => world.pure[F]
  }
~~~~~~~~

Ponieważ `NeedsAgent` i `Stale` nie pokrywają wszystkich możliwych sytuacji, musimy również zdefiniować
zachowanie domyślne, które nie robi nic. Przypomnijmy z Rozdziału 2: `.pure` tworzy (monadyczny) kontekst używany 
wewnątrz `for` z prostej wartości.

`foldLeftM` działa podobnie do `foldLeft`, z tą różnicą, że przyjmowana funkcja może zwracać wartość opakowaną w kontekst.
W naszym przypadku każda iteracja zwraca `F[WorldView]`. `M` w nazwie jest skrótem od _Monadic_. Niedługo dowiemy się
więcej o tego typu *wyniesionych* (_lifted_) funkcjach, które zachowują się tak, jak byśmy oczekiwali, ale przyjmują
funkcje zwracające wartości monadyczne zamiast zwykłych wartości.


## Testy jednostkowe

Podejście funkcyjne do pisania aplikacji jest marzeniem projektanta: można skupić się na logice biznesowej,pozostawiając
implementacji algebr pozostałym członkom zespołu.

Nasza aplikacja bardzo silnie zależy od upływu czasu oraz zewnętrznych webserwisów. Gdyby była to tradycyjna aplikacja
napisania w duchu OOP, stworzylibyśmy mocki dla wszystkich wywołań lub testowych aktorów dla wysyłanych wiadomości.
Mockowanie w FP jest równoznaczne z dostarczeniem alternatywnej implementacji algebr, od których zależymy. Algebry 
izolują części systemu, które muszą zostać *zamockowane*, czyli po prostu inaczej interpretowane w kontekście testów 
jednostkowych.

Zaczniemy od przygotowania danych testowych:

{lang="text"}
~~~~~~~~
  object Data {
    val node1   = MachineNode("1243d1af-828f-4ba3-9fc0-a19d86852b5a")
    val node2   = MachineNode("550c4943-229e-47b0-b6be-3d686c5f013f")
    val managed = NonEmptyList(node1, node2)
  
    val time1: Epoch = epoch"2017-03-03T18:07:00Z"
    val time2: Epoch = epoch"2017-03-03T18:59:00Z" // +52 mins
    val time3: Epoch = epoch"2017-03-03T19:06:00Z" // +59 mins
    val time4: Epoch = epoch"2017-03-03T23:07:00Z" // +5 hours
  
    val needsAgents = WorldView(5, 0, managed, Map.empty, Map.empty, time1)
  }
  import Data._
~~~~~~~~

A> String interpolator `epoch` został napisany przy użyciu biblioteki [contextual](https://github.com/propensive/contextual) 
A> autorstwa Jona Pretty'iego. Biblioteka ta pozwala nam tworzyć obiekty ze stringów z naszą własną weryfikacją na etapie kompilacji.
A>
A> {lang="text"}
A> ~~~~~~~~
A>   import java.time.Instant
A>   object EpochInterpolator extends Verifier[Epoch] {
A>     def check(s: String): Either[(Int, String), Epoch] =
A>       try Right(Epoch(Instant.parse(s).toEpochMilli))
A>       catch { case _ => Left((0, "not in ISO-8601 format")) }
A>   }
A>   implicit class EpochMillisStringContext(sc: StringContext) {
A>     val epoch = Prefix(EpochInterpolator, sc)
A>   }
A> ~~~~~~~~

Implementujemy algebry poprzez rozszerzenie interfejsów `Drone` i `Machines` podając konkretny kontekst monadyczny,
który w najprostszym przypadku to po prostu `Id`.

Nasza "mockowa" implementacja zwyczajnie odtwarza wcześniej przygotowany `WorldView`. 
Stan naszego systemu został wyizolowany, więc możemy użyć `var` do jego przechowywania:

{lang="text"}
~~~~~~~~
  class Mutable(state: WorldView) {
    var started, stopped: Int = 0
  
    private val D: Drone[Id] = new Drone[Id] {
      def getBacklog: Int = state.backlog
      def getAgents: Int = state.agents
    }
  
    private val M: Machines[Id] = new Machines[Id] {
      def getAlive: Map[MachineNode, Epoch] = state.alive
      def getManaged: NonEmptyList[MachineNode] = state.managed
      def getTime: Epoch = state.time
      def start(node: MachineNode): MachineNode = { started += 1 ; node }
      def stop(node: MachineNode): MachineNode = { stopped += 1 ; node }
    }
  
    val program = new DynAgentsModule[Id](D, M)
  }
~~~~~~~~

A> Powrócimy do tego kodu trochę później i zamienimy `var` na coś dużo bezpieczniejszego.

Kiedy piszemy testy jednostkowe (używając `FlatSpec` z biblioteki Scalatest), tworzymy instancje `Mutable` 
i importujemy wszystkie jej pola i metody.

Nasze `drone` i `machines` używają `Id` jako kontekstu wykonania, więc interpretacja naszego programu
zwraca `Id[WoldView]`, na którym bez żadnych problemów możemy wykonywać asercje.

W tym trywialnym scenariuszu sprawdzamy, czy `initial` zwraca tę sama wartość, której użyliśmy 
w naszej statycznej implementacji:

{lang="text"}
~~~~~~~~
  "Business Logic" should "generate an initial world view" in {
    val mutable = new Mutable(needsAgents)
    import mutable._
  
    program.initial shouldBe needsAgents
  }
~~~~~~~~

Możemy też stworzyć bardziej skomplikowane testy dla metod `update` i `act`,
które pomogą nam znaleźć błędy i dopracować wymagania:

{lang="text"}
~~~~~~~~
  it should "remove changed nodes from pending" in {
    val world = WorldView(0, 0, managed, Map(node1 -> time3), Map.empty, time3)
    val mutable = new Mutable(world)
    import mutable._
  
    val old = world.copy(alive = Map.empty,
                         pending = Map(node1 -> time2),
                         time = time2)
    program.update(old) shouldBe world
  }
  
  it should "request agents when needed" in {
    val mutable = new Mutable(needsAgents)
    import mutable._
  
    val expected = needsAgents.copy(
      pending = Map(node1 -> time1)
    )
  
    program.act(needsAgents) shouldBe expected
  
    mutable.stopped shouldBe 0
    mutable.started shouldBe 1
  }
~~~~~~~~

Przejście przez pełen komplet testów byłby dość nudny, poniższe testy można łatwo zaimplementować,używając tego 
samego podejścia:

- nie proś o nowych agentów, gdy kolejka oczekujących jest niepusta
- nie wyłączaj agentów, jeśli węzły są zbyt młode
- wyłącz agenty, gdy backlog jest pusty a węzły wkrótce wygenerują nowe koszta
- nie wyłączaj agentów, gdy obecne są oczekujące akcje
- wyłącz agenty, gdy są zbyt stare, a backlog jest pusty
- wyłącz agenty, nawet jeśli wykonują prace, jeśli są zbyt starzy
- zignoruj nieodpowiadające oczekujące akcje podczas aktualizacji

Wszystkie te testy są synchroniczne i działają na wątku uruchamiającym testy oraz mogą być uruchamiane równolegle.
Gdybyśmy zaprojektowali nasze testy z użyciem Akki, narażone byłyby na arbitralne timeouty, a błędy ukryte byłyby 
w logach.

Ciężko jest przecenić zwiększenie produktywności wynikające z prostych testów logiki biznesowej. Weź pod uwagę, że
90% czasu programisty podczas interakcji z klientem poświęcone jest na ulepszanie, aktualizowanie i poprawianie 
tych właśnie reguł. Wszystko inne to tylko szczegóły implementacyjne.


## Przetwarzanie równoległe

Aplikacja, którą stworzyliśmy, uruchamia każdą z algebraicznych metod sekwencyjnie, mimo tego, że jest kilka oczywistych miejsc,
w których praca może być wykonywana równolegle.

### `initial`

W naszej definicji metody `initial` moglibyśmy zarządać wszystkich informacji równocześnie, zamiast wykonywać tylko jedno
zapytanie na raz.

W przeciwieństwie do metody `flatMap`, która działa sekwencyjnie, Scalaz dostarcza składnie `Apply` 
przewidzianą do operacji równoległych:

{lang="text"}
~~~~~~~~
  ^^^^(D.getBacklog, D.getAgents, M.getManaged, M.getAlive, M.getTime)
~~~~~~~~

możemy również użyć notacji infiksowej (_infix notation_):

{lang="text"}
~~~~~~~~
  (D.getBacklog |@| D.getAgents |@| M.getManaged |@| M.getAlive |@| M.getTime)
~~~~~~~~

Jeśli każda z operacji równoległych zwraca ten sam kontekst, możemy wywołać funkcję w momencie, gdy wszystkie zwrócą wynik. 
Przepiszmy `initial` tak, aby skorzystać z tej możliwości:

{lang="text"}
~~~~~~~~
  def initial: F[WorldView] =
    ^^^^(D.getBacklog, D.getAgents, M.getManaged, M.getAlive, M.getTime) {
      case (db, da, mm, ma, mt) => WorldView(db, da, mm, ma, Map.empty, mt)
    }
~~~~~~~~


### act

W aktualnej implementacji `act` zatrzymujemy każdy z węzłów sekwencyjnie, czekając na wynik i kontynuując pracę, 
dopiero gdy operacja się zakończy. Moglibyśmy jednak zatrzymać wszystkie węzły równolegle i na koniec zaktualizować
nasz obraz świata.

Wadą tego rozwiązania jest fakt, że błąd w którejkolwiek akcji spowoduje zwarcie, zanim zdążymy zaktualizować pole
`pending`. Wydaje się to być rozsądnym kompromisem, gdyż nasza metoda `update` poradzi sobie z sytuacją, w której
węzeł niespodziewanie się zatrzyma.

Potrzebujemy metody, która operuje na typie `NonEmptyList` i pozwoli nam prze`map`ować każdy element na
`F[MachineNode]` i zwróci `F[NonEmptyList[MachineNode]]`. Metoda ta nazywa się `traverse`, a gdy na jej rezultacie 
wywołamy `flatMap`, otrzymamy wartość typu `NonEmptyList[MachineNode]` z którą możemy sobie poradzić w prosty sposób:

{lang="text"}
~~~~~~~~
  for {
    stopped <- nodes.traverse(M.stop)
    updates = stopped.map(_ -> world.time).toList.toMap
    update = world.copy(pending = world.pending ++ updates)
  } yield update
~~~~~~~~

Co więcej, wygląda na to, że wersja równoległa jest łatwiejsza do zrozumienia niż wersja sekwencyjna.


## Podsumowanie

1. *Algebry* definiują interfejsy między systemami
2. *Moduły* implementują algebry, używając innych algebr
3. *Interpretery* to konkretne implementacje algebr dla określonego `F[_]`
4. Interpretery testowe mogą zamienić części systemu wywołujące efekty uboczne, dając nam wysokie pokrycie testami.


# Dane i funkcjonalności

Przychodząc ze świata obiektowego, jesteśmy przyzwyczajeni do myślenia o danych i funkcjonalnościach jako jednym:
hierarchie klas zawierają metody, a traity mogą wymagać obecności konkretnych pól (danych). 

Polimorfizm obiektu w czasie wykonania, bazujący na relacji "jest" (_is a_), wymaga od klas, aby dziedziczyły po wspólnym interfejsie. 
Rozwiązanie to może wywołać spory bałagan, gdy tylko ilość naszego kodu zacznie się istotnie zwiększać. Proste struktury danych zostają 
przysłonięte setkami linii kodu implementującego kolejne metody, traity, które wmiksowujemy do naszych klas, zaczynają cierpieć na problemy 
związane z kolejnością inicjalizacji, a testowanie i mockowanie ściśle powiązanych komponentów staje się katorgą.

FP podchodzi inaczej do tego problemu, rozdzielając definicje funkcjonalności i danych. W tym rozdziale poznamy podstawowe
typy danych i zalety ograniczenia się do podzbioru funkcjonalności oferowanych przez Scalę. Odkryjemy również *typeklasy* 
jako sposób na osiągnięcie polimorfizmu już na etapie kompilacji: zaczniemy myśleć o strukturach danych w kategoriach relacji
"ma" (_has a_) zamiast "jest".


## Dane

Podstawowymi materiałami używanymi do budowania typów danych są:

- `final case class`, czyli klasy znane również jako *produkty* (_products_)
- `sealed abstract class` znane również jako *koprodukty* (_coproducts_)
- `case object` oraz typy proste takie jak `Int`, `Double`, `String` to *wartości* (_values_)[^values]

[^values]: Chodzi tutaj o wartości na poziomie typów (_type level_). Dla przykładu: produktem na poziomie wartości (_value level_),
    jest nowa wartość złożona z wielu wartości, np. `(1,2,3)`. Produktem na poziomie typów jest nowy typ złożony z wielu typów 
    (czyli wartości na poziomie typów), np. `(Int, String, Int)`. Może to wydawać się zawiłe, ale nie ma potrzeby się tym przejmować.
    Ważne jest, aby zrozumieć, że mamy 2 poziomy, na których możemy definiować byty: poziom typów i poziom wartości, 
    i że w tym wypadku mówimy o wartościach na poziomie typów.

z tym ograniczeniem, że nie mogą one mieć żadnych metod ani pól innych niż parametry konstruktora. Preferujemy
`abstract class` nad `trait`, aby zyskać lepszą kompatybilność binarną i nie zachęcać do wmiksowywania traitów.

Wspólna nazwa dla *produktów*, *koproduktów* i *wartości* to *Algebraiczny Typ Danych*[^adt] (ADT).

[^adt]: _Algebraic Data Type_

Składamy typy danych analogicznie do algebry Boole’a opartej na operacjach `AND` i `XOR` (wykluczający `OR`):
produkt zawiera wszystkie typy, z których się składa, a koprodukt jest jednym z nich. Na przykład

-   produkt: `ABC = a AND b AND c`
-   koprodukt: `XYZ = x XOR y XOR z`

co zapisane w Scali wygląda tak:

{lang="text"}
~~~~~~~~
  // values
  case object A
  type B = String
  type C = Int
  
  // product
  final case class ABC(a: A.type, b: B, c: C)
  
  // coproduct
  sealed abstract class XYZ
  case object X extends XYZ
  case object Y extends XYZ
  final case class Z(b: B) extends XYZ
~~~~~~~~


### Rekursywne ADT

Kiedy ADT odnosi się to samego siebie, staje się *Rekursywnym Algebraicznym Typem Danych*.

`scalaz.IList`, bezpieczna alternatywa dla typu `List` z biblioteki standardowej, to rekursywne ADT, ponieważ
`ICons` zawiera referencje do `IList`.:

{lang="text"}
~~~~~~~~
  sealed abstract class IList[A]
  final case class INil[A]() extends IList[A]
  final case class ICons[A](head: A, tail: IList[A]) extends IList[A]
~~~~~~~~


### Funkcje w ADT

ADT mogą zawierać *czyste funkcje*

{lang="text"}
~~~~~~~~
  final case class UserConfiguration(accepts: Int => Boolean)
~~~~~~~~

ale sprawia to, że stają się mniej oczywiste, niż mogłoby się wydawać, gdyż sposób, w jaki są wyrażone w JVMie,
nie jest idealny. Dla przykładu `Serializable`, `hashCode`, `equals` i `toString` nie zachowują się tak, jak
byśmy się tego spodziewali.

Niestety, `Serializable` używany jest przez wiele frameworków mimo tego, że istnieje dużo lepszych alternatyw. Częstą
pułapką jest zapomnienie, że `Serializable` może próbować zserializować całe domknięcie (_closure_) funkcji,
co może np. zabić produkcyjny serwer, na którym uruchomiona jest aplikacja. Podobnymi problemami obciążone są inne typy Javowe
takie jak na przykład `Throwable`, który niesie w sobie referencje do arbitralnych obiektów.

Zbadamy dostępne alternatywy, gdy pochylimy się nad biblioteką Scalaz w następnym rozdziale. Kosztem tych alternatyw będzie 
poświęcenie interoperacyjności (_interoperability_) z częścią ekosystemu Javy i Scali.


### Wyczerpywalność[^exhaustivity]

[^exhaustivity]: _Exhaustivity_

Istotne jest, że definiując typy danych, używamy konstrukcji `sealed abstract class`, a nie `abstract class`. Zapieczętowanie
(_sealing_) klasy oznacza, że wszystkie podtypy (_subtypes_) muszą być zdefiniowane w tym samym pliku, pozwalając tym samym
kompilatorowi na sprawdzanie, czy pattern matching jest wyczerpujący. Dodatkowo informacja ta może być wykorzystana przez makra,
które pomagają nam eliminować boilerplate.

{lang="text"}
~~~~~~~~
  scala> sealed abstract class Foo
         final case class Bar(flag: Boolean) extends Foo
         final case object Baz extends Foo
  
  scala> def thing(foo: Foo) = foo match {
           case Bar(_) => true
         }
  <console>:14: error: match may not be exhaustive.
  It would fail on the following input: Baz
         def thing(foo: Foo) = foo match {
                               ^
~~~~~~~~

Jak widzimy, kompilator jest w stanie pokazać deweloperowi, co zostało zepsute, gdy ten dodał nowy wariant do koproduktu
lub pominął już istniejący. Używamy tutaj flagi kompilatora `-Xfatal-warnings`, bo w przeciwnym przypadku błąd ten jest jedynie ostrzeżeniem.

Jednakże kompilator nie jest w stanie wykonać koniecznych sprawdzeń, gdy klasa nie jest zapieczętowana lub gdy używamy 
dodatkowych ograniczeń (_guards_), np.:

{lang="text"}
~~~~~~~~
  scala> def thing(foo: Foo) = foo match {
           case Bar(flag) if flag => true
         }
  
  scala> thing(Baz)
  scala.MatchError: Baz (of class Baz$)
    at .thing(<console>:15)
~~~~~~~~

Aby zachować bezpieczeństwo, nie używaj ograniczeń na zapieczętowanych typach.

Nowa flaga, [`-Xstrict-patmat-analysis`](https://github.com/scala/scala/pull/5617), została zaproponowana, aby dodatkowo
wzmocnić bezpieczeństwo pattern matchingu.


### Alternatywne produkty i koprodukty

Inną formą wyrażenia produktu jest tupla (inaczej krotka, ang. _tuple_), która przypomina finalną case klasę pozbawioną etykiet.

`(A.type, B, C)` jest równoznaczna z `ABC` z wcześniejszego przykładu, ale do konstruowania ADT 
lepiej jest używać klas, ponieważ brak nazw jest problematyczne w praktyce. Dodatkowo case klasy są zdecydowanie bardziej wydajne
przy operowaniu na wartościach typów prostych (_primitive values_).

Inną formą wyrażenia koproduktu jest zagnieżdżanie typu `Either`, np.

{lang="text"}
~~~~~~~~
  Either[X.type, Either[Y.type, Z]]
~~~~~~~~

co jest równoznaczne z zapieczętowaną klasą abstrakcyjną `XYZ`. Aby uzyskać czystszą składnię do definiowania zagnieżdżonych
typów `Either`, możemy zdefiniować alias typu zakończony dwukropkiem, co sprawi, że używając notacji infiksowej, będzie on wiązał
argument po prawej stronie jako pierwszy[^eitherright].

[^eitherright]: A więc `String |: Int |: Double` rozumiany jest jako `String |: (Int |: Double)`, a nie `(String |: Int) |: Double`.

{lang="text"}
~~~~~~~~
  type |:[L,R] = Either[L, R]
  
  X.type |: Y.type |: Z
~~~~~~~~

Anonimowe koprodukty stają się przydatne, gdy nie jesteśmy w stanie umieścić wszystkich typów w jednym pliku.

{lang="text"}
~~~~~~~~
  type Accepted = String |: Long |: Boolean
~~~~~~~~

Alternatywnym rozwiązaniem jest zdefiniowanie nowej zapieczętowanej klasy, której podtypy opakowują potrzebne nam typy.


{lang="text"}
~~~~~~~~
  sealed abstract class Accepted
  final case class AcceptedString(value: String) extends Accepted
  final case class AcceptedLong(value: Long) extends Accepted
  final case class AcceptedBoolean(value: Boolean) extends Accepted
~~~~~~~~

Pattern matching na tych formach koproduktów jest dość mozolny, dlatego też w Dottym (kompilatorze Scali następnej generacji) 
dostępne są [Unie](https://contributors.scala-lang.org/t/733) (_union types_). Istnieją również biblioteki (oparte o makra), 
takie jak [totalitarian](https://github.com/propensive/totalitarian) czy [iota](https://github.com/frees-io/iota),
które dostarczają kolejne sposoby na wyrażanie koproduktów.


### Przekazywanie informacji

Typy danych, oprócz pełnienia funkcji kontenerów na kluczowe informacje biznesowe, pozwalają nam również
wyrażać ograniczenia dla tychże danych. Na przykład instancja typu

{lang="text"}
~~~~~~~~
  final case class NonEmptyList[A](head: A, tail: IList[A])
~~~~~~~~

nigdy nie będzie pusta. Sprawia to, że `scalaz.NonEmptyList` jest użytecznym typem danych mimo tego, że
zawiera dokładnie te same dane jak `IList`.

Produkty często zawierają typy, które są dużo bardziej ogólne, niż ma to sens. W tradycyjnym podejściu
obiektowym moglibyśmy obsłużyć taki przypadek poprzez walidację danych za pomocą asercji:

{lang="text"}
~~~~~~~~
  final case class Person(name: String, age: Int) {
    require(name.nonEmpty && age > 0) // breaks Totality, don't do this!
  }
~~~~~~~~

Zamiast tego, możemy użyć typu `Either` i zwracać `Right[Person]` dla poprawnych instancji, zapobiegając tym samym przed
propagacją niepoprawnych instancji. Zauważ, że konstruktor jest prywatny: 

{lang="text"}
~~~~~~~~
  final case class Person private(name: String, age: Int)
  object Person {
    def apply(name: String, age: Int): Either[String, Person] = {
      if (name.nonEmpty && age > 0) Right(new Person(name, age))
      else Left(s"bad input: $name, $age")
    }
  }
  
  def welcome(person: Person): String =
    s"${person.name} you look wonderful at ${person.age}!"
  
  for {
    person <- Person("", -1)
  } yield welcome(person)
~~~~~~~~


#### Rafinowane typy danych[^refined]

[^refined]: _Refined Data Types_

Prostym sposobem ograniczenie zbioru możliwych wartości ogólnego typu jest użycie biblioteki [refined](https://github.com/fthomas/refined).
Aby zainstalować `refined`, dodaj poniższą linię do pliku `build.sbt`.

{lang="text"}
~~~~~~~~
  libraryDependencies += "eu.timepit" %% "refined-scalaz" % "0.9.2"
~~~~~~~~

oraz poniższe importy do swojego kodu

{lang="text"}
~~~~~~~~
  import eu.timepit.refined
  import refined.api.Refined
~~~~~~~~

`Refined` pozwala nam zdefiniować klasę `Person`, używając rafinacji ad-hoc, aby zapisać dokładne wymagania co do typu.
Rafinację taką wyrażamy jako typ `A Refined B`.

A> Wszystkie dwuparametrowe typy w Scali można zapisać w sposób inifksowy, a więc `Either[String, Int]`
A> jest tym samym co `String Either Int`. Istnieje konwencja, aby używać `Refined` w ten właśnie sposób,
A> gdyż `A Refined B` może być czytane jako "takie `A`, które spełnia wymagania zdefiniowane w `B`".

{lang="text"}
~~~~~~~~
  import refined.numeric.Positive
  import refined.collection.NonEmpty
  
  final case class Person(
    name: String Refined NonEmpty,
    age: Int Refined Positive
  )
~~~~~~~~

Dostęp do oryginalnej wartości odbywa się poprzez `.value`. Aby skonstruować instancje rafinowanego typu 
w czasie działa programu, możemy użyć metody `.refineV`, która zwróci nam `Either`.

{lang="text"}
~~~~~~~~
  scala> import refined.refineV
  scala> refineV[NonEmpty]("")
  Left(Predicate isEmpty() did not fail.)
  
  scala> refineV[NonEmpty]("Sam")
  Right(Sam)
~~~~~~~~

Jeśli dodamy poniższy import

{lang="text"}
~~~~~~~~
  import refined.auto._
~~~~~~~~

możemy konstruować poprawne wartości z walidacją na etapie kompilacji:

{lang="text"}
~~~~~~~~
  scala> val sam: String Refined NonEmpty = "Sam"
  Sam
  
  scala> val empty: String Refined NonEmpty = ""
  <console>:21: error: Predicate isEmpty() did not fail.
~~~~~~~~

Możemy również wyrażać bardziej skomplikowane wymagania, np. za pomocą gotowej reguły `MaxSize` dostępnej
po dodaniu poniższych importów

{lang="text"}
~~~~~~~~
  import refined.W
  import refined.boolean.And
  import refined.collection.MaxSize
~~~~~~~~

Oto jak wyrażamy wymagania, aby `String`  był jednocześnie niepusty i nie dłuższy niż 10 znaków:

{lang="text"}
~~~~~~~~
  type Name = NonEmpty And MaxSize[W.`10`.T]
  
  final case class Person(
    name: String Refined Name,
    age: Int Refined Positive
  )
~~~~~~~~

A> Notacja `W` jest skrótem od angielskiego "witness". Składania ta stanie się zdecydowanie prostsza w Scali 2.13,
A> która niesie wsparcie dla *typów literałowych* (_literal types_):
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   type Name = NonEmpty And MaxSize[10]
A> ~~~~~~~~

Łatwo jest zdefiniować własne ograniczenia, które nie są dostępne bezpośrednio w bibliotece. Na przykład
w naszej aplikacji `drone-dynamic-agents` potrzebować będziemy sposobu, aby upewnić się, że `String` jest wiadomością
zgodną z formatem `application/x-www-form-urlencoded`. Stwórzmy więc taką regułę, używając wyrażeń regularnych:

{lang="text"}
~~~~~~~~
  sealed abstract class UrlEncoded
  object UrlEncoded {
    private[this] val valid: Pattern =
      Pattern.compile("\\A(\\p{Alnum}++|[-.*_+=&]++|%\\p{XDigit}{2})*\\z")
  
    implicit def urlValidate: Validate.Plain[String, UrlEncoded] =
      Validate.fromPredicate(
        s => valid.matcher(s).find(),
        identity,
        new UrlEncoded {}
      )
  }
~~~~~~~~


### Dzielenie się jest łatwe

Przez to, że ADT nie dostarczają żadnych funkcjonalności, mają minimalny zbiór zależności. Sprawia to, że dzielenie 
tychże typów z innymi deweloperami jest nad wyraz łatwe i używając prostego jeżyka modelowania danych, komunikacja oparta o kod, a 
nie specjalnie przygotowane dokumenty, staje się możliwa nawet wewnątrz zespołów interdyscyplinarnych (a więc 
składających się dodatkowo z np. administratorów baz danych, specjalistów od UI czy analityków biznesowych).

Dodatkowo łatwiejsze staje się tworzenie narzędzi, które pomogą w konsumowaniu i produkowaniu
schematów danych dla innych języków danych albo łączeniu protokołów komunikacji.


### Wyliczanie złożoności

Złożoność typu danych to liczba możliwych do stworzenia wartości tego typu. Dobry typ danych ma najmniejszą możliwą
złożoność, która pozwala mu przechować potrzebne informacje.

Typy proste mają z góry określoną złożoność:

-   `Unit` ma dokładnie jedną wartość (dlatego nazywa się "jednostką")
-   `Boolean` ma dwie wartości
-   `Int` ma 4,294,967,295 wartości
-   `String` ma efektywnie nieskończenie wiele wartości

Aby policzyć złożoność produktu, wystarczy pomnożyć złożoności jego składowych.

-   `(Boolean, Boolean)` ma 4 wartości (`2*2`)
-   `(Boolean, Boolean, Boolean)` ma 6 wartości (`2*2*2`)

Aby policzyć złożoność koproduktu, sumujemy złożoności poszczególnych wariantów.

-   `(Boolean |: Boolean)` ma 4 wartości (`2+2`)
-   `(Boolean |: Boolean |: Boolean)` ma 6 wartości (`2+2+2`)

Aby określić złożoność ADT sparametryzowanego typem, mnożymy każdą z części przez złożoność parametru:

-   `Option[Boolean]` ma 3 wartości, `Some[Boolean]` i `None` (`2+1`)

W FP funkcje są *totalne* i muszą zwracać wartość dla każdego wejścia, bez żadnych *wyjątków*, a zmniejszanie złożoności
wejścia i wyjścia jest najlepszą drogą do osiągnięcia totalności. Jako zasadę kciuka przyjąć można, że funkcja jest
źle zaprojektowana, jeśli złożoność jej wyjścia jest większa niż złożoność produktu jej wejść: w takim przypadku staje się 
ona źródłem entropii.

Złożoność funkcji totalnej jest liczbą możliwych funkcji, które pasują do danej sygnatury typu, a więc innymi słowy,
złożoność wyjścia do potęgi równej złożoności wejścia.

-   `Unit => Boolean` ma złożoność 2
-   `Boolean => Boolean` ma złożoność 4
-   `Option[Boolean] => Option[Boolean]` ma złożoność 27
-   `Boolean => Int` to zaledwie trylion kombinacji
-   `Int => Boolean` ma złożoność tak wielką, że gdyby każdej implementacji przypisać liczbę, to każda z tych liczb wymagałaby
4 gigabajtów pamięci, aby ją zapisać

W praktyce `Int => Boolean` będzie zazwyczaj czymś tak trywialnym, jak sprawdzenie parzystości lub rzadkie (_sparse_) 
wyrażenie zbioru bitów (`BitSet`). Funkcja taka w ADT powinna być raczej zastąpiona koproduktem istotnych funkcji.

Gdy nasza złożoność to "nieskończoność na wejściu, nieskończoność na wyjściu" powinniśmy wprowadzić bardziej restrykcyjne typy
i walidacje wejścia, na przykład używając konstrukcji `Refined` wspomnianej w poprzedniej sekcji.

Zdolność do wyliczania złożoności sygnatury typu ma jeszcze jedno praktyczne zastosowanie:
możemy odszukać prostsze sygnatury przy pomocy matematyki na poziomie szkoły średniej! Aby przejść od sygnatury
do jej złożoności, po prostu zamień

-   `Either[A, B]` na `a + b`
-   `(A, B)` na `a * b`
-   `A => B` na `b ^ a`

a następnie poprzestawiaj i zamień z powrotem. Dla przykładu powiedzmy, że zaprojektowaliśmy framework oparty na callbackach i 
dotarliśmy do miejsca, w którym potrzebujemy takiej sygnatury:

{lang="text"}
~~~~~~~~
  (A => C) => ((B => C) => C)
~~~~~~~~

Możemy ją przekonwertować i przetransformować

{lang="text"}
~~~~~~~~
  (c ^ (c ^ b)) ^ (c ^ a)
  = c ^ ((c ^ b) * (c ^ a))
  = c ^ (c ^ (a + b))
~~~~~~~~

a następnie zamienić z powrotem, aby otrzymać

{lang="text"}
~~~~~~~~
  (Either[A, B] => C) => C
~~~~~~~~

która jest zdecydowanie prostsza: wystarczy, że użytkownik dostarczy nam `Either[A, B] => C`.

Ta sama metoda może być użyta aby udowodnić, że

{lang="text"}
~~~~~~~~
  A => B => C
~~~~~~~~

jest równoznaczna z

{lang="text"}
~~~~~~~~
  (A, B) => C
~~~~~~~~

co znane jest jako *currying* lub *rozwijanie funkcji*.


### Preferuj koprodukty nad produkty

Archetypowym problemem, który pojawia się bardzo często, są wzajemnie wykluczające się parametry konfiguracyjne
`a`, `b` i `c`. Produkt `(a: Boolean, b: Boolean, c: Boolean)` ma złożoność równą 8, podczas gdy złożoność koproduktu

{lang="text"}
~~~~~~~~
  sealed abstract class Config
  object Config {
    case object A extends Config
    case object B extends Config
    case object C extends Config
  }
~~~~~~~~

to zaledwie 3. Lepiej jest zamodelować opisany scenariusz jako koprodukt niż pozwolić na wyrażenie pięciu zupełnie nieprawidłowych
przypadków.

Złożoność typu danych wpływa również na testowanie kodu na nim opartego i praktycznie niemożliwym jest przetestowanie wszystkich
możliwych wejść do funkcji. Całkiem łatwo jest jednak przetestować próbkę wartości za pomocą biblioteki do
testowania właściwości[^ppt] [Scalacheck](https://www.scalacheck.org/). Jeśli prawdopodobieństwo poprawności losowej próbki danych
jest niskie, jest to znak, że dane są niepoprawnie zamodelowane.

[^ppt]: _Property based testing_.


### Optymalizacja

Dużą zaletą używania jedynie podzbioru języka Scala do definiowania typów danych jest to, że narzędzia mogą 
optymalizować bytecode potrzebny do reprezentacji tychże.

Na przykład, możemy spakować pola typu `Boolean` i `Option` do tablicy bajtów, cache'ować wartości,
memoizować `hashCode`, optymalizować `equals`, używać wyrażeń `@switch` przy pattern matchingu i wiele, wiele więcej.

Optymalizacje te nie mogą być zastosowane do hierarchii klas w stylu OOP, które to mogą przechowywać wewnętrzny stan,
rzucać wyjątki lub dostarczać doraźne implementacje metod.


## Funkcjonalności

Czyste funkcje są najczęściej definiowane jako metody wewnątrz obiektu (definicji typu `object`).

{lang="text"}
~~~~~~~~
  package object math {
    def sin(x: Double): Double = java.lang.Math.sin(x)
    ...
  }
  
  math.sin(1.0)
~~~~~~~~

Jednakże, używanie obiektów może być nieco niezręczne, gdyż wymaga od programisty czytania kodu od wewnątrz do zewnątrz -
zamiast od lewej do prawej. Dodatkowo, funkcje z obiektu zawłaszczają przestrzeń nazw. Jeśli chcielibyśmy zdefiniować
funkcje `sin(t: T)` gdzieś indziej, napotkalibyśmy błędy niejednoznacznych referencji (_ambigous reference_). Jest
to ten sam problem, który spotykamy w Javie, gdy wybieramy między metodami statycznymi i tymi definiowanymi w klasie.

W> Deweloperzy, którzy umieszczają swoje metody w `trait`ach, a następnie oczekują od użytkowników wmiksowywania tych traitów
W> w sposób znany jako *cake pattern*, po śmierci trafią prosto do piekła. Stanie się tak, ponieważ API zaimplementowane w
W> ten sposób ujawnia swoje szczegóły implementacyjne, rozdyma generowany bytecode, sprawia, że zachowanie kompatybilności 
W> binarnej jest praktycznie niemożliwe oraz myli funkcje autopodpowiadania w IDE.

Korzystając z konstrukcji `implicit class` (znanej również jako *extension methodology* lub *syntax*) i odrobiny boilerplate'u
możemy uzyskać znaną nam składnię:

{lang="text"}
~~~~~~~~
  scala> implicit class DoubleOps(x: Double) {
           def sin: Double = math.sin(x)
         }
  
  scala> (1.0).sin
  res: Double = 0.8414709848078965
~~~~~~~~

Często dobrze jest pominąć definiowanie obiektu i od razu sięgnąć po klasę niejawną (`implicit class`), ograniczając boilerplate do minimum:

{lang="text"}
~~~~~~~~
  implicit class DoubleOps(x: Double) {
    def sin: Double = java.lang.Math.sin(x)
  }
~~~~~~~~

A> `implicit class` to tak naprawdę jedynie wygodniejsza składnia do definiowania niejawnych konwersji (_implicit conversion_):
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   implicit def DoubleOps(x: Double): DoubleOps = new DoubleOps(x)
A>   class DoubleOps(x: Double) {
A>     def sin: Double = java.lang.Math.sin(x)
A>   }
A> ~~~~~~~~
A> 
A> Co niestety ma swój koszt: za każdym razem, gdy wywołujemy metodę dodaną w ten sposób, tworzony i usuwany jest obiekt
A> klasy `DoubleOps`, co może powodować zwiększony koszt sprzątania pamięci (_garbage collecting_).
A> 
A> Istnieje nieco bardziej rozwlekła forma klas niejawnych, która pozwala uniknąć zbędnej alokacji, przez co jest 
A> formą zalecaną:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   implicit final class DoubleOps(private val x: Double) extends AnyVal {
A>     def sin: Double = java.lang.Math.sin(x)
A>   }
A> ~~~~~~~~


### Funkcje polimorficzne

Bardziej popularnym rodzajem funkcji są funkcje polimorficzne, które żyją wewnątrz *typeklas*[^tc]. Typeklasa to trait, który:

- nie ma wewnętrznego stanu
- ma parametr typu
- ma przynajmniej jedną metodą abstrakcyjną (*kombinator prymitywny* (_primitive combinator_))
- może mieć metody uogólnione (*kombinatory pochodne* (_derived combinators_))
- może rozszerzać inne typeklasy

[^tc]: Ten potworek to spolszczona wersja słowa _typeclass_. Tłumaczenie tego terminu jako "klasa typu" jest rozwlekłe
    i odbiegające dość daleko od wersji angielskiej. Zdecydowaliśmy się więc pozostać przy wersji oryginalnej, 
    dostosowując jedynie pisownie.

Dla każdego typu może istnieć tylko jedna instancja typeklasy, a właściwość ta nazywa się *koherencją* lub *spójnością* *typeklas* (_typeclass coherence_).
Typeklasy mogą na pierwszy rzut oka wydawać się bardzo podobne do algebraicznych interfejsów, różnią się jednak tym, że algebry
nie muszą zachowywać spójności.

A> W spójności typeklas chodzi głównie o konsekwencję, która zwiększa nasze zaufanie do niejawnych parametrów.
A> Analizowanie i rozumowanie na temat kodu, który zachowuje się inaczej zależnie od zaimportowanych symboli,
A> byłoby bardzo trudne. Spójność typeklas w praktyce sprawia, że możemy uznać, że importy nie wpływają na zachowanie programu.
A> 
A> Dodatkowo właściwość ta pozwala nam globalnie cache'ować niejawne wartości w czasie wykonania programu, 
A> oszczędzając tym samym pamięć i zwiększając wydajność poprzez zmniejszenie ilości pracy wykonywanej przez garbage collector.

Typeklasy używane się m.in. w bibliotece standardowej Scali. Przyjrzymy się uproszczonej wersji `scala.math.Numeric`,
aby zademonstrować zasadę działania tej konstrukcji:

{lang="text"}
~~~~~~~~
  trait Ordering[T] {
    def compare(x: T, y: T): Int
  
    def lt(x: T, y: T): Boolean = compare(x, y) < 0
    def gt(x: T, y: T): Boolean = compare(x, y) > 0
  }
  
  trait Numeric[T] extends Ordering[T] {
    def plus(x: T, y: T): T
    def times(x: T, y: T): T
    def negate(x: T): T
    def zero: T
  
    def abs(x: T): T = if (lt(x, zero)) negate(x) else x
  }
~~~~~~~~

Możemy zaobserwować wszystkie kluczowe cechy typeklasy w praktyce:

-   nie ma wewnętrznego stanu
-   `Ordering` i `Numeric` mają parametr typu `T`
-   `Ordering` definiuje abstrakcyjną metodą `compare`, a `Numeric` metody `plus`, `times`, `negate` i `zero`
-   `Ordering` definiuje uogólnione `lt` i `gt` bazujące na `compare`, `Numeric` robi to samo z `abs`,
    bazując na `lt`, `negate` oraz `zero`
-   `Numeric` rozszerza `Ordering`

Możemy teraz napisać funkcję dla typów, które "posiadają" instancję typeklasy `Numeric`:

{lang="text"}
~~~~~~~~
  def signOfTheTimes[T](t: T)(implicit N: Numeric[T]): T = {
    import N._
    times(negate(abs(t)), t)
  }
~~~~~~~~

Nie zależymy już od hierarchii klas w stylu OOP! Oznacza to, że wejście do naszej funkcji nie musi być instancją typu 
`Numeric`, co jest niezwykle ważne, kiedy chcemy zapewnić wsparcie dla klas zewnętrznych, których definicji nie jesteśmy
w stanie zmienić.

Inną zaletą typeklas jest to, że dane wiązane są z funkcjonalnościami na etapie kompilacji, a nie za pomocą dynamicznej 
dyspozycji (_dynamic dispatch_) w czasie działania programu, jak ma to miejsce w OOP.

Dla przykładu, tam, gdzie klasa `List` może mieć tylko jedną implementację danej metody, używając typeklas, możemy
używać różnych implementacji zależnie od typu elementów zawartych wewnątrz. Tym samym wykonujemy część pracy 
w czasie kompilacji, zamiast zostawiać ją do czasu wykonania.


### Składnia

Składnia użyta to zapisania `signOfTheTimes` jest nieco niezgrabna, ale jest kilka rzeczy, które możemy poprawić. 

Użytkownicy chcieliby, aby nasza metoda używała *wiązania kontekstu* (_context bounds_), ponieważ wtedy
sygnaturę można przeczytać wprost jako: "przyjmuje `T`, dla którego istnieje `Numeric`"

{lang="text"}
~~~~~~~~
  def signOfTheTimes[T: Numeric](t: T): T = ...
~~~~~~~~

Niestety, teraz musielibyśmy wszędzie używać `implicitly[Numeric[T]]`. Możemy pomóc sobie, definiując
metodę pomocniczą w obiekcie towarzyszącym typeklasy

{lang="text"}
~~~~~~~~
  object Numeric {
    def apply[T](implicit numeric: Numeric[T]): Numeric[T] = numeric
  }
~~~~~~~~

aby uzyskać dostęp do jej instancji w bardziej zwięzły sposób:

{lang="text"}
~~~~~~~~
  def signOfTheTimes[T: Numeric](t: T): T = {
    val N = Numeric[T]
    import N._
    times(negate(abs(t)), t)
  }
~~~~~~~~

Nadal jednak jest to, dla nas, implementatorów, problem. Zmuszeni jesteśmy używać czytanej od wewnątrz do zewnątrz składni
metod statycznych zamiast czytanej od lewej do prawej składni tradycyjnej. Możemy sobie z tym poradzić poprzez
definicję obiektu `ops` wewnątrz obiektu towarzyszącego typeklasy:

{lang="text"}
~~~~~~~~
  object Numeric {
    def apply[T](implicit numeric: Numeric[T]): Numeric[T] = numeric
  
    object ops {
      implicit class NumericOps[T](t: T)(implicit N: Numeric[T]) {
        def +(o: T): T = N.plus(t, o)
        def *(o: T): T = N.times(t, o)
        def unary_-: T = N.negate(t)
        def abs: T = N.abs(t)
  
        // duplicated from Ordering.ops
        def <(o: T): T = N.lt(t, o)
        def >(o: T): T = N.gt(t, o)
      }
    }
  }
~~~~~~~~

Zauważ, że zapis `-x` rozwijany jest przez kompilator do `x.unary_-`, dlatego też definiujemy rozszerzającą metodę (_extension method_)
`unary_-`. Możemy teraz zapisać naszą funkcję w sposób zdecydowanie czystszy:

{lang="text"}
~~~~~~~~
  import Numeric.ops._
  def signOfTheTimes[T: Numeric](t: T): T = -(t.abs) * t
~~~~~~~~

Dobra wiadomość jest taka, że nie musimy pisać całego tego boilerplatu własnoręcznie, ponieważ
[Simulacrum](https://github.com/mpilquist/simulacrum) dostarcza makro anotacje `@typeclass`, która automatycznie
generuje dla nas metodę `apply` i obiekt `ops`. Dodatkowo pozwala nam nawet zdefiniować alternatywne (zazwyczaj symboliczne)
nazwy dla metod. Całość:

{lang="text"}
~~~~~~~~
  import simulacrum._
  
  @typeclass trait Ordering[T] {
    def compare(x: T, y: T): Int
    @op("<") def lt(x: T, y: T): Boolean = compare(x, y) < 0
    @op(">") def gt(x: T, y: T): Boolean = compare(x, y) > 0
  }
  
  @typeclass trait Numeric[T] extends Ordering[T] {
    @op("+") def plus(x: T, y: T): T
    @op("*") def times(x: T, y: T): T
    @op("unary_-") def negate(x: T): T
    def zero: T
    def abs(x: T): T = if (lt(x, zero)) negate(x) else x
  }
  
  import Numeric.ops._
  def signOfTheTimes[T: Numeric](t: T): T = -(t.abs) * t
~~~~~~~~

Kiedy używamy operatora symbolicznego, możemy czytać (nazywać) go jak odpowiadającą mu metodę. Np. `<` przeczytamy
jako "less then", a nie "left angle bracket".

### Instancje

*Instancje* typu `Numeric` (które są również instancjami `Ordering`) są definiowane jako `implicit val` i rozszerzają
typeklasę, mogąc tym samym dostarczać bardziej optymalne implementacje generycznych metod:

{lang="text"}
~~~~~~~~
  implicit val NumericDouble: Numeric[Double] = new Numeric[Double] {
    def plus(x: Double, y: Double): Double = x + y
    def times(x: Double, y: Double): Double = x * y
    def negate(x: Double): Double = -x
    def zero: Double = 0.0
    def compare(x: Double, y: Double): Int = java.lang.Double.compare(x, y)
  
    // optimised
    override def lt(x: Double, y: Double): Boolean = x < y
    override def gt(x: Double, y: Double): Boolean = x > y
    override def abs(x: Double): Double = java.lang.Math.abs(x)
  }
~~~~~~~~

Mimo że używamy tutaj `+`, `*`, `unary_-`, `<` i `>`, które zdefiniowane są też przy użyciu `@ops` (i mogłyby spowodować
nieskończoną pętlę wywołań), są one również zdefiniowane bezpośrednio dla typu `Double`. Metody klasy są używane w 
pierwszej kolejności, a dopiero w przypadku ich braku kompilator szuka metod rozszerzających. W rzeczywistości kompilator Scali
obsługuje wywołania tych metod w specjalny sposób i zamienia je bezpośrednio na instrukcje kodu bajtowego, odpowiednio `dadd`, `dmul`, `dcmpl` i `dcmpg`.

Możemy również zaimplementować `Numeric` dla Javowego `BigDecimal` (unikaj `scala.BigDecimal`, 
[jest całkowicie zepsuty](https://github.com/scala/bug/issues/9670)).

{lang="text"}
~~~~~~~~
  import java.math.{ BigDecimal => BD }
  
  implicit val NumericBD: Numeric[BD] = new Numeric[BD] {
    def plus(x: BD, y: BD): BD = x.add(y)
    def times(x: BD, y: BD): BD = x.multiply(y)
    def negate(x: BD): BD = x.negate
    def zero: BD = BD.ZERO
    def compare(x: BD, y: BD): Int = x.compareTo(y)
  }
~~~~~~~~

Możemy też zdefiniować nasz własny typ danych do reprezentowania liczb zespolonych:

{lang="text"}
~~~~~~~~
  final case class Complex[T](r: T, i: T)
~~~~~~~~

Tym samym uzyskamy `Numeric[Complex[T]]`, jeśli istnieje `Numeric[T]`. Instancje te zależą od typu `T`, a więc definiujemy
je jako `def`, a nie `val`.

{lang="text"}
~~~~~~~~
  implicit def numericComplex[T: Numeric]: Numeric[Complex[T]] =
    new Numeric[Complex[T]] {
      type CT = Complex[T]
      def plus(x: CT, y: CT): CT = Complex(x.r + y.r, x.i + y.i)
      def times(x: CT, y: CT): CT =
        Complex(x.r * y.r + (-x.i * y.i), x.r * y.i + x.i * y.r)
      def negate(x: CT): CT = Complex(-x.r, -x.i)
      def zero: CT = Complex(Numeric[T].zero, Numeric[T].zero)
      def compare(x: CT, y: CT): Int = {
        val real = (Numeric[T].compare(x.r, y.r))
        if (real != 0) real
        else Numeric[T].compare(x.i, y.i)
      }
    }
~~~~~~~~

Uważny czytelnik zauważy, że `abs` jest czymś zupełnie innym, niż oczekiwałby matematyk. Poprawna wartość zwracana
z tej metody powinna być typu `T`, a nie `Complex[T]`.

`scala.math.Numeric` stara się robić zbyt wiele i nie generalizuje ponad liczby rzeczywiste. Pokazuje nam to, że 
małe, dobrze zdefiniowane typeklasy są często lepsze niż monolityczne kolekcje szczegółowych funkcjonalności.


### Niejawne rozstrzyganie[^implres]

[^implres]: _Implicit resolution_

Wielokrotnie używaliśmy wartości niejawnych: ten rozdział ma na celu doprecyzować, czym one są i jak tak naprawdę działają.

O *parametrach niejawnych* (_implicit parameters_) mówimy, gdy metoda żąda, aby unikalna instancja określonego typu znajdowała się
w *niejawnym zakresie* (_implicit scope_) wywołującego. Może do tego używać specjalnej składni ograniczeń kontekstu lub
deklarowac je wprost.
Parametry niejawne są więc dobrym sposobem na przekazywanie konfiguracji poprzez warstwy naszej aplikacji.

W tym przykładzie `foo` wymaga aby dostępne były instancje typeklas `Numeric` i `Typeable` dla A, oraz instancja typu
`Handler`, który przyjmuje dwa parametry typu.

{lang="text"}
~~~~~~~~
  def foo[A: Numeric: Typeable](implicit A: Handler[String, A]) = ...
~~~~~~~~

*Konwersje niejawne* pojawiają się, gdy używamy `implicit def`. Jednym z użyć niejawnych konwersji jest stosowanie 
metod rozszerzających. Kiedy kompilator próbuje odnaleźć metodę, która ma zostać wywołana na obiekcie, przegląda metody zdefiniowane 
w klasie tego obiektu, a następnie wszystkie klasy, po których ona dziedziczy (reguła podobna do tych znanych 
z Javy). Jeśli takie poszukiwanie się nie powiedzie, kompilator zaczyna przeglądać *zakres niejawny* w poszukiwaniu
konwersji do innych typów, a następnie na nich szuka wspomnianej metody.

Inny przykładem użycia niejawnych konwersji jest *derywacja typeklas* (_typeclass derivation_). W poprzednim rozdziale
napisaliśmy metodę niejawną, która tworzyła instancję `Numeric[Complex[T]]` jeśli dostępna była instancja `Numeric[T]`.
Możemy w ten sposób łączyć wiele niejawnych metod (również rekurencyjnie), dochodząc tym samym do metody zwanej
"typeful programming", która pozwala nam wykonywać obliczenia na etapie kompilacji, a nie w czasie działania programu.

Część, która łączy niejawne parametry (odbiorców) z niejawnymi konwersjami i wartościami (dostawcami), nazywa się niejawnym rozstrzyganiem.

Najpierw w poszukiwaniu wartości niejawnych przeszukiwany jest standardowy zakres zmiennych, wg kolejności:

-   zakres lokalny, wliczając lokalne importy (np. ciało bloku lub metody)
-   zakres zewnętrzny, wliczając lokalne importy (np. ciało klasy)
-   przodkowie (np. ciało klasy, po której dziedziczymy)
-   aktualny obiekt pakietu (_package object_)
-   obiekty pakietów nadrzędnych (kiedy używamy zagnieżdżonych pakietów)
-   importy globalne zdefiniowane w pliku

Jeśli nie uda się odnaleźć pasującej metody, przeszukiwany jest zakres specjalny, składający się z:
wnętrza obiektu towarzyszącego danego typu, jego obiektu pakietu, obiektów pakietów zewnętrznych (jeśli jest zagnieżdżony)),
a w przypadku porażki to samo powtarzane jest dla typów, po których nasza klasa dziedziczy. Operacje te wykonywane są kolejno dla:

-   typu zadanego parametru
-   oczekiwanego typu parametru
-   parametru typu (jeśli istnieje)

Jeśli w tej samej fazie poszukiwań znalezione zostaną dwie pasujące wartości niejawne, zgłaszany jest błąd niejednoznaczności
*ambigous implicit error*.

Wartości niejawne często definiowane są wewnątrz traitów, które następnie rozszerzane są przez obiekty. 
Praktyka ta podyktowana jest próbą kontrolowania priorytetów wg których kompilator dobiera pasującą wartość, unikając
jednocześnie błędów niejednoznaczności.

Specyfikacja języka Scala jest dość nieprecyzyjna, jeśli chodzi o przypadki skrajne, co sprawia, że aktualna implementacja
kompilatora staje się standardem. Są pewne reguły, którymi będziemy się kierować w tej książce, jak na przykład
używanie `implicit val` zamiast `implicit object`, mimo że ta druga opcja jest bardziej zwięzła. [Kaprys 
kompilatora](https://github.com/scala/bug/issues/10411) sprawia, że wartości definiowane jako `implicit object` 
wewnątrz obiektu towarzyszącego są traktowane inaczej niż te definiowane za pomocą `implicit val`.

Niejawne rozstrzyganie zawodzi, kiedy typeklasy tworzą hierarchię tak jak w przypadku klas `Ordering` i `Numeric`.
Jeśli napiszemy funkcję, która przyjmuje niejawny parametr typu `Ordering` i zawołamy ją z typem prymitywnym, który
posiada instancję `Numeric` zdefiniowaną w obiekcie towarzyszącym typu `Numeric`, kompilator rzeczonej instancji nie znajdzie.

Niejawne rozstrzyganie staje się prawdziwą loterią, gdy w grze [pojawią się aliasy typu](https://github.com/scala/bug/issues/10582),
które zmieniają *kształt* parametru. Dla przykładu, parametr niejawny używający aliasu `type Values[A] = List[Option[A]]` 
prawdopodobnie nie zostanie połączony z niejawną wartością zdefiniowaną dla typu  `List[Option[A]]` ponieważ kształt
zmienia się z *kolekcji kolekcji* elementów typu `A` na *kolekcję* elementów typu `A`.


## Modelowanie OAuth2

Zakończymy ten rozdział praktycznym przykładem modelowania danych i derywacji typeklas połączonych z projektowaniem
algebr i modułów, o którym mówiliśmy w poprzednim rozdziale.

W naszej aplikacje `drone-dynamic-agents` chcielibyśmy komunikować się z serwerem Drone i Google Cloud używając JSONa poprzez
REST API. Obie usługi używają [OAuth2](https://tools.ietf.org/html/rfc6749) do uwierzytelniania użytkowników. Istnieje
wiele interpretacji OAuth2, ale my skupimy się na tej, która działa z Google Cloud (wersja współpracująca z Drone 
jest jeszcze prostsza).


### Opis

Każda aplikacja komunikująca się z Google Cloud musi mieć skonfigurowany *Klucz Kliencki OAuth 2.0* (_OAuth 2.0 Client Key_) poprzez

{lang="text"}
~~~~~~~~
  https://console.developers.google.com/apis/credentials?project={PROJECT_ID}
~~~~~~~~

co da nam dostęp do *ID Klienta* (_Client ID_) oraz *Sekretu Klienta* (_Client secret_).

Aplikacja może wtedy uzyskać jednorazowy *kod* poprzez sprawienie, aby użytkownik wykonał *Prośbę o Autoryzację* (_Authorization Request_)
w swojej przeglądarce (tak, naprawdę, **w swojej przeglądarce**). Musimy więc wyświetlić poniższą stronę:

{lang="text"}
~~~~~~~~
  https://accounts.google.com/o/oauth2/v2/auth?\
    redirect_uri={CALLBACK_URI}&\
    prompt=consent&\
    response_type=code&\
    scope={SCOPE}&\
    access_type=offline&\
    client_id={CLIENT_ID}
~~~~~~~~

*Kod* dostarczony zostanie pod `{CALLBACK_URI}` w postaci żądania `GET`. Aby go odebrać, musimy posiadać serwer http
słuchający na interfejsie `localhost`.

Gdy zdobędziemy *kod*, możemy wykonać *Żądanie o Token Dostępu* (_Access Token Request_):

{lang="text"}
~~~~~~~~
  POST /oauth2/v4/token HTTP/1.1
  Host: www.googleapis.com
  Content-length: {CONTENT_LENGTH}
  content-type: application/x-www-form-urlencoded
  user-agent: google-oauth-playground
  code={CODE}&\
    redirect_uri={CALLBACK_URI}&\
    client_id={CLIENT_ID}&\
    client_secret={CLIENT_SECRET}&\
    scope={SCOPE}&\
    grant_type=authorization_code
~~~~~~~~

na które odpowiedzią będzie dokument JSON

{lang="text"}
~~~~~~~~
  {
    "access_token": "BEARER_TOKEN",
    "token_type": "Bearer",
    "expires_in": 3600,
    "refresh_token": "REFRESH_TOKEN"
  }
~~~~~~~~

*Tokeny posiadacza* (_Bearer tokens_) zazwyczaj wygasają po godzinie i mogą być odświeżone poprzez
wykonanie kolejnego żądania http z użyciem *tokenu odświeżającego* (_refresh token_):

{lang="text"}
~~~~~~~~
  POST /oauth2/v4/token HTTP/1.1
  Host: www.googleapis.com
  Content-length: {CONTENT_LENGTH}
  content-type: application/x-www-form-urlencoded
  user-agent: google-oauth-playground
  client_secret={CLIENT_SECRET}&
    grant_type=refresh_token&
    refresh_token={REFRESH_TOKEN}&
    client_id={CLIENT_ID}
~~~~~~~~

na który odpowiedzią jest

{lang="text"}
~~~~~~~~
  {
    "access_token": "BEARER_TOKEN",
    "token_type": "Bearer",
    "expires_in": 3600
  }
~~~~~~~~

Wszystkie żądania do serwera powinny zwierać nagłówek

{lang="text"}
~~~~~~~~
  Authorization: Bearer BEARER_TOKEN
~~~~~~~~

z podstawioną rzeczywistą wartością `BEARER_TOKEN`.

Google wygasza wszystkie tokeny oprócz najnowszych 50, a więc czas odświeżania to tylko wskazówka. *Tokeny odświeżające*
trwają pomiędzy sesjami i mogą być wygaszone ręcznie przez użytkownika. Tak więc możemy mieć jednorazową aplikację
do pobierania tokenu odświeżającego, który następnie umieścimy w konfiguracji drugiej aplikacji.

Drone nie implementuje endpointu `/auth` ani tokenów odświeżających, a jedynie dostarcza `BEARER_TOKEN` poprzez
interfejs użytkownika.


### Dane

Pierwszym krokiem będzie zamodelowanie danych potrzebnych do implementacji OAuth2. Tworzymy więc ADT z dokładnie takimi
samymi polami jak te wymagane przez serwer OAuth2. Użyjemy typów `String` i `Long` dla zwięzłości, ale moglibyśmy użyć typów 
rafinowanych, gdyby wyciekały one do naszego modelu biznesowego.

{lang="text"}
~~~~~~~~
  import refined.api.Refined
  import refined.string.Url
  
  final case class AuthRequest(
    redirect_uri: String Refined Url,
    scope: String,
    client_id: String,
    prompt: String = "consent",
    response_type: String = "code",
    access_type: String = "offline"
  )
  final case class AccessRequest(
    code: String,
    redirect_uri: String Refined Url,
    client_id: String,
    client_secret: String,
    scope: String = "",
    grant_type: String = "authorization_code"
  )
  final case class AccessResponse(
    access_token: String,
    token_type: String,
    expires_in: Long,
    refresh_token: String
  )
  final case class RefreshRequest(
    client_secret: String,
    refresh_token: String,
    client_id: String,
    grant_type: String = "refresh_token"
  )
  final case class RefreshResponse(
    access_token: String,
    token_type: String,
    expires_in: Long
  )
~~~~~~~~

W> Za wszelką cenę unikaj używania typu `java.net.URL`: wykonuje on zapytanie do serwera DNS, 
W> gdy używamy `toString`, `equals` lub `hashCode`.
W>
W> Oprócz tego, że jest to kompletnie szalone i **bardzo bardzo** wolne, metody te mogą wyrzucić wyjątek I/O (nie są *czyste*) oraz
W> mogą zmieniać swoje zachowanie w zależności od konfiguracji sieciowej (nie są *deterministyczne*).
W>
W> Rafinowany typ `String Refined Url` pozwala nam porównywać instancje, bazując na typie `String` oraz
W> w bezpieczny sposób budować `URL`, jeśli wymaga od nas tego zewnętrzne API.
W>
W> Nie mniej, w kodzie, który wymaga wysokiej wydajności, wolelibyśmy zamienić `java.net.URL` na zewnętrzny parser
W> URLi, np. [jurl](https://github.com/anthonynsimon/jurl), gdyż nawet bezpieczne części `java.net.*` stają się
W> niezwykle wolne, gdy używane są na dużą skalę.


### Funkcjonalność

Musimy przetransformować klasy zdefiniowane w poprzedniej sekcji do JSONa, URLi i formy znanej z żądań HTTP POST.
Ponieważ aby to osiągnąć, niezbędny jest polimorfizm, potrzebować będziemy typeklas.

[`jsonformat`](https://github.com/scalaz/scalaz-deriving/tree/master/examples/jsonformat/src) to prosta biblioteka do 
pracy z JSONem, którą poznamy dokładniej w jednym z następnych rozdziałów. Została ona stworzona, stawiając na 
pierwszym miejscu pryncypia programowania funkcyjnego i czytelność kodu. Składa się ona z AST do opisu JSONa 
oraz typeklas do jego kodowania i dekodowania:

{lang="text"}
~~~~~~~~
  package jsonformat
  
  sealed abstract class JsValue
  final case object JsNull                                    extends JsValue
  final case class JsObject(fields: IList[(String, JsValue)]) extends JsValue
  final case class JsArray(elements: IList[JsValue])          extends JsValue
  final case class JsBoolean(value: Boolean)                  extends JsValue
  final case class JsString(value: String)                    extends JsValue
  final case class JsDouble(value: Double)                    extends JsValue
  final case class JsInteger(value: Long)                     extends JsValue
  
  @typeclass trait JsEncoder[A] {
    def toJson(obj: A): JsValue
  }
  
  @typeclass trait JsDecoder[A] {
    def fromJson(json: JsValue): String \/ A
  }
~~~~~~~~

A> `\/` to wersja typu `Either` z biblioteki Scalaz, wyposażona w metodę `.flatMap`. Możemy używać tego typu
A> w konstrukcji `for`, podczas gdy `Either` umożliwia to dopiero od wersji Scali 2.12. Czytamy go jako 
*dysjunkcja* (_disjunction_) lub *wściekły zając* (_angry rabbit_).
A>
A> `scala.Either` został [dodany do biblioteki standardowej](https://issues.scala-lang.org/browse/SI-250) przez 
A> twórcę Scalaz, Tony'ego Morrisa, w 2017 roku. Typ `\/` został stworzony, gdy
A> do typu `Either` dodane zostały niebezpieczne (_unsafe_) metody.

Potrzebować będziemy instancji `JsDecoder[AccessResponse]` i `JsDecoder[RefreshResponse]`. Możemy je zbudować,
używają, funkcji pomocniczej:

{lang="text"}
~~~~~~~~
  implicit class JsValueOps(j: JsValue) {
    def getAs[A: JsDecoder](key: String): String \/ A = ...
  }
~~~~~~~~

Umieścimy je w obiektach towarzyszących naszych typów danych, aby zawsze znajdowały się w zakresie niejawnym:

{lang="text"}
~~~~~~~~
  import jsonformat._, JsDecoder.ops._
  
  object AccessResponse {
    implicit val json: JsDecoder[AccessResponse] = j =>
      for {
        acc <- j.getAs[String]("access_token")
        tpe <- j.getAs[String]("token_type")
        exp <- j.getAs[Long]("expires_in")
        ref <- j.getAs[String]("refresh_token")
      } yield AccessResponse(acc, tpe, exp, ref)
  }
  
  object RefreshResponse {
    implicit val json: JsDecoder[RefreshResponse] = j =>
      for {
        acc <- j.getAs[String]("access_token")
        tpe <- j.getAs[String]("token_type")
        exp <- j.getAs[Long]("expires_in")
      } yield RefreshResponse(acc, tpe, exp)
  }
~~~~~~~~

Możemy teraz sparsować ciąg znaków do typu `AccessResponse` lub `RefreshResponse`

{lang="text"}
~~~~~~~~
  scala> import jsonformat._, JsDecoder.ops._
  scala> val json = JsParser("""
                       {
                         "access_token": "BEARER_TOKEN",
                         "token_type": "Bearer",
                         "expires_in": 3600,
                         "refresh_token": "REFRESH_TOKEN"
                       }
                       """)
  
  scala> json.map(_.as[AccessResponse])
  AccessResponse(BEARER_TOKEN,Bearer,3600,REFRESH_TOKEN)
~~~~~~~~

Musimy stworzyć nasze własne typeklasy do kodowania danych w postaci URLi i żądań POST. 
Poniżej widzimy całkiem rozsądny design:

{lang="text"}
~~~~~~~~
  // URL query key=value pairs, in un-encoded form.
  final case class UrlQuery(params: List[(String, String)])
  
  @typeclass trait UrlQueryWriter[A] {
    def toUrlQuery(a: A): UrlQuery
  }
  
  @typeclass trait UrlEncodedWriter[A] {
    def toUrlEncoded(a: A): String Refined UrlEncoded
  }
~~~~~~~~

Musimy zapewnić instancje dla typów podstawowych:

{lang="text"}
~~~~~~~~
  import java.net.URLEncoder
  
  object UrlEncodedWriter {
    implicit val encoded: UrlEncodedWriter[String Refined UrlEncoded] = identity
  
    implicit val string: UrlEncodedWriter[String] =
      (s => Refined.unsafeApply(URLEncoder.encode(s, "UTF-8")))
  
    implicit val url: UrlEncodedWriter[String Refined Url] =
      (s => s.value.toUrlEncoded)
  
    implicit val long: UrlEncodedWriter[Long] =
      (s => Refined.unsafeApply(s.toString))
  
    implicit def ilist[K: UrlEncodedWriter, V: UrlEncodedWriter]
      : UrlEncodedWriter[IList[(K, V)]] = { m =>
      val raw = m.map {
        case (k, v) => k.toUrlEncoded.value + "=" + v.toUrlEncoded.value
      }.intercalate("&")
      Refined.unsafeApply(raw) // by deduction
    }
  
  }
~~~~~~~~

Używamy `Refined.unsafeApply`, kiedy jesteśmy pewni, że zawartość stringa jest już poprawnie zakodowana i możemy 
pominąć standardową weryfikację.

`ilist` jest przykładem prostej derywacji typeklasy, w sposób podobny do tego, którego użyliśmy przy `Numeric[Complex]`.
Metoda `.intercalate` to bardziej ogólna wersja `.mkString`.

A> `UrlEncodedWriter` wykorzystuje funkcjonalność *Pojedynczych Metod Abstrakcyjnych_* (SAM, _Single Abstract Method_) 
A> języka Scala. Pełna forma powyższego zapisu to:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   implicit val string: UrlEncodedWriter[String] =
A>     new UrlEncodedWriter[String] {
A>       override def toUrlEncoded(s: String): String = ...
A>     }
A> ~~~~~~~~
A> 
A> Kiedy kompilator Scali oczekuje klasy, która posiada jedną metodę abstrakcyjną, a otrzyma lambdę, dopisuje on 
A> automatycznie niezbędny boilerplate.
A> 
A> Zanim funkcjonalność ta została dodana, powszechnym było definiowanie metody `instance` w obiekcie
A> towarzyszącym typeklasy
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   def instance[T](f: T => String): UrlEncodedWriter[T] =
A>     new UrlEncodedWriter[T] {
A>       override def toUrlEncoded(t: T): String = f(t)
A>     }
A> ~~~~~~~~
A> 
A> pozwalającej na
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   implicit val string: UrlEncodedWriter[String] = instance { s => ... }
A> ~~~~~~~~
A> 
A> Praktyka ta nadal stosowana jest w projektach, które muszą wspierać starsze wersje języka lub dla typeklas
A> które wymagają więcej niż jednej metody.
A> 
A> Warto pamiętać, że istnieje wiele błędów związanych z typami SAM, ponieważ nie współdziałają one ze wszystkimi 
A> funkcjonalnościami języka. Jeśli napotkasz dziwne błędy kompilatora, warto zrezygnować z tego udogodnienia.

W rozdziale poświęconym *Derywacji typeklas* pokażemy jak stworzyć instancję `UrlQueryWriter` automatycznie oraz jak
oczyścić nieco kod, który już napisaliśmy. Na razie jednak napiszmy boilerplate dla typów, których chcemy używać:

{lang="text"}
~~~~~~~~
  import UrlEncodedWriter.ops._
  object AuthRequest {
    implicit val query: UrlQueryWriter[AuthRequest] = { a =>
      UrlQuery(List(
        ("redirect_uri"  -> a.redirect_uri.value),
        ("scope"         -> a.scope),
        ("client_id"     -> a.client_id),
        ("prompt"        -> a.prompt),
        ("response_type" -> a.response_type),
        ("access_type"   -> a.access_type))
    }
  }
  object AccessRequest {
    implicit val encoded: UrlEncodedWriter[AccessRequest] = { a =>
      IList(
        "code"          -> a.code.toUrlEncoded,
        "redirect_uri"  -> a.redirect_uri.toUrlEncoded,
        "client_id"     -> a.client_id.toUrlEncoded,
        "client_secret" -> a.client_secret.toUrlEncoded,
        "scope"         -> a.scope.toUrlEncoded,
        "grant_type"    -> a.grant_type.toUrlEncoded
      ).toUrlEncoded
    }
  }
  object RefreshRequest {
    implicit val encoded: UrlEncodedWriter[RefreshRequest] = { r =>
      IList(
        "client_secret" -> r.client_secret.toUrlEncoded,
        "refresh_token" -> r.refresh_token.toUrlEncoded,
        "client_id"     -> r.client_id.toUrlEncoded,
        "grant_type"    -> r.grant_type.toUrlEncoded
      ).toUrlEncoded
    }
  }
~~~~~~~~


### Moduł

Tym samym zakończyliśmy modelowanie danych i funkcjonalności niezbędnych do implementacji protokołu OAuth2.
Przypomnij sobie z poprzedniego rozdziału, że komponenty, które interagują ze światem zewnętrznym definiujemy jako algebry,
a logikę biznesową jako moduły, aby pozwolić na gruntowne jej przetestowanie.

Definiujemy algebry, na których bazujemy oraz używamy ograniczeń kontekstu, aby pokazać, że nasze odpowiedzi muszą posiadać
instancję `JsDecoder`, a żądania `UrlEncodedWriter`:

{lang="text"}
~~~~~~~~
  trait JsonClient[F[_]] {
    def get[A: JsDecoder](
      uri: String Refined Url,
      headers: IList[(String, String)]
    ): F[A]
  
    def post[P: UrlEncodedWriter, A: JsDecoder](
      uri: String Refined Url,
      payload: P,
      headers: IList[(String, String] = IList.empty
    ): F[A]
  }
~~~~~~~~

Zauważ, że definiujemy jedynie szczęśliwy scenariusz w API klasy `JsonClient`. Obsługą błędów zajmiemy się w jednym
z kolejnych rozdziałów.

Pozyskanie `CodeToken` z serwera Google `OAuth2` wymaga

1. wystartowania serwera HTTP na lokalnej maszynie i odczytanie numeru portu, na którym nasłuchuje.
2. otworzenia strony internetowej w przeglądarce użytkownika, tak aby mógł zalogować się do usług Google swoimi danymi
i uwierzytelnić aplikacje
3. przechwycenia kodu, poinformowania użytkownika o następnych krokach i zamknięcia serwera HTTP.

Możemy zamodelować to jako trzy metody wewnątrz algebry `UserInteraction`.

{lang="text"}
~~~~~~~~
  final case class CodeToken(token: String, redirect_uri: String Refined Url)
  
  trait UserInteraction[F[_]] {
    def start: F[String Refined Url]
    def open(uri: String Refined Url): F[Unit]
    def stop: F[CodeToken]
  }
~~~~~~~~

Ujęte w ten sposób wydaje się to niemal proste.

Potrzebujemy również algebry pozwalającej abstrahować nam nad lokalnym czasem systemu

{lang="text"}
~~~~~~~~
  trait LocalClock[F[_]] {
    def now: F[Epoch]
  }
~~~~~~~~

oraz typu danych, którego użyjemy w implementacji logiki odświeżania tokenów

{lang="text"}
~~~~~~~~
  final case class ServerConfig(
    auth: String Refined Url,
    access: String Refined Url,
    refresh: String Refined Url,
    scope: String,
    clientId: String,
    clientSecret: String
  )
  final case class RefreshToken(token: String)
  final case class BearerToken(token: String, expires: Epoch)
~~~~~~~~

Możemy teraz napisać nasz moduł klienta OAuth2:

{lang="text"}
~~~~~~~~
  import http.encoding.UrlQueryWriter.ops._
  
  class OAuth2Client[F[_]: Monad](
    config: ServerConfig
  )(
    user: UserInteraction[F],
    client: JsonClient[F],
    clock: LocalClock[F]
  ) {
    def authenticate: F[CodeToken] =
      for {
        callback <- user.start
        params   = AuthRequest(callback, config.scope, config.clientId)
        _        <- user.open(params.toUrlQuery.forUrl(config.auth))
        code     <- user.stop
      } yield code
  
    def access(code: CodeToken): F[(RefreshToken, BearerToken)] =
      for {
        request <- AccessRequest(code.token,
                                 code.redirect_uri,
                                 config.clientId,
                                 config.clientSecret).pure[F]
        msg     <- client.post[AccessRequest, AccessResponse](
                     config.access, request)
        time    <- clock.now
        expires = time + msg.expires_in.seconds
        refresh = RefreshToken(msg.refresh_token)
        bearer  = BearerToken(msg.access_token, expires)
      } yield (refresh, bearer)
  
    def bearer(refresh: RefreshToken): F[BearerToken] =
      for {
        request <- RefreshRequest(config.clientSecret,
                                  refresh.token,
                                  config.clientId).pure[F]
        msg     <- client.post[RefreshRequest, RefreshResponse](
                     config.refresh, request)
        time    <- clock.now
        expires = time + msg.expires_in.seconds
        bearer  = BearerToken(msg.access_token, expires)
      } yield bearer
  }
~~~~~~~~


## Podsumowanie

-  *algebraiczne typy danych* (ADT) są definiowane jako *produkty* (`final case class`) i *koprodukty* 
    (`sealed abstract class`).
-   Typy `Refined` egzekwują ograniczenia na zbiorze możliwych wartości.
-   konkretne funkcje mogą być definiowane wewnątrz klas niejawnych (`implicit class`), aby zachować
    kierunek czytania od lewej do prawej.
-   funkcje polimorficzne definiowane są wewnątrz *typeklas*. Funkcjonalności zapewniane są poprzez 
    *ograniczenia kontekstu* wyrażające relacje "ma", a nie hierarchie klas wyrażające relacje "jest".
-   anotacja `@simulacrum.typeclass` generuje obiekt `.ops` wewnątrz obiektu towarzyszącego, zapewniając wygodniejszą
    składnię dla metod typeklasy.
-   *derywacja typeklas* to kompozycja typeklas odbywająca się w czasie kompilacji.


# Typeklasy ze Scalaz

W tym rozdziale przejdziemy przez niemal wszystkie typeklasy zdefiniowane w `scalaz-core`. Nie wszystkie z nich
znajdują zastosowanie w `drone-dynamic-agents`, więc czasami będziemy używać samodzielnych przykładów.

Napotkać można krytykę w stosunku do konwencji nazewniczych stosowanych w Scalaz i programowaniu funkcyjnym w 
ogólności. Większość nazw podąża za konwencjami wprowadzonymi w Haskellu, który bazował z kolei na dziale matematyki
zwanym *Teorią kategorii*. Możesz śmiało użyć aliasów typów, jeśli uważasz, że rzeczowniki pochodzące od 
głównej funkcjonalności są łatwiejsze do zapamiętania (np. `Mappable`, `Pureable`, `FlatMappable`).

Zanim wprowadzimy hierarchię typeklas, popatrzmy na cztery metody, które są najistotniejsze z punktu widzenia
kontroli przepływu. Metod tych używać będziemy w większości typowych aplikacji funkcyjnych:

| Typeklasa     | Metoda     | Z         | Mając dane  | Do        |
|-------------- |----------- |---------- |------------ |---------- |
| `Functor`     | `map`      | `F[A]`    | `A => B`    | `F[B]`    |
| `Applicative` | `pure`     | `A`       |             | `F[A]`    |
| `Monad`       | `flatMap`  | `F[A]`    | `A => F[B]` | `F[B]`    |
| `Traverse`    | `sequence` | `F[G[A]]` |             | `G[F[A]]` |

Wiemy, że operacje zwracające `F[_]` mogą być wykonywane sekwencyjnie wewnątrz konstrukcji `for` przy użyciu
metody `.flatMap`, która zdefiniowana jest wewnątrz `Monad[F]`. Możemy myśleć o `F[A]` jak o kontenerze na 
pewien *efekt*, którego rezultatem jest wartość typu `A`. `.flatMap` pozwala nam wygenerować nowe efekty `F[B]` 
na podstawie rezultatów wykonania wcześniejszych efektów.

Oczywiście nie wszystkie konstruktory typu `F[_]` wiążą się z efektami ubocznymi, nawet jeśli mają instancję
`Monad[F]`, często są to po prostu struktury danych. Używając najmniej konkretnej (czyli najbardziej ogólnej) abstrakcji
możemy w łatwy sposób współdzielić kod operujący na typach `List`, `Either`, `Future` i wielu innych.

Jeśli jedyne czego potrzebujemy to przetransformować wynik `F[_]`, wystarczy, że użyjemy metody `map`, definiowanej w 
typeklasie `Functor`. W rozdziale 3 uruchamialiśmy efekty równolegle, tworząc produkt i mapując go. W Programowaniu
Funkcyjnym obliczenia wykonywane równolegle są uznawane za **słabsze** niż te wykonywane sekwencyjnie.

Pomiędzy `Monad`ą i `Functor`em leży `Applicative`, która definiuje metodę `pure` pozwalającą nam wynosić (_lift_)
wartości do postaci efektów lub tworzyć struktury danych z pojedynczych wartości. 

`.sequence` jest użyteczna, gdy chcemy poprzestawiać konstruktory typów. Gdy mamy `F[G[_]]` a potrzebujemy `G[F[_]]`,
np. zamiast `List[Future[Int]]` potrzebujemy `Future[List[Int]]`, wtedy właśnie użyjemy `.sequence`.


## Plan

Ten rozdział jest dłuższy niż zazwyczaj i wypełniony po brzegi informacjami. Przejście przez niego w wielu podejściach 
jest czymś zupełnie normalnym, a zapamiętanie  wszystkiego wymagałoby supermocy. Potraktuj go raczej jako miejsce, do którego
możesz wracać, gdy będziesz potrzebował więcej informacji.

Pominięte zostały typeklasy, które rozszerzają typ `Monad`, gdyż zasłużyły na swój własny rozdział.

Scalaz używa generacji kodu, ale nie za pomocą simulacrum. Niemniej, dla zwięzłości prezentujemy przykłady bazujące na 
anotacji `@typeclass`. Równoznaczna składanie dostępna jest, gdy zaimportujemy `scalaz._` i `Scalaz._`, a jej 
implementacja znajduje się w pakiecie `scalaz.syntax` w kodzie źródłowym scalaz.

{width=100%}
![](images/scalaz-core-tree.png)

{width=60%}
![](images/scalaz-core-cliques.png)

{width=60%}
![](images/scalaz-core-loners.png)


## Rzeczy złączalne[^appendables]

[^appendables]: _Appendable Things_

{width=25%}
![](images/scalaz-semigroup.png)

{lang="text"}
~~~~~~~~
  @typeclass trait Semigroup[A] {
    @op("|+|") def append(x: A, y: =>A): A
  
    def multiply1(value: F, n: Int): F = ...
  }
  
  @typeclass trait Monoid[A] extends Semigroup[A] {
    def zero: A
  
    def multiply(value: F, n: Int): F =
      if (n <= 0) zero else multiply1(value, n - 1)
  }
  
  @typeclass trait Band[A] extends Semigroup[A]
~~~~~~~~

A> `|+|` znany jest jako operator "TIE Fighter"[^tiefighter]. Istnieje również bardzo ekscytujący "Advanced TIE
A> Fighter", który omówimy w następnej sekcji.

[^tiefighter]: [Myśliwiec TIE](https://pl.wikipedia.org/wiki/TIE_fighter)

`Semigroup` (półgrupa) może być zdefiniowana dla danego typu, jeśli możemy połączyć ze sobą dwie jego wartości. Operacja ta
musi być *łączna* (_associative_), co oznacza, że kolejność zagnieżdżonych operacji nie powinna mieć znaczenia, np:

{lang="text"}
~~~~~~~~
  (a |+| b) |+| c == a |+| (b |+| c)
  
  (1 |+| 2) |+| 3 == 1 |+| (2 |+| 3)
~~~~~~~~

`Monoid` jest półgrupą z elementem *zerowym* (_zero_, zwanym również elementem *pustym* (_empty_), *tożsamym* (_identity_) lub *neutralnym*).
Połączenie `zero` z dowolną inną wartością `a` powinno zwracać to samo niezmienione `a`.

{lang="text"}
~~~~~~~~
  a |+| zero == a
  
  a |+| 0 == a
~~~~~~~~

Prawdopodobnie przywołaliśmy tym samym wspomnienie typu `Numeric` z Rozdziału 4. Istnieją implementacje typeklasy
`Monoid` dla wszystkich prymitywnych typów liczbowych, ale koncepcja rzeczy *złączalnych* jest użyteczna również
dla typów innych niż te liczbowe.

{lang="text"}
~~~~~~~~
  scala> "hello" |+| " " |+| "world!"
  res: String = "hello world!"
  
  scala> List(1, 2) |+| List(3, 4)
  res: List[Int] = List(1, 2, 3, 4)
~~~~~~~~

`Band` (pas) dodaje prawo, gwarantujące, że `append` wywołane na dwóch takich samych elementach jest
*idempotentne*, tzn. zwraca tę samą wartość. Przykładem są typy, które mają tylko jedną wartość, takie jak `Unit`,
kresy górne (_least upper bound_), lub zbiory (`Set`). `Band` nie wnosi żadnych dodatkowych metod, ale użytkownicy 
mogą wykorzystać dodatkowe gwarancje do optymalizacji wydajności.

A> Viktor Klang z Lightbendu zaproponował frazę
A> [effectively-once delivery](https://twitter.com/viktorklang/status/789036133434978304) dla przetwarzania wiadomości 
A> za pomocą idempotentnych operacji, takich jak `Band.append`.

Jako realistyczny przykład dla `Monoid`u, rozważmy system transakcyjny, który posiada ogromną bazę reużywalnych
wzorów transakcji. Wypełnianie wartości domyślnych dla nowej transakcji wymaga wybrania i połączenia wielu 
wzorów, z zasadą "ostatni wygrywa", jeśli dwa wzory posiadają wartości dla tego samego pola. "Wybieranie" jest
wykonywane dla nas przez osobny system, a naszym zadaniem jest jedynie połączyć wzory według kolejności.

Stworzymy prosty schemat, aby zobrazować zasadę działania, pamiętając przy tym, że prawdziwy system oparty byłby na dużo bardziej
skomplikowanym ADT.

{lang="text"}
~~~~~~~~
  sealed abstract class Currency
  case object EUR extends Currency
  case object USD extends Currency
  
  final case class TradeTemplate(
    payments: List[java.time.LocalDate],
    ccy: Option[Currency],
    otc: Option[Boolean]
  )
~~~~~~~~

Jeśli chcemy napisać metodę, która przyjmuje parametr `templates: List[TradeTemplate]`, wystarczy, że zawołamy

{lang="text"}
~~~~~~~~
  val zero = Monoid[TradeTemplate].zero
  templates.foldLeft(zero)(_ |+| _)
~~~~~~~~

i gotowe!

Jednak aby móc zawołać `zero` lub `|+|` musimy mieć dostęp do instancji `Monoid[TradeTemplate]`. Chociaż 
w ostatnim rozdziale zobaczymy jak wyderywować taką instancję w sposób generyczny, na razie stworzymy ją ręcznie:  

{lang="text"}
~~~~~~~~
  object TradeTemplate {
    implicit val monoid: Monoid[TradeTemplate] = Monoid.instance(
      (a, b) => TradeTemplate(a.payments |+| b.payments,
                              a.ccy |+| b.ccy,
                              a.otc |+| b.otc),
      TradeTemplate(Nil, None, None)
    )
  }
~~~~~~~~

Jednak nie jest to do końca to, czego byśmy chcieli, gdyż `Monoid[Option[A]]` łączy ze sobą wartości wewnętrzne, np.

{lang="text"}
~~~~~~~~
  scala> Option(2) |+| None
  res: Option[Int] = Some(2)
  scala> Option(2) |+| Option(1)
  res: Option[Int] = Some(3)
~~~~~~~~

podczas gdy my chcielibyśmy zachowania "ostatni wygrywa". Możemy więc nadpisać domyślną instancję `Monoid[Option[A]]` 
naszą własną:

{lang="text"}
~~~~~~~~
  implicit def lastWins[A]: Monoid[Option[A]] = Monoid.instance(
    {
      case (None, None)   => None
      case (only, None)   => only
      case (None, only)   => only
      case (_   , winner) => winner
    },
    None
  )
~~~~~~~~

Wszystko kompiluje się poprawnie, więc wypróbujmy nasze dzieło...

{lang="text"}
~~~~~~~~
  scala> import java.time.{LocalDate => LD}
  scala> val templates = List(
           TradeTemplate(Nil,                     None,      None),
           TradeTemplate(Nil,                     Some(EUR), None),
           TradeTemplate(List(LD.of(2017, 8, 5)), Some(USD), None),
           TradeTemplate(List(LD.of(2017, 9, 5)), None,      Some(true)),
           TradeTemplate(Nil,                     None,      Some(false))
         )
  
  scala> templates.foldLeft(zero)(_ |+| _)
  res: TradeTemplate = TradeTemplate(
                         List(2017-08-05,2017-09-05),
                         Some(USD),
                         Some(false))
~~~~~~~~

Jedyne co musieliśmy zrobić to zdefiniować jeden mały kawałek logiki biznesowej, a całą resztę
zrobił za nas `Monoid`!

Zauważ, że listy płatności są ze sobą łączone. Dzieje się tak, ponieważ domyślny `Monoid[List]` zachowuje się ten właśnie sposób.
Gdyby wymagania biznesowe były inne, wystarczyłoby dostarczyć inną instancję `Monoid[List[LocalDate]]`. Przypomnij sobie
z Rozdziału 4, że dzięki polimorfizmowi czasu kompilacji możemy zmieniać zachowanie `append` dla `List[E]` w zależności
od `E`, a nie tylko od implementacji `List`.

A> Kiedy w Rozdziale 4 wprowadzaliśmy typeklasy, powiedzieliśmy, że dla danego typu może istnieć tylko jedna instancja,
A> a więc w aplikacji istnieje tylko jeden `Monoid[Option[Boolean]]`. *Osierocone instancje* (_orphan instances_), takie jak 
A> `lastWins` to najprostsza droga do zaburzenia spójności.
A>
A> Moglibyśmy uzasadniać lokalne zaburzenie spójności, zmieniając dostęp do `lastwins` na prywatny, ale gdy dojdziemy do 
A> typeklasy `Plus`, zobaczymy lepszy sposób na implementację naszego monoidu. Kiedy dotrzemy do typów tagowanych, zobaczymy
A> sposób jeszcze lepszy: użycie `LastOption` zamiast `Option` w definicji modelu.
A>
A> Dzieci, prosimy, nie zaburzajcie spójności typeklas.


## Rzeczy obiektowe

W rozdziale o Danych i funkcjonalnościach powiedzieliśmy, że sposób, w jaki JVM rozumie równość nie działa dla wielu typów,
które możemy umieścić wewnątrz ADT. Problem ten wynika z faktu, że JVM był projektowany dla języka Java, a `equals` 
zdefiniowane jest w klasie `java.lang.Object`, nie ma więc możliwości, aby `equals` usunąć ani zagwarantować, że jest
explicite zaimplementowany. 

Niemniej, w FP wolimy używać typeklas do wyrażania polimorficznych zachowań i pojęcie równości również może zostać
w ten sposób wyrażone.

{width=20%}
![](images/scalaz-comparable.png)

{lang="text"}
~~~~~~~~
  @typeclass trait Equal[F]  {
    @op("===") def equal(a1: F, a2: F): Boolean
    @op("/==") def notEqual(a1: F, a2: F): Boolean = !equal(a1, a2)
  }
~~~~~~~~

`===` (*potrójne równa się*, _triple equals_) jest bezpieczniejszy względem typów (_typesafe_) niż `==` (*podwójne równa się*,
_double equals_), ponieważ użycie go wymaga, aby po obu stronach porównania znajdowały się instancje dokładnie tego samego typu.
W ten sposób możemy zapobiec wielu częstym błędom.

`equal` ma te same wymagania jak `Object.equals`

-   *przemienność* (_commutative_): `f1 === f2` implikuje `f2 === f1`
-   *zwrotność* (_reflexive_): `f === f`
-   *przechodniość* (_transitive_): `f1 === f2 && f2 === f3` implikuje `f1 === f3`

Poprzez odrzucenie uniwersalnego `Object.equals`, gdy konstruujemy ADT, nie bierzemy za pewnik, że wiemy jak
porównywać instancje danego typu. Jeśli instancja `Equal` nie będzie dostępna, nasz kod się nie skompiluje. 

Kontynuując praktykę odrzucania zaszłości z Javy, zamiast mówić, że dane są instancją `java.lang.Comparable`,
powiemy, że mają instancję typeklasy `Order`:

{lang="text"}
~~~~~~~~
  @typeclass trait Order[F] extends Equal[F] {
    @op("?|?") def order(x: F, y: F): Ordering
  
    override  def equal(x: F, y: F): Boolean = order(x, y) == Ordering.EQ
    @op("<" ) def lt(x: F, y: F): Boolean = ...
    @op("<=") def lte(x: F, y: F): Boolean = ...
    @op(">" ) def gt(x: F, y: F): Boolean = ...
    @op(">=") def gte(x: F, y: F): Boolean = ...
  
    def max(x: F, y: F): F = ...
    def min(x: F, y: F): F = ...
    def sort(x: F, y: F): (F, F) = ...
  }
  
  sealed abstract class Ordering
  object Ordering {
    case object LT extends Ordering
    case object EQ extends Ordering
    case object GT extends Ordering
  }
~~~~~~~~

`Order` implementuje `.equal`, wykorzystując nową metodę prostą `.order`. Kiedy typeklasa implementuje 
*kombinator prymitywny* rodzica za pomocą *kombinatora pochodnego*, musimy dodać *domniemane prawo podstawiania* 
(_implied law of substitution_). Jeśli instancja `Order` ma nadpisać `.equal` z powodów wydajnościowych, musi ona zachowywać
się dokładnie tak samo jak oryginał.

Rzeczy, które definiują porządek, mogą również być dyskretne, pozwalając nam na przechodzenie do poprzedników i 
następników:

{lang="text"}
~~~~~~~~
  @typeclass trait Enum[F] extends Order[F] {
    def succ(a: F): F
    def pred(a: F): F
    def min: Option[F]
    def max: Option[F]
  
    @op("-+-") def succn(n: Int, a: F): F = ...
    @op("---") def predn(n: Int, a: F): F = ...
  
    @op("|->" ) def fromToL(from: F, to: F): List[F] = ...
    @op("|-->") def fromStepToL(from: F, step: Int, to: F): List[F] = ...
    @op("|=>" ) def fromTo(from: F, to: F): EphemeralStream[F] = ...
    @op("|==>") def fromStepTo(from: F, step: Int, to: F): EphemeralStream[F] = ...
  }
~~~~~~~~

{lang="text"}
~~~~~~~~
  scala> 10 |--> (2, 20)
  res: List[Int] = List(10, 12, 14, 16, 18, 20)
  
  scala> 'm' |-> 'u'
  res: List[Char] = List(m, n, o, p, q, r, s, t, u)
~~~~~~~~

A> `|-->` to Miecz Świetlny Scalaz. To jest właśnie składnia Programisty Funkcyjnego. Nie jakieś niezdarne albo losowe `fromStepToL`.
A>  Elegancka składnia... na bardziej cywilizowane czasy.

`EphemeralStream` omówimy w następnym rozdziale, na razie wystarczy nam wiedzieć, że jest to potencjalnie nieskończona
struktura danych, która unika problemów z przetrzymywaniem pamięci obecnych w klasie `Stream` z biblioteki standardowej.

Podobnie do `Object.equals`, koncepcja metody `.toString` dostępnej  w każdej klasie ma sens jedynie w Javie.
Chcielibyśmy wymusić możliwość konwersji do ciągu znaków w czasie kompilacji i dokładnie to robi typeklasa `Show`:

{lang="text"}
~~~~~~~~
  trait Show[F] {
    def show(f: F): Cord = ...
    def shows(f: F): String = ...
  }
~~~~~~~~

Lepiej poznamy klasę `Cord` w rozdziale poświęconym typom danych, teraz jedyne co musimy wiedzieć, to to że
`Cord` jest wydajną strukturą danych służącą do przechowywania i manipulowania instancjami typu `String`.


## Rzeczy mapowalne

Skupmy się teraz na rzeczach, które możemy w jakiś sposób przemapowywać (_map over_) lub trawersować (_traverse_):

{width=100%}
![](images/scalaz-mappable.png)


### Funktor

{lang="text"}
~~~~~~~~
  @typeclass trait Functor[F[_]] {
    def map[A, B](fa: F[A])(f: A => B): F[B]
  
    def void[A](fa: F[A]): F[Unit] = map(fa)(_ => ())
    def fproduct[A, B](fa: F[A])(f: A => B): F[(A, B)] = map(fa)(a => (a, f(a)))
  
    def fpair[A](fa: F[A]): F[(A, A)] = map(fa)(a => (a, a))
    def strengthL[A, B](a: A, f: F[B]): F[(A, B)] = map(f)(b => (a, b))
    def strengthR[A, B](f: F[A], b: B): F[(A, B)] = map(f)(a => (a, b))
  
    def lift[A, B](f: A => B): F[A] => F[B] = map(_)(f)
    def mapply[A, B](a: A)(f: F[A => B]): F[B] = map(f)((ff: A => B) => ff(a))
  }
~~~~~~~~

Jedyną metodą abstrakcyjną jest `map`  i musi się ona *komponować* (_składać_, _compose_), tzn. mapowanie za pomocą `f`, a następnie `g`
musi dawać ten sam wyniki jak mapowanie z użyciem złożenia tych funkcji (`f ∘ g`).

{lang="text"}
~~~~~~~~
  fa.map(f).map(g) == fa.map(f.andThen(g))
~~~~~~~~

Metoda `map` nie może też wykonywać żadnych zmian, jeśli przekazana do niej funkcja to `identity` (czyli `x => x`)

{lang="text"}
~~~~~~~~
  fa.map(identity) == fa
  
  fa.map(x => x) == fa
~~~~~~~~

`Functor` definiuje kilka pomocniczych metod wokół `map`, które mogą być zoptymalizowane przez konkretne instancje.
Dokumentacja została celowo pominięta, aby zachęcić do samodzielnego odgadnięcia co te metody robią, zanim spojrzymy na ich
implementację. Poświęć chwilę na przestudiowanie samych sygnatur, zanim ruszysz dalej:

{lang="text"}
~~~~~~~~
  def void[A](fa: F[A]): F[Unit]
  def fproduct[A, B](fa: F[A])(f: A => B): F[(A, B)]
  
  def fpair[A](fa: F[A]): F[(A, A)]
  def strengthL[A, B](a: A, f: F[B]): F[(A, B)]
  def strengthR[A, B](f: F[A], b: B): F[(A, B)]
  
  // harder
  def lift[A, B](f: A => B): F[A] => F[B]
  def mapply[A, B](a: A)(f: F[A => B]): F[B]
~~~~~~~~

1.  `void` przyjmuje instancję `F[A]` i zawsze zwraca
    `F[Unit]`, a więc gubi wszelkie przechowywane wartości, ale zachowuje strukturę.
2.  `fproduct` przyjmuje takie same argumenty jak `map`, ale zwraca `F[(A, B)]`,
    a więc łączy wynik operacji z wcześniejszą zawartością. Operacja ta przydaje się, gdy chcemy zachować 
    argumenty przekazane do funkcji. 
3.  `fpair` powiela element `A` do postaci `F[(A, A)]`
4.  `strengthL` łączy zawartość `F[B]` ze stałą typu `A` po lewej stronie.
5.  `strengthR` łączy zawartość `F[A]` ze stałą typu `B` po prawej stronie.
6.  `lift` przyjmuje funkcję `A => B`i zwraca `F[A] => F[B]`. Innymi słowy, przyjmuje funkcję, która operuje na
    zawartości `F[A]` i zwraca funkcję, która operuje na `F[A]` bezpośrednio.
7.  `mapply` to łamigłówka. Powiedzmy, że mamy `F[_]` z funkcją `A => B` w środku oraz wartość `A`, w rezultacie 
    możemy otrzymać `F[B]`. Sygnatura wygląda podobnie do `pure`, ale wymaga od wołającego dostarczenia `F[A => B]`.

`fpair`, `strengthL` i `strengthR` wyglądają całkiem bezużytecznie, ale przydają się, gdy chcemy zachować pewne informacje,
które w innym wypadku zostałyby utracone.

`Functor` ma też specjalną składnię:

{lang="text"}
~~~~~~~~
  implicit class FunctorOps[F[_]: Functor, A](self: F[A]) {
    def as[B](b: =>B): F[B] = Functor[F].map(self)(_ => b)
    def >|[B](b: =>B): F[B] = as(b)
  }
~~~~~~~~

`.as` i `>|` to metody pozwalające na zastąpienie wyniku przez przekazaną stałą.

A> Gdy Scalaz dostarcza funkcjonalności za pomocą rozszerzeń, zamiast bezpośrednio w typeklasie, dzieje się tak
A> z powodu kompatybilności binarnej.
A>
A> Gdy ukazuje się wersja `X.Y.0` Scalaz, nie ma możliwości dodania metod do typeklasy w tej samej serii wydań dla
A> Scali 2.10 i 2.11. Warto więc zawsze spojrzeć zarówno na definicję typeklasy, jak i zdefiniowanej dla niej 
A> dodatkowej składni.

W naszej przykładowej aplikacji wprowadziliśmy jeden brzydki hak, definiując metody `start` i `stop` tak,
aby zwracały swoje własne wejście:

{lang="text"}
~~~~~~~~
  def start(node: MachineNode): F[MachineNode]
  def stop (node: MachineNode): F[MachineNode]
~~~~~~~~

Pozwala nam to opisywać logikę biznesową w bardzo zwięzły sposób, np.

{lang="text"}
~~~~~~~~
  for {
    _      <- m.start(node)
    update = world.copy(pending = Map(node -> world.time))
  } yield update
~~~~~~~~

albo

{lang="text"}
~~~~~~~~
  for {
    stopped <- nodes.traverse(m.stop)
    updates = stopped.map(_ -> world.time).toList.toMap
    update  = world.copy(pending = world.pending ++ updates)
  } yield update
~~~~~~~~

Ale hak ten wprowadza zbędną komplikację do implementacji. Lepiej będzie, gdy pozwolimy naszej algebrze zwracać
`F[Unit]` a następnie użyjemy `as`:

{lang="text"}
~~~~~~~~
  m.start(node) as world.copy(pending = Map(node -> world.time))
~~~~~~~~

oraz

{lang="text"}
~~~~~~~~
  for {
    stopped <- nodes.traverse(a => m.stop(a) as a)
    updates = stopped.map(_ -> world.time).toList.toMap
    update  = world.copy(pending = world.pending ++ updates)
  } yield update
~~~~~~~~


### Foldable

Technicznie rzecz biorąc, `Foldable` przydaje się dla struktur danych, przez które możemy przejść
a na koniec wyprodukować wartość podsumowującą. Jednak stwierdzenie to nie oddaje pełnej natury tej
"jednotypeklasowej armii", która jest w stanie dostarczyć większość tego, co spodziewalibyśmy
się znaleźć w Collections API.

Do omówienia mamy tyle metod, że musimy je sobie podzielić. Zacznijmy od metod abstrakcyjnych:

{lang="text"}
~~~~~~~~
  @typeclass trait Foldable[F[_]] {
    def foldMap[A, B: Monoid](fa: F[A])(f: A => B): B
    def foldRight[A, B](fa: F[A], z: =>B)(f: (A, =>B) => B): B
    def foldLeft[A, B](fa: F[A], z: B)(f: (B, A) => B): B = ...
~~~~~~~~

Instancja `Foldable` musi zaimplementować jedynie `foldMap` i `foldRight`, aby uzyskać pełną funkcjonalność
tej typeklasy, aczkolwiek poszczególne metody są często optymalizowane dla konkretnych struktur danych.

`.foldMap` ma alternatywną nazwę do celów marketingowych: **MapReduce**. Mając do dyspozycji `F[A]`, 
funkcję z `A` na `B` i sposób na łączenie `B` (dostarczony przez `Monoid` wraz z elementem zerowym),
możemy wyprodukować "podsumowującą" wartość typu `B`. Kolejność operacji nie jest narzucana, co pozwala
na wykonywanie ich równolegle.

`.foldRight` nie wymaga, aby jej parametry miały instancję `Monoid`u, co oznacza, że musimy podać
wartość zerową `z` oraz sposób łączenia elementów z wartością podsumowująca. Kierunek przechodzenia jest
zdefiniowany jako od prawej do lewej, co sprawia, że operacje nie mogą być zrównoleglone.

A> Metoda `foldRight` jest koncepcyjnie identyczna jak `foldRight` z biblioteki standardowej scali. Jednak z tą drugą jest jeden
A> problem, który został rozwiązany w scalaz: bardzo duże struktury danych mogą powodować przepełnienie stosu (_stack overflow_).
A> `List.foldRight`, oszukuje implementując `foldRight` jako odwrócony `foldLeft`.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   override def foldRight[B](z: B)(op: (A, B) => B): B =
A>     reverse.foldLeft(z)((right, left) => op(left, right))
A> ~~~~~~~~
A> 
A> Koncepcja odwracania nie jest jednak uniwersalna i to obejście nie może być stosowane dla wszystkich struktur danych.
A> Powiedzmy, że chcielibyśmy odnaleźć małą liczbę w kolekcji `Stream` z wczesnym wyjściem (_early exit_):
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   scala> def isSmall(i: Int): Boolean = i < 10
A>   scala> (1 until 100000).toStream.foldRight(false) {
A>            (el, acc) => isSmall(el) || acc
A>          }
A>   java.lang.StackOverflowError
A>     at scala.collection.Iterator.toStream(Iterator.scala:1403)
A>     ...
A> ~~~~~~~~
A> 
A> Scalaz rozwiązuje ten problemy, przyjmując wartość zagregowaną *poprzez nazwę* (_by name_)
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   scala> (1 |=> 100000).foldRight(false)(el => acc => isSmall(el) || acc )
A>   res: Boolean = true
A> ~~~~~~~~
A> 
A> co oznacza, że wartość `acc` nie jest ewaluowana, dopóki nie jest potrzebna.
A> 
A> Warto pamiętać, że nie wszystkie operacje użyte z `foldRight` są bezpieczne od przepełnienia stosu. Używając 
A> `EphemeralStream` ze Scalaz również moglibyśmy otrzymać `StackOverflowError`, gdybyśmy
A> wymagali obliczenia wszystkich dostępnych elementów.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   scala> (1L |=> 100000L).foldRight(0L)(el => acc => el |+| acc )
A>   java.lang.StackOverflowError
A>     at scalaz.Foldable.$anonfun$foldr$1(Foldable.scala:100)
A>     ...
A> ~~~~~~~~

`foldLeft` trawersuje elementy od lewej do prawej. Metoda ta może być zaimplementowana za pomocą `foldMap`, ale
większość instancji woli dostarczyć osobną implementację dla tak podstawowej operacji. Ponieważ z reguły implementacje 
tej metody są ogonowo rekursywne (_tail recursive_), nie ma tutaj parametrów przekazywanych *przez nazwę*.

Jedyny prawem obowiązującym `Foldable` jest to, że `foldLeft` i `foldRight` powinny być spójne z `foldMap` dla
operacji monoidalnych, np. dodawanie na koniec listy dla `foldLeft` i dodawanie na początek dla `foldRight`.
Niemniej `foldLeft` i `foldRight` nie muszą być zgodne ze sobą nawzajem: w rzeczywistości często produkują
odwrotne rezultaty.

Najprostszą rzeczą, którą możemy zrobić z `foldMap` to użyć funkcji `identity` i uzyskać tym samym `fold` 
(naturalną sumę elementów monoidalnych), z dodatkowymi wariantami pozwalającymi dobrać odpowiednią metodę 
zależnie od kryteriów wydajnościowych:

{lang="text"}
~~~~~~~~
  def fold[A: Monoid](t: F[A]): A = ...
  def sumr[A: Monoid](fa: F[A]): A = ...
  def suml[A: Monoid](fa: F[A]): A = ...
~~~~~~~~
 
Gdy uczyliśmy się o `Monoid`zie, napisaliśmy:

{lang="text"}
~~~~~~
  scala> templates.foldLeft(Monoid[TradeTemplate].zero)(_ |+| _)
~~~~~~~~

Teraz wiemy już, że było to niemądre i powinniśmy zrobić tak:

{lang="text"}
~~~~~~~~
  scala> templates.toIList.fold
  res: TradeTemplate = TradeTemplate(
                         List(2017-08-05,2017-09-05),
                         Some(USD),
                         Some(false))
~~~~~~~~

`.fold` nie zadziała na klasie `List` z biblioteki standardowej, ponieważ ta definiuje już metodę o nazwie
`fold`, która robi coś podobnego na swój własny sposób.

Osobliwie nazywająca się metoda `intercalate` wstawia konkretną instancję typu `A` pomiędzy każde dwa elementy przed wykonaniem `fold.`

{lang="text"}
~~~~~~~~
  def intercalate[A: Monoid](fa: F[A], a: A): A = ...
~~~~~~~~

i jest tym samym uogólnioną wersją `mkString`:

{lang="text"}
~~~~~~~~
  scala> List("foo", "bar").intercalate(",")
  res: String = "foo,bar"
~~~~~~~~

`foldLeft` pozwala na dostęp do konkretnego elementu poprzez jego indeks oraz daje nam kilka innych, blisko związanych 
metod:

{lang="text"}
~~~~~~~~
  def index[A](fa: F[A], i: Int): Option[A] = ...
  def indexOr[A](fa: F[A], default: =>A, i: Int): A = ...
  def length[A](fa: F[A]): Int = ...
  def count[A](fa: F[A]): Int = length(fa)
  def empty[A](fa: F[A]): Boolean = ...
  def element[A: Equal](fa: F[A], a: A): Boolean = ...
~~~~~~~~

Scalaz jest biblioteką czystą, składającą się wyłącznie z *funkcji totalnych*. Tam, gdzie `List.apply` wyrzuca wyjątek,
`Foldable.index` zwraca `Option[A]` oraz pozwala użyć wygodnego `indexOr`, który zwraca `A`, bazując na wartości domyślnej.
`.element` podobny jest do `.contains` z biblioteki standardowej, ale używa `Equal` zamiast niejasno zdefiniowanego
pojęcia równości pochodzącego z JVMa.

Metody te *naprawdę* wyglądają jak API kolekcji. No i oczywiście każdy obiekt mający instancje `Foldable` może być 
przekonwertowany na listę:

{lang="text"}
~~~~~~~~
  def toList[A](fa: F[A]): List[A] = ...
~~~~~~~~

Istnieją również konwersje do innych typów danych zarówno z biblioteki standardowej, jak i Scalaz, takie jak:
`.toSet`, `.toVector`, `.toStream`, `.to[T <: TraversableLike]`, `.toIList` itd.

Dostępne są również przydatne metody do weryfikacji predykatów

{lang="text"}
~~~~~~~~
  def filterLength[A](fa: F[A])(f: A => Boolean): Int = ...
  def all[A](fa: F[A])(p: A => Boolean): Boolean = ...
  def any[A](fa: F[A])(p: A => Boolean): Boolean = ...
~~~~~~~~

`filterLength` zlicza elementy, które spełniają predykat, `all` i `any` zwracają `true`, jeśli wszystkie (lub jakikolwiek)
elementy spełniają predykat i mogą zakończyć działanie bez sprawdzania wszystkich elementów.

A> W poprzednim rozdziale widzieliśmy `NonEmptyList`. Dla zwięzłości używać będziemy skrótu `Nel` zamiast `NonEmptyList`.
A>
A> Widzieliśmy też typ `IList `, który, jak pamiętacie, jest odpowiednikiem `List`, ale pozbawionym
A> nieczystych metod, takich jak na przykład `apply`.

Możemy też podzielić `F[A]` na części bazując na kluczu `B` za pomocą metody `splitBy`

{lang="text"}
~~~~~~~~
  def splitBy[A, B: Equal](fa: F[A])(f: A => B): IList[(B, Nel[A])] = ...
  def splitByRelation[A](fa: F[A])(r: (A, A) => Boolean): IList[Nel[A]] = ...
  def splitWith[A](fa: F[A])(p: A => Boolean): List[Nel[A]] = ...
  def selectSplit[A](fa: F[A])(p: A => Boolean): List[Nel[A]] = ...
  
  def findLeft[A](fa: F[A])(f: A => Boolean): Option[A] = ...
  def findRight[A](fa: F[A])(f: A => Boolean): Option[A] = ...
~~~~~~~~

na przykład

{lang="text"}
~~~~~~~~
  scala> IList("foo", "bar", "bar", "faz", "gaz", "baz").splitBy(_.charAt(0))
  res = [(f, [foo]), (b, [bar, bar]), (f, [faz]), (g, [gaz]), (b, [baz])]
~~~~~~~~

Zwróć uwagę, że otrzymaliśmy dwa elementy zaindeksowane za pomocą `'b'`.

`splitByRelation` pozwala uniknąć dostarczania instancji `Equal`, ale za to wymaga podania operatora porównującego.

`splitWith` dzieli elementy na grupy, które spełniają i nie spełniają predykatu. `selectSplit` wybiera grupy elementów,
które spełniają predykat, a pozostałe odrzuca. To jedna z tych rzadkich sytuacji gdzie dwie metody mają tę samą sygnaturę,
ale działają inaczej. 

`findLeft` i `findRight` pozwalając znaleźć pierwszy element (od lewej lub prawej), który spełnia predykat.

Dalej korzystając z `Equal` i `Order` dostajemy metody `distinct`, które zwracają elementy unikalne.

{lang="text"}
~~~~~~~~
  def distinct[A: Order](fa: F[A]): IList[A] = ...
  def distinctE[A: Equal](fa: F[A]): IList[A] = ...
  def distinctBy[A, B: Equal](fa: F[A])(f: A => B): IList[A] =
~~~~~~~~

`distinct` jest zaimplementowany w sposób bardziej wydajny niż `distinctE`, ponieważ może bazować na kolejności,
a dzięki niej odszukiwać elementy unikalne w sposób podobny do tego, w jaki działa algorytm quicksort. Dzięki temu 
jest zdecydowanie szybszy niż `List.distinct`. Struktury danych (takie jak zbiory) mogą implementować `distinct` w 
swoich `Foldable` bez dodatkowego wysiłku. 

`distinctBy` pozwala na grupowanie, bazując na rezultacie wywołania podanej funkcji na każdym z oryginalnych elementów.
Przykładowe użycie: grupowanie imion ze względu na pierwszą literę słowa.

Możemy wykorzystać `Order` również do odszukiwania elementów minimalnych i maksymalnych (lub obu ekstremów), wliczając w to
warianty używające `Of`, lub `By` aby najpierw przemapować elementy do innego typu lub użyć innego typu do samego porównania.

{lang="text"}
~~~~~~~~
  def maximum[A: Order](fa: F[A]): Option[A] = ...
  def maximumOf[A, B: Order](fa: F[A])(f: A => B): Option[B] = ...
  def maximumBy[A, B: Order](fa: F[A])(f: A => B): Option[A] = ...
  
  def minimum[A: Order](fa: F[A]): Option[A] = ...
  def minimumOf[A, B: Order](fa: F[A])(f: A => B): Option[B] = ...
  def minimumBy[A, B: Order](fa: F[A])(f: A => B): Option[A] = ...
  
  def extrema[A: Order](fa: F[A]): Option[(A, A)] = ...
  def extremaOf[A, B: Order](fa: F[A])(f: A => B): Option[(B, B)] = ...
  def extremaBy[A, B: Order](fa: F[A])(f: A => B): Option[(A, A)] =
~~~~~~~~

Możemy na przykład zapytać o to, który element typu `String` jest maksimum ze względu (`By`) na swoją długość lub jaka jest maksymalna
długość elementów (`Of`).

{lang="text"}
~~~~~~~~
  scala> List("foo", "fazz").maximumBy(_.length)
  res: Option[String] = Some(fazz)
  
  scala> List("foo", "fazz").maximumOf(_.length)
  res: Option[Int] = Some(4)
~~~~~~~~

Podsumowuje to kluczowe funkcjonalności `Foldable`. Cokolwiek spodziewalibyśmy się zobaczyć
w API kolekcji, jest już prawdopodobnie dostępna dzięki `Foldable`, a jeśli nie jest, to prawdopodobnie być powinno.

Na koniec spojrzymy na kilka wariacji metod, które widzieliśmy już wcześniej. Zacznijmy od tych, które przyjmują
instancję typu `Semigroup` zamiast `Monoid`:


{lang="text"}
~~~~~~~~
  def fold1Opt[A: Semigroup](fa: F[A]): Option[A] = ...
  def foldMap1Opt[A, B: Semigroup](fa: F[A])(f: A => B): Option[B] = ...
  def sumr1Opt[A: Semigroup](fa: F[A]): Option[A] = ...
  def suml1Opt[A: Semigroup](fa: F[A]): Option[A] = ...
  ...
~~~~~~~~

zwracając tym samym `Option`, aby móc obsłużyć puste struktury danych (`Semigroup` nie definiuje elementu zerowego).

A> Metody te czytamy jako "one-Option", nie `10 pt`.

Typeklasa `Foldable1` zawiera dużo więcej wariantów bazujących na `Semigroup`ie (wszystkie z sufiksem `1`)
i używanie jej ma sens dla struktur, które nigdy nie są puste, nie wymagając definiowania pełnego `Monoid`u dla elementów. 

Co ważne, istnieją również warianty pracujące w oparciu o typy monadyczne. Używaliśmy już `foldLeftM`, kiedy po raz 
pierwszy pisaliśmy logikę biznesową naszej aplikacji. Teraz wiemy, że pochodzi ona z `Foldable`:

{lang="text"}
~~~~~~~~
  def foldLeftM[G[_]: Monad, A, B](fa: F[A], z: B)(f: (B, A) => G[B]): G[B] = ...
  def foldRightM[G[_]: Monad, A, B](fa: F[A], z: =>B)(f: (A, =>B) => G[B]): G[B] = ...
  def foldMapM[G[_]: Monad, A, B: Monoid](fa: F[A])(f: A => G[B]): G[B] = ...
  def findMapM[M[_]: Monad, A, B](fa: F[A])(f: A => M[Option[B]]): M[Option[B]] = ...
  def allM[G[_]: Monad, A](fa: F[A])(p: A => G[Boolean]): G[Boolean] = ...
  def anyM[G[_]: Monad, A](fa: F[A])(p: A => G[Boolean]): G[Boolean] = ...
  ...
~~~~~~~~


### Traverse

`Traverse` to skrzyżowanie `Functor`a z `Foldable`.

{lang="text"}
~~~~~~~~
  trait Traverse[F[_]] extends Functor[F] with Foldable[F] {
    def traverse[G[_]: Applicative, A, B](fa: F[A])(f: A => G[B]): G[F[B]]
    def sequence[G[_]: Applicative, A](fga: F[G[A]]): G[F[A]] = ...
  
    def reverse[A](fa: F[A]): F[A] = ...
  
    def zipL[A, B](fa: F[A], fb: F[B]): F[(A, Option[B])] = ...
    def zipR[A, B](fa: F[A], fb: F[B]): F[(Option[A], B)] = ...
    def indexed[A](fa: F[A]): F[(Int, A)] = ...
    def zipWithL[A, B, C](fa: F[A], fb: F[B])(f: (A, Option[B]) => C): F[C] = ...
    def zipWithR[A, B, C](fa: F[A], fb: F[B])(f: (Option[A], B) => C): F[C] = ...
  
    def mapAccumL[S, A, B](fa: F[A], z: S)(f: (S, A) => (S, B)): (S, F[B]) = ...
    def mapAccumR[S, A, B](fa: F[A], z: S)(f: (S, A) => (S, B)): (S, F[B]) = ...
  }
~~~~~~~~

Na początku rozdziału pokazaliśmy, jak ważne są metody `traverse` i `sequence`, gdy chcemy odwrócić kolejność konstruktorów typu
(np. z `List[Future[_]]` na `Future[List[_]]`).

W `Foldable` nie mogliśmy założyć, że `reverse` jest pojęciem uniwersalnym, ale sprawa wygląda zupełnie inaczej, gdy mamy do 
dyspozycji `Traverse`.

Możemy też `zip`ować ze sobą dwie rzeczy, które mają instancję `Traverse`, dostając `None`, gdy jedna ze stron
nie ma już więcej elementów. Specjalnym wariantem tej operacji jest dodanie indeksów do każdego elementu za pomocą
`indexed`.

`zipWithL` i `zipWithR` pozwalają połączyć elementy w nowy typ i od razu stworzyć `F[C]`.

`mapAccumL` i `mapAccumR` to standardowe `map` połączone z akumulatorem. Jeśli nawyki z Javy każą nam sięgnąć po zmienna typu `var`
i używać jej wewnątrz `map`, to najprawdopodobniej powinniśmy użyć `mapAccumL`.

Powiedzmy, że mamy listę słów i chcielibyśmy ukryć te, które już wcześniej widzieliśmy. Chcemy, aby algorytm działał również
dla nieskończonych strumieni danych, a więc kolekcja może być przetworzona jedynie raz.

{lang="text"}
~~~~~~~~
  scala> val freedom =
  """We campaign for these freedoms because everyone deserves them.
     With these freedoms, the users (both individually and collectively)
     control the program and what it does for them."""
     .split("\\s+")
     .toList
  
  scala> def clean(s: String): String = s.toLowerCase.replaceAll("[,.()]+", "")
  
  scala> freedom
         .mapAccumL(Set.empty[String]) { (seen, word) =>
           val cleaned = clean(word)
           (seen + cleaned, if (seen(cleaned)) "_" else word)
         }
         ._2
         .intercalate(" ")
  
  res: String =
  """We campaign for these freedoms because everyone deserves them.
     With _ _ the users (both individually and collectively)
     control _ program _ what it does _ _"""
~~~~~~~~

Na koniec `Traverse1`, podobnie jak `Foldable1`, dostarcza warianty wspomnianych metod dla struktur danych, które nigdy nie są
puste, przyjmując słabszą `Semigroup`ę zamiast `Monoid`u i `Apply` zamiast `Applicative`. Przypomnijmy, że 
`Semigroup` nie musi dostarczać `.empty`, a `Apply` nie wymaga `.point`.


### Align

`Align` służy do łączenia i wyrównywania wszystkiego, co ma instancję typu `Functor`. Zanim spojrzymy
na `Align`, poznajmy typ danych `\&/` (wymawiany jako *te*, *these* lub *hurray!*),

{lang="text"}
~~~~~~~~
  sealed abstract class \&/[+A, +B]
  final case class This[A](aa: A) extends (A \&/ Nothing)
  final case class That[B](bb: B) extends (Nothing \&/ B)
  final case class Both[A, B](aa: A, bb: B) extends (A \&/ B)
~~~~~~~~

A więc jest to wyrażenie alternatywy łącznej `OR`: `A` lub `B`, lub `A` i `B` jednocześnie.

{lang="text"}
~~~~~~~~
  @typeclass trait Align[F[_]] extends Functor[F] {
    def alignWith[A, B, C](f: A \&/ B => C): (F[A], F[B]) => F[C]
    def align[A, B](a: F[A], b: F[B]): F[A \&/ B] = ...
  
    def merge[A: Semigroup](a1: F[A], a2: F[A]): F[A] = ...
  
    def pad[A, B]: (F[A], F[B]) => F[(Option[A], Option[B])] = ...
    def padWith[A, B, C](f: (Option[A], Option[B]) => C): (F[A], F[B]) => F[C] = ...
~~~~~~~~

`alignWith` przyjmuje funkcję z albo `A`, albo `B` (albo obu) na `C` i zwraca wyniesioną funkcję z tupli `F[A]` i `F[B]`
na `F[C]`. `align` konstruuje `\&/` z dwóch `F[_]`.

`merge` pozwala nam połączyć dwie instancje `F[A]` tak długo, jak jesteśmy w stanie dostarczyć instancję `Semigroup[A]`.
Dla przykładu, `Semigroup[Map[K,V]]]` deleguje logikę do `Semigroup[V]`, łącząc wartości dla tych samych kluczy, a w
konsekwencji sprawiając, że `Map[K, List[A]]` zachowuje się jak multimapa:

{lang="text"}
~~~~~~~~
  scala> Map("foo" -> List(1)) merge Map("foo" -> List(1), "bar" -> List(2))
  res = Map(foo -> List(1, 1), bar -> List(2))
~~~~~~~~

a `Map[K, Int]` po prostu sumuje wartości.

{lang="text"}
~~~~~~~~
  scala> Map("foo" -> 1) merge Map("foo" -> 1, "bar" -> 2)
  res = Map(foo -> 2, bar -> 2)
~~~~~~~~

`.pad` i `.padWith` służą do częściowego łącznie struktur danych, które mogą nie mieć wymaganych wartości po jednej ze stron.
Dla przykładu, jeśli chcielibyśmy zagregować niezależne głosy i zachować informację skąd one pochodziły:

{lang="text"}
~~~~~~~~
  scala> Map("foo" -> 1) pad Map("foo" -> 1, "bar" -> 2)
  res = Map(foo -> (Some(1),Some(1)), bar -> (None,Some(2)))
  
  scala> Map("foo" -> 1, "bar" -> 2) pad Map("foo" -> 1)
  res = Map(foo -> (Some(1),Some(1)), bar -> (Some(2),None))
~~~~~~~~

Istnieją też wygodne warianty `align`, które używają struktury `\&/`

{lang="text"}
~~~~~~~~
  ...
    def alignSwap[A, B](a: F[A], b: F[B]): F[B \&/ A] = ...
    def alignA[A, B](a: F[A], b: F[B]): F[Option[A]] = ...
    def alignB[A, B](a: F[A], b: F[B]): F[Option[B]] = ...
    def alignThis[A, B](a: F[A], b: F[B]): F[Option[A]] = ...
    def alignThat[A, B](a: F[A], b: F[B]): F[Option[B]] = ...
    def alignBoth[A, B](a: F[A], b: F[B]): F[Option[(A, B)]] = ...
  }
~~~~~~~~

i które powinny być jasne po przeczytaniu sygnatur. Przykłady:

{lang="text"}
~~~~~~~~
  scala> List(1,2,3) alignSwap List(4,5)
  res = List(Both(4,1), Both(5,2), That(3))
  
  scala> List(1,2,3) alignA List(4,5)
  res = List(Some(1), Some(2), Some(3))
  
  scala> List(1,2,3) alignB List(4,5)
  res = List(Some(4), Some(5), None)
  
  scala> List(1,2,3) alignThis List(4,5)
  res = List(None, None, Some(3))
  
  scala> List(1,2,3) alignThat List(4,5)
  res = List(None, None, None)
  
  scala> List(1,2,3) alignBoth List(4,5)
  res = List(Some((1,4)), Some((2,5)), None)
~~~~~~~~

Zauważ, że warianty `A` i `B` używają alternatywy łącznej, a `This` i `That` są wykluczające,
zwracając `None`, gdy wartość istnieje po obu stronach lub nie istnieje po wskazanej stronie.


## Wariancja

Musimy wrócić na moment do `Functor`a i omówić jego przodka, którego wcześniej zignorowaliśmy

{width=100%}
![](images/scalaz-variance.png)

`InvariantFunctor`, znany również jako *funktor wykładniczy*, definiuje metodę `xmap`, która pozwala zamienić
`F[A]` w `F[B]` jeśli przekażemy do niej funkcje z `A` na `B` i z `B` na `A`.

`Functor` to skrócona nazwa na to, co powinno nazywać się *funktorem kowariantnym*.
Podobnie `Contravariant` to tak naprawdę *funktor kontrawariantny*.

`Functor` implementuje metodę `xmap` za pomocą `map` i ignoruje funkcję z `B` na `A`. `Contravariant` z kolei
implementuje ją z użyciem `contramap` i ignoruje funkcję z `A` na `B`:

{lang="text"}
~~~~~~~~
  @typeclass trait InvariantFunctor[F[_]] {
    def xmap[A, B](fa: F[A], f: A => B, g: B => A): F[B]
    ...
  }
  
  @typeclass trait Functor[F[_]] extends InvariantFunctor[F] {
    def map[A, B](fa: F[A])(f: A => B): F[B]
    def xmap[A, B](fa: F[A], f: A => B, g: B => A): F[B] = map(fa)(f)
    ...
  }
  
  @typeclass trait Contravariant[F[_]] extends InvariantFunctor[F] {
    def contramap[A, B](fa: F[A])(f: B => A): F[B]
    def xmap[A, B](fa: F[A], f: A => B, g: B => A): F[B] = contramap(fa)(g)
    ...
  }
~~~~~~~~

Co istotne, określenia *kowariantny*, *kontrawariantny* i *inwariantny*, mimo że związane na poziomie
teoretycznym, nie przekładają się bezpośrednio na znaną ze Scali wariancję typów (czyli modyfikatory `+` i `-` 
umieszczane przy parametrach typów). *Inwariancja* oznacza tutaj, że możliwym jest przetłumaczenie zawartości
`F[A]` do `F[B]`. Używając `identity`, możemy zobaczyć, że `A` może być w bezpieczny sposób zrzutowane (w górę lub w dół)
do `B`, zależnie od wariancji funktora.

`.map` może być rozumiana poprzez swój kontrakt: "jeśli dasz mi `F` dla `A` i sposób na zamianę `A` w `B`, wtedy dam ci `F` dla `B`".

Podobnie, `.contramap` mówi, że: "jeśli dasz mi `F` dla `A` i sposób na zamianę `B` w `A`, wtedy dam ci `F` dla `B`".

Rozważymy następujący przykład: w naszej aplikacji wprowadzamy typy domenowe `Alpha`, `Beta` i `Gamma`, aby zabezpieczyć się
przed pomieszaniem liczb w kalkulacjach finansowych:

{lang="text"}
~~~~~~~~
  final case class Alpha(value: Double)
~~~~~~~~

ale sprawia to, że nie mamy żadnych instancji typeklas dla tych nowych typów. Jeśli chcielibyśmy użyć takich
wartości w JSONie, musielibyśmy dostarczyć `JsEncoder` i `JsDecoder`.

Jednakże, `JsEncoder` ma instancję typeklasy `Contravariant` a `JsDecoder` typeklasy `Functor`, a więc możemy
wyderywować potrzebne nam instancje, spełniając kontrakt:

-   "jeśli dasz mi `JsDecoder` dla `Double` i sposób na zamianę `Double` w `Alpha`, wtedy dam ci `JsDecoder` dla `Alpha`".
-   "jeśli dasz mi `JsEncoder` dla `Double` i sposób na zamianę `Alpha` w `Double`, wtedy dam ci `JsEncoder` dla `Alpha`".

{lang="text"}
~~~~~~~~
  object Alpha {
    implicit val decoder: JsDecoder[Alpha] = JsDecoder[Double].map(Alpha(_))
    implicit val encoder: JsEncoder[Alpha] = JsEncoder[Double].contramap(_.value)
  }
~~~~~~~~

Metody w klasie mogą ustawić swoje parametry typu w *pozycji kontrawariantnej* (parametry metody) lub
w *pozycji kowariantnej* (typ zwracany). Jeśli typeklasa łączy pozycje kowariantne i kontrawariantne może oznaczać to, że
ma instancję typeklasy `InvariantFunctor`, ale nie `Functor` ani `Contrawariant`.

## Apply i Bind

Potraktuj tę część jako rozgrzewkę przed typami `Applicative` i `Monad`

{width=100%}
![](images/scalaz-apply.png)


### Apply

`Apply` rozszerza typeklasę `Functor` poprzez dodanie metody `ap`, która jest podobna do `map` w tym, że aplikuje otrzymaną funkcje na wartościach.
Jednak w przypadku `ap` funkcja jest opakowana w ten sam kontekst co wartości, które są do niej przekazywane.

{lang="text"}
~~~~~~~~
  @typeclass trait Apply[F[_]] extends Functor[F] {
    @op("<*>") def ap[A, B](fa: =>F[A])(f: =>F[A => B]): F[B]
    ...
~~~~~~~~

A> `<*>` to Zaawansowany TIE Fighter, taki sam jak ten którym latał Darth Vader. Odpowiedni, bo wygląda jak
A> rozgniewany rodzic. Albo smutny Pikachu.

Warto poświęcić chwilę na zastanowienie się co to znaczy, że prosta struktura danych, taka jak `Option[A]`, posiada
następującą implementację `.ap`

{lang="text"}
~~~~~~~~
  implicit def option[A]: Apply[Option[A]] = new Apply[Option[A]] {
    override def ap[A, B](fa: =>Option[A])(f: =>Option[A => B]) = f match {
      case Some(ff) => fa.map(ff)
      case None    => None
    }
    ...
  }
~~~~~~~~

Aby zaimplementować `.ap`, musimy najpierw wydostać funkcję `ff: A => B` z `f: Option[A => B]`, a następnie
możemy przemapować `fa` z jej użyciem. Ekstrakcja funkcji z kontekstu to ważna funkcjonalność, którą przynosi `Apply`. 
Pozwala tym samym na łączenie wielu funkcji wewnątrz jednego kontekstu.

Wracając do `Apply`, znajdziemy tam rodzinę funkcji `applyX`, która pozwala nam łączyć równoległe obliczenia, a następnie
mapować ich połączone wyniki:

{lang="text"}
~~~~~~~~
  @typeclass trait Apply[F[_]] extends Functor[F] {
    ...
    def apply2[A,B,C](fa: =>F[A], fb: =>F[B])(f: (A, B) => C): F[C] = ...
    def apply3[A,B,C,D](fa: =>F[A],fb: =>F[B],fc: =>F[C])(f: (A,B,C) =>D): F[D] = ...
    ...
    def apply12[...]
~~~~~~~~

Potraktuj `.apply2` jako obietnicę: "jeśli dasz mi `F` z `A` i `F` z `B` oraz sposób na połączenie `A` i `B` w `C`, wtedy
mogę dać ci `F` z `C`". Istnieje wiele zastosowań dla tej obietnicy, a 2 najważniejsze to:

-   tworzenie typeklas dla produktu `C` z jego składników `A` i `B`
-   wykonywanie *efektów* równolegle, jak w przypadku algebr dla drone i google, które stworzyliśmy w Rozdziale 3,
    a następnie łączenie ich wyników.

W rzeczy samej, `Apply` jest na tyle użyteczne, że ma swoją własną składnię:

{lang="text"}
~~~~~~~~
  implicit class ApplyOps[F[_]: Apply, A](self: F[A]) {
    def *>[B](fb: F[B]): F[B] = Apply[F].apply2(self,fb)((_,b) => b)
    def <*[B](fb: F[B]): F[A] = Apply[F].apply2(self,fb)((a,_) => a)
    def |@|[B](fb: F[B]): ApplicativeBuilder[F, A, B] = ...
  }
  
  class ApplicativeBuilder[F[_]: Apply, A, B](a: F[A], b: F[B]) {
    def tupled: F[(A, B)] = Apply[F].apply2(a, b)(Tuple2(_))
    def |@|[C](cc: F[C]): ApplicativeBuilder3[C] = ...
  
    sealed abstract class ApplicativeBuilder3[C](c: F[C]) {
      ..ApplicativeBuilder4
        ...
          ..ApplicativeBuilder12
  }
~~~~~~~~

której użyliśmy w Rozdziale 3:

{lang="text"}
~~~~~~~~
  (d.getBacklog |@| d.getAgents |@| m.getManaged |@| m.getAlive |@| m.getTime)
~~~~~~~~

A> Operator `|@\` ma wiele imion. Niektórzy nazywają go *Składnią Produktu Kartezjańskiego* (_Cartesian Product Syntax_),
A> inni wolą *Cinnamon Bun*, *Admirał Ackbar* lub *Macaulay Culkin*. My wolimy nazywać go *Krzyk* (_The Scream_)
A> przez podobieństwo do obrazu Muncha oraz przez to, że jest to dźwięk jaki wydaje procesor, gdy równolegle oblicza
A> Wszystko.

Operatory `<*` i `*>` (prawy i lewy ptak) oferują wygodny sposób na zignorowanie wyniku jednego z dwóch równoległych 
efektów.

Niestety, mimo wygody, którą daje operator `|@\`, jest z nim jeden problem: dla każdego kolejnego efektu alokowany jest
nowy obiekt typu `ApplicativeBuilder`. Gdy prędkość obliczeń ograniczona jest przez operacje I/O nie ma to znaczenia.
Jednak gdy wykonujesz obliczenia w całości na CPU, lepiej jest użyć *krotnego wynoszenia* (_lifting with arity_), które nie
produkuje żadnych obiektów pośrednich:

{lang="text"}
~~~~~~~~
  def ^[F[_]: Apply,A,B,C](fa: =>F[A],fb: =>F[B])(f: (A,B) =>C): F[C] = ...
  def ^^[F[_]: Apply,A,B,C,D](fa: =>F[A],fb: =>F[B],fc: =>F[C])(f: (A,B,C) =>D): F[D] = ...
  ...
  def ^^^^^^[F[_]: Apply, ...]
~~~~~~~~

na przykład:

{lang="text"}
~~~~~~~~
  ^^^^(d.getBacklog, d.getAgents, m.getManaged, m.getAlive, m.getTime)
~~~~~~~~

Możemy też zawołać `applyX` bezpośrednio:

{lang="text"}
~~~~~~~~
  Apply[F].apply5(d.getBacklog, d.getAgents, m.getManaged, m.getAlive, m.getTime)
~~~~~~~~

Mimo tego, że `Apply` używany jest najczęściej z efektami, działa równie dobrze ze strukturami danych. Rozważ przepisanie

{lang="text"}
~~~~~~~~
  for {
    foo <- data.foo: Option[String]
    bar <- data.bar: Option[Int]
  } yield foo + bar.shows
~~~~~~~~

jako

{lang="text"}
~~~~~~~~
  (data.foo |@| data.bar)(_ + _.shows)
~~~~~~~~

Gdy chcemy jedynie połączyć wyniki w tuple, istnieją metody, które służą dokładnie do tego:

{lang="text"}
~~~~~~~~
  @op("tuple") def tuple2[A,B](fa: =>F[A],fb: =>F[B]): F[(A,B)] = ...
  def tuple3[A,B,C](fa: =>F[A],fb: =>F[B],fc: =>F[C]): F[(A,B,C)] = ...
  ...
  def tuple12[...]
~~~~~~~~

{lang="text"}
~~~~~~~~
  (data.foo tuple data.bar) : Option[(String, Int)]
~~~~~~~~

Dostępne są też uogólnione wersje `ap` dla więcej niż dwóch parametrów:

{lang="text"}
~~~~~~~~
  def ap2[A,B,C](fa: =>F[A],fb: =>F[B])(f: F[(A,B) => C]): F[C] = ...
  def ap3[A,B,C,D](fa: =>F[A],fb: =>F[B],fc: =>F[C])(f: F[(A,B,C) => D]): F[D] = ...
  ...
  def ap12[...]
~~~~~~~~

razem z wariantami `.lift`, które przyjmują zwykłe funkcje i wynoszą je do kontekstu `F[_]`, uogólniając `Functor.lift`

{lang="text"}
~~~~~~~~
  def lift2[A,B,C](f: (A,B) => C): (F[A],F[B]) => F[C] = ...
  def lift3[A,B,C,D](f: (A,B,C) => D): (F[A],F[B],F[C]) => F[D] = ...
  ...
  def lift12[...]
~~~~~~~~

oraz `.apF`, częściowo zaaplikowana wersja `ap`

{lang="text"}
~~~~~~~~
  def apF[A,B](f: =>F[A => B]): F[A] => F[B] = ...
~~~~~~~~

A na koniec `.forever`

{lang="text"}
~~~~~~~~
  def forever[A, B](fa: F[A]): F[B] = ...
~~~~~~~~

który powtarza efekt w nieskończoność bez zatrzymywania się. Przy jej użyciu instancja `Apply` musi być zabezpieczona prze
przepełnieniem stosu (_stack-safe_), w przeciwnym wypadku wywołanie spowoduje `StackOverflowError`. 


### Bind

`Bind` wprowadza metodę `.bind`, która jest synonimiczna do `.flatMap` i pozwala na mapowanie efektów/struktur danych
z użyciem funkcji zwracających nowy efekt/strukturę danych bez wprowadzania dodatkowych zagnieżdżeń.

{lang="text"}
~~~~~~~~
  @typeclass trait Bind[F[_]] extends Apply[F] {
  
    @op(">>=") def bind[A, B](fa: F[A])(f: A => F[B]): F[B]
    def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = bind(fa)(f)
  
    override def ap[A, B](fa: =>F[A])(f: =>F[A => B]): F[B] =
      bind(f)(x => map(fa)(x))
    override def apply2[A, B, C](fa: =>F[A], fb: =>F[B])(f: (A, B) => C): F[C] =
      bind(fa)(a => map(fb)(b => f(a, b)))
  
    def join[A](ffa: F[F[A]]): F[A] = bind(ffa)(identity)
  
    def mproduct[A, B](fa: F[A])(f: A => F[B]): F[(A, B)] = ...
    def ifM[B](value: F[Boolean], t: =>F[B], f: =>F[B]): F[B] = ...
  
  }
~~~~~~~~

Metoda `.join` może wydawać się znajoma tym, którzy używali `.flatten` z biblioteki standardowej. Przyjmuje ona
zagnieżdżone konteksty i łączy je w jeden.

Wprowadzone zostały kombinatory pochodne dla `.ap` i `.apply2`, aby zapewnić spójność z `.bind`. Zobaczymy później, że 
to wymaganie niesie ze sobą konsekwencje dla potencjalnego zrównoleglania obliczeń.

`mproduct` przypomina `Functor.fproduct` i paruje wejście i wyjście funkcji wewnątrz `F`.

`ifM` to sposób na tworzenie warunkowych struktur danych lub efektów:

{lang="text"}
~~~~~~~~
  scala> List(true, false, true).ifM(List(0), List(1, 1))
  res: List[Int] = List(0, 1, 1, 0)
~~~~~~~~

`ifM` i `ap` są zoptymalizowane do cachowania i reużywania gałezi kodu. Porównajmy je z dłuższą wersją

{lang="text"}
~~~~~~~~
  scala> List(true, false, true).flatMap { b => if (b) List(0) else List(1, 1) }
~~~~~~~~

która produkuje nowe `List(0)` i `List(1, 1)` za każdym razem, gdy dana gałąź jest wywoływana.

A> Tego rodzaju optymizacje są możliwe w FP, ponieważ wszystkie metody są deterministyczne, lub inaczej mówiąc
A> *referencyjnie transparentne*.
A>
A> Jeśli metoda zwraca inne wartości dla tych samych argumentów, jest ona *nieczysta* i zaburza rozumowanie oraz
A> optymalizacje, które moglibyśmy zastosować.
A>
A> Jeśli `F` jest efektem, być może jedną z naszych algebr, nie oznacza to, że wynik wywołania algebry jest cachowany.
A> Raczej powinniśmy powiedzieć, że cachowana jest referencja do operacji. Wydajnościowa optymalizacja `ifM` istotna jest
A> tylko dla struktur danych i staje się tym wyraźniejsza im bardziej skomplikowana praca dzieje się w danej gałęzi.
A> 
A> Dogłędbniej zbadamy koncepcje determinizmu i cachowania wartości w następnym rozdziale.

`Bind` wprowadza też specjalne operatory:

{lang="text"}
~~~~~~~~
  implicit class BindOps[F[_]: Bind, A] (self: F[A]) {
    def >>[B](b: =>F[B]): F[B] = Bind[F].bind(self)(_ => b)
    def >>![B](f: A => F[B]): F[A] = Bind[F].bind(self)(a => f(a).map(_ => a))
  }
~~~~~~~~

Używając `>>` odrzucamy wejście do `bind`, a używając `>>!` odrzucamy wyjście` 


## Aplikatywy i monady

Z punkty widzenia oferowanych funkcjonalności, `Applicative` to `Apply` z dodaną metodą `pure`, a `Monad`
rozszerza `Applicative`, dodając `Bind`.

{width=100%}
![](images/scalaz-applicative.png)

{lang="text"}
~~~~~~~~
  @typeclass trait Applicative[F[_]] extends Apply[F] {
    def point[A](a: =>A): F[A]
    def pure[A](a: =>A): F[A] = point(a)
  }
  
  @typeclass trait Monad[F[_]] extends Applicative[F] with Bind[F]
~~~~~~~~

Pod wieloma względami `Applicative` i `Monad` są zwieńczeniem wszystkiego, co do tej pory widzieliśmy w tym rozdziale.
`.pure` (lub `.point` - alias powszechnie używany przy strukturach danych) pozwala nam na tworzenie efektów lub 
struktur danych z pojedynczych wartości.

Instancje `Applicative` muszę spełniać prawa gwarantujące spójność metod:

-   **Tożsamość (Identity)**: `fa <*> pure(identity) == fa` (gdzie `fa` to `F[A]`) - zaaplikowanie `pure(identity)` nic nie zmienia
-   **Homomorfizm (Homomorphism)**: `pure(a) <*> pure(ab) === pure(ab(a))`, (gdzie `ab` to funkcja `A => B`) - zaaplikowanie funkcji
    osadzonej w kontekście `F` za pomocą `pure` na wartości potraktowanej w ten sam sposób jest równoznaczne z wywołaniem
    tej funkcji na wspomnianej wartości i wywołaniem `pure` na rezultacie.
-   **Zamiana (Interchange)**: `pure(a) <*> fab === fab <*> pure(f => f(a))`, (gdzie `fab` to `F[A => B]`) - `pure` jest tożsama lewo- i prawostronnie
-   **Mappy**: `map(fa)(f) === fa <*> pure(f)`

`Monad` dodaje następujące prawa

-   **Tożsamość lewostronna (Left Identity)**: `pure(a).bind(f) === f(a)`
-   **Tożsamość prawostronna (Right Identity)**: `a.bind(pure(_)) === a`
-   **Łączność (Associativity)**: `fa.bind(f).bind(g) === fa.bind(a => f(a).bind(g))` gdzie
    `fa` to `F[A]`, `f` to `A => F[B]`, a `g` to `B => F[C]`.
    
Łączność mówi nam, że połączone wywołania `bind` muszą być zgodne z wywołaniami zagnieżdżonymi. Jednakże, 
nie oznacza to, że możemy zamieniać kolejność wywołań - to gwarantowałaby *przemienność* (_commutativity_).
Dla przykładu, pamiętając, że `flatMap` to alias na `bind`, nie możemy zamienić

{lang="text"}
~~~~~~~~
  for {
    _ <- machine.start(node1)
    _ <- machine.stop(node1)
  } yield true
~~~~~~~~

na

{lang="text"}
~~~~~~~~
  for {
    _ <- machine.stop(node1)
    _ <- machine.start(node1)
  } yield true
~~~~~~~~

`start` i `stop` są _**nie**przemienne_, ponieważ uruchomienie, a następnie zatrzymanie węzła jest czymś innym
niż zatrzymanie i uruchomienie.

Nie mniej, zarówno `start`, jak i `stop` są przemienne same ze sobą samym, a więc możemy zamienić

{lang="text"}
~~~~~~~~
  for {
    _ <- machine.start(node1)
    _ <- machine.start(node2)
  } yield true
~~~~~~~~

na

{lang="text"}
~~~~~~~~
  for {
    _ <- machine.start(node2)
    _ <- machine.start(node1)
  } yield true
~~~~~~~~

Obie formy są równoznaczne w tym konkretnym przypadku, ale nie w ogólności. Robimy tutaj dużo założeń
co do Google Container API, ale wydaje się to być rozsądnych wyjściem.

Okazuje się, że w konsekwencji powyższych praw `Monad`a musi być przemienna, jeśli chcemy pozwolić na równoległe
działanie metod `applyX`. W Rozdziale 3 oszukaliśmy uruchamiając efekty w ten sposób

{lang="text"}
~~~~~~~~
  (d.getBacklog |@| d.getAgents |@| m.getManaged |@| m.getAlive |@| m.getTime)
~~~~~~~~

ponieważ wiedzieliśmy, że są one ze sobą przemienne. Kiedy w dalszych rozdziałach zajmiemy się interpretacją 
naszej aplikacji, dostarczymy dowód na przemienność operacji lub pozwolimy na uruchomienie ich sekwencyjnie.

Subtelności sposobów radzenia sobie z porządkowaniem efektów, i tym, czym te efekty tak naprawdę są, zasługują
na osobny rozdział. Porozmawiamy o nich przy Zaawansowanych monadach.


## Dziel i rządź

{width=100%}
![](images/scalaz-divide.png)

`Divide` to kontrawariantny odpowiednik `Apply`

{lang="text"}
~~~~~~~~
  @typeclass trait Divide[F[_]] extends Contravariant[F] {
    def divide[A, B, C](fa: F[A], fb: F[B])(f: C => (A, B)): F[C] = divide2(fa, fb)(f)
  
    def divide1[A1, Z](a1: F[A1])(f: Z => A1): F[Z] = ...
    def divide2[A, B, C](fa: F[A], fb: F[B])(f: C => (A, B)): F[C] = ...
    ...
    def divide22[...] = ...
~~~~~~~~

`divide` mówi nam, że jeśli potrafimy podzielić `C` na `A` i `B` oraz mamy do dyspozycji `F[A]` i `F[B]`
to możemy stworzyć `F[C]`. Stąd też *dziel i rządź*.

Jest to świetny sposób na generowanie instancji kowariantnych typeklas dla typów będących produktami poprzez 
podzielenie tychże produktów na części. Scalaz oferuje instancje `Divide[Equal]`, spróbujmy więc stworzyć `Equal`
dla nowego typu `Foo`.

{lang="text"}
~~~~~~~~
  scala> case class Foo(s: String, i: Int)
  scala> implicit val fooEqual: Equal[Foo] =
           Divide[Equal].divide2(Equal[String], Equal[Int]) {
             (foo: Foo) => (foo.s, foo.i)
           }
  scala> Foo("foo", 1) === Foo("bar", 1)
  res: Boolean = false
~~~~~~~~

Podążając za `Apply`, `Divide` również dostarcza zwięzłą składnię dla tupli

{lang="text"}
~~~~~~~~
  ...
    def tuple2[A1, A2](a1: F[A1], a2: F[A2]): F[(A1, A2)] = ...
    ...
    def tuple22[...] = ...
  }
~~~~~~~~

Ogólnie rzecz biorąc, jeśli typeklasa, oprócz instancji `Contravariant`, jest w stanie dostarczyć również `Divide`,
to znaczy, że jesteśmy w stanie wyderywować jej instancje dla dowolnej case klasy. Sprawa wygląda analogicznie dla
typeklas kowariantnych z instancją `Apply`. Zgłębimy ten temat w rozdziale poświęconym Derywacji typeklas.

`Divisible` to odpowiednik `Applicative` dla rodziny `Contravariant`. Wprowadzana ona metodę `.conquer`, odpowiednik `.pure`:

{lang="text"}
~~~~~~~~
  @typeclass trait Divisible[F[_]] extends Divide[F] {
    def conquer[A]: F[A]
  }
~~~~~~~~

`.conquer` pozwala na tworzenie trywialnych implementacji, w których parametr typu jest ignorowany. Takie instancje 
nazywane są *ogólnie kwantyfikowanymi* (_universally quantified_). Na przykład, `Divisible[Equal].conquer[INil[String]]` tworzy
instancję `Equal`, która zawsze zwraca `true`.


## Plus

{width=100%}
![](images/scalaz-plus.png)

`Plus` to `Semigroup`a dla konstruktorów typu a `PlusEmpty` to odpowiednik `Monoid`u (obowiązują ich nawet te same prawa).
Nowością jest typeklasa `IsEmpty`, która pozwala na sprawdzenie czy `F[A]` jest puste:

{lang="text"}
~~~~~~~~
  @typeclass trait Plus[F[_]] {
    @op("<+>") def plus[A](a: F[A], b: =>F[A]): F[A]
  }
  @typeclass trait PlusEmpty[F[_]] extends Plus[F] {
    def empty[A]: F[A]
  }
  @typeclass trait IsEmpty[F[_]] extends PlusEmpty[F] {
    def isEmpty[A](fa: F[A]): Boolean
  }
~~~~~~~~

A> `<+>` to TIE Interceptor, co sprawia, że prawie wyczerpaliśmy gamę myśliwców TIE

Pozornie może się wydawać, że `<+>` zachowuje się tak samo, jak `|+|`:

{lang="text"}
~~~~~~~~
  scala> List(2,3) |+| List(7)
  res = List(2, 3, 7)
  
  scala> List(2,3) <+> List(7)
  res = List(2, 3, 7)
~~~~~~~~

Najlepiej jest przyjąć, że `<+>` operuje jedynie na `F[_]` nigdy nie patrząc na zawartość.
Przyjęła się konwencja, że `Plus` ignoruje porażki i wybiera "pierwszego zwycięzcę". Dzięki temu
`<+>` może być używany jako mechanizm szybkiego wyjścia oraz obsługi porażek przez fallbacki.

{lang="text"}
~~~~~~~~
  scala> Option(1) |+| Option(2)
  res = Some(3)
  
  scala> Option(1) <+> Option(2)
  res = Some(1)
  
  scala> Option.empty[Int] <+> Option(1)
  res = Some(1)
~~~~~~~~

Na przykład, jeśli chcielibyśmy pominąć obiekty `None` wewnątrz `NonEmptyList[Option[Int]]` i wybrać pierwszego
zwycięzcę (`Some`), możemy użyć `<+>` w połączeniu z `Foldable1.foldRight1`:

{lang="text"}
~~~~~~~~
  scala> NonEmptyList(None, None, Some(1), Some(2), None)
         .foldRight1(_ <+> _)
  res: Option[Int] = Some(1)
~~~~~~~~

Teraz, gdy znamy już `Plus`, okazuje się, że wcale nie musieliśmy zaburzać koherencji typeklas w sekcji o Rzeczach złączalnych
(definiując lokalną instancję `Monoid[Option[A]]`). Naszym celem było "wybranie ostatniego zwycięzcy",
co jest tożsame z wybranie pierwszego po odwróceniu kolejności elementów. Zwróć uwagę na użycie Interceptora TIE z
`ccy` i `otc` w odwróconej kolejności.

{lang="text"}
~~~~~~~~
  implicit val monoid: Monoid[TradeTemplate] = Monoid.instance(
    (a, b) => TradeTemplate(a.payments |+| b.payments,
                            b.ccy <+> a.ccy,
                            b.otc <+> a.otc),
    TradeTemplate(Nil, None, None)
  )
~~~~~~~~

`Applicative` i `Monad` mają wyspecjalizowaną wersję `PlusEmpty`

{lang="text"}
~~~~~~~~
  @typeclass trait ApplicativePlus[F[_]] extends Applicative[F] with PlusEmpty[F]
  
  @typeclass trait MonadPlus[F[_]] extends Monad[F] with ApplicativePlus[F] {
    def unite[T[_]: Foldable, A](ts: F[T[A]]): F[A] = ...
  
    def withFilter[A](fa: F[A])(f: A => Boolean): F[A] = ...
  }
~~~~~~~~

`.unite` pozwala nam zwinąć strukturę danych, używając `PlusEmpty[F].monoid` zamiast `Monoidu` zdefiniowanego dla
typu wewnętrznego. Dla `List[Either[String, Int]]` oznacza to, że instancje `Left[String]` zamieniane są na `.empty`,
a następnie wszytko jest złączane. Jest to wygodny sposób na pozbycie się błędów:

{lang="text"}
~~~~~~~~
  scala> List(Right(1), Left("boo"), Right(2)).unite
  res: List[Int] = List(1, 2)
  
  scala> val boo: Either[String, Int] = Left("boo")
         boo.foldMap(a => a.pure[List])
  res: List[String] = List()
  
  scala> val n: Either[String, Int] = Right(1)
         n.foldMap(a => a.pure[List])
  res: List[Int] = List(1)
~~~~~~~~

`withFilter` pozwala nam na użycie konstrukcji `for`, którą opisywaliśmy w Rozdziale 2. Można nawet powiedzieć, że
Scala ma wbudowane wsparcie nie tylko dla `Monad`, ale i `MonadPlus`!

Wracając na moment do `Foldable`, możemy odkryć kilka metod, których wcześniej nie omawialiśmy:

{lang="text"}
~~~~~~~~
  @typeclass trait Foldable[F[_]] {
    ...
    def msuml[G[_]: PlusEmpty, A](fa: F[G[A]]): G[A] = ...
    def collapse[X[_]: ApplicativePlus, A](x: F[A]): X[A] = ...
    ...
  }
~~~~~~~~

`msuml` wykonuje `fold`, używając `Monoidu` z `PlusEmpty[G]`, a `collapse` używa `foldRight` w kombinacji
z instancją `PlusEmpty` typu docelowego:

{lang="text"}
~~~~~~~~
  scala> IList(Option(1), Option.empty[Int], Option(2)).fold
  res: Option[Int] = Some(3) // uses Monoid[Option[Int]]
  
  scala> IList(Option(1), Option.empty[Int], Option(2)).msuml
  res: Option[Int] = Some(1) // uses PlusEmpty[Option].monoid
  
  scala> IList(1, 2).collapse[Option]
  res: Option[Int] = Some(1)
~~~~~~~~


## Samotne wilki

Niektóre z typeklas w Scalaz są w pełni samodzielne i nie należą do ogólnej hierarchii.

{width=80%}
![](images/scalaz-loners.png)


### Zippy

{lang="text"}
~~~~~~~~
  @typeclass trait Zip[F[_]]  {
    def zip[A, B](a: =>F[A], b: =>F[B]): F[(A, B)]
  
    def zipWith[A, B, C](fa: =>F[A], fb: =>F[B])(f: (A, B) => C)
                        (implicit F: Functor[F]): F[C] = ...
  
    def ap(implicit F: Functor[F]): Apply[F] = ...
  
    @op("<*|*>") def apzip[A, B](f: =>F[A] => F[B], a: =>F[A]): F[(A, B)] = ...
  
  }
~~~~~~~~

Metoda kluczowa tutaj to `zip`. Jest to słabsza wersja `Divide.tuple2`. Jeśli dostępny jest `Functor[F]` to 
`.zipWith` może zachowywać się jak `Apply.apply2`. Używając `ap`, możemy nawet stworzyć pełnoprawne `Apply[F]` z
instancji `Zip[F]` i `Functor[F]`.

`.apzip` przyjmuje `F[A]` i wyniesioną funkcję `F[A] => F[B]` produkując `F[(A, B)]`, podobnie do `Functor.fproduct`.

A> `<*|*>` to operator przerażających Jawów z sagi Star Wars.

{lang="text"}
~~~~~~~~
  @typeclass trait Unzip[F[_]]  {
    @op("unfzip") def unzip[A, B](a: F[(A, B)]): (F[A], F[B])
  
    def firsts[A, B](a: F[(A, B)]): F[A] = ...
    def seconds[A, B](a: F[(A, B)]): F[B] = ...
  
    def unzip3[A, B, C](x: F[(A, (B, C))]): (F[A], F[B], F[C]) = ...
    ...
    def unzip7[A ... H](x: F[(A, (B, ... H))]): ...
  }
~~~~~~~~

Bazą jest `unzip` dzielący `F[(A,B)]` na `F[A]` i `F[B]`, a `firsts` i `seconds` pozwalają na wybranie
jednej z części. Co ważne, `unzip` jest odwrotnością `zip`.

Metody od `unzip3` do `unzip7` to aplikacje `unzip`  pozwalające zmniejszyć ilość boilerplatu. Na przykład, 
jeśli dostaniemy garść zagnieżdżonych tupli to `Unzip[Id]` jest wygodnym sposobem na ich wypłaszczenie:

{lang="text"}
~~~~~~~~
  scala> Unzip[Id].unzip7((1, (2, (3, (4, (5, (6, 7)))))))
  res = (1,2,3,4,5,6,7)
~~~~~~~~

W skrócie, `Zip` i `Unzip` są słabszymi wersjami `Divide` i `Apply` dostarczającymi użyteczne funkcjonalności
bez zobowiązywania `F` do składania zbyt wielu obietnic.


### Optional

`Optional` to uogólnienie struktur danych, które mogą opcjonalnie zawierać jakąś wartość, np. `Option` lub `Either`.

Przypomnijmy, że `\/` (*dysjunkcja*) ze Scalaz jest ulepszoną wersją `scala.Either`. Poznamy też `Maybe` - ulepszoną wersję
`scala.Option`.

{lang="text"}
~~~~~~~~
  sealed abstract class Maybe[A]
  final case class Empty[A]()    extends Maybe[A]
  final case class Just[A](a: A) extends Maybe[A]
~~~~~~~~

{lang="text"}
~~~~~~~~
  @typeclass trait Optional[F[_]] {
    def pextract[B, A](fa: F[A]): F[B] \/ A
  
    def getOrElse[A](fa: F[A])(default: =>A): A = ...
    def orElse[A](fa: F[A])(alt: =>F[A]): F[A] = ...
  
    def isDefined[A](fa: F[A]): Boolean = ...
    def nonEmpty[A](fa: F[A]): Boolean = ...
    def isEmpty[A](fa: F[A]): Boolean = ...
  
    def toOption[A](fa: F[A]): Option[A] = ...
    def toMaybe[A](fa: F[A]): Maybe[A] = ...
  }
~~~~~~~~

Powyższe metody powinny wydawać się znajome, może z wyjątkiem `pextract`, która pozwala `F[_]` na zwrócenie 
przechowywanej wartości lub specyficznego dla implementacji `F[B]`. Na przykład `Optional[Option].pextract` zwróci
nam `Option[Nothing] \/ A`, czyli `None \/ A`.

Scalaz daje nam operator trenarny dla wszystkich typów mających swoją instancję `Optional`.

{lang="text"}
~~~~~~~~
  implicit class OptionalOps[F[_]: Optional, A](fa: F[A]) {
    def ?[X](some: =>X): Conditional[X] = new Conditional[X](some)
    final class Conditional[X](some: =>X) {
      def |(none: =>X): X = if (Optional[F].isDefined(fa)) some else none
    }
  }
~~~~~~~~

Przykład:

{lang="text"}
~~~~~~~~
  scala> val knock_knock: Option[String] = ...
         knock_knock ? "who's there?" | "<tumbleweed>"
~~~~~~~~


## Ko-rzeczy

*Ko-rzecz* zazwyczaj ma sygnaturę przeciwną do tego, co robi *rzecz*, ale nie musi koniecznie być jej odwrotnością.
Aby podkreślić relacje między *rzeczą* i *ko-rzeczą*, wszędzie gdzie to możliwe zawrzemy obie sygnatury.

{width=100%}
![](images/scalaz-cothings.png)

{width=80%}
![](images/scalaz-coloners.png)


### Cobind

{lang="text"}
~~~~~~~~
  @typeclass trait Cobind[F[_]] extends Functor[F] {
    def cobind[A, B](fa: F[A])(f: F[A] => B): F[B]
  //def   bind[A, B](fa: F[A])(f: A => F[B]): F[B]
  
    def cojoin[A](fa: F[A]): F[F[A]] = ...
  //def   join[A](ffa: F[F[A]]): F[A] = ...
  }
~~~~~~~~

`cobind` (znany również jako `coflatmap`) przyjmuje funkcję `F[A] => B`, która operuje na `F[A]`, a nie jego elementach.
Ale nie zawsze będzie to pełne `fa`, często jest to substruktura stworzona przez metodę `cojoin` (znaną również jako 
`coflatten`), która rozwija strukturę danych.

Przekonywające przykłady użycia `Cobind` są rzadkie, jednak kiedy spojrzymy na tabele permutacji metod typeklasy `Functor`,
ciężko jest uzasadnić, czemu niektóre metody miałyby być ważniejsze od innych.

| method      | parameter          |
|------------ |------------------- |
| `map`       | `A => B`           |
| `contramap` | `B => A`           |
| `xmap`      | `(A => B, B => A)` |
| `ap`        | `F[A => B]`        |
| `bind`      | `A => F[B]`        |
| `cobind`    | `F[A] => B`        |


### Comonad

{lang="text"}
~~~~~~~~
  @typeclass trait Comonad[F[_]] extends Cobind[F] {
    def copoint[A](p: F[A]): A
  //def   point[A](a: =>A): F[A]
  }
~~~~~~~~

`.copoint` (znany też jako `.copure`) wydostaje element z kontekstu. Efekty z reguły nie posiadają instancji 
tej typeklasy, gdyż na przykład interpretacja `IO[A]` do `A` zaburza transparentność referencyjną. 
Dla struktur danych jednakże może to być na przykład wygodny sposób na pokazanie wszystkich elementów wraz z ich sąsiadami.

Rozważmy strukturę *sąsiedztwa* (`Hood`), która zawiera pewien element (`focus`) oraz elementy na 
lewo i prawo od niego (`lefts` i `rights`).

{lang="text"}
~~~~~~~~
  final case class Hood[A](lefts: IList[A], focus: A, rights: IList[A])
~~~~~~~~

`lefts` i `right` powinny być uporządkowane od najbliższego do najdalszego elementu względem elementu środkowego `focus`,
tak abyśmy mogli przekonwertować taką strukturę do `IList` za pomocą poniższej implementacji

{lang="text"}
~~~~~~~~
  object Hood {
    implicit class Ops[A](hood: Hood[A]) {
      def toIList: IList[A] = hood.lefts.reverse ::: hood.focus :: hood.rights
~~~~~~~~

Możemy zaimplementować metody do poruszania się w lewo (`previous`) i w prawo (`next`)

{lang="text"}
~~~~~~~~
  ...
      def previous: Maybe[Hood[A]] = hood.lefts match {
        case INil() => Empty()
        case ICons(head, tail) =>
          Just(Hood(tail, head, hood.focus :: hood.rights))
      }
      def next: Maybe[Hood[A]] = hood.rights match {
        case INil() => Empty()
        case ICons(head, tail) =>
          Just(Hood(hood.focus :: hood.lefts, head, tail))
      }
~~~~~~~~

Wprowadzając metodę `more`, jesteśmy w stanie obliczyć *wszystkie* możliwe do osiągnięcia pozycje (`positions`) w danym `Hood`. 

{lang="text"}
~~~~~~~~
  ...
      def more(f: Hood[A] => Maybe[Hood[A]]): IList[Hood[A]] =
        f(hood) match {
          case Empty() => INil()
          case Just(r) => ICons(r, r.more(f))
        }
      def positions: Hood[Hood[A]] = {
        val left  = hood.more(_.previous)
        val right = hood.more(_.next)
        Hood(left, hood, right)
      }
    }
~~~~~~~~

Możemy teraz stworzyć `Comonad[Hood]`

{lang="text"}
~~~~~~~~
  ...
    implicit val comonad: Comonad[Hood] = new Comonad[Hood] {
      def map[A, B](fa: Hood[A])(f: A => B): Hood[B] =
        Hood(fa.lefts.map(f), f(fa.focus), fa.rights.map(f))
      def cobind[A, B](fa: Hood[A])(f: Hood[A] => B): Hood[B] =
        fa.positions.map(f)
      def copoint[A](fa: Hood[A]): A = fa.focus
    }
  }
~~~~~~~~

`cojoin` daje nam `Hood[Hood[IList]]` zawierające wszystkie możliwe sąsiedztwa w naszej początkowej liście

{lang="text"}
~~~~~~~~
  scala> val middle = Hood(IList(4, 3, 2, 1), 5, IList(6, 7, 8, 9))
  scala> middle.cojoin
  res = Hood(
          [Hood([3,2,1],4,[5,6,7,8,9]),
           Hood([2,1],3,[4,5,6,7,8,9]),
           Hood([1],2,[3,4,5,6,7,8,9]),
           Hood([],1,[2,3,4,5,6,7,8,9])],
          Hood([4,3,2,1],5,[6,7,8,9]),
          [Hood([5,4,3,2,1],6,[7,8,9]),
           Hood([6,5,4,3,2,1],7,[8,9]),
           Hood([7,6,5,4,3,2,1],8,[9]),
           Hood([8,7,6,5,4,3,2,1],9,[])])
~~~~~~~~

Okazuje się, że `cojoin` to tak naprawdę `positions`! A więc możemy nadpisać ją, używając bezpośredniej 
(a przez to wydajniejszej) implementacji

{lang="text"}
~~~~~~~~
  override def cojoin[A](fa: Hood[A]): Hood[Hood[A]] = fa.positions
~~~~~~~~

`Comonad` generalizuje koncepcję sąsiedztwa dla arbitralnych struktur danych. `Hood` jest przykładem *zippera* 
(brak związku z `Zip`). Scalaz definiuje typ danych `Zipper` dla strumieni (jednowymiarowych nieskończonych struktur danych),
które omówimy w następnym rozdziale.

Jednym z zastosowanie zippera jest *automat komórkowy* (_cellular automata_), który wylicza wartość każdej komórki
w następnej generacji na podstawie aktualnych wartości sąsiadów tej komórki.

### Cozip

{lang="text"}
~~~~~~~~
  @typeclass trait Cozip[F[_]] {
    def cozip[A, B](x: F[A \/ B]): F[A] \/ F[B]
  //def   zip[A, B](a: =>F[A], b: =>F[B]): F[(A, B)]
  //def unzip[A, B](a: F[(A, B)]): (F[A], F[B])
  
    def cozip3[A, B, C](x: F[A \/ (B \/ C)]): F[A] \/ (F[B] \/ F[C]) = ...
    ...
    def cozip7[A ... H](x: F[(A \/ (... H))]): F[A] \/ (... F[H]) = ...
  }
~~~~~~~~

Mimo że nazwa tej typeklasy brzmi `Cozip`, lepiej jest spojrzeć na jej symetrię względem metody `unzip`.
Tam, gdzie `unzip` zamienia `F[_]` zawierające produkt (tuple) na produkt zawierający `F[_]`, tam
`cozip` zamienia `F[_]` zawierające koprodukty (dysjunkcje) na koprodukt zawierający `F[_]`.


## Bi-rzeczy

Czasem mamy do czynienia z typami, które przyjmują dwa parametry typu i chcielibyśmy prze`map`ować obie jego
strony. Możemy na przykład śledzić błędy po lewej stronie `Either` i chcieć przetransformować
wiadomości z tychże błędów.

Typeklasy `Functor` / `Foldable` / `Traverse` mają swoich krewnych, którzy pozwalają nam mapować obie strony wspieranych typów.

{width=30%}
![](images/scalaz-bithings.png)

{lang="text"}
~~~~~~~~
  @typeclass trait Bifunctor[F[_, _]] {
    def bimap[A, B, C, D](fab: F[A, B])(f: A => C, g: B => D): F[C, D]
  
    @op("<-:") def leftMap[A, B, C](fab: F[A, B])(f: A => C): F[C, B] = ...
    @op(":->") def rightMap[A, B, D](fab: F[A, B])(g: B => D): F[A, D] = ...
    @op("<:>") def umap[A, B](faa: F[A, A])(f: A => B): F[B, B] = ...
  }
  
  @typeclass trait Bifoldable[F[_, _]] {
    def bifoldMap[A, B, M: Monoid](fa: F[A, B])(f: A => M)(g: B => M): M
  
    def bifoldRight[A,B,C](fa: F[A, B], z: =>C)(f: (A, =>C) => C)(g: (B, =>C) => C): C
    def bifoldLeft[A,B,C](fa: F[A, B], z: C)(f: (C, A) => C)(g: (C, B) => C): C = ...
  
    def bifoldMap1[A, B, M: Semigroup](fa: F[A,B])(f: A => M)(g: B => M): Option[M] = ...
  }
  
  @typeclass trait Bitraverse[F[_, _]] extends Bifunctor[F] with Bifoldable[F] {
    def bitraverse[G[_]: Applicative, A, B, C, D](fab: F[A, B])
                                                 (f: A => G[C])
                                                 (g: B => G[D]): G[F[C, D]]
  
    def bisequence[G[_]: Applicative, A, B](x: F[G[A], G[B]]): G[F[A, B]] = ...
  }
~~~~~~~~

A> `<-:` i `:->` to szczęśliwe operatory (_happy operators_)!

Mimo że sygnatury metod są dość rozwlekłe, to są to niemal dokładnie te same metody, które znamy 
z typeklas `Functor`, `Foldable` i `Traverse`, z tą różnicą, że przyjmują dwie funkcje zamiast jednej. 
Czasami funkcje te muszą zwracać ten sam typ, aby wyniki można było połączyć za pomocą `Monoid`u lub `Semigroup`y.

{lang="text"}
~~~~~~~~
  scala> val a: Either[String, Int] = Left("fail")
         val b: Either[String, Int] = Right(13)
  
  scala> b.bimap(_.toUpperCase, _ * 2)
  res: Either[String, Int] = Right(26)
  
  scala> a.bimap(_.toUpperCase, _ * 2)
  res: Either[String, Int] = Left(FAIL)
  
  scala> b :-> (_ * 2)
  res: Either[String,Int] = Right(26)
  
  scala> a :-> (_ * 2)
  res: Either[String, Int] = Left(fail)
  
  scala> { s: String => s.length } <-: a
  res: Either[Int, Int] = Left(4)
  
  scala> a.bifoldMap(_.length)(identity)
  res: Int = 4
  
  scala> b.bitraverse(s => Future(s.length), i => Future(i))
  res: Future[Either[Int, Int]] = Future(<not completed>)
~~~~~~~~

Dodatkowo możemy wrócić na chwile do `MonadPlus` (czyli `Monad`y z metodami `filterWith` i `unite`), aby zobaczyć,
że potrafi ona rozdzielać (`separate`) zawartość `Monad`y, jeśli tylko jej typ ma instancję `Bifoldable`.

{lang="text"}
~~~~~~~~
  @typeclass trait MonadPlus[F[_]] {
    ...
    def separate[G[_, _]: Bifoldable, A, B](value: F[G[A, B]]): (F[A], F[B]) = ...
    ...
  }
~~~~~~~~

Jest to bardzo przydatny mechanizm, kiedy mamy do czynienia z kolekcją bi-rzeczy i chcemy podzielić ją
na kolekcję `A` i kolekcję `B`.

{lang="text"}
~~~~~~~~
  scala> val list: List[Either[Int, String]] =
           List(Right("hello"), Left(1), Left(2), Right("world"))
  
  scala> list.separate
  res: (List[Int], List[String]) = (List(1, 2), List(hello, world))
~~~~~~~~


## Podsumowanie

Dużo tego! Właśnie odkryliśmy standardową bibliotekę polimorficznych funkcjonalności. Ale patrząc na to z innej perspektywy:
w Collections API z biblioteki standardowej Scali jest więcej traitów niż typeklas w Scalaz.

To całkiem normalne, jeśli twoja czysto funkcyjna aplikacja korzysta jedynie z małej części omówionych typeklas,
a większość funkcjonalności czerpie z typeklas i algebr domenowych. Nawet jeśli twoje domenowe typeklasy są
tylko wyspecjalizowanymi odpowiednikami tych zdefiniowanych w Scalaz, to jest zupełnie ok, aby zrefaktorować je
później.

Aby ułatwić nieco sprawę, dołączyliśmy cheat-sheet wszystkich typeklas i ich głównych metod w załączniku. Jest on zainspirowany przez 
[Scalaz Cheatsheet](http://arosien.github.io/scalaz-cheatsheets/typeclasses.pdf) Adama Rosiena.

Aby pomóc jeszcze bardziej, Valentin Kasas pokazuję jak  [połączyć `N` rzeczy](https://twitter.com/ValentinKasas/status/879414703340081156)

{width=70%}
![](images/shortest-fp-book.png)


# Typy danych ze Scalaz

Kto nie kocha porządnej struktury danych? Odpowiedź brzmi *nikt*, a struktury danych są super!

W tym rozdziale poznamy typy danych przypominające kolekcje oraz takie, które wzbogacają Scalę o dodatkowe 
możliwości i zwiększają bezpieczeństwo typów.

Podstawowym powodem, dla którego używamy wielu różnych typów kolekcji jest wydajność. Wektor i lista mogą
zrobić to samo, ale ich charakterystyki wydajnościowe są inne: wektor oferuje dostęp do losowego elementu w czasie stałym
gdy lista musi zostać w czasie tej operacji przetrawersowana.

W> Szacunki wydajnościowe, wliczając w to twierdzenia w tym rozdziale, powinny być zawsze brane z przymrużeniem oka. 
W> Nowoczesne architektury procesorów, pipelining i garbage collector w JVMie mogą zaburzyć nasze intuicyjne wyliczenia
W> bazujące na zliczaniu wykonywanych operacji.
W> 
W> Gorzka prawda o współczesnych komputerach jest taka, że empiryczne testy wydajnościowe mogą szokować i zaskakiwać.
W> Przykładem może być to, że w praktyce `List`a jest często szybsza niż `Vector`. Jeśli badasz wydajność, używaj
W> narzędzi takich jak [JMH](http://openjdk.java.net/projects/code-tools/jmh/).

Wszystkie kolekcje, które tutaj zaprezentujemy są *trwałe* (_persistent_): jeśli dodamy lub usuniemy element, nadal możemy
używać poprzedniej, niezmienionej wersji. Współdzielenie strukturalne (_structural sharing_) jest kluczowe dla 
wydajności trwałych struktur danych, bez tego musiałyby one być tworzone od nowa przy każdej operacji.

W przeciwieństwie do kolekcji z bibliotek standardowych Javy i Scali, w Scalaz typy danych nie tworzą hierarchii, a przez to
są dużo prostsze do zrozumienia. Polimorfizm jest zapewniany przez zoptymalizowane instancje typeklas które poznaliśmy
w poprzednim rozdziale. Sprawia to, że zmiana implementacji podyktowana zwiększeniem wydajności, lub dostarczenie własnej, 
jest dużo prostsze.

## Wariancja typów

Wiele z typów danych zdefiniowanych w Scalaz jest *inwariantna*. Dla przykładu `IList[A]` **nie** jest podtypem
`IList[B]` nawet jeśli `A <: B`.

### Kowariancja

Problem z kowariantnymi parametrami typu, takimi jak `A` w `class List[+A]`, jest taki, że `List[A]` jest podtypem
(a więc dziedziczy po) `List[Any]` i bardzo łatwo jest przez przypadek zgubić informacje o typach.

{lang="text"}
~~~~~~~~
  scala> List("hello") ++ List(' ') ++ List("world!")
  res: List[Any] = List(hello,  , world!)
~~~~~~~~

Zauważ, że druga lista jest typu `List[Char]` i kompilator niezbyt pomocnie wyinferował `Any` jako 
*Najmniejszą Górną Granicę* (_Least Upper Bound_, LUB). Porównajmy to z `IList`, która wymaga bezpośredniego wywołania 
`.widen[Any]`, aby pozwolić na ten haniebny uczynek:

{lang="text"}
~~~~~~~~
  scala> IList("hello") ++ IList(' ') ++ IList("world!")
  <console>:35: error: type mismatch;
   found   : Char(' ')
   required: String
  
  scala> IList("hello").widen[Any]
           ++ IList(' ').widen[Any]
           ++ IList("world!").widen[Any]
  res: IList[Any] = [hello, ,world!]
~~~~~~~~

Podobnie, gdy kompilator inferuje typ z dopiskiem `with Product with Serializable` to najprawdopodobniej 
miało miejsce przypadkowe rozszerzenie typu spowodowane kowariancją.

Niestety, musimy uważać nawet gdy konstruujemy typy inwariantne, ponieważ obliczenie LUB wykonywane jest również
dla parametrów typu:

{lang="text"}
~~~~~~~~
  scala> IList("hello", ' ', "world")
  res: IList[Any] = [hello, ,world]
~~~~~~~~

Kolejny podobny problem powodowany jest przez typ `Nothing`, który jest podtypem wszystkich innych typów, wliczając w to
ADT, klasy finalne, typy prymitywne oraz `null`.

Nie istnieją wartości typu `Nothing`.  Funkcje które przyjmują `Nothing` jako parametr nie mogą zostać uruchomione, a
funkcje które zwracają ten typ nigdy nie zwrócą rezultatu. Typ `Nothing` został wprowadzony, aby umożliwić używanie 
kowariantnych parametrów typu, ale w konsekwencji umożliwił pisanie kodu który nie może być uruchomiony, często przez przypadek.
Scalaz twierdzi, że wcale nie potrzebujemy kowariantnych parametrów typu, ograniczając się tym samym do praktycznego
kodu, który może zostać uruchomiony.


### Sprzeciwwariancja 

Z drugiej strony, parametry *kontrawariantne* takie jak `A` w `trait Thing[-A]` mogą ujawnić niszczycielskie
[błędy w kompilatorze](https://issues.scala-lang.org/browse/SI-2509). Spójrzmy na to co Paul Phillips (były
członek zespołu pracującego nad `scalac`) nazywa *contrarivariance*:

{lang="text"}
~~~~~~~~
  scala> :paste
         trait Thing[-A]
         def f(x: Thing[ Seq[Int]]): Byte   = 1
         def f(x: Thing[List[Int]]): Short  = 2
  
  scala> f(new Thing[ Seq[Int]] { })
         f(new Thing[List[Int]] { })
  
  res = 1
  res = 2
~~~~~~~~

Tak jak byśmy oczekiwali, kompilator odnalazł najdokładniejsze dopasowanie metod do argumentów.
Sprawa komplikuje się jednak gdy użyjemy wartości niejawnych

{lang="text"}
~~~~~~~~
  scala> :paste
         implicit val t1: Thing[ Seq[Int]] =
           new Thing[ Seq[Int]] { override def toString = "1" }
         implicit val t2: Thing[List[Int]] =
           new Thing[List[Int]] { override def toString = "2" }
  
  scala> implicitly[Thing[ Seq[Int]]]
         implicitly[Thing[List[Int]]]
  
  res = 1
  res = 1
~~~~~~~~

Niejawne rozstrzyganie odwraca definicje "najbardziej dokładnego" dla typów kontrawariantnych, czyniąc je tym samym
kompletnie bezużytecznymi do reprezentacji typeklas i czegokolwiek co wymaga polimorficznych funkcjonalności. 
Zachowanie to zostało poprawione w Dotty.


### Ograniczenia podtypów

`scala.Option` ma metodę `.flatten`, która konwertuje `Option[Option[B]]` na `Option[B]`.
Niestety kompilator Scali nie pozwala nam na poprawne zapisanie sygnatury tej metody. 
Rozważmy poniższą implementację która pozornie wydaje się poprawna:

{lang="text"}
~~~~~~~~
  sealed abstract class Option[+A] {
    def flatten[B, A <: Option[B]]: Option[B] = ...
  }
~~~~~~~~

`A` wprowadzone w definicji `.flatten` przysłania `A` wprowadzone w definicji klasy. Tak więc jest to równoznaczne z

{lang="text"}
~~~~~~~~
  sealed abstract class Option[+A] {
    def flatten[B, C <: Option[B]]: Option[B] = ...
  }
~~~~~~~~

czyli nie do końca jest tym czego chcieliśmy.

Jako obejście tego problemu wprowadzono klasy `<:<` i `=:=` wraz z niejawnymi metodami, które zawsze tworzą
instancje dla poprawnych typów.

{lang="text"}
~~~~~~~~
  sealed abstract class <:<[-From, +To] extends (From => To)
  implicit def conforms[A]: A <:< A = new <:<[A, A] { def apply(x: A): A = x }
  
  sealed abstract class =:=[ From,  To] extends (From => To)
  implicit def tpEquals[A]: A =:= A = new =:=[A, A] { def apply(x: A): A = x }
~~~~~~~~

`=:=` może być użyty do wymuszenia, aby dwa parametry typu były dokładnie takie same. `<:<` służy do wyrażenia
relacji podtypowania, pozwalając tym samym na implementację `.flatten` jako

{lang="text"}
~~~~~~~~
  sealed abstract class Option[+A] {
    def flatten[B](implicit ev: A <:< Option[B]): Option[B] = this match {
      case None        => None
      case Some(value) => ev(value)
    }
  }
  final case class Some[+A](value: A) extends Option[A]
  case object None                    extends Option[Nothing]
~~~~~~~~

Scalaz definiuje ulepszone wersje `<:<` i `=:=`: *Liskov* (z aliasem `<=<`) oraz *Leibniz* (`===`).

{lang="text"}
~~~~~~~~
  sealed abstract class Liskov[-A, +B] {
    def apply(a: A): B = ...
    def subst[F[-_]](p: F[B]): F[A]
  
    def andThen[C](that: Liskov[B, C]): Liskov[A, C] = ...
    def onF[X](fa: X => A): X => B = ...
    ...
  }
  object Liskov {
    type <~<[-A, +B] = Liskov[A, B]
    type >~>[+B, -A] = Liskov[A, B]
  
    implicit def refl[A]: (A <~< A) = ...
    implicit def isa[A, B >: A]: A <~< B = ...
  
    implicit def witness[A, B](lt: A <~< B): A => B = ...
    ...
  }
  
  // type signatures have been simplified
  sealed abstract class Leibniz[A, B] {
    def apply(a: A): B = ...
    def subst[F[_]](p: F[A]): F[B]
  
    def flip: Leibniz[B, A] = ...
    def andThen[C](that: Leibniz[B, C]): Leibniz[A, C] = ...
    def onF[X](fa: X => A): X => B = ...
    ...
  }
  object Leibniz {
    type ===[A, B] = Leibniz[A, B]
  
    implicit def refl[A]: Leibniz[A, A] = ...
  
    implicit def subst[A, B](a: A)(implicit f: A === B): B = ...
    implicit def witness[A, B](f: A === B): A => B = ...
    ...
  }
~~~~~~~~

Poza dostarczeniem przydatnych metod i niejawnych konwersji, `<=<` i `===` są bardziej pryncypialne niż ich odpowiedniki
z biblioteki standardowej.

A> Liskov zawdzięcza swą nazwę Barbarze Liskov, autorce *Zasady podstawienia Liskov*,która stała się fundamentem 
A> Programowania Zorientowanego Obiektowo.
A>
A> Gottfried Wilhelm Leibniz to człowiek który odkrył *wszystko* w 17 wieku. Wierzył w [Boga zwanego Monadą](https://en.wikipedia.org/wiki/Monad_(philosophy)).
A> Eugenio Moggi później reużył tej nazwy dla abstrakcji, którą znamy jako `scalaz.Monad`. Już nie Bóg, ale jeszcze nie śmiertelnik.

## Ewaluacja

Java to język o *ścisłej* (_strict_) ewaluacji: wszystkie parametry przekazane do metody muszę zostać wyewaluowane do 
*wartości* zanim metoda zostanie uruchomiona. Scala wprowadza pojęcie parametrów przekazywanych *przez nazwę* (_by-name_)
za pomocą składni `a: =>A`. Takie parametry opakowywane są w zero-argumentową funkcję, która jest wywoływana za każdym razem, gdy odnosimy
się do `a`. Widzieliśmy tego typu parametry wielokrotnie, gdy omawialiśmy typeklasy.

Scala pozwala również na ewaluacje wartości *na żądanie* za pomocą słowa kluczowego `lazy`: obliczenia są wykonywane najwyżej raz
aby wyprodukować wartość przy pierwszym użyciu. Niestety Scala nie wspiera ewaluacji *na żądanie* dla parametrów metod.

A> Jeśli obliczenie wartości `lazy val` wyrzuci wyjątek, to jest ono powtarzane za każdym kolejnym użyciem tej zmiennej.
A> Ponieważ wyjątki mogą zaburzać transparencje referencyjną, ograniczymy się do omawiania definicji `lazy val`, które
A> zawsze produkują poprawną wartość.

Scalaz formalizuje te trzy strategie ewaluacji za pomocą ADT

{lang="text"}
~~~~~~~~
  sealed abstract class Name[A] {
    def value: A
  }
  object Name {
    def apply[A](a: =>A) = new Name[A] { def value = a }
    ...
  }
  
  sealed abstract class Need[A] extends Name[A]
  object Need {
    def apply[A](a: =>A): Need[A] = new Need[A] {
      private lazy val value0: A = a
      def value = value0
    }
    ...
  }
  
  final case class Value[A](value: A) extends Need[A]
~~~~~~~~

Najsłabszą formą ewaluacji jest `Name`, która nie daje żadnych gwarancji obliczeniowych. Następna jest `Need` gwarantująca
ewaluację *najwyżej raz* (_at most once_). `Value` jest obliczana przed utworzeniem, gwarantując tym samym ewaluację 
*dokładnie raz* (_exactly once_).

Gdybyśmy chcieli być pedantyczni, moglibyśmy wrócić do wszystkich typeklas, które poznaliśmy do tej pory i zamienić przyjmowane 
parametry w ich metodach na `Name`, `Need` i `Value`. Zamiast tego możemy też po prostu założyć, że normalne parametry
mogą być zawsze opakowane w `Value`, a te przekazywane *przez nazwę* w `Name`.

Gdy piszemy *czyste programy* możemy śmiało zamienić dowolne `Name` na `Need` lub `Value`, i vice versa, bez zmieniania
poprawności programu. To jest właśnie esencja *transparencji referencyjnej*: zdolność do zamiany obliczeń na wartość wynikową
lub wartości na obliczenia potrzebne do jej uzyskania.

W programowaniu funkcyjnym prawie zawsze potrzebujemy `Value` lub `Need` (znane też jako parametry *ścisłe* i *leniwe*), ale nie mamy
zbyt wiele pożytku z `Name`. Ponieważ na poziomie języka nie mamy bezpośredniego wsparcia dla leniwych parametrów, metody często
przyjmują wartości *przez nazwę* a następnie konwertują je do `Need`, zwiększając tym samym wydajność.

A> Typ `Lazy` (pisany z wielkiej litery) jest często używany w bibliotekach Scalowych do wyrażania semantyki przekazywania
A> *przez nazwę*. Jest to błąd w nazewnictwie, który już zdążył się zadomowić.
A> 
A> Ogólnie rzecz biorąc, dość leniwie podchodzimy do lenistwa. Czasem warto dociec jaki dokładnie rodzaj
A> leniwego zachowania omawiamy. Albo nie. Bo po co?

`Name` dostarcza instancje poniższych typeklas:

-   `Monad`
-   `Comonad`
-   `Traverse1`
-   `Align`
-   `Zip` / `Unzip` / `Cozip`

A> "Nie ma nic za darmo", mówi powiedzenie i tak samo jest z parametrami *leniwymi* i przekazywanymi *przez nazwę*.
A> Kiedy Scala konwertuje te parametry do kodu bajtowego pojawia się narzut związany z dodatkową alokacją pamięci.
A> 
A> Zanim przepiszesz wszystko z użyciem parametrów przekazywanych *przez nazwę*, upewnij się, że koszt nie przyćmiewa zysków.
A> Nie ma żadnej wartości dodanej, jeśli nie istnieje możliwość **nie** ewaluowania danej wartości. Kod wymagający 
A> wysokiej wydajności uruchomiony w ścisłej pętli i zawsze wymagający konkretnej wartości danego parametru znacząco ucierpi na takim 
A> refactoringu.

## Memoizacja

Scalaz potrafi memoizować funkcje za pomocą typu `Memo`, który nie daje żadnych gwarancji co do ewaluacji z powodu
dużej gamy różniących się implementacji:

{lang="text"}
~~~~~~~~
  sealed abstract class Memo[K, V] {
    def apply(z: K => V): K => V
  }
  object Memo {
    def memo[K, V](f: (K => V) => K => V): Memo[K, V]
  
    def nilMemo[K, V]: Memo[K, V] = memo[K, V](identity)
  
    def arrayMemo[V >: Null : ClassTag](n: Int): Memo[Int, V] = ...
    def doubleArrayMemo(n: Int, sentinel: Double = 0.0): Memo[Int, Double] = ...
  
    def immutableHashMapMemo[K, V]: Memo[K, V] = ...
    def immutableTreeMapMemo[K: scala.Ordering, V]: Memo[K, V] = ...
  }
~~~~~~~~

`memo` pozwala nam na tworzenie własnych implementacji `Memo`. `nilMemo` nie memoizuje w ogóle, a więc funkcja wykonywana 
jest za każdym wywołaniem. Pozostałe implementacje przechwytują wywołania funkcji i cache'ują wynik przy użyciu kolekcji z 
biblioteki standardowej.

Aby wykorzystać `Memo` wystarczy, że opakujemy naszą funkcje z użyciem wybranej implementacji, a następnie używać będziemy
zwróconej nam funkcji zamiast tej oryginalnej:

{lang="text"}
~~~~~~~~
  scala> def foo(n: Int): String = {
           println("running")
           if (n > 10) "wibble" else "wobble"
         }
  
  scala> val mem = Memo.arrayMemo[String](100)
         val mfoo = mem(foo)
  
  scala> mfoo(1)
  running // evaluated
  res: String = wobble
  
  scala> mfoo(1)
  res: String = wobble // memoised
~~~~~~~~

Jeśli funkcja przyjmuje więcej niż jeden argument musimy wywołać na niej `tupled` konwertując ją tym samym
do jednoargumentowej funkcji przyjmującej tuple.

{lang="text"}
~~~~~~~~
  scala> def bar(n: Int, m: Int): String = "hello"
         val mem = Memo.immutableHashMapMemo[(Int, Int), String]
         val mbar = mem((bar _).tupled)
  
  scala> mbar((1, 2))
  res: String = "hello"
~~~~~~~~

`Memo` jest traktowany w specjalny sposób i typowe reguły *czystości* są nieco osłabione przy jego implementacji.
Aby nosić miano czystego wystarczy, aby wykonanie `K => V` było referencyjnie transparentne. Przy implementacji możemy
używać mutowalnych struktur danych lub wykonywać operacje I/O, np., aby uzyskać LRU lub rozproszony cache bez deklarowania efektów
w sygnaturze typu. Inne funkcyjne języki programowania udostępniają automatyczną memoizację zarządzaną przez środowisko 
uruchomieniowe, `Memo` to nasz sposób na dodanie podobnej funkcjonalności do JVMa, niestety jedynie jako "opt-in".


## Tagowanie

W podrozdziale wprowadzającym `Monoid` stworzyliśmy `Monoid[TradeTemplate]` jednocześnie uświadamiając sobie, że
domyślna instancja `Monoid[Option[A]]` ze Scalaz nie robi tego czego byśmy od niej oczekiwali. Nie jest to jednak przeoczenie
ze strony Scalaz: często będziemy napotykali sytuację w której dany typ danych może mieć wiele poprawnych implementacji
danej typeklasy a ta domyślna nie robi tego czego byśmy chcieli lub w ogóle nie jest zdefiniowana.

Najprostszym przykładem jest `Monoid[Boolean]` (koniunkcja `&&` vs alternatywa `||`) lub `Monoid[Int]` (mnożenie vs dodawanie).

Aby zaimplementować `Monoid[TradeTemplate]` musieliśmy albo zaburzyć spójność typeklas albo użyć innej typeklasy niż `Monoid`.

`scalaz.Tag` został zaprojektowany jako rozwiązanie tego problemu, ale bez sprowadzania ograniczeń, które napotkaliśmy.

Definicja jest dość pokrzywiona, ale składnia dostarczana użytkownikowi jest bardzo przejrzysta. Oto w jaki sposób możemy
oszukać kompilator i zdefiniować typ `A @@ T`, który zostanie uproszczony do `A` w czasie wykonania programu:

{lang="text"}
~~~~~~~~
  type @@[A, T] = Tag.k.@@[A, T]
  
  object Tag {
    @inline val k: TagKind = IdTagKind
    @inline def apply[A, T](a: A): A @@ T = k(a)
    ...
  
    final class TagOf[T] private[Tag]() { ... }
    def of[T]: TagOf[T] = new TagOf[T]
  }
  sealed abstract class TagKind {
    type @@[A, T]
    def apply[A, T](a: A): A @@ T
    ...
  }
  private[scalaz] object IdTagKind extends TagKind {
    type @@[A, T] = A
    @inline override def apply[A, T](a: A): A = a
    ...
  }
~~~~~~~~

A> A więc tagujemy rzeczy używając koków księżniczki Lei: `@@`.

Kilka użytecznych tagów znajdziemy w obiekcie `Tags`

{lang="text"}
~~~~~~~~
  object Tags {
    sealed trait First
    val First = Tag.of[First]
  
    sealed trait Last
    val Last = Tag.of[Last]
  
    sealed trait Multiplication
    val Multiplication = Tag.of[Multiplication]
  
    sealed trait Disjunction
    val Disjunction = Tag.of[Disjunction]
  
    sealed trait Conjunction
    val Conjunction = Tag.of[Conjunction]
  
    ...
  }
~~~~~~~~

`First` i `Last` służą do wyboru między instancjami `Monoidu`, które wybierają odpowiednio pierwszy lub ostatni 
operand. Za pomocą `Multiplication` możemy zmienić zachowanie `Monoid`u dla typów liczbowych z dodawania na mnożenie.
`Disjunction` i `Conjunction` pozwalają wybrać między `&&` i `||` dla typu `Boolean`.

W naszym przykładzie definiującym `TradeTemplate`, zamiast `Option[Currency]` mogliśmy użyć `Option[Currency] @@ Tags.Last`.
W rzeczywistości jest to przypadek tak częsty, że mogliśmy użyć wbudowanego aliasu `LastOption`.  

{lang="text"}
~~~~~~~~
  type LastOption[A] = Option[A] @@ Tags.Last
~~~~~~~~

i tym samym sprawić, że implementacja `Monoid[TradeTemplate]` będzie znacznie czystsza

{lang="text"}
~~~~~~~~
  final case class TradeTemplate(
    payments: List[java.time.LocalDate],
    ccy: LastOption[Currency],
    otc: LastOption[Boolean]
  )
  object TradeTemplate {
    implicit val monoid: Monoid[TradeTemplate] = Monoid.instance(
      (a, b) =>
        TradeTemplate(a.payments |+| b.payments,
                      a.ccy |+| b.ccy,
                      a.otc |+| b.otc),
        TradeTemplate(Nil, Tag(None), Tag(None))
    )
  }
~~~~~~~~

Tworzymy wartości typu `LastOption` poprzez zaaplikowanie `Tag` na instancji `Option`. W tym wypadku wołamy
`Tag(None)`.

W rozdziale o derywacji typeklas pójdziemy o jeden krok dalej i stworzymy `monoid` automatycznie.

Kuszącym może wydać się pomysł użycia `Tag`ów do oznaczania danych na potrzeby walidacji (np. `String @@ PersonName`),
ale należy oprzeć się tym pokusom, gdyż za takim oznaczeniem nie stoją żadne weryfikacje wartości używanych w czasie wykonania.
`Tag` powinien być używany tylko do selekcji typeklas, a do ograniczania możliwych wartości dużo lepiej jest użyć 
biblioteki `Refined`, która poznaliśmy w Rozdziale 4.


## Transformacja Naturalna

Funkcja z jednego typu w drugi zapisywana jest w Scali jako `A => B`, ale jest to tylko syntax sugar dla 
`Function1[A, B]`. Scalaz dostarcza podobny mechanizm w formie `F ~> G` dla funkcji z konstruktora typu
`F[_]` do `G[_]`.

Te właśnie `F ~> G` nazywamy *transformacjami naturalnymi* (_natural transformation_) i są one 
*uniwersalnie kwantyfikowane*, ponieważ nie ma dla nich znaczenia zawartość `F[_]`.

{lang="text"}
~~~~~~~~
  type ~>[-F[_], +G[_]] = NaturalTransformation[F, G]
  trait NaturalTransformation[-F[_], +G[_]] {
    def apply[A](fa: F[A]): G[A]
  
    def compose[E[_]](f: E ~> F): E ~> G = ...
    def andThen[H[_]](f: G ~> H): F ~> H = ...
  }
~~~~~~~~

Przykładem transformacji naturalnej jest funkcja, która konwertuje `IList` na `List`

{lang="text"}
~~~~~~~~
  scala> val convert = new (IList ~> List) {
           def apply[A](fa: IList[A]): List[A] = fa.toList
         }
  
  scala> convert(IList(1, 2, 3))
  res: List[Int] = List(1, 2, 3)
~~~~~~~~

Lub, bardziej zwięźle, korzystając ze składni udostępnianej przez `kind-projector`:

{lang="text"}
~~~~~~~~
  scala> val convert = λ[IList ~> List](_.toList)
  
  scala> val convert = Lambda[IList ~> List](_.toList)
~~~~~~~~

Jednak w codziennej pracy zdecydowanie częściej będziemy używać transformacji naturalnych do konwersji między
algebrami. Możemy, na przykład, chcieć zaimplementować naszą algebrę `Machines`, służącą do komunikacji z Google Container
Engine, za pomocą gotowej, zewnętrznej algebry `BigMachines`. Zamiast zmieniać naszą logikę biznesową i wszystkie testy,
tak aby używały nowej algebry, możemy spróbować napisać transformację naturalną `BigMachines ~> Machines`. 
Powrócimy do tego pomysłu w rozdziale o Zaawansowanych Monadach.


## `Isomorphism`

Czasami mamy do czynienia z dwoma typami, które tak naprawdę są dokładnie tym samym.
Powoduje to problemy z kompatybilnością, ponieważ kompilator najczęściej nie ma tej wiedzy.
Najczęściej takie sytuacje mają miejsce, gdy chcemy użyć zewnętrznych bibliotek, które definiują
coś co już mamy w naszym kodzie.

W takich właśnie okolicznościach z pomocą przychodzi `Isomorphism`, który definiuje relację równoznaczności
między dwoma typami. Ma on 3 warianty dla typów o różnym kształcie:

{lang="text"}
~~~~~~~~
  object Isomorphism {
    trait Iso[Arr[_, _], A, B] {
      def to: Arr[A, B]
      def from: Arr[B, A]
    }
    type IsoSet[A, B] = Iso[Function1, A, B]
    type <=>[A, B] = IsoSet[A, B]
    object IsoSet {
      def apply[A, B](to: A => B, from: B => A): A <=> B = ...
    }
  
    trait Iso2[Arr[_[_], _[_]], F[_], G[_]] {
      def to: Arr[F, G]
      def from: Arr[G, F]
    }
    type IsoFunctor[F[_], G[_]] = Iso2[NaturalTransformation, F, G]
    type <~>[F[_], G[_]] = IsoFunctor[F, G]
    object IsoFunctor {
      def apply[F[_], G[_]](to: F ~> G, from: G ~> F): F <~> G = ...
    }
  
    trait Iso3[Arr[_[_, _], _[_, _]], F[_, _], G[_, _]] {
      def to: Arr[F, G]
      def from: Arr[G, F]
    }
    type IsoBifunctor[F[_, _], G[_, _]] = Iso3[~~>, F, G]
    type <~~>[F[_, _], G[_, _]] = IsoBifunctor[F, G]
  
    ...
  }
~~~~~~~~

Aliasy typów `IsoSet`, `IsoFunctor` i `IsoBiFunctor` pokrywają najczęstsze przypadki: zwykłe funkcje,
transformacje naturalne i binaturalne. Funkcje pomocnicze pozwalają nam generować instancje `Iso` z gotowych
funkcji lub transformacji, ale często łatwiej jest użyć do tego klas `Template`. Na przykład:

{lang="text"}
~~~~~~~~
  val listIListIso: List <~> IList =
    new IsoFunctorTemplate[List, IList] {
      def to[A](fa: List[A]) = fromList(fa)
      def from[A](fa: IList[A]) = fa.toList
    }
~~~~~~~~

Jeśli wprowadzimy izomorfizm, możemy wygenerować wiele standardowych typeklas. Dla przykładu

{lang="text"}
~~~~~~~~
  trait IsomorphismSemigroup[F, G] extends Semigroup[F] {
    implicit def G: Semigroup[G]
    def iso: F <=> G
    def append(f1: F, f2: =>F): F = iso.from(G.append(iso.to(f1), iso.to(f2)))
  }
~~~~~~~~

pozwala nam wyderywować `Semigroup[F]` dla typu `F` jeśli mamy `F <=> G` oraz `Semigroup[G]`.
Niemal wszystkie typeklasy w hierarchii mają wariant dla typów izomorficznych. Jeśli złapiemy się na 
kopiowaniu implementacji danej typeklasy, warto rozważyć zdefiniowanie `Isomorphism`u.


## Kontenery


### Maybe

Widzieliśmy już `Maybe`, Scalazowe ulepszenie `scala.Option`. Jest to ulepszenie dzięki swojej inwariancji oraz braku
jakichkolwiek nieczystych metod, taki jak `Option.get`, które mogą rzucać wyjątki.

Zazwyczaj typ ten używany jest do reprezentacji rzeczy, które mogą być nieobecne, bez podawania żadnej przyczyny
ani wyjaśnienia dla tej nieobecności.

{lang="text"}
~~~~~~~~
  sealed abstract class Maybe[A] { ... }
  object Maybe {
    final case class Empty[A]()    extends Maybe[A]
    final case class Just[A](a: A) extends Maybe[A]
  
    def empty[A]: Maybe[A] = Empty()
    def just[A](a: A): Maybe[A] = Just(a)
  
    def fromOption[A](oa: Option[A]): Maybe[A] = ...
    def fromNullable[A](a: A): Maybe[A] = if (null == a) empty else just(a)
    ...
  }
~~~~~~~~

`.empty` i `.just` są lepsze niż tworzenie `Just` i `Maybe` bezpośrednio, ponieważ zwracają `Maybe` pomagając tym samym
w inferencji typów. Takie podejście często nazywane jest zwracaniem typu sumy (_sum type_), a więc mimo posiadania
wielu implementacji zapieczętowanego traita (_sealed trait_) nigdy nie używamy konkretnych podtypów w sygnaturach metod.

Pomocnicza klasa niejawna pozwala nam zawołać `.just` na dowolnej wartości i uzyskać `Maybe`.

{lang="text"}
~~~~~~~~
  implicit class MaybeOps[A](self: A) {
    def just: Maybe[A] = Maybe.just(self)
  }
~~~~~~~~

`Maybe` posiada instancje wszystkich poniższych typeklas

-   `Align`
-   `Traverse`
-   `MonadPlus` / `IsEmpty`
-   `Cobind`
-   `Cozip` / `Zip` / `Unzip`
-   `Optional`

oraz deleguje implementację poniższych do instancji dla typu `A`

-   `Monoid` / `Band`
-   `Equal` / `Order` / `Show`

Dodatkowo, `Maybe` oferuje funkcjonalności nie dostępne w żadnej typeklasie

{lang="text"}
~~~~~~~~
  sealed abstract class Maybe[A] {
    def cata[B](f: A => B, b: =>B): B = this match {
      case Just(a) => f(a)
      case Empty() => b
    }
  
    def |(a: =>A): A = cata(identity, a)
    def toLeft[B](b: =>B): A \/ B = cata(\/.left, \/-(b))
    def toRight[B](b: =>B): B \/ A = cata(\/.right, -\/(b))
    def <\/[B](b: =>B): A \/ B = toLeft(b)
    def \/>[B](b: =>B): B \/ A = toRight(b)
  
    def orZero(implicit A: Monoid[A]): A = getOrElse(A.zero)
    def orEmpty[F[_]: Applicative: PlusEmpty]: F[A] =
      cata(Applicative[F].point(_), PlusEmpty[F].empty)
    ...
  }
~~~~~~~~

`.cata` to zwięźlejsza alternatywa dla `.map(f).getOrElse(b)` dostępna również po postacią `|` jeśli `f` to `identity`
(co jest równoznaczne z `.getOrElse`).

`.toLeft` i `.toRight` oraz ich aliasy symbolicznie tworzą dysjunkcje (opisane w następnym podrozdziale) przyjmując
wartość używaną w przypadku napotkania `Empty`.

`.orZero` używa instancji typeklasy `Monoid` do zdobycia wartości domyślnej.

`.orEmpty` używa `ApplicativePlus`, aby stworzyć jednoelementowy lub pusty kontener. Pamiętajmy, że podobną funkcjonalność
dla kolekcji udostępnia nam `.to` pochodzące z `Foldable`.

{lang="text"}
~~~~~~~~
  scala> 1.just.orZero
  res: Int = 1
  
  scala> Maybe.empty[Int].orZero
  res: Int = 0
  
  scala> Maybe.empty[Int].orEmpty[IList]
  res: IList[Int] = []
  
  scala> 1.just.orEmpty[IList]
  res: IList[Int] = [1]
  
  scala> 1.just.to[List] // from Foldable
  res: List[Int] = List(1)
~~~~~~~~

A> Metody definiowane są tutaj w stylu OOP, a nie używając `object` lub `implicit class` jak uczyliśmy się w Rozdziale 4.
A> Jest to częste zjawisko w Scalaz i wynika w dużej mierze z zaszłości historycznych:
A> 
A> -   edytory tekstu miały tendencję do nie znajdywania metod rozszerzających, ale teraz działa to bez żadnego
A>     problemu w IntelliJ, ENSIME i ScalaIDE.
A> -   istnieją rzadkie przypadki, w których kompilator nie potrafi poprawie wyinferować typu, a więc i znaleźć
A>     metod rozszerzających
A> -   biblioteka standardowa definiuje kilka instancji klas niejawnych, które dodają metody do wszystkich wartości, często
A>     z konfliktującymi nazwami. Czołowym przykładem jest `+`, który zamienia wszystko w skonkatenowany `String`.
A> 
A> To samo zachodzi również dla funkcjonalności dostarczanych przez typeklasy, jak na przykład `Optional`
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   sealed abstract class Maybe[A] {
A>     def getOrElse(a: =>A): A = ...
A>     ...
A>   }
A> ~~~~~~~~
A> 
A> Jednak niedawne wersje Scali rozwiązały wiele błędów i szansa na napotkanie problemów jest dużo mniejsza.


### Either

Typ ulepszający `scala.Either` w Scalaz jest symbolem, ale przyjęło się nazywać go *either* lub `Disjunction`.

{lang="text"}
~~~~~~~~
  sealed abstract class \/[+A, +B] { ... }
  final case class -\/[+A](a: A) extends (A \/ Nothing)
  final case class \/-[+B](b: B) extends (Nothing \/ B)
  
  type Disjunction[+A, +B] = \/[A, B]
  
  object \/ {
    def left [A, B]: A => A \/ B = -\/(_)
    def right[A, B]: B => A \/ B = \/-(_)
  
    def fromEither[A, B](e: Either[A, B]): A \/ B = ...
    ...
  }
~~~~~~~~

z odpowiednią składnią

{lang="text"}
~~~~~~~~
  implicit class EitherOps[A](val self: A) {
    final def left [B]: (A \/ B) = -\/(self)
    final def right[B]: (B \/ A) = \/-(self)
  }
~~~~~~~~

pozwalającą na łatwe tworzenie wartości. Zauważ, że te metody przyjmują typ *drugiej strony* jako parametr. A więc
jeśli chcesz stworzyć `String \/ Int` mając `Int`, wołając `.right` musisz przekazać `String`.

{lang="text"}
~~~~~~~~
  scala> 1.right[String]
  res: String \/ Int = \/-(1)
  
  scala> "hello".left[Int]
  res: String \/ Int = -\/(hello)
~~~~~~~~

Symboliczna natura `\/` sprawia, że dobrze się go czyta, gdy użyty jest jako infiks. Pamiętaj, że typy symboliczne w Scali
wiążą argumenty od lewej, a więc zagnieżdżone `\/` muszą być ujęte w nawiasy.

`\/` posiada prawostronne (czyli `flatMap` wykonywany jest na `\/-`) instancje typeklas:

-   `Monad` / `MonadError`
-   `Traverse` / `Bitraverse`
-   `Plus`
-   `Optional`
-   `Cozip`

oraz zależne od zawartości

-   `Equal` / `Order`
-   `Semigroup` / `Monoid` / `Band`

Dodatkowo dostajemy kilka niestandardowych metod

{lang="text"}
~~~~~~~~
  sealed abstract class \/[+A, +B] { self =>
    def fold[X](l: A => X, r: B => X): X = self match {
      case -\/(a) => l(a)
      case \/-(b) => r(b)
    }
  
    def swap: (B \/ A) = self match {
      case -\/(a) => \/-(a)
      case \/-(b) => -\/(b)
    }
  
    def |[BB >: B](x: =>BB): BB = getOrElse(x) // Optional[_]
    def |||[C, BB >: B](x: =>C \/ BB): C \/ BB = orElse(x) // Optional[_]
  
    def +++[AA >: A: Semigroup, BB >: B: Semigroup](x: =>AA \/ BB): AA \/ BB = ...
  
    def toEither: Either[A, B] = ...
  
    final class SwitchingDisjunction[X](right: =>X) {
      def <<?:(left: =>X): X = ...
    }
    def :?>>[X](right: =>X) = new SwitchingDisjunction[X](right)
    ...
  }
~~~~~~~~

`.fold` przypomina `Maybe.cata` i wymaga, aby obie strony zostały przemapowane do tego samego typu.

`.swap` zamienia strony miejscami, lewa na prawo, prawa na lewo.

Alias `|` na `getOrElse` jest podobny do tego w `Maybe`. Dostajemy też `|||` jako alias na `orElse`. 

`+++` pozwala na łączenie dysjunkcji priorytetyzując te, które wypełnione są po lewej stronie.

-   `right(v1) +++ right(v2)` gives `right(v1 |+| v2)`
-   `right(v1) +++ left (v2)` gives `left (v2)`
-   `left (v1) +++ right(v2)` gives `left (v1)`
-   `left (v1) +++ left (v2)` gives `left (v1 |+| v2)`

`.toEither` zapewnia kompatybilność z biblioteką standardową.

Połączenie `:?>>` i `<<?:` pozwala w wygodny sposób zignorować zawartość `\/` wybierając jednocześnie nową wartość 
zależnie od jego typu.

{lang="text"}
~~~~~~~~
  scala> 1 <<?: foo :?>> 2
  res: Int = 2 // foo is a \/-
  
  scala> 1 <<?: foo.swap :?>> 2
  res: Int = 1
~~~~~~~~


### Validation

Na pierwszy rzut oka `Validation` (zaliasowana jako `\?/` czyli *szczęśliwy Elvis*) wydaje się być klonem
`Disjunction`:

{lang="text"}
~~~~~~~~
  sealed abstract class Validation[+E, +A] { ... }
  final case class Success[A](a: A) extends Validation[Nothing, A]
  final case class Failure[E](e: E) extends Validation[E, Nothing]
  
  type ValidationNel[E, +X] = Validation[NonEmptyList[E], X]
  
  object Validation {
    type \?/[+E, +A] = Validation[E, A]
  
    def success[E, A]: A => Validation[E, A] = Success(_)
    def failure[E, A]: E => Validation[E, A] = Failure(_)
    def failureNel[E, A](e: E): ValidationNel[E, A] = Failure(NonEmptyList(e))
  
    def lift[E, A](a: A)(f: A => Boolean, fail: E): Validation[E, A] = ...
    def liftNel[E, A](a: A)(f: A => Boolean, fail: E): ValidationNel[E, A] = ...
    def fromEither[E, A](e: Either[E, A]): Validation[E, A] = ...
    ...
  }
~~~~~~~~

Z pomocną składnią

{lang="text"}
~~~~~~~~
  implicit class ValidationOps[A](self: A) {
    def success[X]: Validation[X, A] = Validation.success[X, A](self)
    def successNel[X]: ValidationNel[X, A] = success
    def failure[X]: Validation[A, X] = Validation.failure[A, X](self)
    def failureNel[X]: ValidationNel[A, X] = Validation.failureNel[A, X](self)
  }
~~~~~~~~

Jednak sama struktura danych to nie wszystko. `Validation` celowo nie posiada instancji `Monad`,
ograniczając się do:

-   `Applicative`
-   `Traverse` / `Bitraverse`
-   `Cozip`
-   `Plus`
-   `Optional`

oraz zależnych od zawartości:

-   `Equal` / `Order`
-   `Show`
-   `Semigroup` / `Monoid`

Dużą zaletą ograniczenia się do `Applicative` jest to, że `Validation` używany jest wyraźnie w sytuacjach,
w których chcemy zebrać wszystkie napotkane problemy, natomiast `Disjunction` zatrzymuje się przy pierwszym i ignoruje
pozostałe. Aby wesprzeć akumulacje błędów mamy do dyspozycji `ValidationNel`, czyli `Validation` z `NonEmptyList[E]` 
po stronie błędów.

Rozważmy wykonanie walidacji danych pochodzących od użytkownika za pomocą `Disjunction` i `flatMap`:

{lang="text"}
~~~~~~~~
  scala> :paste
         final case class Credentials(user: Username, name: Fullname)
         final case class Username(value: String) extends AnyVal
         final case class Fullname(value: String) extends AnyVal
  
         def username(in: String): String \/ Username =
           if (in.isEmpty) "empty username".left
           else if (in.contains(" ")) "username contains spaces".left
           else Username(in).right
  
         def realname(in: String): String \/ Fullname =
           if (in.isEmpty) "empty real name".left
           else Fullname(in).right
  
  scala> for {
           u <- username("sam halliday")
           r <- realname("")
         } yield Credentials(u, r)
  res = -\/(username contains spaces)
~~~~~~~~

Jeśli użyjemy `|@|`

{lang="text"}
~~~~~~~~
  scala> (username("sam halliday") |@| realname("")) (Credentials.apply)
  res = -\/(username contains spaces)
~~~~~~~~

nadal dostaniemy tylko pierwszy błąd. Wynika to z faktu, że `Disjunction` jest `Monad`ą a jego metody
`.applyX` muszą być spójne z `.flatMap` i nie mogą zakładać, że operacje mogą być wykonywane poza kolejnością.
Porównajmy to z:

{lang="text"}
~~~~~~~~
  scala> :paste
         def username(in: String): ValidationNel[String, Username] =
           if (in.isEmpty) "empty username".failureNel
           else if (in.contains(" ")) "username contains spaces".failureNel
           else Username(in).success
  
         def realname(in: String): ValidationNel[String, Fullname] =
           if (in.isEmpty) "empty real name".failureNel
           else Fullname(in).success
  
  scala> (username("sam halliday") |@| realname("")) (Credentials.apply)
  res = Failure(NonEmpty[username contains spaces,empty real name])
~~~~~~~~

Tym razem dostaliśmy z powrotem wszystkie napotkane błędy!

`Validation` ma wiele metod analogicznych do tych w `Disjunction`, takich jak `.fold`, `.swap` i `+++`, plus
kilka ekstra:

{lang="text"}
~~~~~~~~
  sealed abstract class Validation[+E, +A] {
    def append[F >: E: Semigroup, B >: A: Semigroup](x: F \?/ B]): F \?/ B = ...
  
    def disjunction: (E \/ A) = ...
    ...
  }
~~~~~~~~

`.append` (z aliasem `+|+`) ma taką samą sygnaturę jak `+++`, ale preferuje wariant `success`

-   `failure(v1) +|+ failure(v2)` zwraca `failure(v1 |+| v2)`
-   `failure(v1) +|+ success(v2)` zwraca `success(v2)`
-   `success(v1) +|+ failure(v2)` zwraca `success(v1)`
-   `success(v1) +|+ success(v2)` zwraca `success(v1 |+| v2)`

A> `+|+` to zdziwiony robot c3p0.

`.disjunction` konwertuje `Validated[A, B]` do `A \/ B`. Dysjunkcja ma lustrzane metody `.validation` i `.validationNel`,
pozwalając tym samym na łatwe przełączanie się miedzy sekwencyjnym i równoległym zbieraniem błędów.

`\/` i `Validation` są bardziej wydajnymi alternatywami dla wyjątków typu checked do walidacji wejścia, unikającymi
zbierania śladu stosu (_stacktrace_). Wymagają one też od użytkownika obsłużenia potencjalnych błędów, sprawiając tym samym,
że tworzone systemy są bardziej niezawodne.

A> Jedną z najwolniejszych operacji na JVMie jest tworzenie wyjątków. Wynika to z zasobów potrzebnych do stworzenia 
A> śladu stosu. Tradycyjne podejście używające wyjątków do walidacji wejścia i parsowania potrafi być tysiąckrotnie 
A> wolniejsze od funkcji używających `\/` lub `Validation`.
A>
A> Niektórzy twierdzą, że przewidywalne wyjątki są referencyjnie transparentne, ponieważ zostaną rzucone za każdym razem.
A> Jednak ślad stosu zależy od ciągu wywołań, dając inny rezultat zależnie od tego kto zawołał daną funkcje, zaburzając
A> tym samym transparencję referencyjną.
A> Nie mniej, rzucanie wyjątku nie jest czyste, ponieważ oznacza, że funkcja nie jest *totalna*.


### These

Napotkaliśmy `These`, strukturę danych wyrażającą logiczne LUB, kiedy poznawaliśmy `Align`.

{lang="text"}
~~~~~~~~
  sealed abstract class \&/[+A, +B] { ... }
  object \&/ {
    type These[A, B] = A \&/ B
  
    final case class This[A](aa: A) extends (A \&/ Nothing)
    final case class That[B](bb: B) extends (Nothing \&/ B)
    final case class Both[A, B](aa: A, bb: B) extends (A \&/ B)
  
    def apply[A, B](a: A, b: B): These[A, B] = Both(a, b)
  }
~~~~~~~~

z metodami upraszczającymi konstrukcję

{lang="text"}
~~~~~~~~
  implicit class TheseOps[A](self: A) {
    final def wrapThis[B]: A \&/ B = \&/.This(self)
    final def wrapThat[B]: B \&/ A = \&/.That(self)
  }
  implicit class ThesePairOps[A, B](self: (A, B)) {
    final def both: A \&/ B = \&/.Both(self._1, self._2)
  }
~~~~~~~~

`These` ma instancje typeklas

-   `Monad`
-   `Bitraverse`
-   `Traverse`
-   `Cobind`

oraz zależnie od zawartości

-   `Semigroup` / `Monoid` / `Band`
-   `Equal` / `Order`
-   `Show`

`These` (`\&/`) ma też wiele metod, których oczekiwalibyśmy od `Disjunction` (`\/`) i `Validation` (`\?/`)

{lang="text"}
~~~~~~~~
  sealed abstract class \&/[+A, +B] {
    def fold[X](s: A => X, t: B => X, q: (A, B) => X): X = ...
    def swap: (B \&/ A) = ...
  
    def append[X >: A: Semigroup, Y >: B: Semigroup](o: =>(X \&/ Y)): X \&/ Y = ...
  
    def &&&[X >: A: Semigroup, C](t: X \&/ C): X \&/ (B, C) = ...
    ...
  }
~~~~~~~~

`.append` ma 9 możliwych ułożeń i dane nigdy nie są tracone, ponieważ `This` i `That` mogą być zawsze
zamienione w `Both`.

`.flatMap` jest prawostronna (`Both` i `That`), przyjmując `Semigroup`y dla strony lewej (`This`), tak aby
móc połączyć zawartości zamiast je porzucać. Metoda `&&&` jest pomocna, gdy chcemy połączyć dwie instancje 
`\&/`, tworząc tuple z prawej strony i porzucając tę stronę zupełnie jeśli nie jest wypełniona w obu instancjach.

Mimo że zwracanie typu `\&/` z naszych funkcji jest kuszące, to jego nadużywanie to antywzorzec.
Głównym powodem dla używania `\&/` jest łączenie i dzielenie potencjalnie nieskończonych *strumieni* danych w 
skończonej pamięci. Dlatego też dostajemy do dyspozycji kilka przydatnych funkcji do operowania na `EphemeralStream`
(zaliasowanym tutaj, aby zmieścić się w jednej linii) lub czymkolwiek z instancją `MonadPlus`

{lang="text"}
~~~~~~~~
  type EStream[A] = EphemeralStream[A]
  
  object \&/ {
    def concatThisStream[A, B](x: EStream[A \&/ B]): EStream[A] = ...
    def concatThis[F[_]: MonadPlus, A, B](x: F[A \&/ B]): F[A] = ...
  
    def concatThatStream[A, B](x: EStream[A \&/ B]): EStream[B] = ...
    def concatThat[F[_]: MonadPlus, A, B](x: F[A \&/ B]): F[B] = ...
  
    def unalignStream[A, B](x: EStream[A \&/ B]): (EStream[A], EStream[B]) = ...
    def unalign[F[_]: MonadPlus, A, B](x: F[A \&/ B]): (F[A], F[B]) = ...
  
    def merge[A: Semigroup](t: A \&/ A): A = ...
    ...
  }
~~~~~~~~


### Either Wyższego Rodzaju

Typ danych `Coproduct` (nie mylić z bardziej ogólnym pojęciem *koproduktu* w ADT) opakowuje `Disjunction`
dla konstruktorów typu:

{lang="text"}
~~~~~~~~
  final case class Coproduct[F[_], G[_], A](run: F[A] \/ G[A]) { ... }
  object Coproduct {
    def leftc[F[_], G[_], A](x: F[A]): Coproduct[F, G, A] = Coproduct(-\/(x))
    def rightc[F[_], G[_], A](x: G[A]): Coproduct[F, G, A] = Coproduct(\/-(x))
    ...
  }
~~~~~~~~

Instancje typeklas po prostu delegują do instancji zdefiniowanych dla `F[_]` i `G[_]`.

Najpopularniejszym przypadkiem, w którym zastosowanie znajduje `Coproduct`, to sytuacja, gdy chcemy
stworzyć anonimowy koprodukt wielu ADT.


### Nie Tak Szybko

Wbudowane w Scalę tuple oraz podstawowe typy danych takie jak `Maybe` lub `Disjunction` są ewaluowane zachłannie 
(_eagerly-evaluated_).

Dla wygody zdefiniowane zostały warianty leniwe, mające instancje oczekiwanych typeklas:

{lang="text"}
~~~~~~~~
  sealed abstract class LazyTuple2[A, B] {
    def _1: A
    def _2: B
  }
  ...
  sealed abstract class LazyTuple4[A, B, C, D] {
    def _1: A
    def _2: B
    def _3: C
    def _4: D
  }
  
  sealed abstract class LazyOption[+A] { ... }
  private final case class LazySome[A](a: () => A) extends LazyOption[A]
  private case object LazyNone extends LazyOption[Nothing]
  
  sealed abstract class LazyEither[+A, +B] { ... }
  private case class LazyLeft[A, B](a: () => A) extends LazyEither[A, B]
  private case class LazyRight[A, B](b: () => B) extends LazyEither[A, B]
~~~~~~~~

Wnikliwy czytelnik zauważy, że przedrostek `Lazy` jest nie do końca poprawny, a nazwy tych typów danych 
prawdopodobnie powinny brzmieć: `ByNameTupleX`, `ByNameOption` i `ByNameEither`.


### Const

`Const`, zawdzięczający nazwę angielskiemu *constant*, czyli *stała*, jest opakowaniem na wartość typu `A`, razem
z nieużywanym parametrem typu `B`.

{lang="text"}
~~~~~~~~
  final case class Const[A, B](getConst: A)
~~~~~~~~

`Const` dostarcza instancję `Applicative[Const[A, ?]]` jeśli tylko dostępny jest `Monoid[A]`:

{lang="text"}
~~~~~~~~
  implicit def applicative[A: Monoid]: Applicative[Const[A, ?]] =
    new Applicative[Const[A, ?]] {
      def point[B](b: =>B): Const[A, B] =
        Const(Monoid[A].zero)
      def ap[B, C](fa: =>Const[A, B])(fbc: =>Const[A, B => C]): Const[A, C] =
        Const(fbc.getConst |+| fa.getConst)
    }
~~~~~~~~

Najważniejszą własnością tej instancji jest to, że ignoruje parametr `B`, łącząc wartości typu `A`, które napotka.

Wracając do naszej aplikacji `drone-dynamic-agents`, powinniśmy najpierw zrefaktorować plik `logic.scala`, tak aby używał
`Applicative` zamiast `Monad`. Poprzednią implementację stworzyliśmy zanim jeszcze dowiedzieliśmy się czym jest
`Applicative`. Teraz wiemy jak zrobić to lepiej:


{lang="text"}
~~~~~~~~
  final class DynAgentsModule[F[_]: Applicative](D: Drone[F], M: Machines[F])
    extends DynAgents[F] {
    ...
    def act(world: WorldView): F[WorldView] = world match {
      case NeedsAgent(node) =>
        M.start(node) >| world.copy(pending = Map(node -> world.time))
  
      case Stale(nodes) =>
        nodes.traverse { node =>
          M.stop(node) >| node
        }.map { stopped =>
          val updates = stopped.strengthR(world.time).toList.toMap
          world.copy(pending = world.pending ++ updates)
        }
  
      case _ => world.pure[F]
    }
    ...
  }
~~~~~~~~

Skoro nasza logika biznesowa wymaga teraz jedynie `Applicative`, możemy zaimplementować nasz mock `F[a]` jako 
`Const[String, a]`. W każdym z przypadków zwracamy nazwę funkcji która została wywołana:

{lang="text"}
~~~~~~~~
  object ConstImpl {
    type F[a] = Const[String, a]
  
    private val D = new Drone[F] {
      def getBacklog: F[Int] = Const("backlog")
      def getAgents: F[Int]  = Const("agents")
    }
  
    private val M = new Machines[F] {
      def getAlive: F[Map[MachineNode, Epoch]]     = Const("alive")
      def getManaged: F[NonEmptyList[MachineNode]] = Const("managed")
      def getTime: F[Epoch]                        = Const("time")
      def start(node: MachineNode): F[Unit]        = Const("start")
      def stop(node: MachineNode): F[Unit]         = Const("stop")
    }
  
    val program = new DynAgentsModule[F](D, M)
  }
~~~~~~~~

Z taką interpretacją naszego programu możemy zweryfikować metody, które są używane:

{lang="text"}
~~~~~~~~
  it should "call the expected methods" in {
    import ConstImpl._
  
    val alive    = Map(node1 -> time1, node2 -> time1)
    val world    = WorldView(1, 1, managed, alive, Map.empty, time4)
  
    program.act(world).getConst shouldBe "stopstop"
  }
~~~~~~~~

Alternatywnie, moglibyśmy zliczyć ilość wywołań za pomocą `Const[Int, ?]` lub `IMap[String, Int]`.

W tym teście zrobiliśmy krok dalej poza tradycyjne testowanie z użyciem *Mocków*. `Const` pozwolił nam
sprawdzić co zostało wywołane bez dostarczania faktycznej implementacji. Podejście takie jest użyteczne
kiedy specyfikacja wymaga od nas, abyśmy wykonali konkretne wywołania w odpowiedzi na dane wejście. 
Dodatkowo, osiągnęliśmy to zachowując bezpieczeństwo w czasie kompilacji.

Idąc dalej tym tokiem myślenia, powiedzmy, że chcielibyśmy monitorować (w środowisku produkcyjnym) węzły,
które zatrzymywane są w metodzie `act`. Możemy stworzyć implementacje `Drone` i `Machines` używając `Const` i 
zawołać je z naszej opakowanej wersji `act`

{lang="text"}
~~~~~~~~
  final class Monitored[U[_]: Functor](program: DynAgents[U]) {
    type F[a] = Const[Set[MachineNode], a]
    private val D = new Drone[F] {
      def getBacklog: F[Int] = Const(Set.empty)
      def getAgents: F[Int]  = Const(Set.empty)
    }
    private val M = new Machines[F] {
      def getAlive: F[Map[MachineNode, Epoch]]     = Const(Set.empty)
      def getManaged: F[NonEmptyList[MachineNode]] = Const(Set.empty)
      def getTime: F[Epoch]                        = Const(Set.empty)
      def start(node: MachineNode): F[Unit]        = Const(Set.empty)
      def stop(node: MachineNode): F[Unit]         = Const(Set(node))
    }
    val monitor = new DynAgentsModule[F](D, M)
  
    def act(world: WorldView): U[(WorldView, Set[MachineNode])] = {
      val stopped = monitor.act(world).getConst
      program.act(world).strengthR(stopped)
    }
  }
~~~~~~~~

Możemy to zrobić, ponieważ `monitor` jest *czysty* i uruchomienie go nie produkuje żadnych efektów ubocznych.

Poniższy fragment uruchamia program z `ConstImpl`, ekstrahując wszystkie wywołania do `Machines.stop` i zwracając
wszystkie zatrzymane węzły razem `WoldView`

{lang="text"}
~~~~~~~~
  it should "monitor stopped nodes" in {
    val underlying = new Mutable(needsAgents).program
  
    val alive = Map(node1 -> time1, node2 -> time1)
    val world = WorldView(1, 1, managed, alive, Map.empty, time4)
    val expected = world.copy(pending = Map(node1 -> time4, node2 -> time4))
  
    val monitored = new Monitored(underlying)
    monitored.act(world) shouldBe (expected -> Set(node1, node2))
  }
~~~~~~~~

Użyliśmy `Const`, aby zrobić coś co przypomina niegdyś popularne w Javie *Programowanie Aspektowe*. 
Na bazie naszej logiki biznesowej zaimplementowaliśmy monitoring nie komplikując tej logiki w żaden sposób.

A będzie jeszcze lepiej. Moglibyśmy uruchomić `ConstImpl` w środowisku produkcyjnym, aby zebrać informacje
o tym co ma zostać zatrzymane, a następnie dostarczyć **zoptymalizowaną** implementację korzystającą
ze specyficznych dla implementacji wywołań batchowych.

Cichym bohaterem tej opowieści jest `Applicative`, a `Const` pozwala nam pokazać co jest dzięki niemu możliwe.
Jeśli musielibyśmy zmienić nasz program tak, aby wymagał `Monad`y, nie moglibyśmy wtedy użyć `Const`, a zamiast tego zmuszeni 
bylibyśmy do napisania pełnoprawnych mocków, aby zweryfikować jakie funkcje zostały wywołane dla danych argumentów.
*Reguła Najmniejszej Mocy* (_Rule of Least Power_) wymaga od nas, abyśmy używali `Applicative` zamiast `Monad` kiedy tylko możemy.


## Kolekcje

W przeciwieństwie do Collections API z biblioteki standardowej, Scalaz opisuje zachowanie kolekcji
za pomocą hierarchii typeklas, np. `Foldable`, `Traverse`, `Monoid`. Co pozostaje do przeanalizowania, to 
konkretne struktury danych, ich charakterystyki wydajnościowe i wyspecjalizowane metody.

Ten podrozdział wnika w szczegóły implementacyjne każdego typu danych. Nie musimy zapamiętać wszystkiego, celem 
jest zrozumieć jak działa każda ze struktur jedynie w ogólności.

Ponieważ wszystkie kolekcje dostarczają instancje mniej więcej tych samych typeklas, nie będziemy ich powtarzać.
W większości przypadków jest to pewna wariacja poniższej listy.

-   `Monoid`
-   `Traverse` / `Foldable`
-   `MonadPlus` / `IsEmpty`
-   `Cobind` / `Comonad`
-   `Zip` / `Unzip`
-   `Align`
-   `Equal` / `Order`
-   `Show`

Struktury danych, które nigdy nie są puste dostarczają 

-   `Traverse1` / `Foldable1`

oraz `Semigroup` zamiast `Monoid` i `Plus` zamiast `IsEmpty`.


### Listy

Używaliśmy `IList[A]` i `NonEmptyList[A]` tyle razy, że powinny już być nam znajome. 
Reprezentują on ideę klasycznej, jedno-połączeniowej listy:

{lang="text"}
~~~~~~~~
  sealed abstract class IList[A] {
    def ::(a: A): IList[A] = ...
    def :::(as: IList[A]): IList[A] = ...
    def toList: List[A] = ...
    def toNel: Option[NonEmptyList[A]] = ...
    ...
  }
  final case class INil[A]() extends IList[A]
  final case class ICons[A](head: A, tail: IList[A]) extends IList[A]
  
  final case class NonEmptyList[A](head: A, tail: IList[A]) {
    def <::(b: A): NonEmptyList[A] = nel(b, head :: tail)
    def <:::(bs: IList[A]): NonEmptyList[A] = ...
    ...
  }
~~~~~~~~

A> Kod źródłowy Scalaz 7.3 ujawnia, że `INil` jest zaimplementowany jako
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   sealed abstract case class INil[A] private() extends IList[A]
A>   object INil {
A>     private[this] val value: INil[Nothing] = new INil[Nothing]{}
A>     def apply[A](): IList[A] = value.asInstanceOf[IList[A]]
A>   }
A> ~~~~~~~~
A> 
A> wykorzystując detale implementacyjne JVMa, aby uniknąć alokacji tworząc `INil`.
A> 
A> Taka optymalizacja jest ręcznie aplikowana do wszystkich bezparametrowych klas.
A> W praktyce Scalaz pełna jest podobnych optymalizacji, ale wszystkie są wcześniej
A> omawiane i wprowadzane tylko w oparciu o dowody na istotny wzrost wydajności przy pełnym zachowaniu
A> semantyki.

Główną zaletą `IList` nad `List` jest brak niebezpiecznych metod, takich jak `.head` (jest ona niebezpieczna, gdyż wyrzuca wyjątek 
w przypadku pustej kolekcji).

Dodatkowo, `IList` jest **dużo** prostsza, gdyż nie jest częścią hierarchii, oraz zużywa zdecydowanie mniej 
pamięci. Ponadto, `List` z biblioteki standardowej ma przerażająca implementację, używającą `var`, aby obejść
problemy wydajnościowe:

{lang="text"}
~~~~~~~~
  package scala.collection.immutable
  
  sealed abstract class List[+A]
    extends AbstractSeq[A]
    with LinearSeq[A]
    with GenericTraversableTemplate[A, List]
    with LinearSeqOptimized[A, List[A]] { ... }
  case object Nil extends List[Nothing] { ... }
  final case class ::[B](
    override val head: B,
    private[scala] var tl: List[B]
  ) extends List[B] { ... }
~~~~~~~~

Tworzenie instancji `List` wymaga ostrożnej, i powolnej, synchronizacji wątków, aby zapewnić
bezpieczne publikowanie. `IList` nie ma żadnych tego typu wymagań, a więc może przegonić `List` pod względem wydajności.

A> Czy `NonEmptyList` to nie po prostu `ICons`? Tak, ale tylko na poziomie struktur danych.
A> Różnica polega na tym, że `ICons` jest częścią ADT `IList`, a `NonEmptyList` nie. Instancje typeklas powinny
A> być zawsze definiowane na poziomie ADT, a nie pojedynczych wariantów, aby uniknąć zbędnej złożoności.


### `EphemeralStream`

`Stream` z biblioteki standardowej jest leniwą wersją `List`y, ale obarczoną wyciekami pamięci i niebezpiecznymi
metodami. `EphemeralStream` nie przetrzymuje referencji do wyliczonych wartości, łagodząc problemy z przetrzymywaniem
pamięci. Jednocześnie pozbawiony jest niebezpiecznych metod, tak jak `Ilist`.

{lang="text"}
~~~~~~~~
  sealed abstract class EphemeralStream[A] {
    def headOption: Option[A]
    def tailOption: Option[EphemeralStream[A]]
    ...
  }
  // private implementations
  object EphemeralStream extends EphemeralStreamInstances {
    type EStream[A] = EphemeralStream[A]
  
    def emptyEphemeralStream[A]: EStream[A] = ...
    def cons[A](a: =>A, as: =>EStream[A]): EStream[A] = ...
    def unfold[A, B](start: =>B)(f: B => Option[(A, B)]): EStream[A] = ...
    def iterate[A](start: A)(f: A => A): EStream[A] = ...
  
    implicit class ConsWrap[A](e: =>EStream[A]) {
      def ##::(h: A): EStream[A] = cons(h, e)
    }
    object ##:: {
      def unapply[A](xs: EStream[A]): Option[(A, EStream[A])] =
        if (xs.isEmpty) None
        else Some((xs.head(), xs.tail()))
    }
    ...
  }
~~~~~~~~

A> Używanie słowa *strumień* (_stream_) dla struktur danych podobnej natury powoli staje się przestarzałe. *Strumienie*
A> są teraz używane wraz z ✨ *Reactive Manifesto* ✨ przez działy marketingu oraz we frameworkach, takich jak Akka Streams.

`.cons`, `.unfold` i `.iterate` to mechanizmy do tworzenia strumieni. `##::` (a więc i `cons`) umieszcza nowy element na 
początku `EStream`u przekazanego przez nazwę. `.unfold` służy do tworzenia skończonych (lecz potencjalnie nieskończonych)
strumieni poprzez ciągłe wywoływanie funkcji `f` zwracającej następną wartość oraz wejście do swojego kolejnego wywołania.
`.iterate` tworzy nieskończony strumień za pomocą funkcji `f` wywoływanej na poprzednim jego elemencie.

`EStream` może pojawiać się w wyrażeniach pattern matchingu z użyciem symbolu `##::`.

A> `##::` wygląda trochę jak Exogorth: gigantyczny kosmiczny robak żyjący na asteroidach.

Mimo że `EStream` rozwiązuje problem przetrzymywania pamięci, nadal możemy ucierpieć z powodu 
*powolnych wycieków pamięci*, jeśli żywa referencja wskazuje na czoło nieskończonego strumienia. 
Problemy tej natury, oraz potrzeba komponowania strumieni wywołujących efekty uboczne są powodem, dla którego
istnieje biblioteka fs2.


### `CorecursiveList`

*Korekursja* (_Corecursion_) ma miejsce, gdy zaczynamy ze stanu bazowego i deterministycznie produkujemy kolejne stany
przejściowe, tak jak miało to miejsce w metodzie `EphemeralStream.unfold`, którą niedawno omawialiśmy:

{lang="text"}
~~~~~~~~
  def unfold[A, B](b: =>B)(f: B => Option[(A, B)]): EStream[A] = ...
~~~~~~~~

Jest to działanie odwrotne do *rekursji*, która rozbija dane do stanu bazowego i kończy działanie.

`CorecursiveList` to struktura danych wyrażająca `EphemeralStream.unfold` i będąca alternatywą dla `EStream`, która
może być wydajniejsza w niektórych przypadkach:

{lang="text"}
~~~~~~~~
  sealed abstract class CorecursiveList[A] {
    type S
    def init: S
    def step: S => Maybe[(S, A)]
  }
  
  object CorecursiveList {
    private final case class CorecursiveListImpl[S0, A](
      init: S0,
      step: S0 => Maybe[(S0, A)]
    ) extends CorecursiveList[A] { type S = S0 }
  
    def apply[S, A](init: S)(step: S => Maybe[(S, A)]): CorecursiveList[A] =
      CorecursiveListImpl(init, step)
  
    ...
  }
~~~~~~~~

Korekursja jest przydatna, gdy implementujemy `Comonad.cojoin`, jak w naszym przykładzie z `Hood`.
`CorecursiveList` to dobry sposób na wyrażenie nieliniowych równań rekurencyjnych, jak te używane w 
biologicznych modelach populacji, systemach kontroli, makroekonomii i modelach bankowości inwestycyjnej.


### `ImmutableArray`

Czyli proste opakowanie na mutowalną tablicę (`Array`) z biblioteki standardowej, ze specjalizacją
dla typów prymitywnych:

{lang="text"}
~~~~~~~~
  sealed abstract class ImmutableArray[+A] {
    def ++[B >: A: ClassTag](o: ImmutableArray[B]): ImmutableArray[B]
    ...
  }
  object ImmutableArray {
    final class StringArray(s: String) extends ImmutableArray[Char] { ... }
    sealed class ImmutableArray1[+A](as: Array[A]) extends ImmutableArray[A] { ... }
    final class ofRef[A <: AnyRef](as: Array[A]) extends ImmutableArray1[A](as)
    ...
    final class ofLong(as: Array[Long]) extends ImmutableArray1[Long](as)
  
    def fromArray[A](x: Array[A]): ImmutableArray[A] = ...
    def fromString(str: String): ImmutableArray[Char] = ...
    ...
  }
~~~~~~~~

Typ `Array` jest bezkonkurencyjny jeśli chodzi prędkość odczytu oraz wielkość stosu. Jednak
nie występuje tutaj w ogóle współdzielenie strukturalne, więc niemutowalne tablice używane są zwykle tylko, gdy
ich zawartość nie ulega zmianie lub jako sposób na bezpieczne owinięcie danych pochodzących z zastanych
części systemu.


### `Dequeue`

`Dequeue` (wymawiana jak talia kart - "deck") to połączona lista, która pozwala na dodawanie i odczytywanie 
elementów z przodu (`cons`) lub tyłu (`snoc`) w stałym czasie. Usuwania elementów z obu końców jest 
stałe statystycznie.

{lang="text"}
~~~~~~~~
  sealed abstract class Dequeue[A] {
    def frontMaybe: Maybe[A]
    def backMaybe: Maybe[A]
  
    def ++(o: Dequeue[A]): Dequeue[A] = ...
    def +:(a: A): Dequeue[A] = cons(a)
    def :+(a: A): Dequeue[A] = snoc(a)
    def cons(a: A): Dequeue[A] = ...
    def snoc(a: A): Dequeue[A] = ...
    def uncons: Maybe[(A, Dequeue[A])] = ...
    def unsnoc: Maybe[(A, Dequeue[A])] = ...
    ...
  }
  private final case class SingletonDequeue[A](single: A) extends Dequeue[A] { ... }
  private final case class FullDequeue[A](
    front: NonEmptyList[A],
    fsize: Int,
    back: NonEmptyList[A],
    backSize: Int) extends Dequeue[A] { ... }
  private final case object EmptyDequeue extends Dequeue[Nothing] { ... }
  
  object Dequeue {
    def empty[A]: Dequeue[A] = EmptyDequeue()
    def apply[A](as: A*): Dequeue[A] = ...
    def fromFoldable[F[_]: Foldable, A](fa: F[A]): Dequeue[A] = ...
    ...
  }
~~~~~~~~

Implementacja bazuje na dwóch listach, jednej dla danych początkowych, drugiej dla końcowych.
Rozważmy instancję przechowującą symbole `a0, a1, a2, a3, a4, a5, a6`

{lang="text"}
~~~~~~~~
  FullDequeue(
    NonEmptyList('a0, IList('a1, 'a2, 'a3)), 4,
    NonEmptyList('a6, IList('a5, 'a4)), 3)
~~~~~~~~

która może być zobrazowana jako

{width=30%}
![](images/dequeue.png)

Zauważ, że lista przechowująca `back` jest w odwróconej kolejności.

Odczyt `snoc` (element końcowy) to proste spojrzenie na `back.head`. Dodanie elementu na koniec `Dequeue` oznacza
dodanie go na początek `back` i stworzenie nowego `FullDequeue` (co zwiększy `backSize` o jeden). Prawie 
cała oryginalna struktura jest współdzielona. Porównaj to z dodaniem nowego elementu na koniec `IList`, co wymaga
stworzenia na nowo całej struktury.

`frontSize` i `backSize` są używane do zbalansowywania `front` i `back`, tak, aby zawsze były podobnych rozmiarów.
Balansowanie oznacza, że niektóre operacje mogą być wolniejsze od innych (np. gdy cała struktura musi być przebudowana),
ale ponieważ dzieje się to okazjonalnie możemy ten koszt uśrednić i powiedzieć, że jest stały.


### `DList`

Zwykłe listy mają kiepską wydajność, gdy duże listy są ze sobą łączone. Rozważmy koszt wykonania poniższej operacji:

{lang="text"}
~~~~~~~~
  ((as ::: bs) ::: (cs ::: ds)) ::: (es ::: (fs ::: gs))
~~~~~~~~

{width=50%}
![](images/dlist-list-append.png)

Tworzonych jest 6 list pośrednich, przechodząc i przebudowując każdą z list trzy krotnie (oprócz `gs`, która jest współdzielona
na wszystkich etapach).

`DList` (od *difference list*, listy różnic) jest bardziej wydajnym rozwiązaniem dla tego scenariusza. Zamiast 
wykonywać obliczenia na każdym z etapów wynik reprezentowany jest jako `IList[A] => IList[A]`.

{lang="text"}
~~~~~~~~
  final case class DList[A](f: IList[A] => IList[A]) {
    def toIList: IList[A] = f(IList.empty)
    def ++(as: DList[A]): DList[A] = DList(xs => f(as.f(xs)))
    ...
  }
  object DList {
    def fromIList[A](as: IList[A]): DList[A] = DList(xs => as ::: xs)
  }
~~~~~~~~

A> Jest to implementacja uproszczona, zawierająca błąd powodujący przepełnienie stosu, którym zajmiemy się
A> w rozdziale poświęconym Zaawansowanym Monadom.

Odpowiednikiem naszych obliczeń jest (symbole muszą zostać stworzone za pomocą `DList.fromIList`)

{lang="text"}
~~~~~~~~
  (((a ++ b) ++ (c ++ d)) ++ (e ++ (f ++ g))).toIList
~~~~~~~~

gdzie praca podzielona jest na *prawostronne* (czyli szybkie) złączenia

{lang="text"}
~~~~~~~~
  (as ::: (bs ::: (cs ::: (ds ::: (es ::: (fs ::: gs))))))
~~~~~~~~

wykorzystując szybki konstruktor na `IList`.

Jak zawsze, nie ma nic za darmo. Występuje tu narzut związany z alokacją pamięci, który może spowolnić
nasz kod, jeśli ten i tak zakładał prawostronne złączenia. Największe przyspieszenie uzyskamy, gdy operacje są lewostronne, np.: 

{lang="text"}
~~~~~~~~
  ((((((as ::: bs) ::: cs) ::: ds) ::: es) ::: fs) ::: gs)
~~~~~~~~

Lista różnic cierpi z powodu kiepskiego marketingu. Najprawdopodobniej znalazłaby się w bibliotece standardowej, gdyby 
tylko nazywała się `ListBuilderFactory`.


### `ISet`

Struktury drzewiaste są doskonałe do przechowywania uporządkowanych danych, tak aby każdy *węzeł binarny*
przechowywał elementy od niego *mniejsze* w jednej gałęzi, a *większe* w drugiej. Jednak naiwna implementacja
takie struktury może w łatwy sposób stać się niesymetryczna, zależnie od kolejności dodawanie elementów. Możliwym jest
utrzymywanie perfekcyjnie zbalansowanego drzewa, ale jest to niewiarygodnie nieefektywne, ponieważ każde wstawienie
elementu do drzewa powodowałoby jego pełne przebudowanie.

`ISet` to implementacja drzewa z *ograniczoną równowagą* (_bounded balance_), co oznacza, że jest ono zrównoważone
w przybliżeniu, używając `size` każdej gałęzi do równoważenia węzła.

{lang="text"}
~~~~~~~~
  sealed abstract class ISet[A] {
    val size: Int = this match {
      case Tip()        => 0
      case Bin(_, l, r) => 1 + l.size + r.size
    }
    ...
  }
  object ISet {
    private final case class Tip[A]() extends ISet[A]
    private final case class Bin[A](a: A, l: ISet[A], r: ISet[A]) extends ISet[A]
  
    def empty[A]: ISet[A] = Tip()
    def singleton[A](x: A): ISet[A] = Bin(x, Tip(), Tip())
    def fromFoldable[F[_]: Foldable, A: Order](xs: F[A]): ISet[A] =
      xs.foldLeft(empty[A])((a, b) => a insert b)
    ...
  }
~~~~~~~~

`ISet` wymaga, aby `A` miało instancję typeklasy `Order` oraz musi ona pozostawać taka sama pomiędzy wywołaniami, 
gdyż inaczej zaburzone zostaną wewnętrzne założenia, prowadząc tym samym do uszkodzenia danych. Innymi słowy, 
zakładamy spójność typeklas, a więc dla dowolnego `A` istnieje tylko jedna instancja `Order[A]`.

ADT `ISet`u niestety pozwala na wyrażenie niepoprawnych drzew. Staramy się pisać ADT tak, aby
w pełni opisywały co jest i nie jest możliwe poprzez restrykcję typów, ale nie zawsze jest to możliwe.
Zamiast tego `Tip` i `Bin`  są prywatne, powstrzymując użytkowników przed przypadkowym niepoprawnych drzew.
`.insert` jest jedynym sposobem na konstrukcję drzew, definiując tym samym jak wygląda poprawna jego forma.

{lang="text"}
~~~~~~~~
  sealed abstract class ISet[A] {
    ...
    def contains(x: A)(implicit o: Order[A]): Boolean = ...
    def union(other: ISet[A])(implicit o: Order[A]): ISet[A] = ...
    def delete(x: A)(implicit o: Order[A]): ISet[A] = ...
  
    def insert(x: A)(implicit o: Order[A]): ISet[A] = this match {
      case Tip() => ISet.singleton(x)
      case self @ Bin(y, l, r) => o.order(x, y) match {
        case LT => balanceL(y, l.insert(x), r)
        case GT => balanceR(y, l, r.insert(x))
        case EQ => self
      }
    }
    ...
  }
~~~~~~~~

Wewnętrzne metody `.balanceL` i `.balanceR` są swoimi lustrzanymi odbiciami, a więc przestudiujemy jedynie
`.balanceL`, która jest wywoływana, gdy dodawana wartość jest *mniejsza* niż aktualny węzeł. Jest ona również
wołana przez metodę `.delete`.

{lang="text"}
~~~~~~~~
  def balanceL[A](y: A, left: ISet[A], right: ISet[A]): ISet[A] = (left, right) match {
  ...
~~~~~~~~

Równoważenie wymaga, abyśmy sklasyfikowali scenariusze, które mogą się zdarzyć. Przejdziemy przez nie kolejno, 
wizualizując `(y, left, right)` po lewej stronie i wersją zbalansowaną (znaną tez jako *drzewo obrócone*, 
_rotated tree_) po prawej.

-   wypełnione koła obrazują `Tip`
-   trzy kolumny to `left | value | right` pochodzące z `Bin`
-   diamenty wizualizują dowolny `ISet`

Pierwszy scenariusz jest trywialny i zachodzi, gdy obie strony to `Tip`y. Nigdy nie napotkamy tego scenariusza wykonując
`.insert`, ale może on wystąpić przy `.delete`

{lang="text"}
~~~~~~~~
  case (Tip(), Tip()) => singleton(y)
~~~~~~~~

{width=50%}
![](images/balanceL-1.png)

Drugi przypadek ma miejsce kiedy lewa strona to `Bin` zawierający jedynie `Tip`. Nie musimy nic równoważyć, dodajemy 
jedynie oczywiste połączenie:

{lang="text"}
~~~~~~~~
  case (Bin(lx, Tip(), Tip()), Tip()) => Bin(y, left, Tip())
~~~~~~~~

{width=60%}
![](images/balanceL-2.png)

Przy trzecim scenariuszu zaczyna robić się interesująco: lewa strona to `Bin` zawierający
`Bin` po swojej prawej stronie.

{lang="text"}
~~~~~~~~
  case (Bin(lx, Tip(), Bin(lrx, _, _)), Tip()) =>
    Bin(lrx, singleton(lx), singleton(y))
~~~~~~~~

{width=70%}
![](images/balanceL-3.png)

Ale co z dwoma diamentami poniżej `lrx`? Czy nie utraciliśmy właśnie informacji? Nie, nie utraciliśmy, ponieważ
możemy wnioskować (na podstawie równoważenia wielkości), że są one zawsze puste (`Tip`). Nie istnieje żadna reguła
w naszych scenariuszach, która pozwala na wyprodukowanie drzewa, w którym którykolwiek z tych węzłów to `Bin`.

Czwarty przypadek jest przeciwieństwem trzeciego.

{lang="text"}
~~~~~~~~
  case (Bin(lx, ll, Tip()), Tip()) => Bin(lx, ll, singleton(y))
~~~~~~~~

{width=70%}
![](images/balanceL-4.png)

W scenariuszu piątym mamy do czynienia z pełnymi drzewami po obu stronach `left` i musimy oprzeć
decyzję o dalszych krokach na ich wielkości.

{lang="text"}
~~~~~~~~
  case (Bin(lx, ll, lr), Tip()) if (2*ll.size > lr.size) =>
    Bin(lx, ll, Bin(y, lr, Tip()))
  case (Bin(lx, ll, Bin(lrx, lrl, lrr)), Tip()) =>
    Bin(lrx, Bin(lx, ll, lrl), Bin(y, lrr, Tip()))
~~~~~~~~

Dla pierwszej gałęzi, `2*ll.size > lr.size`

{width=50%}
![](images/balanceL-5a.png)

a dla drugiej, `2*ll.size <= lr.size`

{width=75%}
![](images/balanceL-5b.png)

Szósty przypadek wprowadza drzewo po prawej stronie. Gdy `left` jest puste tworzymy oczywiste połączenie. 
Taka sytuacja nigdy nie pojawia się w wyniku `.insert` ponieważ `left` jest zawsze pełne:

{lang="text"}
~~~~~~~~
  case (Tip(), r) => Bin(y, Tip(), r)
~~~~~~~~

{width=50%}
![](images/balanceL-6.png)

Ostatni scenariusz zachodzi, gdy mamy pełne drzewa po obu stronach. Jeśli `left` jest mniejszy niż 
trzykrotność `right`, możemy po prostu stworzyć nowy `Bin`.

{lang="text"}
~~~~~~~~
  case _ if l.size <= 3 * r.size => Bin(y, l, r)
~~~~~~~~

{width=50%}
![](images/balanceL-7a.png)

Jednak gdy ten warunek nie jest spełniony i `left` jest większy od `right` więcej niż trzykrotnie, musimy
zrównoważyć drzewa jak w przypadku piątym.

{lang="text"}
~~~~~~~~
  case (Bin(lx, ll, lr), r) if (2*ll.size > lr.size) =>
    Bin(lx, ll, Bin(y, lr, r))
  case (Bin(lx, ll, Bin(lrx, lrl, lrr)), r) =>
    Bin(lrx, Bin(lx, ll, lrl), Bin(y, lrr, r))
~~~~~~~~

{width=60%}
![](images/balanceL-7b.png)

{width=75%}
![](images/balanceL-7c.png)

Tym samym doszliśmy do końca analizy metody `.insert` i tego jak tworzony jest `ISet`. Nie powinno dziwić, że
`Foldable` jest zaimplementowany w oparciu o przeszukiwanie-w-głąb. Metody takie jak `.minimum` i `.maximum`
są optymalne, gdyż struktura danych bazuje na uporządkowaniu elementów.

Warto zaznaczyć, że niektóre metody *nie mogą* być zaimplementowane tak wydajnie jak byśmy chcieli. Rozważmy
sygnaturę `Foldable.element`

{lang="text"}
~~~~~~~~
  @typeclass trait Foldable[F[_]] {
    ...
    def element[A: Equal](fa: F[A], a: A): Boolean
    ...
  }
~~~~~~~~

Oczywistą implementacją `.element` jest użyć przeszukiwania (prawie) binarnego `ISet.contains`.
Jednak nie jest to możliwe, gdyż `.element` dostarcza `Equal`, a `.contains` wymaga instancji `Order`.

Z tego samego powodu `ISet` nie jest w stanie dostarczyć instancji typeklasy `Functor`, co w praktyce okazuje się
sensownym ograniczeniem: wykonanie `.map` powodowałoby przebudowanie całej struktury. Rozsądnie jest przekonwertować
nasz zbiór do innego typu danych, na przykład `IList`, wykonać `.map` i przekonwertować wynik z powrotem. W konsekwencji
nie jesteśmy w stanie uzyskać `Traverse[ISet]` ani `Applicative[ISet]`.


### `IMap`

{lang="text"}
~~~~~~~~
  sealed abstract class ==>>[A, B] {
    val size: Int = this match {
      case Tip()           => 0
      case Bin(_, _, l, r) => 1 + l.size + r.size
    }
  }
  object ==>> {
    type IMap[A, B] = A ==>> B
  
    private final case class Tip[A, B]() extends (A ==>> B)
    private final case class Bin[A, B](
      key: A,
      value: B,
      left: A ==>> B,
      right: A ==>> B
    ) extends ==>>[A, B]
  
    def apply[A: Order, B](x: (A, B)*): A ==>> B = ...
  
    def empty[A, B]: A ==>> B = Tip[A, B]()
    def singleton[A, B](k: A, x: B): A ==>> B = Bin(k, x, Tip(), Tip())
    def fromFoldable[F[_]: Foldable, A: Order, B](fa: F[(A, B)]): A ==>> B = ...
    ...
  }
~~~~~~~~

Wygląda znajomo? W rzeczy samej, `IMap` (alias na operator prędkości światła `==>>`) to kolejne równoważone
drzewo, z tą różnicą, że każdy węzeł zawiera dodatkowe pole `value: B`, pozwalając na przechowywanie par klucz/wartość.
Instancja `Order` wymagana jest jedynie dla typu klucza `A`, a dodatkowo dostajemy zestaw przydatnych metod do aktualizowania 
wpisów

{lang="text"}
~~~~~~~~
  sealed abstract class ==>>[A, B] {
    ...
    def adjust(k: A, f: B => B)(implicit o: Order[A]): A ==>> B = ...
    def adjustWithKey(k: A, f: (A, B) => B)(implicit o: Order[A]): A ==>> B = ...
    ...
  }
~~~~~~~~


### `StrictTree` i `Tree`

Zarówno `StrictTree` jak i `Tree` to implementacje *Rose Tree*, drzewiastej struktury danych z nieograniczoną
ilością gałęzi w każdym węźle. Niestety, z powodów historycznych, zbudowane na bazie kolekcji z biblioteki standardowej...

{lang="text"}
~~~~~~~~
  case class StrictTree[A](
    rootLabel: A,
    subForest: Vector[StrictTree[A]]
  )
~~~~~~~~

`Tree` to leniwa (_by-need_) wersja `StrictTree` z wygodnymi konstruktorami

{lang="text"}
~~~~~~~~
  class Tree[A](
    rootc: Need[A],
    forestc: Need[Stream[Tree[A]]]
  ) {
    def rootLabel = rootc.value
    def subForest = forestc.value
  }
  object Tree {
    object Node {
      def apply[A](root: =>A, forest: =>Stream[Tree[A]]): Tree[A] = ...
    }
    object Leaf {
      def apply[A](root: =>A): Tree[A] = ...
    }
  }
~~~~~~~~

Użytkownik Rose Tree powinien sam zadbać o balansowanie drzewa, co jest odpowiednie, gdy chcemy
wyrazić hierarchiczną wiedzę domenową jako strukturę danych. Dla przykładu, w sztucznej inteligencji
Rose Tree może być użyte w [algorytmach klastrowania](https://arxiv.org/abs/1203.3468)
do organizacji danych w hierarchie coraz bardziej podobnych rzeczy. Możliwe jest również wyrażenie dokumentów XML
jako Rose Tree.

Pracując z danymi hierarchicznymi dobrze jest rozważyć tę strukturę danych zanim stworzymy swoją własną.

### `FingerTree`

Finger tree (drzewo-dłoń, drzewo palczaste?) to uogólniona sekwencja z zamortyzowanym stałym czasem dostępu do elementów i logarytmicznym
złączaniem. `A` to typ elementów, a `V` na razie zignorujemy:

{lang="text"}
~~~~~~~~
  sealed abstract class FingerTree[V, A] {
    def +:(a: A): FingerTree[V, A] = ...
    def :+(a: =>A): FingerTree[V, A] = ...
    def <++>(right: =>FingerTree[V, A]): FingerTree[V, A] = ...
    ...
  }
  object FingerTree {
    private class Empty[V, A]() extends FingerTree[V, A]
    private class Single[V, A](v: V, a: =>A) extends FingerTree[V, A]
    private class Deep[V, A](
      v: V,
      left: Finger[V, A],
      spine: =>FingerTree[V, Node[V, A]],
      right: Finger[V, A]
    ) extends FingerTree[V, A]
  
    sealed abstract class Finger[V, A]
    final case class One[V, A](v: V, a1: A) extends Finger[V, A]
    final case class Two[V, A](v: V, a1: A, a2: A) extends Finger[V, A]
    final case class Three[V, A](v: V, a1: A, a2: A, a3: A) extends Finger[V, A]
    final case class Four[V, A](v: V, a1: A, a2: A, a3: A, a4: A) extends Finger[V, A]
  
    sealed abstract class Node[V, A]
    private class Node2[V, A](v: V, a1: =>A, a2: =>A) extends Node[V, A]
    private class Node3[V, A](v: V, a1: =>A, a2: =>A, a3: =>A) extends Node[V, A]
    ...
  }
~~~~~~~~

A> `<++>` to bombowiec TIE, ale przyznajemy, że wysyłanie torped protonowych to lekka przesada.
A> Jego działanie jest takie same jak `|+|` czyli `Monoid`owego Myśliwca TIE.

Przedstawmy `FingerTree` jako kropki, `Finger` jako prostokąty, a `Node` jako prostokąty wewnątrz prostokątów:

{width=35%}
![](images/fingertree.png)

Dodanie elementy na początek `FingerTree` za pomocą `+:` jest wydajne, ponieważ `Deep` po prostu dodaje nowy element
do swojego lewego (`left`) palca. Jeśli palec to `Four`, to przebudowujemy `spine`, tak, aby przyjął 3 z tych 
elementów jako `Node3`. Dodawanie na koniec (`:+`) odbywa się tak samo, ale w odwrotnej kolejności.

Złączanie za pomocą `|+|` lub `<++>` jest bardziej wydajne niż dodawanie po jednym elemencie, ponieważ instancje `Deep` 
mogą zachować swoje zewnętrzne gałęzie przebudowując jedynie `spine`.

Do tej pory ignorowaliśmy `V`. Ukryliśmy też niejawny parametr obecny we wszystkich wariantach tego ADT: `implicit measurer: Reducer[A, V]`.

A> Przechowywanie instancji typeklas w ADT jest w kiepskim stylu, a dodatkowo zwiększa ilość wymaganej pamięci o 
A> 64 bity na każdy element. Implementacja `FingerTree` ma niemal dekadę na karku i nadaje się do przepisania.

`Reducer` to rozszerzenie typeklasy `Monoid` pozwalające na dodanie pojedynczych elementów do `M`

{lang="text"}
~~~~~~~~
  class Reducer[C, M: Monoid] {
    def unit(c: C): M
  
    def snoc(m: M, c: C): M = append(m, unit(c))
    def cons(c: C, m: M): M = append(unit(c), m)
  }
~~~~~~~~

Na przykład `Reducer[A, IList[A]]` może zapewnić wydajną implementację `.cons`

{lang="text"}
~~~~~~~~
  implicit def reducer[A]: Reducer[A, IList[A]] = new Reducer[A, IList[A]] {
    override def unit(a: A): IList[A] = IList.single(a)
    override def cons(a: A, as: IList[A]): IList[A] = a :: as
  }
~~~~~~~~

A> `Reducer` powinien nazywać się `CanActuallyBuildFrom` na cześć podobnie nazywającej się klasy z biblioteki standardowej,
A> ponieważ w praktyce służy on do budowania kolekcji.


#### `IndSeq`

Jeśli jako `V` użyjemy `Int`, dostaniemy sekwencje zindeksowaną, gdzie miarą jest *wielkość*, pozwalając nam
na wyszukiwanie elementu po indeksie poprzez porównywanie indeksu z rozmiarem każdej gałezi w drzewie:

{lang="text"}
~~~~~~~~
  final class IndSeq[A](val self: FingerTree[Int, A])
  object IndSeq {
    private implicit def sizer[A]: Reducer[A, Int] = _ => 1
    def apply[A](as: A*): IndSeq[A] = ...
  }
~~~~~~~~

#### `OrdSeq`

Inną odmianą `FingerTree` jest sekwencja uporządkowana, gdzie miarą jest największa wartość w danej gałęzi:

{lang="text"}
~~~~~~~~
  final class OrdSeq[A: Order](val self: FingerTree[LastOption[A], A]) {
    def partition(a: A): (OrdSeq[A], OrdSeq[A]) = ...
    def insert(a: A): OrdSeq[A] = ...
    def ++(xs: OrdSeq[A]): OrdSeq[A] = ...
  }
  object OrdSeq {
    private implicit def keyer[A]: Reducer[A, LastOption[A]] = a => Tag(Some(a))
    def apply[A: Order](as: A*): OrdSeq[A] = ...
  }
~~~~~~~~

`OrdSeq` nie posiada instancji żadnych typeklas, co sprawia, że przydatna jest tylko do stopniowego budowania
uporządkowanej sekwencji (zawierającej duplikaty). Jeśli zajdzie taka potrzeba, możemy zawsze skorzystać z bazowego `FingerTree`.


#### `Cord`

Najpopularniejszym użyciem `FingerTree` jest przechowanie tymczasowej reprezentacji `String`ów w instancjach `Show`.
Budowanie pojedynczego `String`a może być tysiąckrotnie szybsze niż domyślna implementacja `.toString` dla `case class`, 
która tworzy nowy ciąg znaków dla każdej warstwy w ADT.

{lang="text"}
~~~~~~~~
  final case class Cord(self: FingerTree[Int, String]) {
    override def toString: String = {
      val sb = new java.lang.StringBuilder(self.measure)
      self.foreach(sb.append) // locally scoped side effect
      sb.toString
    }
    ...
  }
~~~~~~~~

Dla przykładu, instancja `Cord[String]` zwraca `Three` ze stringiem po środku i cudzysłowami po obu stronach

{lang="text"}
~~~~~~~~
  implicit val show: Show[String] = s => Cord(FingerTree.Three("\"", s, "\""))
~~~~~~~~

Sprawiając, że `String` wygląda tak jak w kodzie źródłowym

{lang="text"}
~~~~~~~~
  scala> val s = "foo"
         s.toString
  res: String = foo
  
  scala> s.show
  res: Cord = "foo"
~~~~~~~~

A> `Cord` w Scalaz 7.2 nie jest niestety tak szybki jak mógłby być. W Scalaz 7.3 zostało to poprawione
A> za pomocą [specjalnej struktury danych zoptymalizowanej do złączania `String`ów](https://github.com/scalaz/scalaz/pull/1793).


### Kolejka Priorytetowa `Heap`

*Kolejka priorytetowa* to struktura danych, która pozwala na szybkie wstawianie uporządkowanych elementów
(zezwalając na duplikaty) oraz szybki dostęp do *najmniejszego* elementu (czyli takiego z najwyższym priorytetem).
Nie jest wymagane, aby elementy inne niż minimalny były przechowywane wg porządku. Naiwna implementacja mogłaby
wyglądać tak:

{lang="text"}
~~~~~~~~
  final case class Vip[A] private (val peek: Maybe[A], xs: IList[A]) {
    def push(a: A)(implicit O: Order[A]): Vip[A] = peek match {
      case Maybe.Just(min) if a < min => Vip(a.just, min :: xs)
      case _                          => Vip(peek, a :: xs)
    }
  
    def pop(implicit O: Order[A]): Maybe[(A, Vip[A])] = peek strengthR reorder
    private def reorder(implicit O: Order[A]): Vip[A] = xs.sorted match {
      case INil()           => Vip(Maybe.empty, IList.empty)
      case ICons(min, rest) => Vip(min.just, rest)
    }
  }
  object Vip {
    def fromList[A: Order](xs: IList[A]): Vip[A] = Vip(Maybe.empty, xs).reorder
  }
~~~~~~~~

Taki `push` jest bardzo szybki (`O(1)`), ale `reorder`, a zatem i `pop` bazują na metodzie `IList.sorted`, której
złożoność to `O(n log n)`.

Scalaz implementuje kolejkę priorytetową za pomocą struktury drzewiastej, gdzie każdy węzeł ma wartość
mniejszą niż jego dzieci. `Heap` pozwala na szybkie wstawianie (`insert`), złączanie (`union`), sprawdzanie 
wielkości (`size`), zdejmowanie (`pop`) i podglądanie (`minimum0`) najmniejszego elementu.

{lang="text"}
~~~~~~~~
  sealed abstract class Heap[A] {
    def insert(a: A)(implicit O: Order[A]): Heap[A] = ...
    def +(a: A)(implicit O: Order[A]): Heap[A] = insert(a)
  
    def union(as: Heap[A])(implicit O: Order[A]): Heap[A] = ...
  
    def uncons(implicit O: Order[A]): Option[(A, Heap[A])] = minimumO strengthR deleteMin
    def minimumO: Option[A] = ...
    def deleteMin(implicit O: Order[A]): Heap[A] = ...
  
    ...
  }
  object Heap {
    def fromData[F[_]: Foldable, A: Order](as: F[A]): Heap[A] = ...
  
    private final case class Ranked[A](rank: Int, value: A)
  
    private final case class Empty[A]() extends Heap[A]
    private final case class NonEmpty[A](
      size: Int,
      tree: Tree[Ranked[A]]
    ) extends Heap[A]
  
    ...
  }
~~~~~~~~

A> wartość `size` jest memoizowana wewnątrz ADT, aby pozwolić na natychmiastowe wykonanie `Foldable.length`,
A> w zamian za dodatkowe 64 bity pamięci za każdy element. Moglibyśmy zaimplementować wariant `Heap` z 
A> mniejszym zużyciem pamięci i wolniejszym `Foldable.length`.

`Heap` zaimplementowany jest za pomogą Rose `Tree` z wartościami typu `Ranked`, gdzie `rank` to głębokość
subdrzewa, pozwalająca na balansowanie całej struktury. Samodzielnie zarządzamy drzewem, tak aby `minimum` 
było zawsze na jego szczycie. Zaletą takiej reprezentacji jest to, że `minimum0` jest darmowe:

{lang="text"}
~~~~~~~~
  def minimumO: Option[A] = this match {
    case Empty()                        => None
    case NonEmpty(_, Tree.Node(min, _)) => Some(min.value)
  }
~~~~~~~~

Dodając nowy element porównujemy ją z aktualnym minimum i podmieniamy je jeśli nowa wartość jest mniejsza:

{lang="text"}
~~~~~~~~
  def insert(a: A)(implicit O: Order[A]): Heap[A] = this match {
    case Empty() =>
      NonEmpty(1, Tree.Leaf(Ranked(0, a)))
    case NonEmpty(size, tree @ Tree.Node(min, _)) if a <= min.value =>
      NonEmpty(size + 1, Tree.Node(Ranked(0, a), Stream(tree)))
  ...
~~~~~~~~

Dodawanie wartości, które nie są minimum skutkuje *nieuporządkowanymi* gałęziami drzewa. Kiedy napotkamy
dwa, lub więcej, poddrzewa tej samej rangi, optymistycznie dodajemy minimum na początek:

{lang="text"}
~~~~~~~~
  ...
    case NonEmpty(size, Tree.Node(min,
           (t1 @ Tree.Node(Ranked(r1, x1), xs1)) #::
           (t2 @ Tree.Node(Ranked(r2, x2), xs2)) #:: ts)) if r1 == r2 =>
      lazy val t0 = Tree.Leaf(Ranked(0, a))
      val sub =
        if (x1 <= a && x1 <= x2)
          Tree.Node(Ranked(r1 + 1, x1), t0 #:: t2 #:: xs1)
        else if (x2 <= a && x2 <= x1)
          Tree.Node(Ranked(r2 + 1, x2), t0 #:: t1 #:: xs2)
        else
          Tree.Node(Ranked(r1 + 1, a), t1 #:: t2 #:: Stream())
  
      NonEmpty(size + 1, Tree.Node(Ranked(0, min.value), sub #:: ts))
  
    case NonEmpty(size,  Tree.Node(min, rest)) =>
      val t0 = Tree.Leaf(Ranked(0, a))
      NonEmpty(size + 1, Tree.Node(Ranked(0, min.value), t0 #:: rest))
  }
~~~~~~~~

Uniknięcie pełnego uporządkowania drzewa sprawia, że `insert` jest bardzo szybki (`O(1)`), a więc
producencie wartości nie są karani. Jednak konsumenci muszą ponieść koszt tej decyzji, gdyż
złożoność `uncons` to `O(log n)`, z racji tego, że musimy odszukać nowe minimum i przebudować drzewo.
Nadal jednak jest to implementacja szybsza od naiwnej.

`union` również odracza porządkowanie pozwalając na wykonanie ze złożonością `O(1)`.

Jeśli domyślna instancja `Order[Foo]` nie wyraża w poprawny sposób priorytetów, których potrzebujemy, możemy
użyć `Tag`u i dostarczyć własną instancję `Order[Foo @@ Custom]` dla `Heap[Foo @@ Custom]`.


### `Diev` (Interwały Dyskretne)

Możemy wydajnie wyrazić (nieuporządkowany) ciąg liczb całkowitych 6, 9, 2, 13, 8, 14, 10, 7, 5 jako serię domkniętych przedziałów:
`[2, 2], [5, 10], [13, 14]`. `Diev` to wydajna implementacja tej metody dla dowolnego `A`, dla którego istnieje 
`Enum[A]`. Tym wydajniejsza im gęstsza jego zawartość.

{lang="text"}
~~~~~~~~
  sealed abstract class Diev[A] {
    def +(interval: (A, A)): Diev[A]
    def +(value: A): Diev[A]
    def ++(other: Diev[A]): Diev[A]
  
    def -(interval: (A, A)): Diev[A]
    def -(value: A): Diev[A]
    def --(other: Diev[A]): Diev[A]
  
    def intervals: Vector[(A, A)]
    def contains(value: A): Boolean
    def contains(interval: (A, A)): Boolean
    ...
  }
  object Diev {
    private final case class DieVector[A: Enum](
      intervals: Vector[(A, A)]
    ) extends Diev[A]
  
    def empty[A: Enum]: Diev[A] = ...
    def fromValuesSeq[A: Enum](values: Seq[A]): Diev[A] = ...
    def fromIntervalsSeq[A: Enum](intervals: Seq[(A, A)]): Diev[A] = ...
  }
~~~~~~~~

Kiedy aktualizujemy `Diev` sąsiednie przedziały są łączone i porządkowane, tak, że dla każdego zbioru wartości
istnieje unikalna reprezentacja.

{lang="text"}
~~~~~~~~
  scala> Diev.fromValuesSeq(List(6, 9, 2, 13, 8, 14, 10, 7, 5))
  res: Diev[Int] = ((2,2)(5,10)(13,14))
  
  scala> Diev.fromValuesSeq(List(6, 9, 2, 13, 8, 14, 10, 7, 5).reverse)
  res: Diev[Int] = ((2,2)(5,10)(13,14))
~~~~~~~~

Świetnym zastosowaniem dla tej struktury są przedziały czasu. Na przykład w `TradeTemplate` z wcześniejszego rozdziału.

{lang="text"}
~~~~~~~~
  final case class TradeTemplate(
    payments: List[java.time.LocalDate],
    ccy: Option[Currency],
    otc: Option[Boolean]
  )
~~~~~~~~

Jeśli okaże się, że lista `payments` jest bardzo gęsta, możemy zamienić ją na `Diev` dla zwiększenia wydajności, 
nie wpływając jednocześnie na logikę biznesową, gdyż polega ona na typeklasie `Monoid`, a nie metodach specyficznych
dla `List`y. Musimy jednak dostarczyć instancję `Enum[LocalDate]`, co jest rzeczą całkiem przydatną.


### `OneAnd`

Przypomnij sobie `Foldable`, czyli odpowiednik API kolekcji ze Scalaz, oraz `Foldable1`, czyli jego wersję dla 
niepustych kolekcji. Do tej pory widzieliśmy instancję `Foldable1` jedynie dla `NonEmptyList`. Okazuje się, że 
`OneAnd` to prosta struktura danych, która potrafi opakować dowolną kolekcję i zamienić ją w `Foldable1`:

{lang="text"}
~~~~~~~~
  final case class OneAnd[F[_], A](head: A, tail: F[A])
~~~~~~~~

Typ `NonEmptyList[A]` mógłby być aliasem na `OneAnd[IList, A]`. W podobny sposób możemy stworzyć niepuste
wersje `Stream`, `DList` i `Tree`. Jednak może to zaburzyć gwarancje co do uporządkowania i unikalności elementów: 
`OneAnd[ISet, A]` to nie tyle niepusty `ISet`, a raczej `ISet` z zagwarantowanym pierwszym elementem, który może
również znajdować się w tym zbiorze.


## Podsumowanie

W tym rozdziale przejrzeliśmy typy danych, jakie Scalaz ma do zaoferowania.

Nie musimy zapamiętać wszystkiego. Niech każda z sekcji zasadzi ziarno pewnej koncepcji, które może o sobie przypomnieć
gdy będziemy szukać rozwiązania dla konkretnego problemu.

Świat funkcyjnych struktur danych jest aktywnie badany i rozwijany. Publikacje naukowe na ten temat ukazują się
regularnie, pokazując nowe podejścia do znanych problemów. Implementacja nowych struktur bazujących na literaturze 
to dobry sposób na swój własny wkład do ekosystemu Scalaz.


# Zaawansowane Monady

Znajomość Zaawansowanych Monad to element obowiązkowy, aby móc nazwać się zaawansowanym programistą funkcyjnym.

Jednocześnie jesteśmy deweloperami, którzy nieustannie pragną prostego życia, a więc i nasza definicja "zaawansowania"
jest raczej skromna. Dla porównania: `scala.concurrent.Future` jest strukturą dużo bardziej skomplikowaną niż jakakolwiek
z prezentowanych w tym rozdziale `Monad`.

## Always in motion is the `Future`[^yoda]

[^yoda]: Cytat z Mistrza Yody.

Największym problemem z `Future` jest to, że rozpoczyna obliczenia w momencie stworzenia, tym samym łącząc definiowanie
programu z jego interpretacją (czyli np. uruchomieniem).

`Future` jest też nie najlepszym wyborem ze względów wydajnościowych: za każdym razem, gdy wywołujemy `.flatMap`
domknięcie jest przekazywane do `Executor`a, wywołując planowanie wątków i zmiany kontekstu. Nie jest niczym
nadzwyczajnym, aby 50% mocy obliczeniowej CPU wykorzystywane było na te właśnie operacje zamiast rzeczywistej pracy.
W efekcie program zrównoleglony za pomocą `Future` może okazać się *wolniejszy* od swojego sekwencyjnego odpowiednika.

Zachłanna ewaluacja w połączeniu ze odwołaniami do executora sprawia, że niemożliwym jest określenie kiedy
zadanie się rozpoczęło, kiedy się zakończyło ani jakie pod-zadania zostały rozpoczęte. Zatem nie powinno nas dziwić,
że "rozwiązania" do monitorowania wydajności frameworków opartych o `Future` są solidnym źródłem utrzymania
dla nowoczesnych odpowiedników sprzedawców "cudownych remediów".

Co więcej, `Future.flatMap` wymaga niejawnego przekazania parametru typu `ExecutionContext`, zmuszając
użytkownika do myślenia o logice biznesowej i semantyce uruchomienia w tym samym momencie.

A> Jeśli `Future` ma swój odpowiednik w sadze Star Wars, to jest nim Anakin Skywalker: upadły
A> wybraniec, który wbiega i niszczy wszystko bez zastanowienia.


## Efekty i efekty uboczne

Jeśli nie możemy wywołać metod z efektami ubocznymi w naszej logice biznesowej, ani w `Future` (ani `Id`, `Either`, 
`Const`, itd.), to **kiedy możemy** je wywołać? Odpowiedź brzmi: wewnątrz `Monad`y, która opóźnia wykonanie 
do czasu interpretacji w punkcie wejścia do aplikacji. W takiej sytuacji możemy odnosić się do operacji I/O i mutacji
jako *efektów*, które widoczne są wprost w systemie typów, odwrotnie niż ukryte i nieoczywiste *efekty uboczne*.

Najprostszą implementacją takiej `Monad`y jest jest `IO`

{lang="text"}
~~~~~~~~
  final class IO[A](val interpret: () => A)
  object IO {
    def apply[A](a: =>A): IO[A] = new IO(() => a)
  
    implicit val monad: Monad[IO] = new Monad[IO] {
      def point[A](a: =>A): IO[A] = IO(a)
      def bind[A, B](fa: IO[A])(f: A => IO[B]): IO[B] = IO(f(fa.interpret()).interpret())
    }
  }
~~~~~~~~

Metoda `.interpret` wywoływana jest tylko raz, na wejściu do naszej aplikacji:

{lang="text"}
~~~~~~~~
  def main(args: Array[String]): Unit = program.interpret()
~~~~~~~~

Niemniej, taka prosta implementacja niesie ze sobą dwa duże problemy:

1. może spowodować przepełnienie stosu
1. nie umożliwia równoległego wykonywania obliczeń

Oba te problemy zostaną przezwyciężone w tym rozdziale. Jednocześnie musimy pamiętać, 
że niezależnie jak skomplikowana jest wewnętrzna implementacja `Monad`y, zasady tutaj opisane zachowują moc:
modularyzujemy definicję programu i jego wykonanie, tak aby móc wyrazić efekty w sygnaturach typów, sprawiając tym samym
że rozumowanie o nich staje się możliwe, a reużycie kodu łatwiejsze.

A> Kompilator Scali z radością pozwoli nam wywołać metody ze skutkami ubocznymi poza bezpiecznym kontekstem. 
A> Linter [Scalafix](https://scalacenter.github.io/scalafix/) może sprawić, że takie wywołania będą możliwe jedynie
A> z wewnątrz `Monad`y odraczającej wykonanie, jak np. `IO`.


## Bezpieczeństwo Stosu

Na JVMie każde wywołanie metody dodaje wpis do stosu wywołań aktualnego wątku (`Thread`), tak jakbyśmy
dopisywali element na początek `List`y. Kiedy metoda kończy działanie, wierzchni wpis jest usuwany. Maksymalna długość
stosu wywołań determinowana jest przez flagę `-Xss` ustawianą przy uruchomieniu polecenia `java`. Wywołania
ogonowo-rekursywne są wykrywane przez kompilator Scali i nie dodają wpisów do stosu. Kiedy przekroczymy dozwolony
limit poprzez zawołanie zbyt wielu metod napotkamy `StackOverflowError`.

Niestety, każde zagnieżdżone wywołanie na naszym `IO`, jak np. `.flatMap`, dodaje kolejne wywołania do stosu.
Najprostszym sposobem, aby zaobserwować to zjawisko, jest powtórzenie akcji w nieskończoność i sprawdzenie czy 
taki program przeżyje dłużej niż kilka sekund. Możemy użyć metody `.forever` pochodzącej z `Apply` (rodzica `Monad`y):

{lang="text"}
~~~~~~~~
  scala> val hello = IO { println("hello") }
  scala> Apply[IO].forever(hello).interpret()
  
  hello
  hello
  hello
  ...
  hello
  java.lang.StackOverflowError
      at java.io.FileOutputStream.write(FileOutputStream.java:326)
      at ...
      at monadio.IO$$anon$1.$anonfun$bind$1(monadio.scala:18)
      at monadio.IO$$anon$1.$anonfun$bind$1(monadio.scala:18)
      at ...
~~~~~~~~

Scalaz definiuje typeklasę `BindRec`, którą mogą implementować `Monad`y niezagrażające przeładowywaniem stosu (_stack safe_):. 
Wymaga ona zachowywania stałegoe rozmiaru stosu przy rekurencyjnych wywołaniach `bind`:

{lang="text"}
~~~~~~~~
  @typeclass trait BindRec[F[_]] extends Bind[F] {
    def tailrecM[A, B](f: A => F[A \/ B])(a: A): F[B]
  
    override def forever[A, B](fa: F[A]): F[B] = ...
  }
~~~~~~~~

Nie dla wszystkich programów potrzebujemy jej instancji, ale jest ona istotna dla `Monad` ogólnego przeznaczenia.

Aby osiągnąć wspomniane bezpieczeństwo, należy zamienić wywołania metod na referencje do ADT, czyli monadę `Free`:

{lang="text"}
~~~~~~~~
  sealed abstract class Free[S[_], A]
  object Free {
    private final case class Return[S[_], A](a: A)     extends Free[S, A]
    private final case class Suspend[S[_], A](a: S[A]) extends Free[S, A]
    private final case class Gosub[S[_], A0, B](
      a: Free[S, A0],
      f: A0 => Free[S, B]
    ) extends Free[S, B] { type A = A0 }
    ...
  }
~~~~~~~~

A> `SUSPEND`, `RETURN` i `GOSUB` to ukłon w stronę poleceń z języka `BASIC` o tych samych nazwach, 
A> służących odpowiednio do zatrzymywania, zakańczania i kontynuowania podprogramu.

ADT `Free` to naturalna reprezentacja metod z interfejsu `Monad`:

1. `Return` reprezentuje `.point`
2. `Gosub` reprezentuje `.bind` / `.flatMap`

Kiedy ADT odwzorowuje argumenty powiązanej funkcji, nazywamy to *kodowaniem Church'a* (_Church encodnig_).

Typ `Free` to skrót od `FreeMonad` i nazywa się tak ponieważ pozwala *wygenerować za darmo* monadę dla dowolnego `S[_]`. Moglibyśmy
na przykład wskazać algebrę `Drone` lub `Machines` z rozdziału 3 jako `S` i wygenerować struktury danych reprezentujące nasz program.
Zastanowimy się jak może nam się to przydać pod koniec tego rozdziału.


### `Trampoline

`Free` jest typem bardziej ogólnym niż w tym momencie potrzebujemy. Ustawiając algebrę `S[_]` na `() => ?`, czyli odroczone wykonanie
znane jako *thunk*, otrzymamy typ `Trampoline`, który pozwoli nam zaimplementować bezpieczną instancję `Monad`y

{lang="text"}
~~~~~~~~
  object Free {
    type Trampoline[A] = Free[() => ?, A]
    implicit val trampoline: Monad[Trampoline] with BindRec[Trampoline] =
      new Monad[Trampoline] with BindRec[Trampoline] {
        def point[A](a: =>A): Trampoline[A] = Return(a)
        def bind[A, B](fa: Trampoline[A])(f: A => Trampoline[B]): Trampoline[B] =
          Gosub(fa, f)
  
        def tailrecM[A, B](f: A => Trampoline[A \/ B])(a: A): Trampoline[B] =
          bind(f(a)) {
            case -\/(a) => tailrecM(f)(a)
            case \/-(b) => point(b)
          }
      }
    ...
  }
~~~~~~~~

`.tailrecM` pochodząca z `BindRec` uruchamia `.bind` tak długo aż otrzymamy `B`. Mimo że technicznie rzecz biorąc
nie jest to implementacja, którą spełnia wymagania anotacji `@tailrec`, to zachowuje stałą wielkość stosu, ponieważ
każde wywołanie zwraca obiekt ze sterty (_heap_), a rekurencja zostaje odroczona.

A> Nazwa `Trampoline` wynika z faktu, że za każdym razem, gdy odkładamy `.bind` na stosie *odbijamy się* z powrotem
A> na stertę.
A>
A> Jedynym odwołaniem do odbijania się w sadze Star Wars jest pojedynek Yody z Dooku. Nie rozmawiajmy o tym.

Dostępne są funkcje ułatwiające tworzenie `Trampoline` zarówno zachłannie (`.done`) jak i przez nazwę (`.delay`). 
Możemy też stworzyć instancję `Trampoline` przekazując inną jej instancję poprzez nazwę (`.suspend`):

{lang="text"}
~~~~~~~~
  object Trampoline {
    def done[A](a: A): Trampoline[A]                  = Return(a)
    def delay[A](a: =>A): Trampoline[A]               = suspend(done(a))
    def suspend[A](a: =>Trampoline[A]): Trampoline[A] = unit >> a
  
    private val unit: Trampoline[Unit] = Suspend(() => done(()))
  }
~~~~~~~~

Kiedy widzimy w naszym kodzie `Trampoline[A]` możemy w głowie podstawić w jej miejsce `A`, ponieważ
jej jedyną funkcją jest sprawienie, że nie przeładujemy stosu. Możemy uzyskać `A` interpretując `Free` za pomocą `.run`.

A> Pouczające, acz nie niezbędne, jest zrozumienie jak jest zaimplementowane jest `Free.run`: `.resume` wykonuje pojedynczą
A> warstwę `Free`, a `.go` prowadzi je do zakończenia.
A> 
A> W poniższym przykładzie `Trampoline[A]` jest użyte jako synonim `Free[() => ?, A]` dla zwiększenia czytelności.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   sealed abstract class Trampoline[A] {
A>     def run: A = go(f => f())
A>   
A>     def go(f: () => Trampoline[A] => Trampoline[A]): A = {
A>       @tailrec def go2(t: Trampoline[A]): A = t.resume match {
A>         case -\/(s) => go2(f(s))
A>         case \/-(r) => r
A>       }
A>       go2(this)
A>     }
A>   
A>     @tailrec def resume: () => Trampoline[A] \/ A = this match {
A>       case Return(a) => \/-(a)
A>       case Suspend(t) => -\/(t.map(Return(_)))
A>       case Gosub(Return(a), f) => f(a).resume
A>       case Gosub(Suspend(t), f) => -\/(t.map(f))
A>       case Gosub(Gosub(a, g), f) => a >>= (z => g(z) >>= f).resume
A>     }
A>     ...
A>   }
A> ~~~~~~~~
A> 
A> Najbardziej zagmatwany jest przypadek zagnieżdżonych `Gosub`. W rzeczywistości wykonujemy zwykłe złożenie funkcji:
A> wykonaj funkcję `g` i przekaż wynik do zewnętrznej funkcji `f`.


### Przykład: Bezpieczne `DList`

W poprzednim rozdziale przedstawiliśmy typ danych `DList` jako

{lang="text"}
~~~~~~~~
  final case class DList[A](f: IList[A] => IList[A]) {
    def toIList: IList[A] = f(IList.empty)
    def ++(as: DList[A]): DList[A] = DList(xs => f(as.f(xs)))
    ...
  }
~~~~~~~~

Jednak w rzeczywistości jego implementacja przypomina bardziej:

{lang="text"}
~~~~~~~~
  final case class DList[A](f: IList[A] => Trampoline[IList[A]]) {
    def toIList: IList[A] = f(IList.empty).run
    def ++(as: =>DList[A]): DList[A] = DList(xs => suspend(as.f(xs) >>= f))
    ...
  }
~~~~~~~~

Zamiast aplikować zagnieżdżone wywołanie `f` używamy wstrzymanej `Trampoline`, którą interpretujemy za pomocą `.run`
kiedy zajdzie taka potrzeba, np. w `toIList`. Zmiany są minimalne, ale w efekcie otrzymaliśmy bezpieczną wersję `DList`,
która nie przepełni stosu niezależnie do tego jak duże będą przetwarzane listy.


### Bezpieczne `IO`

Używając `Trampoline` możemy w podobny sposób zabezpieczyć nasze `IO`:

{lang="text"}
~~~~~~~~
  final class IO[A](val tramp: Trampoline[A]) {
    def unsafePerformIO(): A = tramp.run
  }
  object IO {
    def apply[A](a: =>A): IO[A] = new IO(Trampoline.delay(a))
  
    implicit val Monad: Monad[IO] with BindRec[IO] =
      new Monad[IO] with BindRec[IO] {
        def point[A](a: =>A): IO[A] = IO(a)
        def bind[A, B](fa: IO[A])(f: A => IO[B]): IO[B] =
          new IO(fa.tramp >>= (a => f(a).tramp))
        def tailrecM[A, B](f: A => IO[A \/ B])(a: A): IO[B] = ...
      }
  }
~~~~~~~~

A> Słyszeliśmy, że lubisz `Monad`y, więc zrobiliśmy dla ciebie `Monad`ę z `Monad`y, żebyś mógł
A> bindować monadycznie, gdy bindujesz monadycznie.

Interpreter, `unsafePerformIO()`, specjalnie został nazwany w tak odstraszający sposób, aby zniechęcić
do używania go poza punktem wejścia naszej aplikacji.

Tym razem nie zobaczymy `StackOverflowError`:

{lang="text"}
~~~~~~~~
  scala> val hello = IO { println("hello") }
  scala> Apply[IO].forever(hello).unsafePerformIO()
  
  hello
  hello
  hello
  ...
  hello
~~~~~~~~

Używanie `Trampoline` zazwyczaj wiąże się ze spadkiem wydajności w porównaniu do używania zwykłej referencji.
Okazuje się, że `Free` nie jest tak do końca za darmo.

A> Zawsze wykonuj benchmarki i nie akceptuj ogólnych stwierdzeń na temat wydajności. Może np. okazać się,
A> że garbage collector będzie działał szybciej, gdy użyjemy `Free` z powodu zmniejszonego rozmiaru obiektów
A> przechowywanych na stosie.


## Biblioteka Transformatorów Monad

Transformatory monad to struktury danych, które opakowują wewnętrzną wartość i dostarczają monadyczny *efekt*.

W Rozdziale 2 używaliśmy `OptionT`, aby móc użyć wartości typu `F[Option[A]]` w konstrukcji `for` tak jakby była to 
po prostu instancja `F[A]`. Uzyskaliśmy w ten sposób *efekt* opcjonalnej wartości. Aby osiągnąć ten sam rezultat
moglibyśmy też użyć `MonadPlus`.

Poniższy zbiór typów danych często nazywany jest Biblioteką Transformatorów Monad (_Monad Transformer Library_, _MTL_).
W tym podrozdziale opiszemy każdy z nich, zwracając uwagę na to do czego mogą być przydatne i jak są zbudowane. 

| Efekt                     | Wnętrze               | Transformator | Typeklasa     |
|--------------------       |---------------------  |-----------    |-------------  |
| opcjonalność              | `F[Maybe[A]]`         | `MaybeT`      | `MonadPlus`   |
| błędy                     | `F[E \/ A]`           | `EitherT`     | `MonadError`  |
| wartość czasu wykonania   | `A => F[B]`           | `ReaderT`     | `MonadReader` |
| dziennik/wielozadaniowość | `F[(W, A)]`           | `WriterT`     | `MonadTell`   |
| zmieniający się stan       | `S => F[(S, A)]`      | `StateT`      | `MonadState`  |
| zachowaj spokój i idź dalej | `F[E \&/ A]`        | `TheseT`      |               |
| kontrola przepływu        | `(A => F[B]) => F[B]` | `ContT`       |               |


### `MonadTrans`

Każdy transformator ma ogólny kształt `T[F[_], A]`, dostarczając instancje co najmniej
`Monad`y oraz `Hoist`(a więc i `MonadTrans`):

{lang="text"}
~~~~~~~~
  @typeclass trait MonadTrans[T[_[_], _]] {
    def liftM[F[_]: Monad, A](a: F[A]): T[F, A]
  }
  
  @typeclass trait Hoist[F[_[_], _]] extends MonadTrans[F] {
    def hoist[M[_]: Monad, N[_]](f: M ~> N): F[M, ?] ~> F[N, ?]
  }
~~~~~~~~

A> `T[_[_], _]` jest kolejnym przykładem typu wyższego rodzaju. Mówi on nam, że `T` przyjmuje dwa
A> parametry typu: pierwszy z nich również przyjmuje parametry typu i wyrażony jest jako `_[_]`,
A> drugi nie jest parametryzowany i zapisany jest jako `_`.

`.liftM` pozwala nam stworzyć instancję transformatora na podstawie `F[A]`, na przykład, aby zbudować
`OptionT[IO, String]`, wystarczy wywołać `.liftM[OptionT]` na `IO[String]`.

`.hoist` wyraża tą samą koncepcję, ale dla transformacji naturalnych.

W ogólności istnieją trzy sposoby na uzyskanie transformatora monady:

- z instancji typu wewnętrznego, używając konstruktora
- z pojedynczej instancji `A`, używają `.pure` z `Monad`y
- z `F[A]`, używając `liftM` z `MonadTrans`

Z racji tego jak działa inferencja typów w Scali, często oznacza to, że dość skomplikowana
sygnatura typu musi być zapisania explicite. Transformatory dostarczają nam trochę wygodniejsze
konstruktory w swoich obiektach towarzyszących jako obejście tego problemu.


### `MaybeT`

`OptionT`, `MaybeT` i `LazyOptionT` są zaimplementowane w podobny sposób, zapewniając opcjonalność
poprzez odpowiednio `Option`, `Maybe` i `LazyOption`. Skupimy się na `MaybeT`, aby uniknąć powtarzania się.

{lang="text"}
~~~~~~~~
  final case class MaybeT[F[_], A](run: F[Maybe[A]])
  object MaybeT {
    def just[F[_]: Applicative, A](v: =>A): MaybeT[F, A] =
      MaybeT(Maybe.just(v).pure[F])
    def empty[F[_]: Applicative, A]: MaybeT[F, A] =
      MaybeT(Maybe.empty.pure[F])
    ...
  }
~~~~~~~~

dostarcza `MonadPlus`

{lang="text"}
~~~~~~~~
  implicit def monad[F[_]: Monad] = new MonadPlus[MaybeT[F, ?]] {
    def point[A](a: =>A): MaybeT[F, A] = MaybeT.just(a)
    def bind[A, B](fa: MaybeT[F, A])(f: A => MaybeT[F, B]): MaybeT[F, B] =
      MaybeT(fa.run >>= (_.cata(f(_).run, Maybe.empty.pure[F])))
  
    def empty[A]: MaybeT[F, A] = MaybeT.empty
    def plus[A](a: MaybeT[F, A], b: =>MaybeT[F, A]): MaybeT[F, A] = a orElse b
  }
~~~~~~~~

Powyższa implementacja może wydawać się skomplikowana, ale w rzeczywistości jedyne co tutaj się dzieje, 
to delegacja operacji do `Monad[F]` i opakowywanie wyniku w `MaybeT`.
Sam klej i taśma.

Z tą monadą możemy pisać logikę obsługującą opcjonalność wewnątrz kontekstu `F[_]`.
Alternatywnie musielibyśmy wszędzie umieszczać `Option` lub `Maybe`.

Wyobraźmy sobie, że odpytujemy portal społecznościowy chcąc zliczyć liczbę gwiazdek danego użytkownika,
zaczynając od `String`a, który może, lub nie, wskazywać na konkretnego użytkownika. Oto nasza algebra:

{lang="text"}
~~~~~~~~
  trait Twitter[F[_]] {
    def getUser(name: String): F[Maybe[User]]
    def getStars(user: User): F[Int]
  }
  def T[F[_]](implicit t: Twitter[F]): Twitter[F] = t
~~~~~~~~

Musimy wywołać `getUser` a wynik przekazać do `getStars`. Jeśli użyjemy typeklasy `Monad`
będzie to dość skomplikowane, bo musimy obsłużyć przypadek `Empty`:

{lang="text"}
~~~~~~~~
  def stars[F[_]: Monad: Twitter](name: String): F[Maybe[Int]] = for {
    maybeUser  <- T.getUser(name)
    maybeStars <- maybeUser.traverse(T.getStars)
  } yield maybeStars
~~~~~~~~

Jednak mając do dyspozycji `MonadPlus` możemy wessać `Maybe` do `F[_]` za pomocą `.orEmpty` i skupić się na ważniejszych rzeczach:

{lang="text"}
~~~~~~~~
  def stars[F[_]: MonadPlus: Twitter](name: String): F[Int] = for {
    user  <- T.getUser(name) >>= (_.orEmpty[F])
    stars <- T.getStars(user)
  } yield stars
~~~~~~~~

Jednakże zwiększenie wymagań co do naszego kontekstu na typeklasę `MonadPlus`
może spowodować problemy na późniejszym etapie, jeśli nie będzie ona dostępna.
Rozwiązaniem jest zmiana kontekstu na `MaybeT[F, ?]` (co automatycznie daje nam
instancję `MonadPlus` dla dowolnej `Monad`y), albo użyć `MaybeT` w prost w zwracanym typie,
za cenę nieco większej ilości kodu:

{lang="text"}
~~~~~~~~
  def stars[F[_]: Monad: Twitter](name: String): MaybeT[F, Int] = for {
    user  <- MaybeT(T.getUser(name))
    stars <- T.getStars(user).liftM[MaybeT]
  } yield stars
~~~~~~~~

Każdy zespół musi sam wybrać między tymi opcjami, na bazie tego jakich interpreterów
planują używać dla swoich programów.


### `EitherT`

Wartość opcjonalna to tak naprawdę szczególny przypadek wartości, która może być błędem,
ale nic o tym błędzie nie wiemy. `EitherT` (i jego leniwy wariant `LazyEitherT`) pozwalają nam
użyć wartości dowolnego typu do wyrażenia błędu, który powie nam co poszło nie tak w naszych
obliczeniach.

W praktyce `EitherT` to opakowana wartość typu `F[A \/ B]`

{lang="text"}
~~~~~~~~
  final case class EitherT[F[_], A, B](run: F[A \/ B])
  object EitherT {
    def either[F[_]: Applicative, A, B](d: A \/ B): EitherT[F, A, B] = ...
    def leftT[F[_]: Functor, A, B](fa: F[A]): EitherT[F, A, B] = ...
    def rightT[F[_]: Functor, A, B](fb: F[B]): EitherT[F, A, B] = ...
    def pureLeft[F[_]: Applicative, A, B](a: A): EitherT[F, A, B] = ...
    def pure[F[_]: Applicative, A, B](b: B): EitherT[F, A, B] = ...
    ...
  }
~~~~~~~~

z instancją `MonadError`

{lang="text"}
~~~~~~~~
  @typeclass trait MonadError[F[_], E] extends Monad[F] {
    def raiseError[A](e: E): F[A]
    def handleError[A](fa: F[A])(f: E => F[A]): F[A]
  }
~~~~~~~~

`.raiseError` i `.handleError` są samo-opisującymi się odpowiednikami `throw` i `catch`, które znamy 
z pracy z wyjątkami.

`MonadError` dostarcza również dodatkową składnię do rozwiązywania popularnych problemów:

{lang="text"}
~~~~~~~~
  implicit final class MonadErrorOps[F[_], E, A](self: F[A])(implicit val F: MonadError[F, E]) {
    def attempt: F[E \/ A] = ...
    def recover(f: E => A): F[A] = ...
    def emap[B](f: A => E \/ B): F[B] = ...
  }
~~~~~~~~

`.attempt` przenosi błędy z kontekstu do wartości.

`.recover` służy do zamiany błędów na wartości dla wszystkich przypadków, w przeciwieństwie do
`.handleError`, która pozwala nam zwrócić `F[A]`, czyli tym samym częściowo obsłużyć błędy.

`.emap`, czyli *either* map, pozwala zaaplikować transformację, która sama w sobie może się nie udać.

`MonadError` dla `EitherT` wygląda następująco:

{lang="text"}
~~~~~~~~
  implicit def monad[F[_]: Monad, E] = new MonadError[EitherT[F, E, ?], E] {
    def monad[F[_]: Monad, E] = new MonadError[EitherT[F, E, ?], E] {
    def bind[A, B](fa: EitherT[F, E, A])
                  (f: A => EitherT[F, E, B]): EitherT[F, E, B] =
      EitherT(fa.run >>= (_.fold(_.left[B].pure[F], b => f(b).run)))
    def point[A](a: =>A): EitherT[F, E, A] = EitherT.pure(a)
  
    def raiseError[A](e: E): EitherT[F, E, A] = EitherT.pureLeft(e)
    def handleError[A](fa: EitherT[F, E, A])
                      (f: E => EitherT[F, E, A]): EitherT[F, E, A] =
      EitherT(fa.run >>= {
        case -\/(e) => f(e).run
        case right => right.pure[F]
      })
  }
~~~~~~~~

Nie powinno też dziwić, że możemy przepisać przykład z `MonadPlus` używając `MonadError` i dostarczając informacje
o błędzie:

{lang="text"}
~~~~~~~~
  def stars[F[_]: Twitter](name: String)
                          (implicit F: MonadError[F, String]): F[Int] = for {
    user  <- T.getUser(name) >>= (_.orError(s"user '$name' not found")(F))
    stars <- T.getStars(user)
  } yield stars
~~~~~~~~

gdzie `.orError` to funkcja pomocnicza zdefiniowana na `Maybe`.

{lang="text"}
~~~~~~~~
  sealed abstract class Maybe[A] {
    ...
    def orError[F[_], E](e: E)(implicit F: MonadError[F, E]): F[A] =
      cata(F.point(_), F.raiseError(e))
  }
~~~~~~~~

A> Często używa się bloków parametrów niejawnych zamiast ograniczeń kontekstu kiedy
A> sygnatury typeklas mają więcej niż jeden parametr.
A>
A> Tak samo częstą praktyką jest nazywanie instancji tychże typeklas tak jak ich głównego parametru, w tym wypadku `F`.

Wersja używająca `EitherT` bezpośrednio:

{lang="text"}
~~~~~~~~
  def stars[F[_]: Monad: Twitter](name: String): EitherT[F, String, Int] = for {
    user <- EitherT(T.getUser(name).map(_ \/> s"user '$name' not found"))
    stars <- EitherT.rightT(T.getStars(user))
  } yield stars
~~~~~~~~

Najprostszą instancją `MonadError` jest `\/`, idealnego typu do testowania logiki biznesowej wymagającej
`MonadError`. Na przykład:

{lang="text"}
~~~~~~~~
  final class MockTwitter extends Twitter[String \/ ?] {
    def getUser(name: String): String \/ Maybe[User] =
      if (name.contains(" ")) Maybe.empty.right
      else if (name === "wobble") "connection error".left
      else User(name).just.right
  
    def getStars(user: User): String \/ Int =
      if (user.name.startsWith("w")) 10.right
      else "stars have been replaced by hearts".left
  }
~~~~~~~~

Nasz test dla `.stars` może pokryć takie warianty:

{lang="text"}
~~~~~~~~
  scala> stars("wibble")
  \/-(10)
  
  scala> stars("wobble")
  -\/(connection error)
  
  scala> stars("i'm a fish")
  -\/(user 'i'm a fish' not found)
  
  scala> stars("fommil")
  -\/(stars have been replaced by hearts)
~~~~~~~~

Tak jak zawsze możemy skupić się na testowaniu logiki biznesowej bez zbędnych dystrakcji.

Możemy w końcu wrócić do naszego `JsonClient`a z Rozdziału 4.3

{lang="text"}
~~~~~~~~
  trait JsonClient[F[_]] {
    def get[A: JsDecoder](
      uri: String Refined Url,
      headers: IList[(String, String)]
    ): F[A]
    ...
  }
~~~~~~~~

gdzie w API zawarliśmy jedynie szczęśliwą ścieżkę wykonania. Jeśli nasz interpreter dla tej algebry
działa jedynie dla `F` mających instancję `MonadError` musimy zdefiniować jakiego rodzaju błędy mogą się pojawić.
I faktycznie, jeśli zdecydujemy się interpretować `EitherT[IO, JsonClient.Error, ?]`, to możemy mieć **dwie** warstwy błędów

{lang="text"}
~~~~~~~~
  object JsonClient {
    sealed abstract class Error
    final case class ServerError(status: Int)       extends Error
    final case class DecodingError(message: String) extends Error
  }
~~~~~~~~

które pokrywają problemy z siecią, ze statusem odpowiedzi serwera oraz z naszym modelem obiektów otrzymywanych z serwera.


#### Wybieranie typu błędu

Społeczność jest podzielona co do najlepszej strategii wyrażania błędów za pomocą `E` w `MonadError`.

Jedna szkoła mówi, że powinniśmy wybrać jakiś ogólny typ, np. `String`. Druga twierdzi, że każda aplikacja powinna mieć ADT 
wyrażające błędy, aby każdy z nich mógł być raportowany i obsługiwany inaczej. Gang niepryncypialny woli używać `Throwable` dla maksymalnej
kompatybilności z JVMem.

Wprowadzenie wspomnianego ADT niesie za sobą dwa problemy:

- dodawanie nowych błędów jest niewygodne, a jeden z plików musi stać się monolitycznym repozytorium błędów, agregując
  ADT z pojedynczych podsystemów.
- niezależnie jak drobnoziarniste będą błędy, ich obsługa jest zazwyczaj taka sama: zaloguj i spróbuj ponownie albo przerwij przetwarzanie. 
  Nie potrzebujemy do tego ADT.

ADT niesie ze sobą wartość jeśli każdy wariant pozwala na inną strategię obsługi.

Kompromisem między ADT i `String`iem jest format pośredni, jak np. JSON, który jest rozumiany przez większość
bibliotek odpowiedzialnych za logowanie i monitoring.

Brak stacktrace'a może znacznie utrudnić zlokalizowanie fragmentu kodu odpowiedzialnego za zgłoszenie danego błędu.
Możemy rozwiązać ten problem używając biblioteki [`sourcecode` autorstwa Li Haoyi](https://github.com/lihaoyi/sourcecode/):

{lang="text"}
~~~~~~~~
  final case class Meta(fqn: String, file: String, line: Int)
  object Meta {
    implicit def gen(implicit fqn: sourcecode.FullName,
                              file: sourcecode.File,
                              line: sourcecode.Line): Meta =
      new Meta(fqn.value, file.value, line.value)
  }
  
  final case class Err(msg: String)(implicit val meta: Meta)
~~~~~~~~

Mimo że `Err` jest referencyjnie transparentny, jego niejawna konstrukcja już nie.
Dwa wywołania `Meta.gen` wyprodukują różne wartości, ponieważ ich umieszczenie w kodzie
wpływa na zwracaną wartość:

{lang="text"}
~~~~~~~~
  scala> println(Err("hello world").meta)
  Meta(com.acme,<console>,10)
  
  scala> println(Err("hello world").meta)
  Meta(com.acme,<console>,11)
~~~~~~~~

Aby zrozumieć czemu tak się dzieje musimy zdać sobie sprawę, że metody `sourcecode.*` to tak
naprawdę makra, które generują dla nas kod. Jeśli napiszemy tę samą logikę wprost, to
wszystko stanie się jasne:

{lang="text"}
~~~~~~~~
  scala> println(Err("hello world")(Meta("com.acme", "<console>", 10)).meta)
  Meta(com.acme,<console>,10)
  
  scala> println(Err("hello world")(Meta("com.acme", "<console>", 11)).meta)
  Meta(com.acme,<console>,11)
~~~~~~~~

Zgadza się, zawarliśmy pakt z diabłem pod postacią makr, ale jeśli mielibyśmy tworzyć obiekty
`Meta` ręcznie to nasz kod zdezaktualizowywałby się szybciej niż nasza dokumentacja.


### `ReaderT`

Monada `ReaderT` opakowuje `A => F[B]` pozwalając programowi `F[B]` zależeć od wartości `A` znanej dopiero w czasie wykonania.
Dla tych zaznajomionych ze wstrzykiwaniem zależności (_dependency injection_), jest to funkcyjny odpowiednik
anotacji `@Inject` znanej ze Springa lub Guice'a, tyle, że bez dodatku XMLa czy refleksji.

`ReaderT` jest w rzeczywistości jedynie aliasem do bardziej ogólnego typu danych
nazwanego na cześć matematyka *Henryka Kleisli*.

{lang="text"}
~~~~~~~~
  type ReaderT[F[_], A, B] = Kleisli[F, A, B]
  
  final case class Kleisli[F[_], A, B](run: A => F[B]) {
    def dimap[C, D](f: C => A, g: B => D)(implicit F: Functor[F]): Kleisli[F, C, D] =
      Kleisli(c => run(f(c)).map(g))
  
    def >=>[C](k: Kleisli[F, B, C])(implicit F: Bind[F]): Kleisli[F, A, C] = ...
    def >==>[C](k: B => F[C])(implicit F: Bind[F]): Kleisli[F, A, C] = this >=> Kleisli(k)
    ...
  }
  object Kleisli {
    implicit def kleisliFn[F[_], A, B](k: Kleisli[F, A, B]): A => F[B] = k.run
    ...
  }
~~~~~~~~

A> Niektórzy nazywają `>=>` *operatorem ryby* (_fish operator_). Zawsze jest też większa ryba, stąd i `>==>`. Inna nazwa to *strzałki Kleisli* (_Kleisli arrows_).

Niejawna konwersja widoczna w obiekcie towarzyszącym pozwala nam używać `Kleisli` tam gdzie spodziewamy się funkcji,
w efekcie czego możemy przekazywać instancje tego typu jako parametr do `.bind` lub `>>=`.

Najpopularniejszym zastosowaniem `ReaderT` jest dostarczanie informacji ze środowiska do naszego programu.
W `drone-dynamic-agents` potrzebujemy dostępu do tokenu odświeżającego OAuth 2.0 dla naszego użytkownika, aby
móc połączyć się z serwerem Google'a. Oczywistym wydaje się odczytanie `RefreshTokens` z dysku przy starcie aplikacji i
dodanie parametru `RefreshToken` do każdej metody. Okazuje się, że jest to problem na tyle częsty ze Martin Odersky
zaproponował nowy mechanizm [funkcji niejawnych](https://www.scala-lang.org/blog/2016/12/07/implicit-function-types.html),
które mogłyby nam tutaj pomóc.

Lepszym rozwiązaniem jest zdefiniowanie algebry, która dostarczy potrzebnej nam konfiguracji, np:

{lang="text"}
~~~~~~~~
  trait ConfigReader[F[_]] {
    def token: F[RefreshToken]
  }
~~~~~~~~

Tym samym odkryliśmy typeklasę `MonadReader`, związaną z `ReaderT`, gdzie `.ask` jest tym samym
co nasza metoda `.token`, a `S` to `RefreshToken`:

{lang="text"}
~~~~~~~~
  @typeclass trait MonadReader[F[_], S] extends Monad[F] {
    def ask: F[S]
  
    def local[A](f: S => S)(fa: F[A]): F[A]
  }
~~~~~~~~

wraz z implementacją

{lang="text"}
~~~~~~~~
  implicit def monad[F[_]: Monad, R] = new MonadReader[Kleisli[F, R, ?], R] {
    def point[A](a: =>A): Kleisli[F, R, A] = Kleisli(_ => F.point(a))
    def bind[A, B](fa: Kleisli[F, R, A])(f: A => Kleisli[F, R, B]) =
      Kleisli(a => Monad[F].bind(fa.run(a))(f))
  
    def ask: Kleisli[F, R, R] = Kleisli(_.pure[F])
    def local[A](f: R => R)(fa: Kleisli[F, R, A]): Kleisli[F, R, A] =
      Kleisli(f andThen fa.run)
  }
~~~~~~~~

Prawa obowiązujące `MonadReader` zastrzegają, że `S` nie może zmieniać się między wywołaniami, a więc
`ask >> ask === ask`. W naszym przypadku oznacza to, że konfiguracja jest czytana raz. Jeśli
później zdecydujemy, że chcielibyśmy przeładowywać konfigurację za każdym razem, gdy jest potrzebna,
to możemy ponownie wprowadzić typ `ConfigReader`, który nie ma takich ograniczeń.

W naszej implementacji OAuth 2.0 możemy zacząć od przeniesienia parametru `Monad` do metod:

{lang="text"}
~~~~~~~~
  def bearer(refresh: RefreshToken)(implicit F: Monad[F]): F[BearerToken] =
    for { ...
~~~~~~~~

a następnie zamienić parametr `refresh` we fragment `Monad`y

{lang="text"}
~~~~~~~~
  def bearer(implicit F: MonadReader[F, RefreshToken]): F[BearerToken] =
    for {
      refresh <- F.ask
~~~~~~~~

W ten sposób możemy przenieść dowolny parametr do `MonadReader`, co niesie największą wartość
dla wywołań, które tylko przekazują tę wartość z zewnątrz. 

Druga metodą w `MonadReader`ze jest `.local`

{lang="text"}
~~~~~~~~
  def local[A](f: S => S)(fa: F[A]): F[A]
~~~~~~~~

Możemy zmodyfikować `S` i uruchomić `fa` wewnątrz takiego kontekstu. Przykładowym zastosowaniem `.local`
może być generowanie "śladów stosu", które mają sens dla naszej domeny, pozwalając nam tym samym
na zagnieżdżone logowanie! Polegając na typie `Meta` z poprzedniego rozdziału, możemy zdefiniować 
poniższą funkcję:

{lang="text"}
~~~~~~~~
  def traced[A](fa: F[A])(implicit F: MonadReader[F, IList[Meta]]): F[A] =
    F.local(Meta.gen :: _)(fa)
~~~~~~~~

i używać jej do opakowywania funkcji, które wymagają takiego kontekstu

{lang="text"}
~~~~~~~~
  def foo: F[Foo] = traced(getBar) >>= barToFoo
~~~~~~~~

automatycznie przekazując dalej wszystko co nie jest oznaczone wprost. Plugin do kompilatora albo makro mogłoby
działać odwrotnie, śledząc wszystko automatycznie.

Jeśli wywołamy `.ask` zobaczymy dokładne ślady prowadzące do naszego wywołania, bez detali implementacyjnych
związanych z kodem bajtowym. Tym samym otrzymaliśmy referencyjnie transparenty ślad stosu!

Ostrożny programista mógłby chcieć w pewnym momencie przyciąć `IList[Meta]` aby uniknąć odpowiednika
przepełnienia stosu. Tym samym bardziej odpowiednią strukturą danych była by `Dequeue`.

`.local` może być użyte również do śledzenie informacji kontekstowych, które są bezpośrednio związane
z aktualnie wykonywanym zadaniem, jak na przykład liczba spacji potrzebnych do wcięcia linii, gdy wyświetlamy
format przyjazny dla ludzi, zwiększając tę liczbę o dwa, gdy zwiększamy zagnieżdżenie.

A> Nie cztery. Nie osiem. Nie TAB.
A>
A> Dwie spacje. Dokładnie dwie spacje. To jest magiczna liczba, którą możemy zahardkodować, ponieważ
A> wszystkie inne warianty są **błędne**.

W końcu, kiedy nie możemy zażądać instancji `MonadReader`, ponieważ nasza aplikacja nie umie takowej
dostarczyć, możemy zawsze zwrócić `ReaderT`

{lang="text"}
~~~~~~~~
  def bearer(implicit F: Monad[F]): ReaderT[F, RefreshToken, BearerToken] =
    ReaderT( token => for {
    ...
~~~~~~~~

Jeśli wywołujący otrzyma `ReaderT` i ma pod ręką parametr `token`, to wystarczy, że wywoła
`access.run(token)`, aby otrzymać `F[BearerToken]`.

Faktycznie, biorąc pod uwagę fakt, że nie mamy zbyt wiele wywołujących, powinniśmy wrócić do tradycyjnych
parametrów funkcji. `MonadReader` ma na najwięcej zastosowań, gdy:

1. możemy chcieć później przerefactorować kod, aby konfiguracja była przeładowywana
2. wartość nie jest używana przez metody pośredniczące (_intermediate callers_)
3. chcemy lokalnie zmienić jakąś zmienną

Dotty może zatrzymać funkcje niejawne dla siebie... my już mamy wszystko co nam potrzeba: `ReaderT` i `MonadReader`.


### `WriterT`

Odwrotnością czytania jest pisanie, a transformator monad `WriterT` służy właśnie do tego.

{lang="text"}
~~~~~~~~
  final case class WriterT[F[_], W, A](run: F[(W, A)])
  object WriterT {
    def put[F[_]: Functor, W, A](value: F[A])(w: W): WriterT[F, W, A] = ...
    def putWith[F[_]: Functor, W, A](value: F[A])(w: A => W): WriterT[F, W, A] = ...
    ...
  }
~~~~~~~~

Opakowywany typ to `F[(W, A)]`, a nasz dziennik jest akumulowany wewnątrz `W`.

Mamy do dyspozycji nie jedną, a dwie powiązane monady: `MonadTell` i `MonadListen`!

{lang="text"}
~~~~~~~~
  @typeclass trait MonadTell[F[_], W] extends Monad[F] {
    def writer[A](w: W, v: A): F[A]
    def tell(w: W): F[Unit] = ...
  
    def :++>[A](fa: F[A])(w: =>W): F[A] = ...
    def :++>>[A](fa: F[A])(f: A => W): F[A] = ...
  }
  
  @typeclass trait MonadListen[F[_], W] extends MonadTell[F, W] {
    def listen[A](fa: F[A]): F[(A, W)]
  
    def written[A](fa: F[A]): F[W] = ...
  }
~~~~~~~~

`MonadTell` służy do spisywania dziennika a `MonadListen` do jego odtwarzania.

Ich implementacja dla `WriterT` wygląda następująco:

{lang="text"}
~~~~~~~~
  implicit def monad[F[_]: Monad, W: Monoid] = new MonadListen[WriterT[F, W, ?], W] {
    def point[A](a: =>A) = WriterT((Monoid[W].zero, a).point)
    def bind[A, B](fa: WriterT[F, W, A])(f: A => WriterT[F, W, B]) = WriterT(
      fa.run >>= { case (wa, a) => f(a).run.map { case (wb, b) => (wa |+| wb, b) } })
  
    def writer[A](w: W, v: A) = WriterT((w -> v).point)
    def listen[A](fa: WriterT[F, W, A]) = WriterT(
      fa.run.map { case (w, a) => (w, (a, w)) })
  }
~~~~~~~~

Oczywistym zastosowaniem `MonadTell` jest logowanie lub zbieranie danych audytowych. Raz jeszcze używając
`Meta` możemy wyobrazić sobie taki log

{lang="text"}
~~~~~~~~
  sealed trait Log
  final case class Debug(msg: String)(implicit m: Meta)   extends Log
  final case class Info(msg: String)(implicit m: Meta)    extends Log
  final case class Warning(msg: String)(implicit m: Meta) extends Log
~~~~~~~~

i użyć `Dequeue[Log]` jako naszego dziennika. Tym razem zmodyfikujemy metodę `authenticate` z części kodu
odpowiedzialnej za obsługę OAuth2.

{lang="text"}
~~~~~~~~
  def debug(msg: String)(implicit m: Meta): Dequeue[Log] = Dequeue(Debug(msg))
  
  def authenticate: F[CodeToken] =
    for {
      callback <- user.start :++> debug("started the webserver")
      params   = AuthRequest(callback, config.scope, config.clientId)
      url      = config.auth.withQuery(params.toUrlQuery)
      _        <- user.open(url) :++> debug(s"user visiting $url")
      code     <- user.stop :++> debug("stopped the webserver")
    } yield code
~~~~~~~~

Moglibyśmy nawet połączyć to podejście ze śledzeniem opartym o `ReaderT`, aby uzyskać ustrukturalizowany log zdarzeń.

Dziennik może zostać odzyskany za pomocą `.written`, a następnie dowolnie modyfikowany.

Jednak istnieje silny argument za tym, aby logowanie otrzymało swoją własną algebrę. Poziom logowania jest często potrzebny
w momencie stworzenia wiadomości dla celów wydajnościowych, a ponad to logowanie często konfigurowane 
i zarządzane jest na poziomie całej aplikacji, a nie pojedynczych komponentów.

Parametr `W` w `WriterT` posiada `Monoid`, pozwalając nam tym samym na wszelkiego rodzaju monoidyczne operacje,
które będą działy się równolegle do naszego głównego programu. Możemy na przykład zliczać ile razy coś się wydarzyło,
budować opis obliczeń lub tworzyć `TradeTemplate` dla nowej transakcji, gdy ją wyceniamy.

Popularną specjalizacją `WriterT` jest użycie go z monadą `Id`, sprawiając, że leżąca pod spodem wartość `run` to prosta tupla `(W, A)`.

{lang="text"}
~~~~~~~~
  type Writer[W, A] = WriterT[Id, W, A]
  object WriterT {
    def writer[W, A](v: (W, A)): Writer[W, A] = WriterT[Id, W, A](v)
    def tell[W](w: W): Writer[W, Unit] = WriterT((w, ()))
    ...
  }
  final implicit class WriterOps[A](self: A) {
    def set[W](w: W): Writer[W, A] = WriterT(w -> self)
    def tell: Writer[A, Unit] = WriterT.tell(self)
  }
~~~~~~~~

W taki sposób możemy nieść dodatkową monoidyczną kalkulację obok dowolnej wartości bez kontekstu `F[_]`.

W skrócie, `WriterT` / `MonadTell` to sposoby na multizadaniowość w stylu FP.


### `StateT`

`StateT` pozwala nam włożyć (`.put`), wyciągnąć (`.get`) i zmodyfikować (`.modify`) wartość zarządzaną przez monadyczny kontekst.
Jest to czysto funkcyjny zamiennik dla `var`.

Jeśli mielibyśmy napisać nieczystą metodę korzystającą z mutowalnego stanu przechowywanego wewnątrz `var`, jej sygnatura
mogłaby przyjąć postać `() => F[A]`, a ona sama zwracałaby inną wartość przy każdym wywołaniu, zaburzając w ten sposób transparentność
referencyjną. W czystym FP taka funkcja przyjmuje stan jako wejście i produkuje i zwraca zmodyfikowany stan jako wyjście.
Dlatego też `StateT` opakowuje `S => F[(S,A)]`.

Powiązana monada to `MonadState`

{lang="text"}
~~~~~~~~
  @typeclass trait MonadState[F[_], S] extends Monad[F] {
    def put(s: S): F[Unit]
    def get: F[S]
  
    def modify(f: S => S): F[Unit] = get >>= (s => put(f(s)))
    ...
  }
~~~~~~~~

A> Typ `S` musi być niemutowalny. `.modify` nie jest tylną furtką do modyfikowania mutowalnych
A> struktur danych. Mutowalność jest nieczysta i dozwolona jedynie wewnątrz bloku `IO`.

Struktura `StateT` jest zaimplementowana nieco inaczej niż transformatory, które widzieliśmy do tej pory,
nie jest case klasą lecz ADT z dwoma wariantami:

{lang="text"}
~~~~~~~~
  sealed abstract class StateT[F[_], S, A]
  object StateT {
    def apply[F[_], S, A](f: S => F[(S, A)]): StateT[F, S, A] = Point(f)
  
    private final case class Point[F[_], S, A](
      run: S => F[(S, A)]
    ) extends StateT[F, S, A]
    private final case class FlatMap[F[_], S, A, B](
      a: StateT[F, S, A],
      f: (S, A) => StateT[F, S, B]
    ) extends StateT[F, S, B]
    ...
  }
~~~~~~~~

które są wyspecjalizowaną formą `Trampoline`, dając nam bezpieczeństwo stosu kiedy chcemy odwołać się
do leżącej pod spodem struktury za pomocą `.run`:

{lang="text"}
~~~~~~~~
  sealed abstract class StateT[F[_], S, A] {
    def run(initial: S)(implicit F: Monad[F]): F[(S, A)] = this match {
      case Point(f) => f(initial)
      case FlatMap(Point(f), g) =>
        f(initial) >>= { case (s, x) => g(s, x).run(s) }
      case FlatMap(FlatMap(f, g), h) =>
        FlatMap(f, (s, x) => FlatMap(g(s, x), h)).run(initial)
    }
    ...
  }
~~~~~~~~

`StateT` ze swoim ADT w trywialny sposób implementuje `MonadState`

{lang="text"}
~~~~~~~~
  implicit def monad[F[_]: Applicative, S] = new MonadState[StateT[F, S, ?], S] {
    def point[A](a: =>A) = Point(s => (s, a).point[F])
    def bind[A, B](fa: StateT[F, S, A])(f: A => StateT[F, S, B]) =
      FlatMap(fa, (_, a: A) => f(a))
  
    def get       = Point(s => (s, s).point[F])
    def put(s: S) = Point(_ => (s, ()).point[F])
  }
~~~~~~~~

`.pure` otrzymał swoją kopię `.stateT` w obiekcie towarzyszącym:

{lang="text"}
~~~~~~~~
  object StateT {
    def stateT[F[_]: Applicative, S, A](a: A): StateT[F, S, A] = ...
    ...
  }
~~~~~~~~

a `MonadTrans.liftM` jak zawsze dostarcza nam konstruktor `F[A] => StateT[F, S, A]`.

Popularną odmiana `StateT` jest `F = Id`. W takim wypadku opakowywany typ to `S => (S, A)`.
Scalaz definiuje alias typu `State` i wygodne funkcje to interakcji z nim, które udają `MonadState`:

{lang="text"}
~~~~~~~~
  type State[a] = StateT[Id, a]
  object State {
    def apply[S, A](f: S => (S, A)): State[S, A] = StateT[Id, S, A](f)
    def state[S, A](a: A): State[S, A] = State((_, a))
  
    def get[S]: State[S, S] = State(s => (s, s))
    def put[S](s: S): State[S, Unit] = State(_ => (s, ()))
    def modify[S](f: S => S): State[S, Unit] = ...
    ...
  }
~~~~~~~~

Wróćmy na chwilę do testów logiki biznesowej z `drone-dynamic-agents`. W Rozdziale 3 stworzyliśmy testowy interpreter `Mutable`,
który przechowywał liczbę wystartowanych i zatrzymanych węzłów w `var`.

{lang="text"}
~~~~~~~~
  class Mutable(state: WorldView) {
    var started, stopped: Int = 0
  
    implicit val drone: Drone[Id] = new Drone[Id] { ... }
    implicit val machines: Machines[Id] = new Machines[Id] { ... }
    val program = new DynAgentsModule[Id]
  }
~~~~~~~~

Teraz wiemy już jak napisać dużo lepszy interpreter używając `State`. Przy okazji skorzystamy z możliwości
zwiększenia dokładności naszej symulacji. Przypomnijmy nasz kluczowy obiekt przechowujący obraz świata:

{lang="text"}
~~~~~~~~
  final case class WorldView(
    backlog: Int,
    agents: Int,
    managed: NonEmptyList[MachineNode],
    alive: Map[MachineNode, Epoch],
    pending: Map[MachineNode, Epoch],
    time: Epoch
  )
~~~~~~~~

Skoro piszemy symulację świata na potrzeby naszych testów, to możemy zdefiniować typ danych
przechwytujący pełen obraz wszystkiego

{lang="text"}
~~~~~~~~
  final case class World(
    backlog: Int,
    agents: Int,
    managed: NonEmptyList[MachineNode],
    alive: Map[MachineNode, Epoch],
    started: Set[MachineNode],
    stopped: Set[MachineNode],
    time: Epoch
  )
~~~~~~~~

A> Jeszcze nie przepisaliśmy naszej aplikacji tak, aby w pełni wykorzystywała typy danych i typeklasy
A> dostępne w Scalaz i w dalszym ciągu używamy kolekcji z biblioteki standardowej. Nie musimy się jednak spieszyć,
A> gdyż to podejście jest proste a wykorzystywane typy mogą być używane w zgodzie z czystym FP.

Główną różnicą jest to, że mamy do dyspozycji zmienne `started` i `stopped`. Nasz interpreter może być budowany na bazie
`State[World, a]` pozwalając nam na weryfikacje tego jak wygląda zarówno `World` jak i `WorldView` po wykonaniu logiki biznesowej.

Interpretery udające zewnętrzne usługi Drone i Google będą wyglądać tak:

{lang="text"}
~~~~~~~~
  import State.{ get, modify }
  object StateImpl {
    type F[a] = State[World, a]
  
    private val D = new Drone[F] {
      def getBacklog: F[Int] = get.map(_.backlog)
      def getAgents: F[Int]  = get.map(_.agents)
    }
  
    private val M = new Machines[F] {
      def getAlive: F[Map[MachineNode, Epoch]]   = get.map(_.alive)
      def getManaged: F[NonEmptyList[MachineNode]] = get.map(_.managed)
      def getTime: F[Epoch]                      = get.map(_.time)
  
      def start(node: MachineNode): F[Unit] =
        modify(w => w.copy(started = w.started + node))
      def stop(node: MachineNode): F[Unit] =
        modify(w => w.copy(stopped = w.stopped + node))
    }
  
    val program = new DynAgentsModule[F](D, M)
  }
~~~~~~~~

a my możemy przepisać nasze testy tak, aby zachowywały konwencję:

- `world1` to stan świata przed uruchomieniem programu
- `view1` to widok świata z punktu widzenia aplikacji
- `world2` to stan świata po uruchomieniu programu
- `view2` to widok świata z punktu widzenia aplikacji po uruchomieniu programu

Przykład:

{lang="text"}
~~~~~~~~
  it should "request agents when needed" in {
    val world1          = World(5, 0, managed, Map(), Set(), Set(), time1)
    val view1           = WorldView(5, 0, managed, Map(), Map(), time1)
  
    val (world2, view2) = StateImpl.program.act(view1).run(world1)
  
    view2.shouldBe(view1.copy(pending = Map(node1 -> time1)))
    world2.stopped.shouldBe(world1.stopped)
    world2.started.shouldBe(Set(node1))
  }
~~~~~~~~

Moglibyśmy spojrzeć na naszą nieskończoną pętlę logiki biznesowej

{lang="text"}
~~~~~~~~
  state = initial()
  while True:
    state = update(state)
    state = act(state)
~~~~~~~~

i użyć w niej `StateT` do zarządzania stanem. Niestety, w ten sposób naruszylibyśmy *Regułę Najmniejszej Mocy* wymagając
`MonadState` zamiast aktualnie wymaganego `Applicative`. Tak więc całkowicie rozsądne jest zarządzanie ręczne
i przekazywanie stanu do `update` i `act`.

### `IndexedStateT`

Kod, który widzieliśmy do tej pory nie pochodzi ze Scalaz. Tak naprawdę `StateT` jest zaimplementowany tam
jako alias typu wskazujący na kolejny typ: `IndexedStateT`.

{lang="text"}
~~~~~~~~
  type StateT[F[_], S, A] = IndexedStateT[F, S, S, A]
~~~~~~~~

Implementacja `IndexedStateT` jest bardzo podobna do tej, którą widzieliśmy do tej pory, z dodatkiem
jednego parametru typu pozwalającego na to by stan wejściowy `S1` był inny niż stan wyjściowy `S2`:

{lang="text"}
~~~~~~~~
  sealed abstract class IndexedStateT[F[_], -S1, S2, A] {
    def run(initial: S1)(implicit F: Bind[F]): F[(S2, A)] = ...
    ...
  }
  object IndexedStateT {
    def apply[F[_], S1, S2, A](
      f: S1 => F[(S2, A)]
    ): IndexedStateT[F, S1, S2, A] = Wrap(f)
  
    private final case class Wrap[F[_], S1, S2, A](
      run: S1 => F[(S2, A)]
    ) extends IndexedStateT[F, S1, S2, A]
    private final case class FlatMap[F[_], S1, S2, S3, A, B](
      a: IndexedStateT[F, S1, S2, A],
      f: (S2, A) => IndexedStateT[F, S2, S3, B]
    ) extends IndexedStateT[F, S1, S3, B]
    ...
  }
~~~~~~~~

`IndexedStateT` nie posiada instancji `MonadState` kiedy `S1 != S2`, więc w takiej sytuacji musi nas zadowolić
instancja samego `Monad`.

Poniższy przykład został zaadaptowany z prezentacji Vincentego Maqrqueza [Index your State](https://www.youtube.com/watch?v=JPVagd9W4Lo).
Wyobraź sobie, że musimy zaprojektować algebraiczny interfejs dla dostępu do wartości typu `String`
za pomocą klucza typu `Int`. Załóżmy, że jedna z implementacji będzie opierała się na komunikacji sieciowej,
a kolejność wywołań jest kluczowa. Nasze pierwsze podejście mogłoby wyglądać tak:

{lang="text"}
~~~~~~~~
  trait Cache[F[_]] {
    def read(k: Int): F[Maybe[String]]
  
    def lock: F[Unit]
    def update(k: Int, v: String): F[Unit]
    def commit: F[Unit]
  }
~~~~~~~~

produkując błędy w czasie wykonania jeśli `.update` lub `.commit` zostaną wywołane bez wcześniejszego użycia
`.lock`. Alternatywą mógłby być skomplikowany DSL, którego nikt nie umiałby użyć bez zaglądania do dokumentacji.

Zamiast tego użyjemy `IndexedStateT`, aby wymusić odpowiedni stan na wywołującym. Zacznijmy od możliwych stanów 
wyrażonych jako ADT

{lang="text"}
~~~~~~~~
  sealed abstract class Status
  final case class Ready()                          extends Status
  final case class Locked(on: ISet[Int])            extends Status
  final case class Updated(values: Int ==>> String) extends Status
~~~~~~~~

i odświeżenia naszej algebry

{lang="text"}
~~~~~~~~
  trait Cache[M[_]] {
    type F[in, out, a] = IndexedStateT[M, in, out, a]
  
    def read(k: Int): F[Ready, Ready, Maybe[String]]
    def readLocked(k: Int): F[Locked, Locked, Maybe[String]]
    def readUncommitted(k: Int): F[Updated, Updated, Maybe[String]]
  
    def lock: F[Ready, Locked, Unit]
    def update(k: Int, v: String): F[Locked, Updated, Unit]
    def commit: F[Updated, Ready, Unit]
  }
~~~~~~~~

co spowoduje, że próba wywołania `.update` bez wcześniejszego `.lock` spowoduje błąd kompilacji

{lang="text"}
~~~~~~~~
  for {
        a1 <- C.read(13)
        _  <- C.update(13, "wibble")
        _  <- C.commit
      } yield a1
  
  [error]  found   : IndexedStateT[M,Locked,Ready,Maybe[String]]
  [error]  required: IndexedStateT[M,Ready,?,?]
  [error]       _  <- C.update(13, "wibble")
  [error]          ^
~~~~~~~~

pozwalając nam konstruować funkcje, które mogą być komponowane dzięki wyrażaniu swojego stanu explicite

{lang="text"}
~~~~~~~~
  def wibbleise[M[_]: Monad](C: Cache[M]): F[Ready, Ready, String] =
    for {
      _  <- C.lock
      a1 <- C.readLocked(13)
      a2 = a1.cata(_ + "'", "wibble")
      _  <- C.update(13, a2)
      _  <- C.commit
    } yield a2
~~~~~~~~

A> Wprowadziliśmy trochę zduplikowanego kodu w naszym API definiując wiele wariantów operacji `.read`
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   def read(k: Int): F[Ready, Ready, Maybe[String]]
A>   def readLocked(k: Int): F[Locked, Locked, Maybe[String]]
A>   def readUncommitted(k: Int): F[Updated, Updated, Maybe[String]]
A> ~~~~~~~~
A> 
A> zamiast
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   def read[S <: Status](k: Int): F[S, S, Maybe[String]]
A> ~~~~~~~~
A> 
A> Powodem jest podtypowanie (_subtyping_), które pozwala na kompilacje tego błędnego kodu
A> nadając mu sygnaturę `F[Nothing, Ready, Maybe[String]]`
A>
A> {lang="text"}
A> ~~~~~~~~
A>   for {
A>     a1 <- C.read(13)
A>     _  <- C.update(13, "wibble")
A>     _  <- C.commit
A>   } yield a1
A> ~~~~~~~~
A> 
A> Wynika to z faktu, że Scala definiuje typ `Nothing`, który jest podtypem wszystkich innych typów.
A> Na szczęście taki kod nie może być wywołany, ale nadal jest to oznaka kiepsko zaprojektowanego API,
A> ponieważ użytkownik musi pamiętać o przypisywaniu typów.
A>
A> Alternatywnie, można by również powstrzymać kompilator przed ingerowaniem `Nothing`, np. za pomocą
A> niejawnego parametru `NotNothing` pochodzącego ze Scalaz.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   def read[S <: Status](k: Int)(implicit NN: NotNothing[S]): F[S, S, Maybe[String]]
A> ~~~~~~~~
A> 
A> Wybór tego, które z trzech zaprezentowanych API jest najlepsze pozostaje kwestią 
A> osobistych preferencji projektanta.


### `IndexedReaderWriterStateT`

Ci, którzy chcieli kombinacji `ReaderT`, `WriterT` i `InedexedStateT` nie będą zawiedzeni.
Transformator `IndexedReaderWriterStateT` opakowuje `(R, S1) => F[(W, A, S2)]` gdzie `R`
to `Reader`, `W` służy do monoidycznych zapisów, a `S` do indeksowanych aktualizacji stanu.

{lang="text"}
~~~~~~~~
  sealed abstract class IndexedReaderWriterStateT[F[_], -R, W, -S1, S2, A] {
    def run(r: R, s: S1)(implicit F: Monad[F]): F[(W, A, S2)] = ...
    ...
  }
  object IndexedReaderWriterStateT {
    def apply[F[_], R, W, S1, S2, A](f: (R, S1) => F[(W, A, S2)]) = ...
  }
  
  type ReaderWriterStateT[F[_], -R, W, S, A] = IndexedReaderWriterStateT[F, R, W, S, S, A]
  object ReaderWriterStateT {
    def apply[F[_], R, W, S, A](f: (R, S) => F[(W, A, S)]) = ...
  }
~~~~~~~~

Do dyspozycji mamy skróty, bo trzeba przyznać, że te typy są tak długie, że wyglądają jak część
API J2EE.

{lang="text"}
~~~~~~~~
  type IRWST[F[_], -R, W, -S1, S2, A] = IndexedReaderWriterStateT[F, R, W, S1, S2, A]
  val IRWST = IndexedReaderWriterStateT
  type RWST[F[_], -R, W, S, A] = ReaderWriterStateT[F, R, W, S, A]
  val RWST = ReaderWriterStateT
~~~~~~~~

`IRWST` to bardziej wydajny odpowiednik ręcznie skonstruowanego *stosu* transformatorów 
`ReaderT[WriterT[IndexedStateT[F, ...], ...], ...]`.


### `TheseT`

`TheseT` pozwala nam wybrać czy błędy mają zakończyć obliczenia czy też mają być zakumulowane
w przypadku częściowego sukcesu. Stąd *zachowaj spokój i idź dalej* (_keep calm and carry on_).

Opakowywany typ danych to `F[A \&/ B]`, gdzie `A` to typ błędów, z wymaganą instancją `Semigroup`
jeśli chcemy je akumulować.

{lang="text"}
~~~~~~~~
  final case class TheseT[F[_], A, B](run: F[A \&/ B])
  object TheseT {
    def `this`[F[_]: Functor, A, B](a: F[A]): TheseT[F, A, B] = ...
    def that[F[_]: Functor, A, B](b: F[B]): TheseT[F, A, B] = ...
    def both[F[_]: Functor, A, B](ab: F[(A, B)]): TheseT[F, A, B] = ...
  
    implicit def monad[F[_]: Monad, A: Semigroup] = new Monad[TheseT[F, A, ?]] {
      def bind[B, C](fa: TheseT[F, A, B])(f: B => TheseT[F, A, C]) =
        TheseT(fa.run >>= {
          case This(a) => a.wrapThis[C].point[F]
          case That(b) => f(b).run
          case Both(a, b) =>
            f(b).run.map {
              case This(a_)     => (a |+| a_).wrapThis[C]
              case That(c_)     => Both(a, c_)
              case Both(a_, c_) => Both(a |+| a_, c_)
            }
        })
  
      def point[B](b: =>B) = TheseT(b.wrapThat.point[F])
    }
  }
~~~~~~~~

Nie istnieje żadna specjalna monada dla `TheseT` ponad `Monad`. Jeśli chcemy zakończyć
obliczenia zwracamy `This` ale akumulujemy błędy zwracając wartość `Both`, która zawiera także
poprawnie obliczoną część wyniku.

Możemy spojrzeć na `TheseT` z innej strony: `A` nie musi być wcale *błędem*. Podobnie jak w przypadku 
`WriterT`, `A` może być nośnikiem dla innej wartości, którą obliczamy wraz z `B`. `TheseT` pozwala
zatrzymać się, gdy coś specyficznego dla `A` tego od nas wymaga. Jak wtedy, gdy Charlie Bucket
wyrzucił swoją czekoladę (`B`) jak tylko odnalazł Złoty Kupon (`A`).

### `ContT`

*Styl Przekazywania Kontynuacji*[^cps] (CPS, _Continuation Passing Style_) to styl programowania, w którym
funkcje nigdy nie zwracają wartości, a zamiast tego *kontynuują* następne obliczenia. CPS jest popularny
w JavaScripcie i Lispie pozwalając na wykonywanie nieblokującego IO za pomocą callbacków, gdy dane stają się dostępne.
Bezpośrednie przełożenie tego wzorca na nieczystą Scalę wygląda mniej więcej tak:
 
[^cps]: Jakkolwiek dziwnie to brzmi

{lang="text"}
~~~~~~~~
  def foo[I, A](input: I)(next: A => Unit): Unit = next(doSomeStuff(input))
~~~~~~~~

Możemy sprawić, że ten kod stanie się czysty wprowadzając kontekst `F[_]`

{lang="text"}
~~~~~~~~
  def foo[F[_], I, A](input: I)(next: A => F[Unit]): F[Unit]
~~~~~~~~

i zwracając funkcję dla danego wejścia

{lang="text"}
~~~~~~~~
  def foo[F[_], I, A](input: I): (A => F[Unit]) => F[Unit]
~~~~~~~~

`ContT` to opakowanie dla takiej właśnie sygnatury, z dodatkiem instancji typeklasy `Monad`

{lang="text"}
~~~~~~~~
  final case class ContT[F[_], B, A](_run: (A => F[B]) => F[B]) {
    def run(f: A => F[B]): F[B] = _run(f)
  }
  object IndexedContT {
    implicit def monad[F[_], B] = new Monad[ContT[F, B, ?]] {
      def point[A](a: =>A) = ContT(_(a))
      def bind[A, C](fa: ContT[F, B, A])(f: A => ContT[F, B, C]) =
        ContT(c_fb => fa.run(a => f(a).run(c_fb)))
    }
  }
~~~~~~~~

i wygodnej składni do tworzenia `ContT` z monadycznej wartości:

{lang="text"}
~~~~~~~~
  implicit class ContTOps[F[_]: Monad, A](self: F[A]) {
    def cps[B]: ContT[F, B, A] = ContT(a_fb => self >>= a_fb)
  }
~~~~~~~~

Jednak proste użycie callbacków nie wnosi nic do programowania czysto funkcyjnego, ponieważ
poznaliśmy już sposób na sekwencyjne łączenie nieblokujących, potencjalnie rozproszonych,
obliczeń: `Monad`ę. Aby zobaczyć dlaczego kontynuacje są użyteczne musimy rozważyć
bardziej złożony przykład ze sztywnymi ograniczeniami projektowymi.


#### Control Flow

Załóżmy, że podzieliliśmy naszą aplikację na moduły, które mogą wykonywać operacje I/O, a każdy z nich
rozwijany jest przez osobny zespół:

{lang="text"}
~~~~~~~~
  final case class A0()
  final case class A1()
  final case class A2()
  final case class A3()
  final case class A4()
  
  def bar0(a4: A4): IO[A0] = ...
  def bar2(a1: A1): IO[A2] = ...
  def bar3(a2: A2): IO[A3] = ...
  def bar4(a3: A3): IO[A4] = ...
~~~~~~~~

Naszym celem jest wyprodukować `A0` na podstawie otrzymanego `A1`. Tam gdzie JavaScript lub Lisp
sięgnęliby po kontynuacje (ponieważ IO może blokować), my możemy po prostu połączyć funkcje

{lang="text"}
~~~~~~~~
  def simple(a: A1): IO[A0] = bar2(a) >>= bar3 >>= bar4 >>= bar0
~~~~~~~~

Możemy wynieść `.simple` do postaci kontynuacji używając `.cps` i odrobiny boilerplate'u:

{lang="text"}
~~~~~~~~
  def foo1(a: A1): ContT[IO, A0, A2] = bar2(a).cps
  def foo2(a: A2): ContT[IO, A0, A3] = bar3(a).cps
  def foo3(a: A3): ContT[IO, A0, A4] = bar4(a).cps
  
  def flow(a: A1): IO[A0]  = (foo1(a) >>= foo2 >>= foo3).run(bar0)
~~~~~~~~

Co zyskaliśmy? Po pierwsze, warto zauważyć, że przepływ kontroli w tej aplikacji biegnie od lewej do prawej strony

{width=60%}
![](images/contt-simple.png)

Co gdy jako autorzy `foo2` chcielibyśmy zmodyfikować wartość `a0`, którą otrzymujemy z prawej strony? 
W praktyce oznacza to podzielenie `foo2` na `foo2a` i `foo2b`

{width=75%}
![](images/contt-process1.png)

Dodajmy ograniczenie, że nie możemy zmodyfikować tego jak zdefiniowane są metody `flow` i `bar0`. 
Może na przykład pochodzą one z frameworka lub biblioteki, których używamy.

Nie jesteśmy w stanie przeprocesować `a0` poprzez modyfikację żadnej z pozostałych metod `barX`, 
jednak używając `ContT` możemy zaimplementować metodę `foo2` tak, aby mogła wykonać obliczenia
na podstawie wyniku kontynuacji `next`:

{width=45%}
![](images/contt-process2.png)

na przykład w taki sposób

{lang="text"}
~~~~~~~~
  def foo2(a: A2): ContT[IO, A0, A3] = ContT { next =>
    for {
      a3  <- bar3(a)
      a0  <- next(a3)
    } yield process(a0)
  }
~~~~~~~~

Nie jesteśmy ograniczeni do `.map`owania wartości. Możemy również wywołać `.bind` i zamienić
liniowy przepływ w pełnoprawny graf!

{width=50%}
![](images/contt-elsewhere.png)

{lang="text"}
~~~~~~~~
  def elsewhere: ContT[IO, A0, A4] = ???
  def foo2(a: A2): ContT[IO, A0, A3] = ContT { next =>
    for {
      a3  <- bar3(a)
      a0  <- next(a3)
      a0_ <- if (check(a0)) a0.pure[IO]
             else elsewhere.run(bar0)
    } yield a0_
  }
~~~~~~~~

Możemy też zostać przy oryginalnym przepływie i ponowić wszystkie dalsze operacje 

{width=45%}
![](images/contt-retry.png)

{lang="text"}
~~~~~~~~
  def foo2(a: A2): ContT[IO, A0, A3] = ContT { next =>
    for {
      a3  <- bar3(a)
      a0  <- next(a3)
      a0_ <- if (check(a0)) a0.pure[IO]
             else next(a3)
    } yield a0_
  }
~~~~~~~~

W tym wypadku ponawiamy operacje tylko raz, a nie w nieskończoność, np. upewniamy się
czy na pewno powinniśmy wykonać jakąś potencjalnie niebezpieczną operację.

W końcu możemy też wykonać akcje specyficzne dla kontekstu `ContT`, czyli w tym wypadku `IO`,
który pozwala nam na obsługę błędów i uprzątnięcie zasobów:

{lang="text"}
~~~~~~~~
  def foo2(a: A2): ContT[IO, A0, A3] = bar3(a).ensuring(cleanup).cps
~~~~~~~~


#### Kiedy Zamówić Spaghetti

Nie przez przypadek nasze diagramy wyglądają jak spaghetti. Tak właśnie się dzieje kiedy
zaczynamy bawić się przepływem kontroli. Wszystkie mechanizmy które omówiliśmy w tym podrozdziale
można w łatwy sposób zaimplementować bezpośrednio, gdy możemy zmodyfikować `flow`, a więc 
nie musimy używać `ContT`.

Jednak jeśli projektowalibyśmy framework, to system pluginów opartych na `ConT` i pozwalający użytkownikom
kontrolować przepływ byłby czymś wartym rozważenia. Czasem użytkownik po prostu chce spaghetti.

Gdyby kompilator Scali był napisany z użyciem CPS, to kolejne fazy kompilacji mogłyby komunikować się
ze sobą w prosty i regularny sposób. Plugin kompilatora mógłby wykonywać akcje bazując na wyinferowanym
typie wyrażenia pochodzącym z późniejszej fazy kompilacji. Podobnie kontynuacje byłyby dobrym API
dla systemu budowania projektów (_build tool_) albo edytora tekstu.

Pułapką `ConT` jest fakt, że nie jest to struktura bezpieczna od przepełnienia stosu, a więc
nie nadaje się do tworzenia programów, które nigdy się nie kończą.


#### Great, kid. Don't get `ContT`.

Bardziej złożony wariant `ContT` znany jako `IndexedContT` opakowuje `(A => F[B] => F[C])`.
Nowy parametr typu `C`definiuje typ zwracany przez cały pogram, który może być inny, niż
ten przekazywany między komponentami. Jednak jeśli `B` nie jest równe `C` to nie jesteśmy w stanie
zdefiniować `Monad`y.

Korzystając z okazji do zgeneralizowania jak to tylko możliwe, zarówno typ `IndexedContT` jak i `ConT` są
w praktyce zaimplementowane jako aliasy na jeszcze bardziej ogólną strukturę `IndexedContsT` (zwróć uwagę
na dodatkowe `s` przed `T`)

{lang="text"}
~~~~~~~~
  final case class IndexedContsT[W[_], F[_], C, B, A](_run: W[A => F[B]] => F[C])
  
  type IndexedContT[f[_], c, b, a] = IndexedContsT[Id, f, c, b, a]
  type ContT[f[_], b, a]           = IndexedContsT[Id, f, b, b, a]
  type ContsT[w[_], f[_], b, a]    = IndexedContsT[w, f, b, b, a]
  type Cont[b, a]                  = IndexedContsT[Id, Id, b, b, a]
~~~~~~~~

w której `W[_]` posiada instancję `Comonad`. Dla wspomnianych aliasów istnieją obiekty towarzyszące
z pomocnymi konstruktorami.

Wprawdzie pięć parametrów typów to raczej przesada, ale takie przegeneralizowanie pozostaje spójne
ze specyfiką kontynuacji.


### Stos Transformatorów i Niejednoznaczne Parametry Niejawne

Czas podsumować naszą wycieczkę wśród transformatorów monad zdefiniowanych w Scalaz.

Kiedy wiele transformatorów jest składanych ze sobą nazywamy to *stosem transformatorów* (_transformer stack_),
i mimo, że jest to dość rozwlekłe, to można odczytać dostarczane w ten sposób funkcjonalności. Jeśli skonstruujemy
kontekst `F[_]` taki jak

{lang="text"}
~~~~~~~~
  type Ctx[A] = StateT[EitherT[IO, E, ?], S, A]
~~~~~~~~

wiemy, że dodajemy obsługę błędów typu `E` (istnieje `MonadError[Ctx. E]`) i stan `A`
(istnieje `MonadState[Ctx, S]`).

Niestety istnieją pewne praktyczne przeciwności co do stosowania takich stosów i towarzyszących im
instancji typeklas:

1. Wiele niejawnych instancji `Monad` oznacza, że kompilator nie może odnaleźć odpowiedniej składni dla kontekstu
2. Monady nie komponują się w sposób ogólny, co oznacza, że kolejność zagnieżdżania ma znaczenie
3. Wszystkie interpretery muszą obsługiwać ten wspólny kontekst. Dla przykładu: jeśli mamy implementację pewnej algebry,
   która używa `IO`, to i tak musimy opakować ją w `StateT` i `EitherT`, mimo że nie będą one używane w interpreterze.
4. Każda warstwa niesie ze sobą koszt wydajnościowy. Niektóre transformatory są gorsze niż inne, np. `StateT` jest szczególnie kosztowny,
   ale nawet `EitherT` może sprawiać problemy z alokacją pamięci dla aplikacji o dużej przepustowości.

Porozmawiajmy o obejściach tych problemów.

#### Brak Składni

Powiedzmy, że mamy algebrę

{lang="text"}
~~~~~~~~
  trait Lookup[F[_]] {
    def look: F[Int]
  }
~~~~~~~~

i typy danych

{lang="text"}
~~~~~~~~
  final case class Problem(bad: Int)
  final case class Table(last: Int)
~~~~~~~~

które chcielibyśmy użyć w naszej logice biznesowej

{lang="text"}
~~~~~~~~
  def foo[F[_]](L: Lookup[F])(
    implicit
      E: MonadError[F, Problem],
      S: MonadState[F, Table]
  ): F[Int] = for {
    old <- S.get
    i   <- L.look
    _   <- if (i === old.last) E.raiseError(Problem(i))
           else ().pure[F]
  } yield i
~~~~~~~~

Pierwszy problem: nasz kod się nie kompiluje.

{lang="text"}
~~~~~~~~
  [error] value flatMap is not a member of type parameter F[Table]
  [error]     old <- S.get
  [error]              ^
~~~~~~~~

Istnieją pewne taktyczne rozwiązania tego problemu. Najbardziej oczywistym jest przyjęcie parametrów wprost

{lang="text"}
~~~~~~~~
  def foo1[F[_]: Monad](
    L: Lookup[F],
    E: MonadError[F, Problem],
    S: MonadState[F, Table]
  ): F[Int] = ...
~~~~~~~~

i wymaganie jedynie `Monad`y niejawnie poprzez ograniczenie kontekstu. Jednak oznacza to, że musimy ręcznie
przekazać `MonadError` i `MonadState` kiedy wywołujemy `foo1` oraz gdy wołamy inne metody, które wymagają 
parametrów niejawnych.

Drugim rozwiązaniem jest pozostawienie parametrów jako `implicit` i użycie przesłaniania nazw tak by wszystkie
stały się jawne. Pozwala to innym wywoływać nas używając niejawnego rozstrzygania, ale my nadal musimy
przekazywać parametry wprost, gdy są potrzebne.

{lang="text"}
~~~~~~~~
  @inline final def shadow[A, B, C](a: A, b: B)(f: (A, B) => C): C = f(a, b)
  
  def foo2a[F[_]: Monad](L: Lookup[F])(
    implicit
    E: MonadError[F, Problem],
    S: MonadState[F, Table]
  ): F[Int] = shadow(E, S) { (E, S) => ...
~~~~~~~~

Moglibyśmy też przesłonić tylko jedną z `Monad`, pozostawiając drugą tak by mogła być użyta do dostarczenia
nam potrzebnej składni i gdy wywołujemy inne metody.

{lang="text"}
~~~~~~~~
  @inline final def shadow[A, B](a: A)(f: A => B): B = f(a)
  ...
  
  def foo2b[F[_]](L: Lookup[F])(
    implicit
    E: MonadError[F, Problem],
    S: MonadState[F, Table]
  ): F[Int] = shadow(E) { E => ...
~~~~~~~~

Trzecia opcja, która niesie ze sobą wyższy koszt początkowy, to stworzenie własnej typeklasy,
która będzie przechowywać referencje do dwóch pozostałych, których potrzebujemy

{lang="text"}
~~~~~~~~
  trait MonadErrorState[F[_], E, S] {
    implicit def E: MonadError[F, E]
    implicit def S: MonadState[F, S]
  }
~~~~~~~~

i którą automatycznie wyderywujemy z dostępnych instancji `MonadError` i `MonadState`

{lang="text"}
~~~~~~~~
  object MonadErrorState {
    implicit def create[F[_], E, S](
      implicit
        E0: MonadError[F, E],
        S0: MonadState[F, S]
    ) = new MonadErrorState[F, E, S] {
      def E: MonadError[F, E] = E0
      def S: MonadState[F, S] = S0
    }
  }
~~~~~~~~

Teraz, gdy potrzebujemy `S` lub `E` mamy do nich dostęp poprzez `F.S` i `F.E`

{lang="text"}
~~~~~~~~
  def foo3a[F[_]: Monad](L: Lookup[F])(
    implicit F: MonadErrorState[F, Problem, Table]
  ): F[Int] =
    for {
      old <- F.S.get
      i   <- L.look
      _ <- if (i === old.last) F.E.raiseError(Problem(i))
      else ().pure[F]
    } yield i
~~~~~~~~

I tak jak w drugim podejściu, możemy wybrać jedną z `Monad` jako niejawną w naszym bloku, importując ją

{lang="text"}
~~~~~~~~
  def foo3b[F[_]](L: Lookup[F])(
    implicit F: MonadErrorState[F, Problem, Table]
  ): F[Int] = {
    import F.E
    ...
  }
~~~~~~~~


#### Komponowanie Transformatorów

`EitherT[StateT[...], ...]` posiada instancję `MonadError`, ale nie `MonadState`, natomiast `StateT[EitherT[...], ...]`
daje nam obie.

Rozwiązaniem jest przestudiowanie reguł niejawnej derywacji transformatorów zawartych w obiektach towarzyszących, 
aby upewnić się, że najbardziej zewnętrzny z nich dostarcza wszystkie instancje, których potrzebujemy.

Zasada kciuka: im bardziej skomplikowany transformator tym bliżej wierzchu stosu powinien być umieszczony. 
W tym rozdziale prezentowaliśmy je z rosnącym poziomem skomplikowania, co powinno ułatwić aplikację tej zasady.


#### Wynoszenie Interpreterów

Kontynuując ten sam przykład, załóżmy, że nasza algebra `Lookup` ma interpreter oparty o `IO`

{lang="text"}
~~~~~~~~
  object LookupRandom extends Lookup[IO] {
    def look: IO[Int] = IO { util.Random.nextInt }
  }
~~~~~~~~

ale chcielibyśmy, aby nasz kontekst wyglądał tak

{lang="text"}
~~~~~~~~
  type Ctx[A] = StateT[EitherT[IO, Problem, ?], Table, A]
~~~~~~~~

aby móc używać `MonadError` i `MonadState`. Oznacza to, że musimy opakować `LookupRandom` tak, aby mógł operować na `Ctx`.

A> Szanse na poprawne ustawienie typów przy pierwszy podejściu wynoszą w przybliżeniu 3720 do jednego.

Najpierw użyjemy metody `.liftM` z `MonadTrans`, która wynosi `F[A]` do postaci `G[F, A]`

{lang="text"}
~~~~~~~~
  final class MonadOps[F[_]: Monad, A](fa: F[A]) {
    def liftM[G[_[_], _]: MonadTrans]: G[F, A] = ...
    ...
  }
~~~~~~~~

Ważne jest, aby pamiętać, że parametr typu przekazywany do `.liftM` sam ma dwa parametry,
pierwszy o kształcie `_[_]` i drugi `_`. Jeśli stworzymy odpowiednie aliasy

{lang="text"}
~~~~~~~~
  type Ctx0[F[_], A] = StateT[EitherT[F, Problem, ?], Table, A]
  type Ctx1[F[_], A] = EitherT[F, Problem, A]
  type Ctx2[F[_], A] = StateT[F, Table, A]
~~~~~~~~

to możemy abstrahować ponad `MonadTrans`, aby wynieść `Lookup[F]` do dowolnego `Lookup[G[F, ?]]`
tak długo jak `G` to transformator monad:

{lang="text"}
~~~~~~~~
  def liftM[F[_]: Monad, G[_[_], _]: MonadTrans](f: Lookup[F]) =
    new Lookup[G[F, ?]] {
      def look: G[F, Int] = f.look.liftM[G]
    }
~~~~~~~~

Możemy więc opakować algebrę kolejno dla `EitherT` i `StateT`

{lang="text"}
~~~~~~~~
  val wrap1 = Lookup.liftM[IO, Ctx1](LookupRandom)
  val wrap2: Lookup[Ctx] = Lookup.liftM[EitherT[IO, Problem, ?], Ctx2](wrap1)
~~~~~~~~

Inny sposobem osiągnięcia tego samego rezultatu w pojedynczym kroku jest użycie typeklasy `MonadIO`,
która pozwala nam wynieść `IO` do stosu transformatorów:

{lang="text"}
~~~~~~~~
  @typeclass trait MonadIO[F[_]] extends Monad[F] {
    def liftIO[A](ioa: IO[A]): F[A]
  }
~~~~~~~~

i posiada instancje dla wszystkich popularnych kombinacji transformatorów.

Boilerplate potrzebny by wynieść interpreter oparty o `IO` do dowolnego kontekstu posiadającego
instancję `MonadIO` to dwie linie kodu (dla definicji interpretera), plus jedna linia dla każdego elementu algebry
i jedna linia wywołująca konwersję:

{lang="text"}
~~~~~~~~
  def liftIO[F[_]: MonadIO](io: Lookup[IO]) = new Lookup[F] {
    def look: F[Int] = io.look.liftIO[F]
  }
  
  val L: Lookup[Ctx] = Lookup.liftIO(LookupRandom)
~~~~~~~~

A> Plugin kompilatora, który automatycznie produkuje `.liftM`, `.liftIO` i pozostały boilerplate,
A> który zobaczyliśmy w tym rozdziale, byłby świetnym wkładem w ekosystem!


#### Wydajność

Największym problemem Transformatorów Monad jest ich narzut wydajnościowy. `EitherT` ma dość mały narzut,
gdzie każde wywołanie `.flatMap` generuje tylko garść obiektów, ale nawet to może wpłynąć na aplikacje
wymagające wysokiej przepustowości, gdzie każda alokacja ma znaczenie. Inne transformatory, takie jak
`StateT`, dodają trampolinę do każdego wywołania, a `ContT` przechowuje cały łańcuch wywołań w pamięci.

A> Dla niektórych aplikacji alokacje nie mają znaczenia, jeśli są one i tak ograniczone przez
A> wydajność sieci albo I/O. Zawsze sprawdzaj.

Jeśli wydajność staje się problemem, jedynym rozwiązaniem jest zrezygnować z Transformatorów Monad,
a przynajmniej ich struktur danych. Dużą zaletą typeklas opartych o `Monad`, takich jak np. `MonadState`,
jest fakt, że możemy stworzyć zoptymalizowany kontekst `F[_]`, który będzie dostarczał wspomniane typeklasy.
Zobaczymy jak stworzyć optymalne `F[_]` w następnych dwóch rozdziałach, kiedy bliżej przyjrzymy się poznanym już
strukturom `Free` i `IO`.

## Darmowy Lunch

Nasza branża pragnie bezpiecznych, wysokopoziomowych języków, które pozwalają na wysoką wydajność developerów
kosztem zmniejszonej wydajności kodu.

Kompilator Just In Time (JIT) na JVMie działa tak dobrze, że proste funkcje mogą działać porównywalnie 
szybko co ich odpowiedniki w C lub C++, ignorując koszt garbage collectora. Jednak JIT wykonuje jedynie
*optymalizacje niskopoziomowe*: predykcję gałęzi (_branch prediction_), inlinowanie metod, rozwijanie pętli itd.

JIT nie zastosuje optymalizacji do naszej logiki biznesowej, takich jak łączenia wywołań sieciowych lub 
uruchamiania niezależnych zadań równolegle. Developer jest odpowiedzialny za tworzenie logiki biznesowej i jej optymalizacje,
co efektywnie obniża czytelność i zwiększa koszt utrzymania kodu. Dobrze by było, gdyby optymalizacja
była problemem zupełnie niezależnym.

Jeśli mielibyśmy do dyspozycji struktury danych, które opisują naszą logikę biznesową w kontekście wysokopoziomowych
konceptów, a nie instrukcji maszynowych, moglibyśmy wykonać *wysokopoziomowe optymalizacje*. Takie struktury danych
są zazwyczaj nazywane *Darmowymi* strukturami (_Free structures_) i mogą być generowane za darmo dla elementów naszych
algebraicznych interfejsów. Przykładowo, instancje *Free Applicative* mogą być wygenerowane i użyte do połączenia 
lub deduplikacji kosztownych operacji sieciowych.

W tym rozdziale zobaczymy jak tworzyć takie darmowe struktury i jak ich używać.


### `Free` (`Monad`)

Zasadniczo, monada opisuje sekwencyjny program, gdzie każdy krok zależy od poprzedniego. 
Ograniczeni więc jesteśmy do modyfikacji, które wiedzą jedynie co już uruchomiliśmy i jaki
krok uruchomimy jako następny.

A> W okolicach 2015 modnym było pisanie programów FP używając `Free`, a więc będzie to ćwiczenie
A> tak samo pomagające zrozumieć tę strukturę jak i nauczyć się jej używać.
A> 
A> Aby stworzyć darmową strukturę potrzeba dużo boilerplate'u, więc potraktujmy to też
A> jako sposób na nauczenie się jak go wygenerować.

Przypomnijmy, `Free` to struktura danych reprezentująca `Monad`ę zdefiniowana jako trzy elementy

{lang="text"}
~~~~~~~~
  sealed abstract class Free[S[_], A] {
    def mapSuspension[T[_]](f: S ~> T): Free[T, A] = ...
    def foldMap[M[_]: Monad](f: S ~> M): M[A] = ...
    ...
  }
  object Free {
    implicit def monad[S[_], A]: Monad[Free[S, A]] = ...
  
    private final case class Suspend[S[_], A](a: S[A]) extends Free[S, A]
    private final case class Return[S[_], A](a: A)     extends Free[S, A]
    private final case class Gosub[S[_], A0, B](
      a: Free[S, A0],
      f: A0 => Free[S, B]
    ) extends Free[S, B] { type A = A0 }
  
    def liftF[S[_], A](value: S[A]): Free[S, A] = Suspend(value)
    ...
  }
~~~~~~~~

-   `Suspend` reprezentuje program, który nie został jeszcze zinterpretowany
-   `Return` to `.pure`
-   `Gosub` to `.bind`

Instancja `Free[S, A]` może być *wygenerowana za darmo* dla dowolnej algebry `S`. Aby zobaczyć to wprost,
rozważmy naszą algebrę `Machines`

{lang="text"}
~~~~~~~~
  trait Machines[F[_]] {
    def getTime: F[Epoch]
    def getManaged: F[NonEmptyList[MachineNode]]
    def getAlive: F[Map[MachineNode, Epoch]]
    def start(node: MachineNode): F[Unit]
    def stop(node: MachineNode): F[Unit]
  }
~~~~~~~~

Zdefiniujmy wygenerowane za darmo `Free` dla algebry `Machines` poprzez stworzenie ADT
odpowiadającego jej elementom. Każdy typ danych ma te same parametry wejściowe, jest sparametryzowany
typem zwracanym i ma taką samą nazwę:

{lang="text"}
~~~~~~~~
  object Machines {
    sealed abstract class Ast[A]
    final case class GetTime()                extends Ast[Epoch]
    final case class GetManaged()             extends Ast[NonEmptyList[MachineNode]]
    final case class GetAlive()               extends Ast[Map[MachineNode, Epoch]]
    final case class Start(node: MachineNode) extends Ast[Unit]
    final case class Stop(node: MachineNode)  extends Ast[Unit]
    ...
~~~~~~~~

Takie ADT jest Abstrakcyjnym Drzewem Składniowym (AST, _Abstract Syntax Tree_) ponieważ każdy element
reprezentuje obliczenia w naszym programie.

W> `Free` dla algebry `Machines` ma formę `Free[Machines.Ast, ?]`, a nie `Free[Machines, ?]`, a więc parametrem jest AST, a nie sama algebra.
W> Łatwo jest się pomylić, gdyż druga forma również bezproblemowo się kompiluje mimo tego, że nie ma najmniejszego sensu.

Następnie zdefiniujmy `.liftF`, implementację `Machines` dla kontekstu `Free[Ast, ?]`. Każda metoda
deleguje implementację do `Free.liftF` tworząc `Suspend`

{lang="text"}
~~~~~~~~
  ...
    def liftF = new Machines[Free[Ast, ?]] {
      def getTime = Free.liftF(GetTime())
      def getManaged = Free.liftF(GetManaged())
      def getAlive = Free.liftF(GetAlive())
      def start(node: MachineNode) = Free.liftF(Start(node))
      def stop(node: MachineNode) = Free.liftF(Stop(node))
    }
  }
~~~~~~~~

Kiedy skonstruowaliśmy program sparametryzowany z użyciem `Free`, aby go uruchomić musimy przekazać
*interpreter* (transformację naturalną `Ast ~> M`) do metody `.foldMap`. Jeśli mielibyśmy interpreter, 
który mapuje operacje do `IO`, moglibyśmy stworzyć program `IO[Unit]` z dostępnego AST 

{lang="text"}
~~~~~~~~
  def program[F[_]: Monad](M: Machines[F]): F[Unit] = ...
  
  val interpreter: Machines.Ast ~> IO = ...
  
  val app: IO[Unit] = program[Free[Machines.Ast, ?]](Machines.liftF)
                        .foldMap(interpreter)
~~~~~~~~

Dla kompletności, zaimplementujmy interpreter, który deleguje operacje do ich bezpośredniej implementacji. Taki
interpreter może być użyteczny jeśli reszta aplikacji również używa `Free` jako kontekstu, a my akurat mamy implementację
algebry bazującą na `IO` pod ręką:

{lang="text"}
~~~~~~~~
  def interpreter[F[_]](f: Machines[F]): Ast ~> F = λ[Ast ~> F] {
    case GetTime()    => f.getTime
    case GetManaged() => f.getManaged
    case GetAlive()   => f.getAlive
    case Start(node)  => f.start(node)
    case Stop(node)   => f.stop(node)
  }
~~~~~~~~

Ale nasza logika biznesowa potrzebuje więcej niż tylko algebry `Machines`. Oprócz niej
potrzebna jest też algebra `Drones`, zdefiniowana jako

{lang="text"}
~~~~~~~~
  trait Drone[F[_]] {
    def getBacklog: F[Int]
    def getAgents: F[Int]
  }
  object Drone {
    sealed abstract class Ast[A]
    ...
    def liftF = ...
    def interpreter = ...
  }
~~~~~~~~

Chcielibyśmy, aby nasze AST było kombinacją AST pochodzących z oby tych algebr. W Rozdziale
6 poznaliśmy `Coproduct`, dysjunkcję wyższego rodzaju:

{lang="text"}
~~~~~~~~
  final case class Coproduct[F[_], G[_], A](run: F[A] \/ G[A])
~~~~~~~~

Możemy więc użyć kontekstu `Free[Coproduct[Machines.Ast, Drone.Ast, ?], ?]`.

Moglibyśmy tworzyć instancję koproduktu ręcznie, ale utonęlibyśmy w morzu boilerplate'u,
a później musielibyśmy robić to raz jeszcze jeśli chcielibyśmy dodać trzecią algebrę.

Z pomocą przychodzi typeklasa `scalaz.Inject`:

{lang="text"}
~~~~~~~~
  type :<:[F[_], G[_]] = Inject[F, G]
  sealed abstract class Inject[F[_], G[_]] {
    def inj[A](fa: F[A]): G[A]
    def prj[A](ga: G[A]): Option[F[A]]
  }
  object Inject {
    implicit def left[F[_], G[_]]: F :<: Coproduct[F, G, ?]] = ...
    ...
  }
~~~~~~~~

Niejawna derywacja wygeneruje instancje `Inject` kiedy będziemy ich potrzebować, pozwalając nam
przepisać metodę `liftF` tak, aby działała dla dowolnej kombinacji AST:

{lang="text"}
~~~~~~~~
  def liftF[F[_]](implicit I: Ast :<: F) = new Machines[Free[F, ?]] {
    def getTime                  = Free.liftF(I.inj(GetTime()))
    def getManaged               = Free.liftF(I.inj(GetManaged()))
    def getAlive                 = Free.liftF(I.inj(GetAlive()))
    def start(node: MachineNode) = Free.liftF(I.inj(Start(node)))
    def stop(node: MachineNode)  = Free.liftF(I.inj(Stop(node)))
  }
~~~~~~~~

W tym wypadku `Ast :<: F` mówi nam, że `Ast` jest częścią pełnego zbioru instrukcji `F`.

A> Plugin kompilatora, który automatycznie wyprodukuje boilerplate związany z `scalaz.Free` byłby
A> świetnym wkładem w ekosystem! Pisanie go własnoręcznie jest nie tylko bolesne, ale wprowadza
A> możliwość zrobienia literówki, która w przypadku dwóch metod o tych samych sygnaturach 
A> może spowodować ciężkie do zdiagnozowania błędy.

Łącząc ze sobą wszystkie elementy, powiedzmy, że mamy program których abstrahuje ponad `Monad`ą

{lang="text"}
~~~~~~~~
  def program[F[_]: Monad](M: Machines[F], D: Drone[F]): F[Unit] = ...
~~~~~~~~
    
oraz mamy gotowe implementacja algebr `Machines` i `Drone`, z użyciem których możemy stworzyć interpretery:

{lang="text"}
~~~~~~~~
  val MachinesIO: Machines[IO] = ...
  val DroneIO: Drone[IO]       = ...
  
  val M: Machines.Ast ~> IO = Machines.interpreter(MachinesIO)
  val D: Drone.Ast ~> IO    = Drone.interpreter(DroneIO)
~~~~~~~~

i połączyć je w większy zbiór instrukcji używając pomocniczych metod z obiektu towarzyszącego
`NaturalTransformation`

{lang="text"}
~~~~~~~~
  object NaturalTransformation {
    def or[F[_], G[_], H[_]](fg: F ~> G, hg: H ~> G): Coproduct[F, H, ?] ~> G = ...
    ...
  }
  
  type Ast[a] = Coproduct[Machines.Ast, Drone.Ast, a]
  
  val interpreter: Ast ~> IO = NaturalTransformation.or(M, D)
~~~~~~~~

aby następnie użyć ich do wyprodukowania `IO`

{lang="text"}
~~~~~~~~
  val app: IO[Unit] = program[Free[Ast, ?]](Machines.liftF, Drone.liftF)
                        .foldMap(interpreter)
~~~~~~~~

Tym samym zatoczyliśmy koło! Mogliśmy przecież od razu użyć `IO` jako naszego kontekstu i uniknąć
`Free`. Po co więc zadaliśmy sobie cały ten trud? Poniżej znajdziemy kilka przykładów, gdy `Free` może być użyteczne.


#### Testowanie: Mocki i Stuby

Może to zabrzmieć obłudnie, jeśli po napisaniu całego tego boilerplate'u powiemy, że `Free` może
służyć do zmniejszenia jego ilości. Istnieje jednak pewna granica, za którą `Ast` zaczyna
mieć sens: gdy mamy dużo testów które wymagają stubowania implementacji.

Jeśli `.Ast` i `.liftF` zostały zdefiniowane dla danej algebry, możemy tworzyć *częściowe interpretery*

{lang="text"}
~~~~~~~~
  val M: Machines.Ast ~> Id = stub[Map[MachineNode, Epoch]] {
    case Machines.GetAlive() => Map.empty
  }
  val D: Drone.Ast ~> Id = stub[Int] {
    case Drone.GetBacklog() => 1
  }
~~~~~~~~

które posłużą nam do testowania naszego `program`u

{lang="text"}
~~~~~~~~
  program[Free[Ast, ?]](Machines.liftF, Drone.liftF)
    .foldMap(or(M, D))
    .shouldBe(1)
~~~~~~~~

Używając częściowych funkcji zamiast totalnych narażamy się na błędy w czasie wykonania. Wiele
zespołów godzi się na ten kompromis w swoich testach jednostkowych, bo popełniony błąd i tak zostanie
wykryty, gdy testy te nie zakończą się sukcesem.

Moglibyśmy osiągnąć to samo zachowanie implementując wszystkie metody z użyciem `???` i nadpisując
te, których aktualnie potrzebujemy.

A> Biblioteka [smock](https://github.com/djspiewak/smock) ma większe możliwości, ale na potrzeby tego krótkiego przykładu
A> możemy sami zdefiniować metodę `stub` używając sztuczki związanej z inferencją typów, która używana jest
A> w wielu miejscach w Scalaz. `Stub` jest osobną klasą, abyśmy mogli podać jedynie parametr typu `A`, pozostawiając
A> `F` i `G` do odgadnięcia kompilatorowi na podstawie wyrażenia po lewej stronie:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object Mocker {
A>     final class Stub[A] {
A>       def apply[F[_], G[_]](pf: PartialFunction[F[A], G[A]]): F ~> G = new (F ~> G) {
A>         def apply[α](fa: F[α]) = pf.asInstanceOf[PartialFunction[F[α], G[α]]](fa)
A>       }
A>     }
A>     def stub[A]: Stub[A] = new Stub[A]
A>   }
A> ~~~~~~~~


#### Monitoring

Aplikacje serwerowe są często monitorowane przez agenty, które manipulują bajtkodem aplikacji, wstrzykując 
profilery i wydobywając różnego rodzaju informacje o działaniu naszego kodu i jego wydajności.

Gdy naszym kontekstem jest `Free` nie musimy uciekać się do manipulacji bajtkodem. Zamiast tego
możemy zaimplementować interpreter, który będzie monitorować wykonywane operacje i raportować je z użyciem efektów ubocznych.

A> Introspekcja kodu w czasie wykonania jest jednym z nielicznych usprawiedliwień dla użycia efektów ubocznych.
A> Jeśli monitoring nie jest widoczny dla aplikacji, to nasze obliczenia nadal możemy traktować jako referencyjnie
A> transparentne. Tego samego argumentu zespoły używają, aby uzasadnić użycie logowania skutkującego efektami ubocznymi,
A> a my użyliśmy go pozwalając sobie na mutację stanu implementując `Memo`.

Rozważmy użycie takiego "agenta" o typie `Ast ~> Ast`, który zapisuje inwokacje metod: 

{lang="text"}
~~~~~~~~
  val Monitor = λ[Demo.Ast ~> Demo.Ast](
    _.run match {
      case \/-(m @ Drone.GetBacklog()) =>
        JmxAbstractFactoryBeanSingletonProviderUtilImpl.count("backlog")
        Coproduct.rightc(m)
      case other =>
        Coproduct(other)
    }
  )
~~~~~~~~

Moglibyśmy też wychwytywać wiadomości, które nas szczególnie interesują i logować, gdy się pojawią.

Możemy dołączyć `Monitor` do naszej produkcyjnej aplikacji opartej na `Free` za pomocą

{lang="text"}
~~~~~~~~
  .mapSuspension(Monitor).foldMap(interpreter)
~~~~~~~~

lub połączyć transformacje naturalne wywołując pojedyncze

{lang="text"}
~~~~~~~~
  .foldMap(Monitor.andThen(interpreter))
~~~~~~~~


#### Monkey Patching

Jako inżynierowie przywykliśmy już do próśb o dodanie dziwacznych obejść do kluczowej logiki aplikacji. 
Moglibyśmy chcieć wyrazić takie przypadki brzegowe jako *wyjątki od reguły* i obsługiwać je niezależnie
od reszty aplikacji.

Wyobraźmy sobie, że otrzymaliśmy poniższą notatkę od działu księgowości

> *PILNE: Bob używa węzła `#c0ffee` przy sprawozdaniu rocznym. NIE ZATRZYMUJCIE TEJ MASZYNY!1!*

Nie ma możliwości, aby wytłumaczyć Bobowi, że nie powinien używać naszych maszyn dla jego super
ważnych zadań, tak więc musimy zhakować naszą logikę biznesową i wypuścić zmianę na środowisko
produkcyjne tak szybko jak to możliwe.

Nasza łatka (_monkey patch_) może być przetłumaczona na strukturę `Free`, pozwalając nam zwrócić
wcześniej przygotowany wynik (`Free.pure`) zamiast wykonywania standardowych operacji. Implementacja
to specjalna transformacja naturalna:

{lang="text"}
~~~~~~~~
  val monkey = λ[Machines.Ast ~> Free[Machines.Ast, ?]] {
    case Machines.Stop(MachineNode("#c0ffee")) => Free.pure(())
    case other                                 => Free.liftF(other)
  }
~~~~~~~~

Praca skończona. Zerknąć czy działa, wypchnąć na produkcję, ustawić alarm na przyszły tydzień
żeby usunąć ten fragment i odebrać Bobowi dostęp do naszych serwerów.

W testach możemy użyć `State`, aby zapisywać wszystkie węzły, które zatrzymaliśmy:

{lang="text"}
~~~~~~~~
  type S = Set[MachineNode]
  val M: Machines.Ast ~> State[S, ?] = Mocker.stub[Unit] {
    case Machines.Stop(node) => State.modify[S](_ + node)
  }
  
  Machines
    .liftF[Machines.Ast]
    .stop(MachineNode("#c0ffee"))
    .foldMap(monkey)
    .foldMap(M)
    .exec(Set.empty)
    .shouldBe(Set.empty)
~~~~~~~~

Zaletą `Free` w tej sytuacji jest pewność, że obsłużyliśmy wszystkie użycia nie musząc
szukać ich w logice biznesowej. Jeśli kontekstem naszej aplikacji jest `IO` to moglibyśmy oczywiście
zaimplementować tę samą funkcjonalność w `Machines[IO]`, ale używając `Free` możemy taką
zamianę wyizolować i przetestować bez dotykania istniejącego kodu i bez wiązania się z `IO`.


### `FreeAp` (`Applicative`)

Mimo tego, że ten rozdział nazywa się **Zaawansowane Monady** kluczowe jest, że 
*nie powinniśmy używać monad dopóki naprawdę **naprawdę** nie musimy*. W tym podrozdziale
zobaczymy czemu `FreeAp` (free applicative) jest lepszy od monady `Free`.

`FreeAp` zdefiniowany jest jako struktura danych reprezentujące metody `ap` i `pure` z typeklasy `Applicative`:

{lang="text"}
~~~~~~~~
  sealed abstract class FreeAp[S[_], A] {
    def hoist[G[_]](f: S ~> G): FreeAp[G,A] = ...
    def foldMap[G[_]: Applicative](f: S ~> G): G[A] = ...
    def monadic: Free[S, A] = ...
    def analyze[M:Monoid](f: F ~> λ[α => M]): M = ...
    ...
  }
  object FreeAp {
    implicit def applicative[S[_], A]: Applicative[FreeAp[S, A]] = ...
  
    private final case class Pure[S[_], A](a: A) extends FreeAp[S, A]
    private final case class Ap[S[_], A, B](
      value: () => S[B],
      function: () => FreeAp[S, B => A]
    ) extends FreeAp[S, A]
  
    def pure[S[_], A](a: A): FreeAp[S, A] = Pure(a)
    def lift[S[_], A](x: =>S[A]): FreeAp[S, A] = ...
    ...
  }
~~~~~~~~

Metody `.hoist` i `.foldMap` odpowiadają metodom `.mapSuspension` i `.foldMap` z `Free`.

Możemy też wygenerować `Free[S, A]` bezpośrednio z naszego `FreeAp[S, A]` używając `.monadic`,
co jest szczególnie przydatne, gdy chcemy włączyć małe programy oparte o `FreeAp` do całego systemu
opartego o `Free`.

Podobnie jak z `Free`, musimy stworzyć `FreeAp` dla naszego AST. Więcej boilerplate'u...

{lang="text"}
~~~~~~~~
  def liftA[F[_]](implicit I: Ast :<: F) = new Machines[FreeAp[F, ?]] {
    def getTime = FreeAp.lift(I.inj(GetTime()))
    ...
  }
~~~~~~~~


#### Grupowanie Wywołań Sieciowych

Rozpoczęliśmy ten rozdział wzniosłymi obietnicami dotyczącymi wydajności. Czas ich dotrzymać.

Aby zrozumieć dlaczego powinniśmy zredukować ilość wywołań sieciowych spójrzmy na [ludzką wersję](https://gist.github.com/hellerbarde/2843375#file-latency_humanized-markdown)
liczb latencji autorstwa Philipa Starka, bazującą na [danych](http://norvig.com/21-days.html#answers) oryginalnie przygotowanych przez Petera Norviga.

| Komputer                          | Ludzka Skala Czasowa | Ludzka Analogia                           |
|-----------------------------------|----------------------|-------------------------------------------|
| Odwołanie do pamięci L1           | 0,5 sek.             | Uderzenie serca                           |
| Mispredykcja gałęzi               | 5 sek.               | Ziewnięcie                                |
| Odwołanie do pamięci L2           | 7 sek.               | Długie ziewnięcie                         |
| Zablokowanie/odblokowanie mutexa  | 25 sek.              | Przygotowanie herbaty                     |
| Odwołanie do pamięci głównej      | 100 sek.             | Umycie zębów                              |
| Skompresowanie 1 KB przez Zippy   | 50 min.               | Pipeline CI kompilatora Scali             |
| Przesłanie 2KB przez sieć 1Gbps   | 5,5 godz.               | Pociąg z Londynu do Edynburga             |
| Losowy odczyt z dysku SSD         | 1,7 dn.             | Weekend                                   |
| Sekwencyjny odczyt 1MB z pamięci  | 2,9 dn.             | Długi weekend                             |
| Podróż po jednym datacenter       | 5,8 dn.             | Długie wakacje w USA                      |
| Sekwencyjny odczyt 1MB z dysku SSD | 11,6 dn.            | Krótkie wakacje w Europie                 |
| Przesunięcie głowicy dyskowej     | 16,5 tyg.           | Semestr akademicki                        |
| Sekwencyjny odczyt 1MB z dysku    | 7,8 mies.           | Pełnopłatny urlop macierzyński w Norwegii |
| Wysłanie pakietu CA->Holandia->CA | 4,8 r.            | Kadencja rządu                            |

Mimo że zarówno `Free` jak i `FreeAp` niosą ze sobą narzut spowodowany alokacją pamięci (100 sekund na ludzkiej skali),
to za każdym razem, gdy uda nam się połączyć dwa żądania sieciowe w jedno zyskujemy prawie 5 lat.

Kiedy jesteśmy w kontekście `Applicative` możemy bezpiecznie optymalizować naszą aplikację bez zaburzania oczekiwań
co do oryginalnego programu i bez komplikowania logiki biznesowej.

Przypomnijmy, że nasza główna logika biznesowa wymaga, na szczęście, jedynie instancji `Applicative`

{lang="text"}
~~~~~~~~
  final class DynAgentsModule[F[_]: Applicative](D: Drone[F], M: Machines[F])
      extends DynAgents[F] {
    def act(world: WorldView): F[WorldView] = ...
    ...
  }
~~~~~~~~

Zacznijmy od stworzenia boilerplate'u `lift` dla nowej algebry `Batch`

{lang="text"}
~~~~~~~~
  trait Batch[F[_]] {
    def start(nodes: NonEmptyList[MachineNode]): F[Unit]
  }
  object Batch {
    sealed abstract class Ast[A]
    final case class Start(nodes: NonEmptyList[MachineNode]) extends Ast[Unit]
  
    def liftA[F[_]](implicit I: Ast :<: F) = new Batch[FreeAp[F, ?]] {
      def start(nodes: NonEmptyList[MachineNode]) = FreeAp.lift(I.inj(Start(nodes)))
    }
  }
~~~~~~~~

oraz instancji `DynAgentsModule` używając `FreeAp` jako kontekstu

{lang="text"}
~~~~~~~~
  type Orig[a] = Coproduct[Machines.Ast, Drone.Ast, a]
  
  val world: WorldView = ...
  val program = new DynAgentsModule(Drone.liftA[Orig], Machines.liftA[Orig])
  val freeap  = program.act(world)
~~~~~~~~

W Rozdziale 6 poznaliśmy typ danych `Const`, który pozwala nam analizować wykonanie programu. Nie powinno
więc dziwić, że `FreeAp.analyze` jest zaimplementowane z jego właśnie użyciem:

{lang="text"}
~~~~~~~~
  sealed abstract class FreeAp[S[_], A] {
    ...
    def analyze[M: Monoid](f: S ~> λ[α => M]): M =
      foldMap(λ[S ~> Const[M, ?]](x => Const(f(x)))).getConst
  }
~~~~~~~~

Używamy transformacji naturalnej i `.analyze`, aby zebrać wszystkie węzły, które powinny zostać wystartowane

{lang="text"}
~~~~~~~~
  val gather = λ[Orig ~> λ[α => IList[MachineNode]]] {
    case Coproduct(-\/(Machines.Start(node))) => IList.single(node)
    case _                                    => IList.empty
  }
  val gathered: IList[MachineNode] = freeap.analyze(gather)
~~~~~~~~

Następnym krokiem jest rozszerzenie zbioru instrukcji z `Orig` do `Extended`, tak by zawierał
`Batch.Ast`, oraz napisanie programu z użyciem `FreeAp`, który wystartuje wszystkie zebrane wcześniej węzły
pojedynczym żądaniem.

{lang="text"}
~~~~~~~~
  type Extended[a] = Coproduct[Batch.Ast, Orig, a]
  def batch(nodes: IList[MachineNode]): FreeAp[Extended, Unit] =
    nodes.toNel match {
      case None        => FreeAp.pure(())
      case Some(nodes) => FreeAp.lift(Coproduct.leftc(Batch.Start(nodes)))
    }
~~~~~~~~

Musimy również pozbyć się wszystkich wywołań `Machines.Start`, co możemy osiągnąć używając jeszcze jednej transformacji naturalnej

{lang="text"}
~~~~~~~~
  val nostart = λ[Orig ~> FreeAp[Extended, ?]] {
    case Coproduct(-\/(Machines.Start(_))) => FreeAp.pure(())
    case other                             => FreeAp.lift(Coproduct.rightc(other))
  }
~~~~~~~~

Mamy teraz dwa programy, które musimy połączyć. Przypomnijmy sobie operator `*>` z `Apply`

{lang="text"}
~~~~~~~~
  val patched = batch(gathered) *> freeap.foldMap(nostart)
~~~~~~~~

I złóżmy to wszystko razem jako jedną metodę

{lang="text"}
~~~~~~~~
  def optimise[A](orig: FreeAp[Orig, A]): FreeAp[Extended, A] =
    (batch(orig.analyze(gather)) *> orig.foldMap(nostart))
~~~~~~~~

I tyle! Wystarczy użyć `.optimise` razem z `act` w głównej pętli naszego programu.


### `Coyoneda` (`Functor`)

To "darmowa" (_free_) struktura danych zawdzięczająca swoją nazwę matematykowi Nobuo Yoneda. Pozwala nam ona wygenerować "za darmo" instancję
typeklasy `Functor` dla dowolnej algebry `S[_]`, tak długo, jak mamy w planie przetransformować ją do algebry, która taką instancję posiada `

{lang="text"}
~~~~~~~~
  sealed abstract class Coyoneda[F[_], A] {
    def run(implicit F: Functor[F]): F[A] = ...
    def trans[G[_]](f: F ~> G): Coyoneda[G, A] = ...
    ...
  }
  object Coyoneda {
    implicit def functor[F[_], A]: Functor[Coyoneda[F, A]] = ...
  
    private final case class Map[F[_], A, B](fa: F[A], f: A => B) extends Coyoneda[F, A]
    def apply[F[_], A, B](sa: F[A])(f: A => B) = Map[F, A, B](sa, f)
    def lift[F[_], A](sa: F[A]) = Map[F, A, A](sa, identity)
    ...
  }
~~~~~~~~

również w wersji kontrawariantnej

{lang="text"}
~~~~~~~~
  sealed abstract class ContravariantCoyoneda[F[_], A] {
    def run(implicit F: Contravariant[F]): F[A] = ...
    def trans[G[_]](f: F ~> G): ContravariantCoyoneda[G, A] = ...
    ...
  }
  object ContravariantCoyoneda {
    implicit def contravariant[F[_], A]: Contravariant[ContravariantCoyoneda[F, A]] = ...
  
    private final case class Contramap[F[_], A, B](fa: F[A], f: B => A)
      extends ContravariantCoyoneda[F, A]
    def apply[F[_], A, B](sa: F[A])(f: B => A) = Contramap[F, A, B](sa, f)
    def lift[F[_], A](sa: F[A]) = Contramap[F, A, A](sa, identity)
    ...
  }
~~~~~~~~

A> Określeniem potocznym na `Coyoneda` jest *coyo* a na `ContravariantCoyoned` *cocoyo*.

API jest nieco prostsze niż `Free` i `FreeAp`, udostępniając transformację poprzez `.trans`
i możliwość pozbycia się struktury poprzez metodę `.run` (która przyjmuje faktyczną implementację
`Functor`a lub `ContravariantFunctor`a).

Coyo i cocoyo są przydatne, gdy chcemy wywołać `.map` lub `.contramap` na typie, który
takich metod nie posiada, ale wiemy, że w końcu i tak przekonwertujemy go do innego typu,
pozbawionego tych ograniczeń, a na razie nie chcemy się z nim wiązać. Dla przykładu, możemy 
stworzyć `Coyoneda[ISet, ?]`, pamiętając, że `ISet` nie posiada instancji typeklasy `Functor`, aby
wywołać metody jej wymagające, a później przekonwertować taki obiekt do typu `IList`.

Aby użyć coyo lub cocoyo do optymalizacji naszego programu, musimy dostarczyć oczekiwany
boilerplate dla każdej algebry, której będziemy używać:

{lang="text"}
~~~~~~~~
  def liftCoyo[F[_]](implicit I: Ast :<: F) = new Machines[Coyoneda[F, ?]] {
    def getTime = Coyoneda.lift(I.inj(GetTime()))
    ...
  }
  def liftCocoyo[F[_]](implicit I: Ast :<: F) = new Machines[ContravariantCoyoneda[F, ?]] {
    def getTime = ContravariantCoyoneda.lift(I.inj(GetTime()))
    ...
  }
~~~~~~~~

Optymalizacją, którą możemy zastosować to *fuzja wywołań `.map`* (_map fusion_), co pozwala nam przepisać

{lang="text"}
~~~~~~~~
  xs.map(a).map(b).map(c)
~~~~~~~~

na

{lang="text"}
~~~~~~~~
  xs.map(x => c(b(a(x))))
~~~~~~~~

unikając pośrednich reprezentacji. Jeśli, na przykład, `xs` to `List`a z tysiącem elementów,
to oszczędzamy dwa tysiące alokacji wywołując `.map` tylko raz.

Jednak dużo prościej jest po prostu ręcznie zmienić oryginalną funkcję albo poczekać
na [`scalaz-plugin`](https://github.com/scalaz/scalaz-plugin), który automatycznie wykona tego typu
optymalizacje.


### Efekty Rozszerzalne

Programy to tylko dane, a struktury typu free wyrażają to wprost, pozwalając nam na
ich rearanżację i optymalizację.

`Free` jest bardziej niezwykła niż nam się wydaje: pozwala sekwencyjnie łączyć arbitralne algebry i typeklasy.

Na przykład, istnieje `Free` dla `MonadState`. `Ast` i `.liftF` są nieco bardziej skomplikowane niż zwykle, bo
muszą uwzględniać parametr typu `S` oraz dziedziczenie po typie `Monad`:

{lang="text"}
~~~~~~~~
  object MonadState {
    sealed abstract class Ast[S, A]
    final case class Get[S]()     extends Ast[S, S]
    final case class Put[S](s: S) extends Ast[S, Unit]
  
    def liftF[F[_], S](implicit I: Ast[S, ?] :<: F) =
      new MonadState[Free[F, ?], S] with BindRec[Free[F, ?]] {
        def get       = Free.liftF(I.inj(Get[S]()))
        def put(s: S) = Free.liftF(I.inj(Put[S](s)))
  
        val delegate         = Free.freeMonad[F]
        def point[A](a: =>A) = delegate.point(a)
        ...
      }
    ...
  }
~~~~~~~~

Daje nam to okazje do użycia zoptymalizowanego interpretera, który może na przykład przechowywać stan w atomowym
polu zamiast budować zagnieżdżone trampoliny `StateT`.

Możemy stworzyć `Ast` i `.liftF` dla niemal dowolnej algebry albo typeklasy. Jedyne ograniczenie jest takie, że
`F[_]` nie może pojawiać się jako parametr w żadnej instrukcji, a więc algebra musi móc mieć instancję typeklasy `Functor`.
Ograniczenie to wyklucza z użycia m.in. `MonadError` i `Monoid`.

A> Powód, dla którego kodowanie free nie działa dla wszystkich algebr i typeklas jest dość subtelny.
A>
A> Rozważmy co się stanie, jeśli stworzymy `Ast` dla `MonadError` gdzie `F[_]` występuje w pozycji kontrawariantnej, czyli
A> np. jako parametr.
A>
A> {lang="text"}
A> ~~~~~~~~
A>   object MonadError {
A>     sealed abstract class Ast[F[_], E, A]
A>     final case class RaiseError[F[_], E, A](e: E) extends Ast[F, E, A]
A>     final case class HandleError[F[_], E, A](fa: F[A], f: E => F[A]) extends Ast[F, E, A]
A>   
A>     def liftF[F[_], E](implicit I: Ast[F, E, ?] :<: F): MonadError[F, E] = ...
A>     ...
A>   }
A> ~~~~~~~~
A> 
A> Kiedy przychodzi moment interpretacji programu używającego `MonadError.Ast` musimy stworzyć koprodukt
A> wszystkich instrukcji. Powiedzmy, że chcemy rozszerzyć program bazujący na `Drone`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   type Ast[a] = Coproduct[MonadError.Ast[Ast, String, ?], Drone.Ast, a]
A> ~~~~~~~~
A> 
A> Taki zapis skutkuje błędem kompilacji, ponieważ `Ast` odwołuje się do samego siebie!
A> 
A> Algebry, które nie składają się w całości z kowariantnych sygnatur, tzn. takich gdzie `F[_]`
A> jest tylko zwracane z funkcji, nie mogą być interpretowane, ponieważ typ zwracany z programu odwołuje się do samego siebie.
A> W rzeczywistości nazwa *algebra*, której używamy ma swoje korzenie w [F-Algebrach](https://en.wikipedia.org/wiki/F-algebra),
A> gdzie F oznacza funktor.
A> 
A> *Podziękowania dla Edmunda Noble'a za zainicjowanie tej dyskusji.*

Wraz z rozrostem AST programu obniża się wydajność interpretera, ponieważ instrukcja dopasowania (_match_)
ma złożoność liniową względem obsługiwanych wariantów. Alternatywą do `scalaz.Coproduct` jest biblioteka [iotaz](https://github.com/frees-io/iota),
która używa zoptymalizowanej struktury danych, aby wykonać tę operację ze złożonością `O(1)` (używając liczb całkowitych
przydzielanych wariantom na etapie kompilacji).

Z przyczyn historycznych free AST dla algebry lub typeklasy jest nazywane *Initial Encoding*,
a bezpośrednia implementacja (np. z użyciem `IO`) to *Finally Tagless*. Mimo że omówiliśmy 
interesujące koncepty używając `Free`, to ogólnie przyjęta jest opinia, że finally tagless
jest podejściem lepszym. Jednak aby użyć tego podejścia musimy mieć do dyspozycji wydajny
typ efektu, który dostarczy nam wszystkie typeklasy, które omówiliśmy. Ponadto nadal
potrzebujemy sposobu na uruchomienie naszego kodu opartego o `Applicative` w sposób równoległy.

I dokładnie tym się teraz zajmiemy.


## `Parallel`

Są dwie operacje wywołujące efekty, które prawie zawsze chcemy wykonywać równolegle:

1. `.map` na kolekcji efektów, zwracając pojedynczy efekt. Można to osiągnąć za pomocą 
   metody `.traverse`, która deleguje do `.apply2` danego efektu.
2. uruchomienie danej liczby efektów z użyciem *operatora krzyku* `|@|` i połączenie ich
   wyników, również delegując do `.apply2`.

W praktyce jednak, żadna z tych operacji nie jest domyślnie wykonywana równolegle. Przyczyna 
jest prosta: jeśli nasze `F[_]` implementuje typeklasę `Monad`, wtedy muszą być zachowane
jej prawa co do `apply2`, tj.

{lang="text"}
~~~~~~~~
  @typeclass trait Bind[F[_]] extends Apply[F] {
    ...
    override def apply2[A, B, C](fa: =>F[A], fb: =>F[B])(f: (A, B) => C): F[C] =
      bind(fa)(a => map(fb)(b => f(a, b)))
    ...
  }
~~~~~~~~

Innymi słowy, **`Monad`om wprost zabrania się wykonywania efektów równolegle**.

Jednak, gdy mamy `F[_]`, które **nie** jest monadyczne, wtedy może ono implementować
`.apply2` w sposób równoległy. Możemy użyć mechanizmu `@@` (tagów), aby stworzyć instancję typeklasy `Applicative` dla 
`F[_] @@ Parallel`, która dorobiła się własnego aliasu `Applicative.Par`

{lang="text"}
~~~~~~~~
  object Applicative {
    type Par[F[_]] = Applicative[λ[α => F[α] @@ Tags.Parallel]]
    ...
  }
~~~~~~~~

Programy monadyczne mogą więc żądać niejawnego `Par` jako dodatku do ich `Monad`

{lang="text"}
~~~~~~~~
  def foo[F[_]: Monad: Applicative.Par]: F[Unit] = ...
~~~~~~~~

Metody `Traverse` ze Scalaz wspierają równoległe wykonanie:

{lang="text"}
~~~~~~~~
  implicit class TraverseSyntax[F[_], A](self: F[A]) {
    ...
    def parTraverse[G[_], B](f: A => G[B])(
      implicit F: Traverse[F], G: Applicative.Par[G]
    ): G[F[B]] = Tag.unwrap(F.traverse(self)(a => Tag(f(a))))
  }
~~~~~~~~

Jeśli w zakresie dostępna jest niejawna instancja `Applictive.Par[IO]`, to możemy wybrać między
sekwencyjną i równoległa trawersacją:

{lang="text"}
~~~~~~~~
  val input: IList[String] = ...
  def network(in: String): IO[Int] = ...
  
  input.traverse(network): IO[IList[Int]] // one at a time
  input.parTraverse(network): IO[IList[Int]] // all in parallel
~~~~~~~~

Podobnie możemy wywołać `.parApply` lub `.parTupled` po tym jak użyliśmy operatorów krzyku

{lang="text"}
~~~~~~~~
  val fa: IO[String] = ...
  val fb: IO[String] = ...
  val fc: IO[String] = ...
  
  (fa |@| fb).parTupled: IO[(String, String)]
  
  (fa |@| fb |@| fc).parApply { case (a, b, c) => a + b + c }: IO[String]
~~~~~~~~

Warto zaznaczyć, że kiedy mamy do czynienia z programami opartymi o `Applicative`, takimi jak

{lang="text"}
~~~~~~~~
  def foo[F[_]: Applicative]: F[Unit] = ...
~~~~~~~~

możemy używać `F[A] @@ Parallel` jako kontekstu, sprawiając, że `.traverse` i `|@|` wykonywane będą równolegle.
Konwersja między zwykłą i równoległą wersją `F[_]` musi być obsłużona ręcznie, co może być uciążliwe, więc
często łatwiej jest po prostu wymagać obu form `Applicative`.

{lang="text"}
~~~~~~~~
  def foo[F[_]: Applicative: Applicative.Par]: F[Unit] = ...
~~~~~~~~


### Łamiąc Prawo

Możemy przyjąć bardziej śmiałe podejście do zrównoleglania: zrezygnować z prawa, które każe
`.apply2` wykonywać operacje sekwencyjnie dla `Monad`. Jest to podejście mocno kontrowersyjne
ale działa zadziwiająco dobrze dla większości rzeczywistych aplikacji. Najpierw musimy jednak prześledzić nasz kod
w poszukiwaniu fragmentów, które mogłyby bazować na tym prawie, aby nie wprowadzić błędów. Później jest już tylko łatwiej.

Opakowujemy `IO`

{lang="text"}
~~~~~~~~
  final class MyIO[A](val io: IO[A]) extends AnyVal
~~~~~~~~

i dostarczamy naszą własną implementację `Monad`y, która uruchamia `.apply2` równolegle, poprzez oddelegowanie
do instancji dla typu `@@ Parallel`

{lang="text"}
~~~~~~~~
  object MyIO {
    implicit val monad: Monad[MyIO] = new Monad[MyIO] {
      override def apply2[A, B, C](fa: MyIO[A], fb: MyIO[B])(f: (A, B) => C): MyIO[C] =
        Applicative[IO.Par].apply2(fa.io, fb.io)(f)
      ...
    }
  }
~~~~~~~~

Od teraz możemy używać `MyIO` zamiast `IO` jako kontekstu naszej aplikacji i korzystać z **automatycznego zrównoleglania**.

A> Opakowywanie istniejących typów i dostarczanie własnych instancji typeklas znane jest jako
A> *newtyping*.
A> 
A> `@@` i newtyping są komplementarne: `@@` pozwala na żądanie konkretnych wariantów typeklas dla naszego modelu domenowego,
A> natomiast newtyping umożliwia definiowanie instancji dla konkretnej implementacji. To samo, tylko z różnymi punktami wejścia. 
A> 
A> Makro `@newtype` [autorstwa Cary'ego Robbinsa](https://github.com/estatico/scala-newtype) dostarcza zoptymalizowaną
A> implementację (bardziej wydajną niż `extends AnyVal`), która pozwala oddelegować te typeklasy, których nie chcemy zmieniać.
A> Możemy więc nadpisać `Monad` i oddelegować `Plus`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   @newtype class MyIO[A](io: IO[A])
A>   object MyIO {
A>     implicit val monad: Monad[MyIO] = ...
A>     implicit val plus: Plus[MyIO] = derived
A>   }
A> ~~~~~~~~

Dla kompletności: naiwna i niewydajna implementacja `Applicative.Par` dla naszego `IO` mogłaby używać `Future`:

{lang="text"}
~~~~~~~~
  object IO {
    ...
    type Par[a] = IO[a] @@ Parallel
    implicit val ParApplicative = new Applicative[Par] {
      override def apply2[A, B, C](fa: =>Par[A], fb: =>Par[B])(f: (A, B) => C): Par[C] =
        Tag(
          IO {
            val forked = Future { Tag.unwrap(fa).interpret() }
            val b      = Tag.unwrap(fb).interpret()
            val a      = Await.result(forked, Duration.Inf)
            f(a, b)
          }
        )
  }
~~~~~~~~

a z powodu [błędu w kompilatorze Scali](https://github.com/scala/bug/issues/10954), który powoduje, że wszystkie instancje dla typów `@@`
traktowane są jako instancje osierocone, musimy explicite zaimportować tą niejawną wartość:

{lang="text"}
~~~~~~~~
  import IO.ParApplicative
~~~~~~~~

W ostatniej sekcji tego rozdziału zobaczymy jak naprawdę zaimplementowany jest typ `IO` w Scalaz.


## `IO`

`IO` ze Scalaz jest najszybszą strukturą danych pozwalającą na programowanie asynchroniczne jaką możemy znaleźć w ekosystemie Scali, 
nawet do 50 razy szybsza niż `Future`.[^fastest] Zaprojektowana została jako monada do obsługi efektów ogólnego przeznaczenia. 

[^fastest]: Biblioteki takie jak Monix, cats-effect i Scalaz nieustannie prześcigają się w optymalizacjach mających na celu
zwiększenie wydajności, stąd ciężko jest określić kto jest aktualnym liderem.

{lang="text"}
~~~~~~~~
  sealed abstract class IO[E, A] { ... }
  object IO {
    private final class FlatMap         ... extends IO[E, A]
    private final class Point           ... extends IO[E, A]
    private final class Strict          ... extends IO[E, A]
    private final class SyncEffect      ... extends IO[E, A]
    private final class Fail            ... extends IO[E, A]
    private final class AsyncEffect     ... extends IO[E, A]
    ...
  }
~~~~~~~~

`IO` ma **dwa** parametry typu, a tym samym posiada instancję typeklasy `Bifunctor`, która pozwala
na zdefiniowanie błędów jako ADT specyficznego dla danej aplikacji. Niestety jesteśmy na JVMie oraz musimy
współpracować z istniejącymi bibliotekami, dlatego też zdefiniowany został pomocny alias, który używa
wyjątków jako typu błędów:

{lang="text"}
~~~~~~~~
  type Task[A] = IO[Throwable, A]
~~~~~~~~

A> `scalaz.ioeffect.IO` to biblioteka definiująca wysoce wydajne `IO` stworzona przez Johna de Goes. Jego cykl życia i wydań
A> jest niezależny od Scalaz i musi być dodany osobno do `build.sbt`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   libraryDependencies += "org.scalaz" %% "scalaz-ioeffect" % "2.10.1"
A> ~~~~~~~~
A> 
A> Pakiety `scalaz-effect` i `scalaz-concurrency` są zdeprecjonowane i nie powinny być używane.
A> Zalecamy używać `scalaz.ioeffect` i zdefiniowanych tam wariantów typeklas i typów danych.


### Tworzenie

Istnieje wiele sposobów na stworzenie `IO` z zarówno zachłannych i leniwych, jak i bezpiecznych i niebezpiecznych bloków kodu:

{lang="text"}
~~~~~~~~
  object IO {
    // eager evaluation of an existing value
    def now[E, A](a: A): IO[E, A] = ...
    // lazy evaluation of a pure calculation
    def point[E, A](a: =>A): IO[E, A] = ...
    // lazy evaluation of a side-effecting, yet Total, code block
    def sync[E, A](effect: =>A): IO[E, A] = ...
    // lazy evaluation of a side-effecting code block that may fail
    def syncThrowable[A](effect: =>A): IO[Throwable, A] = ...
  
    // create a failed IO
    def fail[E, A](error: E): IO[E, A] = ...
    // asynchronously sleeps for a specific period of time
    def sleep[E](duration: Duration): IO[E, Unit] = ...
    ...
  }
~~~~~~~~

wraz z wygodnymi konstruktorami dla `Task`a:

{lang="text"}
~~~~~~~~
  object Task {
    def apply[A](effect: =>A): Task[A] = IO.syncThrowable(effect)
    def now[A](effect: A): Task[A] = IO.now(effect)
    def fail[A](error: Throwable): Task[A] = IO.fail(error)
    def fromFuture[E, A](io: Task[Future[A]])(ec: ExecutionContext): Task[A] = ...
  }
~~~~~~~~

Najczęściej używanym wariantem, szczególnie przy pracy z istniejącym kodem, jest `Task.apply` oraz `Task.fromFuture`:

{lang="text"}
~~~~~~~~
  val fa: Task[Future[String]] = Task { ... impure code here ... }
  
  Task.fromFuture(fa)(ExecutionContext.global): Task[String]
~~~~~~~~

Nie możemy przekazywać instancji `Future` bezpośrednio, ponieważ obliczenia wewnątrz niej rozpoczynają się zachłannie w momencie
stworzenia, dlatego też tworzenie to musi odbyć się wewnątrz bezpiecznego bloku.

Zauważmy, że `ExecutionContext` **nie** jest przekazywany niejawnie, odwrotnie niż przyjęta konwencja.
W Scalaz parametry niejawne zarezerwowane są dla typeklas, a `ExecutionContext` to parametr konfiguracyjny,
a więc powinien być przekazany wprost.


### Uruchamianie

Interpreter `IO` nazywa się `RTS`, od *runtime system*, ale jego implementacja wybiega poza zakres tej książki.
W zamian omówimy funkcjonalności, które nam udostępnia.

`IO` to po prostu struktura danych, którą interpretujemy *na końcu świata* poprzez rozszerzenie `SafeApp` i zaimplementowanie
metody `.run`

{lang="text"}
~~~~~~~~
  trait SafeApp extends RTS {
  
    sealed trait ExitStatus
    object ExitStatus {
      case class ExitNow(code: Int)                         extends ExitStatus
      case class ExitWhenDone(code: Int, timeout: Duration) extends ExitStatus
      case object DoNotExit                                 extends ExitStatus
    }
  
    def run(args: List[String]): IO[Void, ExitStatus]
  
    final def main(args0: Array[String]): Unit = ... calls run ...
  }
~~~~~~~~

A> `Void` to typ danych, który nie ma żadnych wartości, podobnie jak `scala.Nothing`. 
A> Różnica między nimi polega na tym, jak traktowani są przez kompilator. `Nothing`
A> używany jest zawsze wtedy, gdy kompilatorowi nie uda się poprawnie wyinferować typów,
A> co może powodować mylące komunikaty błędów. `Void` nie ma tych problemów.
A> 
A> `Void` jako typ błędu oznacza, że operacja **musi się udać**, co oznacza, że
A> wszystkie błędy zostały wcześniej obsłużone.

Jeśli integrujemy się z istniejącym systemem i nie mamy kontroli nad punktem wejścia do naszej aplikacji, możemy
rozszerzyć `RTS` zyskując dostęp do niebezpiecznych metod, których możemy użyć, aby wyewaluować `IO`
na wejściu do czysto funkcyjnej części kodu. 


### Funkcjonalności

`IO` dostarcza instancje dla `Bifunctor`, `MonadError[E, ?]`, `BindRec`, `Plus`, `MonadPlus` (jeśli `E` formuje `Monoid`) oraz
`Applicative[IO.Par[E, ?]]`.

W dodatku do funkcjonalności pochodzących z typeklas, dostajemy implementację kilku specyficznych metod:

{lang="text"}
~~~~~~~~
  sealed abstract class IO[E, A] {
    // retries an action N times, until success
    def retryN(n: Int): IO[E, A] = ...
    // ... with exponential backoff
    def retryBackoff(n: Int, factor: Double, duration: Duration): IO[E, A] = ...
  
    // repeats an action with a pause between invocations, until it fails
    def repeat[B](interval: Duration): IO[E, B] = ...
  
    // cancel the action if it does not complete within the timeframe
    def timeout(duration: Duration): IO[E, Maybe[A]] = ...
  
    // runs `release` on success or failure.
    // Note that IO[Void, Unit] cannot fail.
    def bracket[B](release: A => IO[Void, Unit])(use: A => IO[E, B]): IO[E, B] = ...
    // alternative syntax for bracket
    def ensuring(finalizer: IO[Void, Unit]): IO[E, A] =
    // ignore failure and success, e.g. to ignore the result of a cleanup action
    def ignore: IO[Void, Unit] = ...
  
    // runs two effects in parallel
    def par[B](that: IO[E, B]): IO[E, (A, B)] = ...
    ...
~~~~~~~~

Instancja `IO` może być *zakończona* (_terminated_), co oznacza, że praca, która
była zaplanowana zostanie odrzucona (nie jest to ani sukces ani błąd). Narzędzia
do pracy z tym stanem to:

{lang="text"}
~~~~~~~~
  ...
    // terminate whatever actions are running with the given throwable.
    // bracket / ensuring is honoured.
    def terminate[E, A](t: Throwable): IO[E, A] = ...
  
    // runs two effects in parallel, return the winner and terminate the loser
    def race(that: IO[E, A]): IO[E, A] = ...
  
    // ignores terminations
    def uninterruptibly: IO[E, A] = ...
  ...
~~~~~~~~


### `Fiber`

`IO` może przywołać *włókna* (_fibers_), czyli lekką abstrakcję ponad wątkami udostępnianymi przez JVM.
Możemy rozgałęziać (`.fork`) `IO` i nadzorować (`.supervise`) niezakończone włókna, aby upewnić się, że
zostaną zakończone kiedy `IO` się wykona

{lang="text"}
~~~~~~~~
  ...
    def fork[E2]: IO[E2, Fiber[E, A]] = ...
    def supervised(error: Throwable): IO[E, A] = ...
  ...
~~~~~~~~

Kiedy mamy do dyspozycji włókno możemy je włączyć z powrotem do `IO` (`.join`) lub przerwać 
wykonywaną pracę (`.interrupt`).

{lang="text"}
~~~~~~~~
  trait Fiber[E, A] {
    def join: IO[E, A]
    def interrupt[E2](t: Throwable): IO[E2, Unit]
  }
~~~~~~~~

Możemy używać włókien do osiągnięcia optymistycznej kontroli współbieżności. Wyobraźmy sobie, że mamy dane (`data`),
które chcemy przeanalizować oraz zwalidować. Możemy optymistycznie rozpocząć analizę i przerwać ją, gdy walidacja, 
która uruchomiona jest równolegle, zakończy się niepowodzeniem.

{lang="text"}
~~~~~~~~
  final class BadData(data: Data) extends Throwable with NoStackTrace
  
  for {
    fiber1   <- analysis(data).fork
    fiber2   <- validate(data).fork
    valid    <- fiber2.join
    _        <- if (!valid) fiber1.interrupt(BadData(data))
                else IO.unit
    result   <- fiber1.join
  } yield result
~~~~~~~~

Innym zastosowaniem włókien jest sytuacja, gdy chcemy rozpocząć akcję i o niej zapomnieć, jak na przykład niskopriorytetowe
logowanie zdarzeń przez sieć.


### `Promise`

Obietnica (`Promise`) reprezentuje asynchroniczną zmienną, która może być ustawiona dokładnie raz (poprzez `.complete` lub `.error`).
Następnie dowolna liczba odbiorców może odczytać taką zmienną używając `.get`.

{lang="text"}
~~~~~~~~
  final class Promise[E, A] private (ref: AtomicReference[State[E, A]]) {
    def complete[E2](a: A): IO[E2, Boolean] = ...
    def error[E2](e: E): IO[E2, Boolean] = ...
    def get: IO[E, A] = ...
  
    // interrupts all listeners
    def interrupt[E2](t: Throwable): IO[E2, Boolean] = ...
  }
  object Promise {
    def make[E, A]: IO[E, Promise[E, A]] = ...
  }
~~~~~~~~

`Promise` nie jest zazwyczaj używany w kodzie aplikacyjnym. Jest to raczej element zaprojektowany do budowania
wyżejpoziomowych frameworków do obsługi współbieżności.

A> Kiedy wiemy, że operacja na pewno się uda, typ błędu `E` może być ustawiony dowolnie, tak aby mógł
A> dostosować się do preferencji użytkownika.


### `IORef`

`IORef` to odpowiednik mutowalnej zmiennej w świecie `IO`.

Możemy odczytać jej wartość oraz dostajemy do dyspozycji szereg operacji do manipulacji tą wartością.

{lang="text"}
~~~~~~~~
  final class IORef[A] private (ref: AtomicReference[A]) {
    def read[E]: IO[E, A] = ...
  
    // write with immediate consistency guarantees
    def write[E](a: A): IO[E, Unit] = ...
    // write with eventual consistency guarantees
    def writeLater[E](a: A): IO[E, Unit] = ...
    // return true if an immediate write succeeded, false if not (and abort)
    def tryWrite[E](a: A): IO[E, Boolean] = ...
  
    // atomic primitives for updating the value
    def compareAndSet[E](prev: A, next: A): IO[E, Boolean] = ...
    def modify[E](f: A => A): IO[E, A] = ...
    def modifyFold[E, B](f: A => (B, A)): IO[E, B] = ...
  }
  object IORef {
    def apply[E, A](a: A): IO[E, IORef[A]] = ...
  }
~~~~~~~~

`IORef` to kolejny typ danych, który może nam dostarczyć wysokowydajną instancję `MonadState`. 
Spróbujmy stworzyć nowy typ wyspecjalizowany do obsługi `Task`ów

{lang="text"}
~~~~~~~~
  final class StateTask[A](val io: Task[A]) extends AnyVal
  object StateTask {
    def create[S](initial: S): Task[MonadState[StateTask, S]] =
      for {
        ref <- IORef(initial)
      } yield
        new MonadState[StateTask, S] {
          override def get       = new StateTask(ref.read)
          override def put(s: S) = new StateTask(ref.write(s))
          ...
        }
  }
~~~~~~~~

Możemy wykorzystać tak zoptymalizowaną implementację `MonadState` w `SafeApp`, gdy nasz `.program`
wymaga instancji tej typeklasy:

{lang="text"}
~~~~~~~~
  object FastState extends SafeApp {
    def program[F[_]](implicit F: MonadState[F, Int]): F[ExitStatus] = ...
  
    def run(@unused args: List[String]): IO[Void, ExitStatus] =
      for {
        stateMonad <- StateTask.create(10)
        output     <- program(stateMonad).io
      } yield output
  }
~~~~~~~~

Bardziej realistyczna aplikacja wymagałaby zdecydowanie większej liczby różnych typeklas i algebr
jako wejścia.

A> Tak zoptymalizowana instancja `MonadState` jest konstruowana w sposób, który łamie koherencję typeklas.
A> Dwie instancje tego samego typu mogą zarządzać innym stanem. Rozważnym byłoby wyizolowanie tworzenia wszystkich takich instancji
A> w punkcie wejścia do naszej aplikacji.


#### `MonadIO`

Typ `MonadIO` który wcześniej widzieliśmy został uproszczony poprzez ukrycie parametru `E`. Prawdziwa jego 
forma wygląda tak:

{lang="text"}
~~~~~~~~
  trait MonadIO[M[_], E] {
    def liftIO[A](io: IO[E, A])(implicit M: Monad[M]): M[A]
  }
~~~~~~~~

wraz z drobną różnicą w boilerplacie kompaniującym naszej algebrze, uwzględniają dodatkowe `E`:

{lang="text"}
~~~~~~~~
  trait Lookup[F[_]] {
    def look: F[Int]
  }
  object Lookup {
    def liftIO[F[_]: Monad, E](io: Lookup[IO[E, ?]])(implicit M: MonadIO[F, E]) =
      new Lookup[F] {
        def look: F[Int] = M.liftIO(io.look)
      }
    ...
  }
~~~~~~~~


## Podsumowanie

1. Typ `Future` jest zepsuty, nie idź tą drogą.
2. Możemy zapanować nad bezpieczeństwem stosu za pomocą `Trampoline`.
3. Biblioteka Transformatorów Monad (MTL) abstrahuje nad popularnymi efektami za pomocą typeklas.
4. Transformatory Monad dostarczają domyślnych implementacji dla typeklas z MTL.
5. Struktura `Free` pozwala nam analizować, optymalizować i łatwo testować nasze programy.
6. `IO` umożliwia implementowanie algebr jako efektów wykonywanych na świecie zewnętrznym.
7. `IO` może wykonywać efekty równolegle i jest wysoce wydajnym fundamentem dla dowolnej aplikacji.


# Derywacja Typeklas

Typeklasy pozwalają na polimorfizm w naszym kodzie, ale aby z nich skorzystać potrzebujemy ich instancji
dla naszych obiektow domenowych.

*Derywacja typeklas* to proces tworzenia nowych instancji na podstawie instancji już istniejących, i to właśnie nim
zajemiemy się w tym rozdziale.

Istnieją cztery główne podejścia do tego zagadnienia:

1. Ręcznie tworzone instancje dla każdego obiektu domenowego. Wykorzystanie tego podejścia na codzień jest
   niewykonalne, gdyż skończylibyśmy z setkami linii czystego boilerplate'u dla każdej case klasy. Jego użyteczność
   ogranicza się więc jedynie do zastosowań edukacyjnych i doraźnych optymalizacji wydajnościowych.
2. Abstrahowanie ponad typeklasami z użyciem isntiejących typeklas ze Scalaz. To podejście wykorzystywane jest przez
   bibliotekę `scalaz-deriving`, która potrafi wygenerować zautomatyzowane testy oraz derywacje dla produktów i 
   koproduktów.
3. Makra, z tym, że napisanie makra dla każdej typeklasy wymaga doświadczonego dewelopera. Na szczęście [Magnolia](https://github.com/propensive/magnolia) 
   Jona Prettiego pozwala zastąpić ręcznie pisane makra prostym API, centralizując skomplikowane interakcje z kompilatorem.
4. Pisanie generycznych programów używając biblioteki [Shapeless](https://github.com/milessabin/shapeless/). Różne elementy opatrzone słowem
   kluczowym `implicit` tworzą osobny język wewnątrz Scali, który może być wykorzystany do implementowania skomplikowanej logiki
   na poziomie typów.

W tym rozdziale przeanalizujemy typeklasy o rosnącym stopniu skomplikowania i ich derywacje. Zaczniemy od `scalaz-deriving` jako
machanizmu najbardziej pryncypialnego, powtarzając niektóre lekcje z Rozdziału 5 "Typeklasy ze Scalaz". Następnie przejdziemy do
Magnolii, która jest najprostsza do użycia, a skończymy na Shapelessie, który jest najpotężniejszy i pozwala na derywacje
o skomplikowanej logice.

## Uruchamianie Przykładów

W tym rozdziale pokażemy jak zdefiniować derywacje pięciu konkretnych typeklas. Każda z nich pokazuje
funkcjonalność, która może być uogólniona:

{lang="text"}
~~~~~~~~
  @typeclass trait Equal[A]  {
    // type parameter is in contravariant (parameter) position
    @op("===") def equal(a1: A, a2: A): Boolean
  }
  
  // for requesting default values of a type when testing
  @typeclass trait Default[A] {
    // type parameter is in covariant (return) position
    def default: String \/ A
  }
  
  @typeclass trait Semigroup[A] {
    // type parameter is in both covariant and contravariant position (invariant)
    @op("|+|") def append(x: A, y: =>A): A
  }
  
  @typeclass trait JsEncoder[T] {
    // type parameter is in contravariant position and needs access to field names
    def toJson(t:
	T): JsValue
  }
  
  @typeclass trait JsDecoder[T] {
    // type parameter is in covariant position and needs access to field names
    def fromJson(j: JsValue): String \/ T
  }
~~~~~~~~

A> Istnieje szkoła, która mówi, że formaty serializcji takie jak JSON i XML **nie** powinny mieć
A> enkoderów i dekoderów w formie typeklas, ponieważ może to prowadzić do dekoherencji typeklas
A> (może zaistnieć więcej niż jeden enkoder lub dekoder dla tego samego typu). Alternatywą jest używanie
A> algebr i zupełne porzucenie `implicit`ów.
A> 
A> Mimo że w teorii możliwe jest zastosowanie technik opisanych w tym rozdziale zarówno do derywacji algebr jak i typeklas
A> to te pierwsze wymagają **zdecydowanie** więcej boilerplate'u. Dlatego też świadomie ograniczymy się
A> do enkoderów i dekoderów które są koherentne. Jak zobaczymy później, automatyczna derywacja po stronie użycia osiągnięta z użyciem
A> Magnolii lub Shapelessa, w połączeniu z ograniczeniami niejawnego rozstrzygania kompilatora, często prowadzi
A> do dekoherencji typeklas.

## `scalaz-deriving`

Biblioteka `scalaz-deriving` jest rozszerzeniem Scalaz i może być dodana do `build.sbt` za pomocą

{lang="text"}
~~~~~~~~
  val derivingVersion = "1.0.0"
  libraryDependencies += "org.scalaz" %% "scalaz-deriving" % derivingVersion
~~~~~~~~

dostarczając nam nowe typeklasy, pokazane poniżej w relacji do kluczowych typeklas ze Scalaz:

{width=60%}
![](images/scalaz-deriving-base.png)

A> W Scalaz 7.3 `Applicative` i `Divisible` będą dziedziczyć po `InvariantApplicative`

Zanim przejdziemy dalej, szybka powtórka z kluczowych typeklas w Scalaz:

{lang="text"}
~~~~~~~~
  @typeclass trait InvariantFunctor[F[_]] {
    def xmap[A, B](fa: F[A], f: A => B, g: B => A): F[B]
  }
  
  @typeclass trait Contravariant[F[_]] extends InvariantFunctor[F] {
    def contramap[A, B](fa: F[A])(f: B => A): F[B]
    def xmap[A, B](fa: F[A], f: A => B, g: B => A): F[B] = contramap(fa)(g)
  }
  
  @typeclass trait Divisible[F[_]] extends Contravariant[F] {
    def conquer[A]: F[A]
    def divide2[A, B, C](fa: F[A], fb: F[B])(f: C => (A, B)): F[C]
    ...
    def divide22[...] = ...
  }
  
  @typeclass trait Functor[F[_]] extends InvariantFunctor[F] {
    def map[A, B](fa: F[A])(f: A => B): F[B]
    def xmap[A, B](fa: F[A], f: A => B, g: B => A): F[B] = map(fa)(f)
  }
  
  @typeclass trait Applicative[F[_]] extends Functor[F] {
    def point[A](a: =>A): F[A]
    def apply2[A,B,C](fa: =>F[A], fb: =>F[B])(f: (A, B) => C): F[C] = ...
    ...
    def apply12[...]
  }
  
  @typeclass trait Monad[F[_]] extends Functor[F] {
    @op(">>=") def bind[A, B](fa: F[A])(f: A => F[B]): F[B]
  }
  @typeclass trait MonadError[F[_], E] extends Monad[F] {
    def raiseError[A](e: E): F[A]
    def emap[A, B](fa: F[A])(f: A => E \/ B): F[B] = ...
    ...
  }
~~~~~~~~


### Nie Powtarzaj Się

Najprostszym sposobem za derywacje typeklasy jest użycie typeklas już istniejących.

Typeklasa `Equal` posiada instancję `Contravariant[Equal]`, która z kolei dostarcza metodę `.contramap`:

{lang="text"}
~~~~~~~~
  object Equal {
    implicit val contravariant = new Contravariant[Equal] {
      def contramap[A, B](fa: Equal[A])(f: B => A): Equal[B] =
        (b1, b2) => fa.equal(f(b1), f(b2))
    }
    ...
  }
~~~~~~~~

Jako użytkownicy `Equal` możemy wykorzystać `.contramap` dla naszych jednoparametrowych typów danych.
Pamiętajmy, że instancje typeklas powinny trafić do obiektu towarzyszącego, aby znaleźć się w niejawnym zakresie:

{lang="text"}
~~~~~~~~
  final case class Foo(s: String)
  object Foo {
    implicit val equal: Equal[Foo] = Equal[String].contramap(_.s)
  }
  
  scala> Foo("hello") === Foo("world")
  false
~~~~~~~~

Jednak nie wszystkie typeklasy mogą posiadać instancję typu `Contravariant`. W szczególności typeklasy, których
parametry występują w pozycji kowariantnej mogą w zamian dostarczać `Functor`:

{lang="text"}
~~~~~~~~
  object Default {
    def instance[A](d: =>String \/ A) = new Default[A] { def default = d }
    implicit val string: Default[String] = instance("".right)
  
    implicit val functor: Functor[Default] = new Functor[Default] {
      def map[A, B](fa: Default[A])(f: A => B): Default[B] = instance(fa.default.map(f))
    }
    ...
  }
~~~~~~~~

Możemy teraz wyderywować `Default[Foo]` za pomocą

{lang="text"}
~~~~~~~~
  object Foo {
    implicit val default: Default[Foo] = Default[String].map(Foo(_))
    ...
  }
~~~~~~~~

Jeśli parametry typeklasy występują zarówno w pozycji kowariantnej jak i kontrawariantej, jak ma to miejsce
w przypadku `Semigroup`, to typeklasa taka może dostarczać `InvariantFunctor`

{lang="text"}
~~~~~~~~
  object Semigroup {
    implicit val invariant = new InvariantFunctor[Semigroup] {
      def xmap[A, B](ma: Semigroup[A], f: A => B, g: B => A) = new Semigroup[B] {
        def append(x: B, y: =>B): B = f(ma.append(g(x), g(y)))
      }
    }
    ...
  }
~~~~~~~~

i do jej derywacji użyjemy `.xmap`

{lang="text"}
~~~~~~~~
  object Foo {
    implicit val semigroup: Semigroup[Foo] = Semigroup[String].xmap(Foo(_), _.s)
    ...
  }
~~~~~~~~

W ogólności łatwiej jest użyć `.xmap` zamiast `.map` lub `.contramap`:

{lang="text"}
~~~~~~~~
  final case class Foo(s: String)
  object Foo {
    implicit val equal: Equal[Foo]         = Equal[String].xmap(Foo(_), _.s)
    implicit val default: Default[Foo]     = Default[String].xmap(Foo(_), _.s)
    implicit val semigroup: Semigroup[Foo] = Semigroup[String].xmap(Foo(_), _.s)
  }
~~~~~~~~

A> Anotacja `@xderiving` automatycznie wstawia `.xmap`. Aby jej użyć dodaj do `build.sbt`
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   addCompilerPlugin("org.scalaz" %% "deriving-plugin" % derivingVersion)
A>   libraryDependencies += "org.scalaz" %% "deriving-macro" % derivingVersion % "provided"
A> ~~~~~~~~
A> 
A> i użyj jej w poniższy sposób
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   @xderiving(Equal, Default, Semigroup)
A>   final case class Foo(s: String)
A> ~~~~~~~~


### `MonadError`

Zazwyczaj rzeczy, które wyciągają informacje z polimorficznej wartości posiadają instancję `Contravariant`,
a te które zapisują do takiej wartości definiują `Functor`. Jednak bardzo często taki odczyt
może się nie powieść. Przykładowo, to, że mamy domyślny `String` nie oznacza wcale, że możemy
bez problemu wyderywować z niego domyślny `String Refined NonEmpty`.

{lang="text"}
~~~~~~~~
  import eu.timepit.refined.refineV
  import eu.timepit.refined.api._
  import eu.timepit.refined.collection._
  
  implicit val nes: Default[String Refined NonEmpty] =
    Default[String].map(refineV[NonEmpty](_))
~~~~~~~~

skutkuje błędem kompilacji

{lang="text"}
~~~~~~~~
  [error] default.scala:41:32: polymorphic expression cannot be instantiated to expected type;
  [error]  found   : Either[String, String Refined NonEmpty]
  [error]  required: String Refined NonEmpty
  [error]     Default[String].map(refineV[NonEmpty](_))
  [error]                                          ^
~~~~~~~~

Kompilator przypomniał nam to, czego dowiedzieliśmy się w Rozdziale 4.1, czyli że `refineV` zwraca `Either`.

Jako autorzy typeklasy `Default` możemy postarać się troch bardziej niż `Functor` i dostarczyć `MonadError[Default, String]`:

{lang="text"}
~~~~~~~~
  implicit val monad = new MonadError[Default, String] {
    def point[A](a: =>A): Default[A] =
      instance(a.right)
    def bind[A, B](fa: Default[A])(f: A => Default[B]): Default[B] =
      instance((fa >>= f).default)
    def handleError[A](fa: Default[A])(f: String => Default[A]): Default[A] =
      instance(fa.default.handleError(e => f(e).default))
    def raiseError[A](e: String): Default[A] =
      instance(e.left)
  }
~~~~~~~~

Mamy teraz dostęp do `.emap` i możemy wyderywować instancję dla naszego rafinowanego typu

{lang="text"}
~~~~~~~~
  implicit val nes: Default[String Refined NonEmpty] =
    Default[String].emap(refineV[NonEmpty](_).disjunction)
~~~~~~~~

W praktyce, możemy dostarczyć regułę dla wszystkich rafinowanych typów

{lang="text"}
~~~~~~~~
  implicit def refined[A: Default, P](
    implicit V: Validate[A, P]
  ): Default[A Refined P] = Default[A].emap(refineV[P](_).disjunction)
~~~~~~~~

gdzie typ `Validate` pochodzi z biblioteki `refined`, a jego instancja wymagana jest przez `refineV`.


A> Biblioteka `refined-scalaz` zapewnia wsparcie dla automatycznej derywacji wszystkich typeklas
A> dla rafinowanych typów za pomocą 
A>
A> {lang="text"}
A> ~~~~~~~~
A>   import eu.timepit.refined.scalaz._
A> ~~~~~~~~
A>
A> jeśli tylko dostępna jest instancja `Contravariant` lub `MonadError[?, String]` dla danej typeklasy.
A>
A> W praktyce jednak mechanizm ten rzadko działa z powodu [ograniczeń kompilatora](https://github.com/scala/bug/issues/10753).

Podobnie możemy użyć `.emap`, aby wyderywować dekoder dla typu `Int` z instancji dla typu `Long`, chroniąc
się przed brakiem totalności `.toInt` z biblioteki standardowej.

{lang="text"}
~~~~~~~~
  implicit val long: Default[Long] = instance(0L.right)
  implicit val int: Default[Int] = Default[Long].emap {
    case n if (Int.MinValue <= n && n <= Int.MaxValue) => n.toInt.right
    case big => s"$big does not fit into 32 bits".left
  }
~~~~~~~~

Jako autorzy `Default` powinniśmy rozważyć API, w którym nie może dojść do błędu,
np. z użyciem takiej sygnatury

{lang="text"}
~~~~~~~~
  @typeclass trait Default[A] {
    def default: A
  }
~~~~~~~~

W takiej sytuacji nie bylibyśmy w stanie zdefiniować `MonadError`, wymuszając, aby
instancje zawsze produkowały poprawną wartość. Poskutkowałoby to większą ilością boilerplate'u,
ale również zwiększonym bezpieczeństwem w czasie kompilacji. Pozostaniemy jednak przy typie
zwracanym `String \/ A`, gdyż może służyć za bardziej ogólny przykład.


### `.fromIso`

Wszystkie typeklasy ze Scalaz mają w swoim obiekcie towarzyszącym metodę o sygnaturze
podobnej do:

{lang="text"}
~~~~~~~~
  object Equal {
    def fromIso[F, G: Equal](D: F <=> G): Equal[F] = ...
    ...
  }
  
  object Monad {
    def fromIso[F[_], G[_]: Monad](D: F <~> G): Monad[F] = ...
    ...
  }
~~~~~~~~

Oznacza to, że jeśli mamy typ `F` oraz sposób na jego konwersję do typu `G`, który posiada instancję danej typeklasy,
to wystarczy zawołać `.fromIso`, aby otrzymać instancję dla `F`.

Dla przykładu, mając typ danych `Bar` możemy bez problemu zdefiniować izomorfizm do `(String, Int)`

{lang="text"}
~~~~~~~~
  import Isomorphism._
  
  final case class Bar(s: String, i: Int)
  object Bar {
    val iso: Bar <=> (String, Int) = IsoSet(b => (b.s, b.i), t => Bar(t._1, t._2))
  }
~~~~~~~~

a następnie wyderywować `Equal[Bar]`, ponieważ istnieją już instancje `Equal` dla tupli dowolnego kształtu

{lang="text"}
~~~~~~~~
  object Bar {
    ...
    implicit val equal: Equal[Bar] = Equal.fromIso(iso)
  }
~~~~~~~~

Mechanizm `.fromIso` może też pomóc nam, jako autorom typeklas. Rozważmy `Default`, której rdzeniem
jest sygnatura `Unit => F[A]`. Tym samym metoda `default` jest izomorficzna w stosunku do `Kleisli[F. Unit, A]`, 
czyli transformatora `ReaderT`.

A skoro `Kleisli` posiada `MonadError` (jeśli tylko posiada go `F`), to możemy wyderywować
`MonadError[Default, String]` poprzez stworzenie izomorfizmu między `Default` i `Kleisli`:

{lang="text"}
~~~~~~~~
  private type Sig[a] = Unit => String \/ a
  private val iso = Kleisli.iso(
    λ[Sig ~> Default](s => instance(s(()))),
    λ[Default ~> Sig](d => _ => d.default)
  )
  implicit val monad: MonadError[Default, String] = MonadError.fromIso(iso)
~~~~~~~~

Tym samym zyskaliśmy `.map`, `.xmap` i `.emap`, których wcześniej używaliśmy, w praktyce za darmo.


### `Divisible` i `Applicative`

Aby wyderywować `Equal` dla naszej dwuparametrowej case klasy użyliśmy instancji dostarczanej przez Scalaz
dla tupli. Ale skąd wzięła się ta instancja?

Bardziej specyficzną typeklasą niż `Contravariant` jest `Divisible`, a `Equal` posiada jej instancję:

{lang="text"}
~~~~~~~~
  implicit val divisible = new Divisible[Equal] {
    ...
    def divide[A1, A2, Z](a1: =>Equal[A1], a2: =>Equal[A2])(
      f: Z => (A1, A2)
    ): Equal[Z] = { (z1, z2) =>
      val (s1, s2) = f(z1)
      val (t1, t2) = f(z2)
      a1.equal(s1, t1) && a2.equal(s2, t2)
    }
    def conquer[A]: Equal[A] = (_, _) => true
  }
~~~~~~~~

A> Implementując `Divisble` kompilator będzie od nas wymagał dostarczenia implementacji `.contramap`, 
A> którą możemy stworzyć bezpośrednio lub posłużyć się kombinatorem pochodnym:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   override def contramap[A, B](fa: F[A])(f: B => A): F[B] =
A>     divide2(conquer[Unit], fa)(c => ((), f(c)))
A> ~~~~~~~~
A> 
A> który został dodany do `Divisble` w Scalaz 7.3.

Bazując na `divide2`, `Dvisible` jest w stanie zbudować derywacje aż do `divide22`, które następnie możemy zawołać
bezpośrednio dla naszych typów danych:

{lang="text"}
~~~~~~~~
  final case class Bar(s: String, i: Int)
  object Bar {
    implicit val equal: Equal[Bar] =
      Divisible[Equal].divide2(Equal[String], Equal[Int])(b => (b.s, b.i))
  }
~~~~~~~~

Odpowiednikiem dla parametrów typu w pozycji kowariantnej jest `Applicative`:

{lang="text"}
~~~~~~~~
  object Bar {
    ...
    implicit val default: Default[Bar] =
      Applicative[Default].apply2(Default[String], Default[Int])(Bar(_, _))
  }
~~~~~~~~

Należy być jednak ostrożnym, aby nie zaburzyć praw rządzących `Divisble` i `Applicative`. 
Szczególnie łatwo jest naruszyć *prawo kompozycji*, które mówi, że oba poniższe
wywołania muszą wyprodukować ten sam wynik

-   `divide2(divide2(a1, a2)(dupe), a3)(dupe)`
-   `divide2(a1, divide2(a2, a3)(dupe))(dupe)`

dla dowolnego `dupe: A => (A, A)`. Dla `Applicative` sprawa wygląda podobnie.

Rozważmy `JsEncoder` i propozycję jej instancji `Divisible`

{lang="text"}
~~~~~~~~
  new Divisible[JsEncoder] {
    ...
    def divide[A, B, C](fa: JsEncoder[A], fb: JsEncoder[B])(
      f: C => (A, B)
    ): JsEncoder[C] = { c =>
      val (a, b) = f(c)
      JsArray(IList(fa.toJson(a), fb.toJson(b)))
    }
  
    def conquer[A]: JsEncoder[A] = _ => JsNull
  }
~~~~~~~~

Z jednej strony prawa kompozycji, dla wejścia typu `String`, otrzymujemy

{lang="text"}
~~~~~~~~
  JsArray([JsArray([JsString(hello),JsString(hello)]),JsString(hello)])
~~~~~~~~

a z drugiej

{lang="text"}
~~~~~~~~
  JsArray([JsString(hello),JsArray([JsString(hello),JsString(hello)])])
~~~~~~~~

Moglibyśmy eksperymentować z różnymi wariacjami `divide`, ale nigdy nie zaspokoilibyśmy
praw dla wszystkich możliwych wejść.

Dlatego też nie możemy dostarczyć `Divisible[JsEncoder]`, gdyż złamalibyśmy matematyczne prawa rządzące tą typeklasą,
tym samym zaburzając wszystkie założenia na bazie których użytkownicy `Divisible` budują swój kod.

Aby pomóc z testowaniem tych praw, typeklasy ze Scalaz zawierają ich skodyfikowaną wersję.
Możemy napisać zautomatyzowany test, przypominający nam, że złamaliśmy daną regułę:

{lang="text"}
~~~~~~~~
  val D: Divisible[JsEncoder] = ...
  val S: JsEncoder[String] = JsEncoder[String]
  val E: Equal[JsEncoder[String]] = (p1, p2) => p1.toJson("hello") === p2.toJson("hello")
  assert(!D.divideLaw.composition(S, S, S)(E))
~~~~~~~~

Z drugiej strony, test podobnej typeklasy `JsDecoder` pokazuje, że prawa `Applicative` są przez nią zachowane

{lang="text"}
~~~~~~~~
  final case class Comp(a: String, b: Int)
  object Comp {
    implicit val equal: Equal[Comp] = ...
    implicit val decoder: JsDecoder[Comp] = ...
  }
  
  def composeTest(j: JsValue) = {
    val A: Applicative[JsDecoder] = Applicative[JsDecoder]
    val fa: JsDecoder[Comp] = JsDecoder[Comp]
    val fab: JsDecoder[Comp => (String, Int)] = A.point(c => (c.a, c.b))
    val fbc: JsDecoder[((String, Int)) => (Int, String)] = A.point(_.swap)
    val E: Equal[JsDecoder[(Int, String)]] = (p1, p2) => p1.fromJson(j) === p2.fromJson(j)
    assert(A.applyLaw.composition(fbc, fab, fa)(E))
  }
~~~~~~~~

dla danych testowych

{lang="text"}
~~~~~~~~
  composeTest(JsObject(IList("a" -> JsString("hello"), "b" -> JsInteger(1))))
  composeTest(JsNull)
  composeTest(JsObject(IList("a" -> JsString("hello"))))
  composeTest(JsObject(IList("b" -> JsInteger(1))))
~~~~~~~~

Jesteśmy teraz w stanie zaufać, przynajmniej do pewnego stopnia, że nasza wyderywowana instancja `MonadError` przestrzega zasad.

Jednak udowodnienie, że taki test przechodzi dla konkretnego zbioru danych nie udowadnia, że prawa są zachowane.
Musimy jeszcze przeanalizować implementację i przekonać siebie samych, że prawa są **raczej** zachowane, a ponad to
powinniśmy spróbować wskazać przypadki w których mogłoby się to okazać nieprawdą.

Jednym ze sposobów generowania różnorodnych danych testowych jest użycie biblioteki [scalacheck](https://github.com/rickynils/scalacheck).
Dostarcza ona typeklasę `Arbitrary`, która integruje się z większością frameworków testowych, pozwalając powtarzać
testy na bazie losowo wygenerowanych danych.

Biblioteka `jsonFormat` dostarcza `Arbitrary[JsValue]` (każdy powinien dostarczać `Arbitrary` dla swoich ADT!) pozwalając nam
na skorzystanie z `forAll`:

{lang="text"}
~~~~~~~~
  forAll(SizeRange(10))((j: JsValue) => composeTest(j))
~~~~~~~~

Taki test daje nam jeszcze większą pewność, że nasza typeklasa spełnia wszystkie prawa kompozycji
dla `Applicative`. Sprawdzając wszystkie prawa dla `Divisble` i `MonadError` dostajemy też
**dużo** smoke testów zupełnie za darmo.

A> Musimy sparametryzować `forAll` za pomocą `SizeRange(10)`, aby ograniczyć wielkość obiektów `JsObject` i `JsArray` do maksymalnie
A> 10 elementów. W ten sposób unikamy przepełnienia stosu, gdyż większe liczby potrafią wygenerować
A> naprawdę gigantyczne dokumenty.


### `Decidable` i `Alt`

Tam gdzie `Divisble` i `Applicative` pozwalają nam na derywacje typeklas dla produktów (w oparciu o tuple),
`Decidable` i `Alt` umożliwiają ją dla koproduktów (opartych o zagnieżdżone dysjunkcje):

{lang="text"}
~~~~~~~~
  @typeclass trait Alt[F[_]] extends Applicative[F] with InvariantAlt[F] {
    def alt[A](a1: =>F[A], a2: =>F[A]): F[A]
  
    def altly1[Z, A1](a1: =>F[A1])(f: A1 => Z): F[Z] = ...
    def altly2[Z, A1, A2](a1: =>F[A1], a2: =>F[A2])(f: A1 \/ A2 => Z): F[Z] = ...
    def altly3 ...
    def altly4 ...
    ...
  }
  
  @typeclass trait Decidable[F[_]] extends Divisible[F] with InvariantAlt[F] {
    def choose1[Z, A1](a1: =>F[A1])(f: Z => A1): F[Z] = ...
    def choose2[Z, A1, A2](a1: =>F[A1], a2: =>F[A2])(f: Z => A1 \/ A2): F[Z] = ...
    def choose3 ...
    def choose4 ...
    ...
  }
~~~~~~~~

Te cztery typeklasy mają symetryczne sygnatury:

| Typeklasa     | Metoda    | Argumenty      | Sygnatura         | Typ zwracany |
|---------------|-----------|----------------|-------------------|--------------|
| `Applicative` | `apply2`  | `F[A1], F[A2]` | `(A1, A2) => Z`   | `F[Z]`       |
| `Alt`         | `altly2`  | `F[A1], F[A2]` | `(A1 \/ A2) => Z` | `F[Z]`       |
| `Divisible`   | `divide2` | `F[A1], F[A2]` | `Z => (A1, A2)`   | `F[Z]`       |
| `Decidable`   | `choose2` | `F[A1], F[A2]` | `Z => (A1 \/ A2)` | `F[Z]`       |

wspierając odpowiednio kowariantne produkty, kowariantne koprodukty, kontrawariantne produkty i kontrawariantne koprodukty.

Możemy stworzyć instancję `Decidable[Equal]`, która pozwoli na derywację `Equal` dla dowolnego ADT!

{lang="text"}
~~~~~~~~
  implicit val decidable = new Decidable[Equal] {
    ...
    def choose2[Z, A1, A2](a1: =>Equal[A1], a2: =>Equal[A2])(
      f: Z => A1 \/ A2
    ): Equal[Z] = { (z1, z2) =>
      (f(z1), f(z2)) match {
        case (-\/(s), -\/(t)) => a1.equal(s, t)
        case (\/-(s), \/-(t)) => a2.equal(s, t)
        case _ => false
      }
    }
  }
~~~~~~~~

Dla przykładowego ADT

{lang="text"}
~~~~~~~~
  sealed abstract class Darth { def widen: Darth = this }
  final case class Vader(s: String, i: Int)  extends Darth
  final case class JarJar(i: Int, s: String) extends Darth
~~~~~~~~

gdzie produkty (`Vader` i `JarJar`) mają swoje instancje `Equal`

{lang="text"}
~~~~~~~~
  object Vader {
    private val g: Vader => (String, Int) = d => (d.s, d.i)
    implicit val equal: Equal[Vader] = Divisible[Equal].divide2(Equal[String], Equal[Int])(g)
  }
  object JarJar {
    private val g: JarJar => (Int, String) = d => (d.i, d.s)
    implicit val equal: Equal[JarJar] = Divisible[Equal].divide2(Equal[Int], Equal[String])(g)
  }
~~~~~~~~

możemy wyderywować instancję dla całego ADT

{lang="text"}
~~~~~~~~
  object Darth {
    private def g(t: Darth): Vader \/ JarJar = t match {
      case p @ Vader(_, _)  => -\/(p)
      case p @ JarJar(_, _) => \/-(p)
    }
    implicit val equal: Equal[Darth] = Decidable[Equal].choose2(Equal[Vader], Equal[JarJar])(g)
  }
  
  scala> Vader("hello", 1).widen === JarJar(1, "hello).widen
  false
~~~~~~~~

A> Scalaz 7.2 nie dostarcza instancji `Decidable[Equal]`, ponieważ ta typeklasa była dodana później.

Typeklasy, która mają `Applicative` kwalifikują się również do `Alt`. Jeśli chcemy użyć triku z `Kleisli.iso`,
musimy rozszerzyć `IsomorphismMonadError` i domiksować `Alt`. Rozszerzmy więc naszą instancję `MonadError[Default, String`:

{lang="text"}
~~~~~~~~
  private type K[a] = Kleisli[String \/ ?, Unit, a]
  implicit val monad = new IsomorphismMonadError[Default, K, String] with Alt[Default] {
    override val G = MonadError[K, String]
    override val iso = ...
  
    def alt[A](a1: =>Default[A], a2: =>Default[A]): Default[A] = instance(a1.default)
  }
~~~~~~~~

A> Podstawą dla `Alt` jest `.alt`, podobnie jak `.ap` dla `Applicative`, ale często lepiej jest 
A> użyć jako metod bazowych `.altly2` i `.apply2` z odpowiednimi nadpisaniami:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   override def ap[A, B](fa: =>F[A])(f: =>F[A => B]): F[B] =
A>     apply2(fa, f)((a, abc) => abc(a))
A>
A>   override def alt[A](a1: =>F[A], a2: =>F[A]): F[A] = altly2(a1, a2) {
A>     case -\/(a) => a
A>     case \/-(a) => a
A>   }
A> ~~~~~~~~
A> 
A> Nie można tylko zapomnieć o implementacji `apply2` i `altly2`, bo skończy się to nieskończoną pętlą w czasie wykonania.

Pozwala nam to tym samym wyderywować `Default[Darath]`

{lang="text"}
~~~~~~~~
  object Darth {
    ...
    private def f(e: Vader \/ JarJar): Darth = e.merge
    implicit val default: Default[Darth] =
      Alt[Default].altly2(Default[Vader], Default[JarJar])(f)
  }
  object Vader {
    ...
    private val f: (String, Int) => Vader = Vader(_, _)
    implicit val default: Default[Vader] =
      Alt[Default].apply2(Default[String], Default[Int])(f)
  }
  object JarJar {
    ...
    private val f: (Int, String) => JarJar = JarJar(_, _)
    implicit val default: Default[JarJar] =
      Alt[Default].apply2(Default[Int], Default[String])(f)
  }
  
  scala> Default[Darth].default
  \/-(Vader())
~~~~~~~~

Wróćmy do typeklas z `scalaz-deriving`, gdzie inwariantnymi odpowiednikami `Alt` i `Decidable` są:

{lang="text"}
~~~~~~~~
  @typeclass trait InvariantApplicative[F[_]] extends InvariantFunctor[F] {
    def xproduct0[Z](f: =>Z): F[Z]
    def xproduct1[Z, A1](a1: =>F[A1])(f: A1 => Z, g: Z => A1): F[Z] = ...
    def xproduct2 ...
    def xproduct3 ...
    def xproduct4 ...
  }
  
  @typeclass trait InvariantAlt[F[_]] extends InvariantApplicative[F] {
    def xcoproduct1[Z, A1](a1: =>F[A1])(f: A1 => Z, g: Z => A1): F[Z] = ...
    def xcoproduct2 ...
    def xcoproduct3 ...
    def xcoproduct4 ...
  }
~~~~~~~~

wspierając typeklasy z `InvariantFunctor`em, jak np. `Monoid` czy `Semigroup`.


### Arbitralna Arność[^arnosc] i `@deriving`

[^arnosc]: Liczba argumentów, eng. _arity_

`InvariantApplicative` i `InvariantAlt` niosą ze sobą dwa problemy:

1. wspierają jedynie produkty o 4 polach i koprodukty o 4 pozycjach.
2. wprowadzają **dużo** boilerplate'u w obiektach towarzyszących.

W tym rozdziale rozwiążemy oba te problemy z użyciem dodatkowych typeklas ze `scalaz-deriving`

{width=75%}
![](images/scalaz-deriving.png)

W praktyce, cztery główne typeklasy `Applicative`, `Divisble`, `Alt` i `Decidable` zostały rozszerzone do
arbitralnej arności używając biblioteki [iotaz](https://github.com/frees-io/iota), stąd też sufiks `z`.

Biblioteka ta definiuje trzy główne typy:

-   `TList`, który opisuje ciąg typów dowolnej długości
-   `Prod[A <: TList]` dla produktów
-   `Cop[A <: TList]` dla koproduktów

Dla przykładu, oto reprezentacje oparte o `TList` dla ADT `Darath` z poprzedniego podrozdziału:

{lang="text"}
~~~~~~~~
  import iotaz._, TList._
  
  type DarthT  = Vader  :: JarJar :: TNil
  type VaderT  = String :: Int    :: TNil
  type JarJarT = Int    :: String :: TNil
~~~~~~~~

które mogą być zinstancjonizowane

{lang="text"}
~~~~~~~~
  val vader: Prod[VaderT]    = Prod("hello", 1)
  val jarjar: Prod[JarJarT]  = Prod(1, "hello")
  
  val VaderI = Cop.Inject[Vader, Cop[DarthT]]
  val darth: Cop[DarthT] = VaderI.inj(Vader("hello", 1))
~~~~~~~~

Aby móc użyć API ze `scalaz-deriving` potrzebujemy `Isomorphism` pomiędzy naszym ADT i generyczną
reprezentacją z `iotaz`. Generuje to sporo boilerplate'u, do które zaraz wrócimy

{lang="text"}
~~~~~~~~
  object Darth {
    private type Repr   = Vader :: JarJar :: TNil
    private val VaderI  = Cop.Inject[Vader, Cop[Repr]]
    private val JarJarI = Cop.Inject[JarJar, Cop[Repr]]
    private val iso     = IsoSet(
      {
        case d: Vader  => VaderI.inj(d)
        case d: JarJar => JarJarI.inj(d)
      }, {
        case VaderI(d)  => d
        case JarJarI(d) => d
      }
    )
    ...
  }
  
  object Vader {
    private type Repr = String :: Int :: TNil
    private val iso   = IsoSet(
      d => Prod(d.s, d.i),
      p => Vader(p.head, p.tail.head)
    )
    ...
  }
  
  object JarJar {
    private type Repr = Int :: String :: TNil
    private val iso   = IsoSet(
      d => Prod(d.i, d.s),
      p => JarJar(p.head, p.tail.head)
    )
    ...
  }
~~~~~~~~

Teraz możemy już bez żadnych problemów zawołać API `Deriving` dla `Equal`, korzystając z tego, 
że `scalaz-deriving` dostarcza zoptymalizowaną instancję `Deriving[Equal]`

{lang="text"}
~~~~~~~~
  object Darth {
    ...
    implicit val equal: Equal[Darth] = Deriving[Equal].xcoproductz(
      Prod(Need(Equal[Vader]), Need(Equal[JarJar])))(iso.to, iso.from)
  }
  object Vader {
    ...
    implicit val equal: Equal[Vader] = Deriving[Equal].xproductz(
      Prod(Need(Equal[String]), Need(Equal[Int])))(iso.to, iso.from)
  }
  object JarJar {
    ...
    implicit val equal: Equal[JarJar] = Deriving[Equal].xproductz(
      Prod(Need(Equal[Int]), Need(Equal[String])))(iso.to, iso.from)
  }
~~~~~~~~

A> Typeklasy używane w `Deriving` są opakowywane w `Need`, co pozwala na ich leniwą konstrukcję,
A> tym samym unikając zbędnej pracy, gdy dana instancja nie jest potrzebna, oraz zabezpiecza nas przed
A> przepełnieniem stosu dla rekurencyjnych ADT.

Aby móc zrobić to samo dla naszej typeklasy `Default`, musimy zdefiniować dodatkową instancję `Deriving[Default]`.
Na szczęście sprowadza się to jedynie do opakowania naszej instancji `Alt`:

{lang="text"}
~~~~~~~~
  object Default {
    ...
    implicit val deriving: Deriving[Default] = ExtendedInvariantAlt(monad)
  }
~~~~~~~~

i wywołania z obiektów towarzyszących

{lang="text"}
~~~~~~~~
  object Darth {
    ...
    implicit val default: Default[Darth] = Deriving[Default].xcoproductz(
      Prod(Need(Default[Vader]), Need(Default[JarJar])))(iso.to, iso.from)
  }
  object Vader {
    ...
    implicit val default: Default[Vader] = Deriving[Default].xproductz(
      Prod(Need(Default[String]), Need(Default[Int])))(iso.to, iso.from)
  }
  object JarJar {
    ...
    implicit val default: Default[JarJar] = Deriving[Default].xproductz(
      Prod(Need(Default[Int]), Need(Default[String])))(iso.to, iso.from)
  }
~~~~~~~~

Tym samym rozwiązaliśmy problem dowolnej liczby parametrów, ale wprowadziliśmy jeszcze więcej boilerplate'u.

Puenta jest taka, że anotacja `@deriving`, pochodząca z `deriving-plugin`, wygeneruje cały ten boilerplate za nas!
Wystarczy zaaplikować ją w korzeniu naszego ADT:

{lang="text"}
~~~~~~~~
  @deriving(Equal, Default)
  sealed abstract class Darth { def widen: Darth = this }
  final case class Vader(s: String, i: Int)  extends Darth
  final case class JarJar(i: Int, s: String) extends Darth
~~~~~~~~

`scalaz-deriving` zawiera również instancje dla typeklas `Order`, `Semigroup` i `Monoid`.
Instancje dla `Show` i `Arbitrary` dostępne są po zainstalowaniu rozszerzeń `scalaz-deriving-magnolia` oraz
`scalaz-deriving-scalacheck`.

Nie ma za co!


### Przykłady

Zakończymy naszą naukę `scalaz-deriving` z w pełni działającymi implementacjami wszystkich
przykładowych typeklas. Jednak zanim do tego dojdziemy, musimy poznać jeszcze jeden typ danych:
`/~\` a.k.a. *wąż na drodze*, który posłuży nam do przechowywania dwóch struktur wyższego rodzaju
sparametryzowanych tym samym typem:

{lang="text"}
~~~~~~~~
  sealed abstract class /~\[A[_], B[_]] {
    type T
    def a: A[T]
    def b: B[T]
  }
  object /~\ {
    type APair[A[_], B[_]]  = A /~\ B
    def unapply[A[_], B[_]](p: A /~\ B): Some[(A[p.T], B[p.T])] = ...
    def apply[A[_], B[_], Z](az: =>A[Z], bz: =>B[Z]): A /~\ B = ...
  }
~~~~~~~~

Zazwyczaj będziemy używać tej struktury w kontekście `Id /~\ TC`, gdzie `TC` to nasz typeklasa,
wyrażając fakt, że mamy wartość oraz instancję typeklasy dla tej wartości.

W dodatku wszystkie metody w API `Deriving` przyjmują niejawny parametr typu `A PairedWith F[A]`, pozwalający
bibliotece `iotaz` na wykonywanie `.zip`, `.traverse` i innych operacji na wartościach typu `Prod` i `Cop`.
Jako że nie używamy tych parametrów bezpośrednio, to możemy je na razie zignorować.


#### `Equal`

Podobnie jak przy `Default`, moglibyśmy zdefiniować `Decidable` o stałej arności i owinąć
w `ExtendedInvariantAlt` (rozwiązanie najprostsze), ale zamiast tego zdefiniujemy `Decidablez` dla
korzyści wydajnościowych. Dokonamy dwóch dodatkowych optymalizacji:

1. wykonanie porównania referencji `.eq` przed zaaplikowaniem `Equal.equal`, pozwalając na
   szybsze określenie równości dla tych samych wartości.
2. szybkie wyjście z `Foldable.all` kiedy którekolwiek z porównań zwróci `false`, tzn. jeśli
   pierwsze pola się nie zgadzają to nie będziemy nawet wymagać instancji `Equal` dla pozostałych
   wartości

{lang="text"}
~~~~~~~~
  new Decidablez[Equal] {
    @inline private final def quick(a: Any, b: Any): Boolean =
      a.asInstanceOf[AnyRef].eq(b.asInstanceOf[AnyRef])
  
    def dividez[Z, A <: TList, FA <: TList](tcs: Prod[FA])(g: Z => Prod[A])(
      implicit ev: A PairedWith FA
    ): Equal[Z] = (z1, z2) => (g(z1), g(z2)).zip(tcs).all {
      case (a1, a2) /~\ fa => quick(a1, a2) || fa.value.equal(a1, a2)
    }
  
    def choosez[Z, A <: TList, FA <: TList](tcs: Prod[FA])(g: Z => Cop[A])(
      implicit ev: A PairedWith FA
    ): Equal[Z] = (z1, z2) => (g(z1), g(z2)).zip(tcs) match {
      case -\/(_)               => false
      case \/-((a1, a2) /~\ fa) => quick(a1, a2) || fa.value.equal(a1, a2)
    }
  }
~~~~~~~~


#### `Default`

Niestety, API `iotaz` dla `.traverse` (i analogicznej `.coptraverse`) wymaga od nas zdefiniowania transformacji naturalnej,
co nawet w obecności `kind-pojector`a jest niezbyt wygodne.

{lang="text"}
~~~~~~~~
  private type K[a] = Kleisli[String \/ ?, Unit, a]
  new IsomorphismMonadError[Default, K, String] with Altz[Default] {
    type Sig[a] = Unit => String \/ a
    override val G = MonadError[K, String]
    override val iso = Kleisli.iso(
      λ[Sig ~> Default](s => instance(s(()))),
      λ[Default ~> Sig](d => _ => d.default)
    )
  
    val extract = λ[NameF ~> (String \/ ?)](a => a.value.default)
    def applyz[Z, A <: TList, FA <: TList](tcs: Prod[FA])(f: Prod[A] => Z)(
      implicit ev: A PairedWith FA
    ): Default[Z] = instance(tcs.traverse(extract).map(f))
  
    val always = λ[NameF ~> Maybe](a => a.value.default.toMaybe)
    def altlyz[Z, A <: TList, FA <: TList](tcs: Prod[FA])(f: Cop[A] => Z)(
      implicit ev: A PairedWith FA
    ): Default[Z] = instance {
      tcs.coptraverse[A, NameF, Id](always).map(f).headMaybe \/> "not found"
    }
  }
~~~~~~~~


#### `Semigroup`

Nie da się zdefiniować `Semigroup`y dla wszystkich koproduktów, ale da się to zrobić dla wszystkich
produktów. W tym celu użyjemy `InvariantApplicative` o dowolnej arności, czyli `InvariantApplicativez`:

{lang="text"}
~~~~~~~~
  new InvariantApplicativez[Semigroup] {
    type L[a] = ((a, a), NameF[a])
    val appender = λ[L ~> Id] { case ((a1, a2), fa) => fa.value.append(a1, a2) }
  
    def xproductz[Z, A <: TList, FA <: TList](tcs: Prod[FA])
                                             (f: Prod[A] => Z, g: Z => Prod[A])
                                             (implicit ev: A PairedWith FA) =
      new Semigroup[Z] {
        def append(z1: Z, z2: =>Z): Z = f(tcs.ziptraverse2(g(z1), g(z2), appender))
      }
  }
~~~~~~~~


#### `JsEncoder` i `JsDecoder`

`scalaz-deriving` nie pozwala na dostęp do nazw pól, więc nie jest możliwe zdefiniowanie enkoderów
i dekoderów z jej użyciem.

A> Wcześniejsza wersja `scalaz-deriving` wspierała taką funkcjonalność, ale okazało się,
A> że nie daje to żadnej przewagi nad używaniem Magnolii, więc wsparcie to zostało usunięte
A> w imię skupienia się na typeklasach posiadających poprawne instancje `Alt` i `Decidable`.


## Magnolia

Magnolia jest biblioteką opierającą się o makra, która dostarcza schludne i dość proste API pomagające w derywowaniu
typeklas. Instaluje się ją za pomocą wpisu w build.sbt

{lang="text"}
~~~~~~~~
  libraryDependencies += "com.propensive" %% "magnolia" % "0.10.1"
~~~~~~~~

Jako autorzy typeklasy musimy zaimplementować poniższe pola

{lang="text"}
~~~~~~~~
  import magnolia._
  
  object MyDerivation {
    type Typeclass[A]
  
    def combine[A](ctx: CaseClass[Typeclass, A]): Typeclass[A]
    def dispatch[A](ctx: SealedTrait[Typeclass, A]): Typeclass[A]
  
    def gen[A]: Typeclass[A] = macro Magnolia.gen[A]
  }
~~~~~~~~

API Magnolii to:

{lang="text"}
~~~~~~~~
  class CaseClass[TC[_], A] {
    def typeName: TypeName
    def construct[B](f: Param[TC, A] => B): A
    def constructMonadic[F[_]: Monadic, B](f: Param[TC, A] => F[B]): F[A]
    def parameters: Seq[Param[TC, A]]
    def annotations: Seq[Any]
  }
  
  class SealedTrait[TC[_], A] {
    def typeName: TypeName
    def subtypes: Seq[Subtype[TC, A]]
    def dispatch[B](value: A)(handle: Subtype[TC, A] => B): B
    def annotations: Seq[Any]
  }
~~~~~~~~

wraz z pomocnikami

{lang="text"}
~~~~~~~~
  final case class TypeName(short: String, full: String)
  
  class Param[TC[_], A] {
    type PType
    def label: String
    def index: Int
    def typeclass: TC[PType]
    def dereference(param: A): PType
    def default: Option[PType]
    def annotations: Seq[Any]
  }
  
  class Subtype[TC[_], A] {
    type SType <: A
    def typeName: TypeName
    def index: Int
    def typeclass: TC[SType]
    def cast(a: A): SType
    def annotations: Seq[Any]
  }
~~~~~~~~

Typeklasa `Monadic` widoczna w `constructMonadic` jest automatycznie generowana za pomocą `import mercator._`, jeśli nasz typ danych
posiada metody `.map` i `.flatMap`.

Nie ma sensu używać Magnolii do derywacji typeklas, które mogą być opisane poprzez `Divisible`/`Decidable`/`Applicative`/`Alt`, 
gdyż te abstrakcje dają nam dodatkową strukturę i testy za darmo. Jednak Magnolia oferuje nam funkcjonalności, których
nie ma `scalaz-deriving`: dostęp do nazw pól, nazw typów, anotacji i domyślnych wartości.


### Przykład: JSON

Musimy zadać sobie kilka pytań odnośnie tego jak chcemy serializować dane: 

1. Czy powinniśmy załączać pola o wartości `null`?
1. Czy dekodując powinniśmy traktować brakujące pola i pola o wartości `null` inaczej?
1. Jak zakodować nazwę koproduktu?
1. Jak poradzić sobie z koproduktami, które nie są `JsObject`em?

Oto nasze odpowiedzi:

- nie załączamy pól o wartości `JsNull`
- brakujące pola traktujemy tak samo jak wartości `null`
- użyjemy specjalnego pola `type`, aby rozróżnić koprodukty na podstawie ich nazw
- wartości prymitywne umieścimy w specjalnym polu `xvalue`

Pozwolimy też użytkownikowi dołączyć anotacje do koproduktów i pól produktów, aby
dostosować te zachowania:

{lang="text"}
~~~~~~~~
  sealed class json extends Annotation
  object json {
    final case class nulls()          extends json
    final case class field(f: String) extends json
    final case class hint(f: String)  extends json
  }
~~~~~~~~

A> Magnolia nie ogranicza nas do jednej rodziny anotacji. Taka implementacja ma pozwolić nam
A> na dokonanie dokładnego porównania z Shapelessem w następnym podrozdziale.

Na przykład 

{lang="text"}
~~~~~~~~
  @json.field("TYPE")
  sealed abstract class Cost
  final case class Time(s: String) extends Cost
  final case class Money(@json.field("integer") i: Int) extends Cost
~~~~~~~~

Zacznijmy od enkodera, który obsługuje jedynie ustawienia domyślne:

{lang="text"}
~~~~~~~~
  object JsMagnoliaEncoder {
    type Typeclass[A] = JsEncoder[A]
  
    def combine[A](ctx: CaseClass[JsEncoder, A]): JsEncoder[A] = { a =>
      val empty = IList.empty[(String, JsValue)]
      val fields = ctx.parameters.foldRight(right) { (p, acc) =>
        p.typeclass.toJson(p.dereference(a)) match {
          case JsNull => acc
          case value  => (p.label -> value) :: acc
        }
      }
      JsObject(fields)
    }
  
    def dispatch[A](ctx: SealedTrait[JsEncoder, A]): JsEncoder[A] = a =>
      ctx.dispatch(a) { sub =>
        val hint = "type" -> JsString(sub.typeName.short)
        sub.typeclass.toJson(sub.cast(a)) match {
          case JsObject(fields) => JsObject(hint :: fields)
          case other            => JsObject(IList(hint, "xvalue" -> other))
        }
      }
  
    def gen[A]: JsEncoder[A] = macro Magnolia.gen[A]
  }
~~~~~~~~

Widzimy w jak prosty sposób możemy posługiwać się nazwami pól oraz
instancjami typeklas dla każdego z nich.

Teraz dodajmy wsparcie dla anotacji, aby obsłużyć preferencje użytkownika. Aby
uniknąć sprawdzania anotacji za każdym kodowaniem, zapiszemy je w lokalnej tablicy. Mimo że 
dostęp do komórek tablicy nie jest totalny, to w praktyce mamy gwarancję, że indeksy zawsze będą się zgadzać.
Wydajność zazwyczaj cierpi przy okazji walki specjalizacji z generalizacją.

{lang="text"}
~~~~~~~~
  object JsMagnoliaEncoder {
    type Typeclass[A] = JsEncoder[A]
  
    def combine[A](ctx: CaseClass[JsEncoder, A]): JsEncoder[A] =
      new JsEncoder[A] {
        private val anns = ctx.parameters.map { p =>
          val nulls = p.annotations.collectFirst {
            case json.nulls() => true
          }.getOrElse(false)
          val field = p.annotations.collectFirst {
            case json.field(name) => name
          }.getOrElse(p.label)
          (nulls, field)
        }.toArray
  
        def toJson(a: A): JsValue = {
          val empty = IList.empty[(String, JsValue)]
          val fields = ctx.parameters.foldRight(empty) { (p, acc) =>
            val (nulls, field) = anns(p.index)
            p.typeclass.toJson(p.dereference(a)) match {
              case JsNull if !nulls => acc
              case value            => (field -> value) :: acc
            }
          }
          JsObject(fields)
        }
      }
  
    def dispatch[A](ctx: SealedTrait[JsEncoder, A]): JsEncoder[A] =
      new JsEncoder[A] {
        private val field = ctx.annotations.collectFirst {
          case json.field(name) => name
        }.getOrElse("type")
        private val anns = ctx.subtypes.map { s =>
          val hint = s.annotations.collectFirst {
            case json.hint(name) => field -> JsString(name)
          }.getOrElse(field -> JsString(s.typeName.short))
          val xvalue = s.annotations.collectFirst {
            case json.field(name) => name
          }.getOrElse("xvalue")
          (hint, xvalue)
        }.toArray
  
        def toJson(a: A): JsValue = ctx.dispatch(a) { sub =>
          val (hint, xvalue) = anns(sub.index)
          sub.typeclass.toJson(sub.cast(a)) match {
            case JsObject(fields) => JsObject(hint :: fields)
            case other            => JsObject(hint :: (xvalue -> other) :: IList.empty)
          }
        }
      }
  
    def gen[A]: JsEncoder[A] = macro Magnolia.gen[A]
  }
~~~~~~~~

Przy dekoderze skorzystamy z metody `.constructMonadic`, która ma sygnaturę podobną do `.traverse`

{lang="text"}
~~~~~~~~
  object JsMagnoliaDecoder {
    type Typeclass[A] = JsDecoder[A]
  
    def combine[A](ctx: CaseClass[JsDecoder, A]): JsDecoder[A] = {
      case obj @ JsObject(_) =>
        ctx.constructMonadic(
          p => p.typeclass.fromJson(obj.get(p.label).getOrElse(JsNull))
        )
      case other => fail("JsObject", other)
    }
  
    def dispatch[A](ctx: SealedTrait[JsDecoder, A]): JsDecoder[A] = {
      case obj @ JsObject(_) =>
        obj.get("type") match {
          case \/-(JsString(hint)) =>
            ctx.subtypes.find(_.typeName.short == hint) match {
              case None => fail(s"a valid '$hint'", obj)
              case Some(sub) =>
                val value = obj.get("xvalue").getOrElse(obj)
                sub.typeclass.fromJson(value)
            }
          case _ => fail("JsObject with type", obj)
        }
      case other => fail("JsObject", other)
    }
  
    def gen[A]: JsDecoder[A] = macro Magnolia.gen[A]
  }
~~~~~~~~

Raz jeszcze dodajemy wsparcie dla preferencji użytkownika i domyślnych wartości pól wraz z paroma 
optymalizacjami:

{lang="text"}
~~~~~~~~
  object JsMagnoliaDecoder {
    type Typeclass[A] = JsDecoder[A]
  
    def combine[A](ctx: CaseClass[JsDecoder, A]): JsDecoder[A] =
      new JsDecoder[A] {
        private val nulls = ctx.parameters.map { p =>
          p.annotations.collectFirst {
            case json.nulls() => true
          }.getOrElse(false)
        }.toArray
  
        private val fieldnames = ctx.parameters.map { p =>
          p.annotations.collectFirst {
            case json.field(name) => name
          }.getOrElse(p.label)
        }.toArray
  
        def fromJson(j: JsValue): String \/ A = j match {
          case obj @ JsObject(_) =>
            import mercator._
            val lookup = obj.fields.toMap
            ctx.constructMonadic { p =>
              val field = fieldnames(p.index)
              lookup
                .get(field)
                .into {
                  case Maybe.Just(value) => p.typeclass.fromJson(value)
                  case _ =>
                    p.default match {
                      case Some(default) => \/-(default)
                      case None if nulls(p.index) =>
                        s"missing field '$field'".left
                      case None => p.typeclass.fromJson(JsNull)
                    }
                }
            }
          case other => fail("JsObject", other)
        }
      }
  
    def dispatch[A](ctx: SealedTrait[JsDecoder, A]): JsDecoder[A] =
      new JsDecoder[A] {
        private val subtype = ctx.subtypes.map { s =>
          s.annotations.collectFirst {
            case json.hint(name) => name
          }.getOrElse(s.typeName.short) -> s
        }.toMap
        private val typehint = ctx.annotations.collectFirst {
          case json.field(name) => name
        }.getOrElse("type")
        private val xvalues = ctx.subtypes.map { sub =>
          sub.annotations.collectFirst {
            case json.field(name) => name
          }.getOrElse("xvalue")
        }.toArray
  
        def fromJson(j: JsValue): String \/ A = j match {
          case obj @ JsObject(_) =>
            obj.get(typehint) match {
              case \/-(JsString(h)) =>
                subtype.get(h) match {
                  case None => fail(s"a valid '$h'", obj)
                  case Some(sub) =>
                    val xvalue = xvalues(sub.index)
                    val value  = obj.get(xvalue).getOrElse(obj)
                    sub.typeclass.fromJson(value)
                }
              case _ => fail(s"JsObject with '$typehint' field", obj)
            }
          case other => fail("JsObject", other)
        }
      }
  
    def gen[A]: JsDecoder[A] = macro Magnolia.gen[A]
  }
~~~~~~~~

Teraz musimy wywołać `JsMagnoliaEncoder.gen` oraz `JsMagnoliaDecoder.gen` z obiektów towarzyszących
naszych typów danych. Na przykład dla API Map Google:

{lang="text"}
~~~~~~~~
  final case class Value(text: String, value: Int)
  final case class Elements(distance: Value, duration: Value, status: String)
  final case class Rows(elements: List[Elements])
  final case class DistanceMatrix(
    destination_addresses: List[String],
    origin_addresses: List[String],
    rows: List[Rows],
    status: String
  )
  
  object Value {
    implicit val encoder: JsEncoder[Value] = JsMagnoliaEncoder.gen
    implicit val decoder: JsDecoder[Value] = JsMagnoliaDecoder.gen
  }
  object Elements {
    implicit val encoder: JsEncoder[Elements] = JsMagnoliaEncoder.gen
    implicit val decoder: JsDecoder[Elements] = JsMagnoliaDecoder.gen
  }
  object Rows {
    implicit val encoder: JsEncoder[Rows] = JsMagnoliaEncoder.gen
    implicit val decoder: JsDecoder[Rows] = JsMagnoliaDecoder.gen
  }
  object DistanceMatrix {
    implicit val encoder: JsEncoder[DistanceMatrix] = JsMagnoliaEncoder.gen
    implicit val decoder: JsDecoder[DistanceMatrix] = JsMagnoliaDecoder.gen
  }
~~~~~~~~

Na szczęście anotacja `@deriving` wspiera derywację z użyciem Magnolii! Jeśli autor typeklasy 
dostarcza w swoim jarze plik `deriving.conf` zawierający poniższe linie

{lang="text"}
~~~~~~~~
  jsonformat.JsEncoder=jsonformat.JsMagnoliaEncoder.gen
  jsonformat.JsDecoder=jsonformat.JsMagnoliaDecoder.gen
~~~~~~~~

to `deriving-macro` wywoła odpowiednie metody:

{lang="text"}
~~~~~~~~
  @deriving(JsEncoder, JsDecoder)
  final case class Value(text: String, value: Int)
  @deriving(JsEncoder, JsDecoder)
  final case class Elements(distance: Value, duration: Value, status: String)
  @deriving(JsEncoder, JsDecoder)
  final case class Rows(elements: List[Elements])
  @deriving(JsEncoder, JsDecoder)
  final case class DistanceMatrix(
    destination_addresses: List[String],
    origin_addresses: List[String],
    rows: List[Rows],
    status: String
  )
~~~~~~~~


### W Pełni Automatyczna Derywacja

Generowanie niejawnych instancji w obiektach towarzyszących typom danych jest techniką znaną
jako generacja *semi-automatyczna* (_semi-auto_), w porównaniu do generacji *w pełni automatycznej* (_full-auto_),
która ma miejsce, gdy metoda `.gen` jest również niejawna

{lang="text"}
~~~~~~~~
  object JsMagnoliaEncoder {
    ...
    implicit def gen[A]: JsEncoder[A] = macro Magnolia.gen[A]
  }
  object JsMagnoliaDecoder {
    ...
    implicit def gen[A]: JsDecoder[A] = macro Magnolia.gen[A]
  }
~~~~~~~~

W takim wypadku użytkownicy mogą zaimportować takie metody i zyskać magiczną derywację
w punkcie użycia

{lang="text"}
~~~~~~~~
  scala> final case class Value(text: String, value: Int)
  scala> import JsMagnoliaEncoder.gen
  scala> Value("hello", 1).toJson
  res = JsObject([("text","hello"),("value",1)])
~~~~~~~~

Może to brzmieć kusząco, gdyż wymaga najmniejszej ilości kodu, ale niesie ze sobą dwie pułapki:

1. makro wykonywane jest przy każdym użyciu, a więc na przykład za każdym razem, gdy wywołamy `.toJson`.
   Spowalnia to kompilacje oraz prowadzi do stworzenia większej ilości obiektów, co może spowodować
   spadek wydajności w czasie wykonania.
2. wyderywowane mogą zostać rzeczy zupełnie niespodziewane.

Punkt pierwszy jest raczej oczywisty, ale nieprzewidziane derywacje manifestują się w formie subtelnych
błędów. Pomyślmy co się wydarzy dla

{lang="text"}
~~~~~~~~
  @deriving(JsEncoder)
  final case class Foo(s: Option[String])
~~~~~~~~

jeśli zapomnimy dostarczyć niejawna instancję dla `Option`. Moglibyśmy oczekiwać, że
`Foo(Some("hello"))` przyjmie formę

{lang="text"}
~~~~~~~~
  {
    "s":"hello"
  }
~~~~~~~~

Ale zamiast tego otrzymamy

{lang="text"}
~~~~~~~~
  {
    "s": {
      "type":"Some",
      "get":"hello"
    }
  }
~~~~~~~~

ponieważ Magnolia wyderywowała dla na nas enkoder dla typu `Option`.

Chcielibyśmy, żeby kompilator informował nas o brakujących elementach, tak więc odradzamy
używanie w pełni automatycznej derywacji.

## Shapeless

Biblioteka [Shapeless](https://github.com/milessabin/shapeless/) jest niezmiennie najbardziej skomplikowaną biblioteką
w ekosystemie Scali. Taka reputacja wynika z faktu, że implementuje ona niemal osoby język do *programowania generycznego*
na poziomie typów i robi to za pomocą maksymalnego wykorzystania wartości niejawnych.

Nie jest to pomysł zupełnie obcy. W Scalaz staramy się ograniczyć używanie takich wartości jedynie
do typeklas, ale czasem prosimy kompilator o dostarczenie różnego rodzaju *dowodów* co do wskazanych typów.
Przykładem mogą być relacje Liskov i Leibniz (`<~<` i `===`) lub zdolność do wstrzyknięcia algebry free do koproduktu
algebry (`Inject`).

A> Nie trzeba rozumieć Shapelessa, żeby być Programistą Funkcyjnym. Jeśli ten rozdział
A> okaże się zbyt ciężki, to po prostu przejdź do następnego.

Aby zainstalować Shapeless musimy dodać poniższy fragment do `build.sbt`

{lang="text"}
~~~~~~~~
  libraryDependencies += "com.chuusai" %% "shapeless" % "2.3.3"
~~~~~~~~

Rdzeniem biblioteki są typy danych `HList` i `Coproduct`

{lang="text"}
~~~~~~~~
  package shapeless
  
  sealed trait HList
  final case class ::[+H, +T <: HList](head: H, tail: T) extends HList
  sealed trait NNil extends HList
  case object HNil extends HNil {
    def ::[H](h: H): H :: HNil = ::(h, this)
  }
  
  sealed trait Coproduct
  sealed trait :+:[+H, +T <: Coproduct] extends Coproduct
  final case class Inl[+H, +T <: Coproduct](head: H) extends :+:[H, T]
  final case class Inr[+H, +T <: Coproduct](tail: T) extends :+:[H, T]
  sealed trait CNil extends Coproduct // no implementations
~~~~~~~~

które są *generycznymi* reprezentacjami odpowiednio produktów i koproduktów. `sealed trait HNil`
służy tylko naszej wygodzie, abyśmy nie musieli pisać `HNil.type`.

Shapeless ma również kopię typu `IsoSet` pod nazwą `Generic`, która pozwala nam przechodzić
między ADT i jego generyczną reprezentacją:

{lang="text"}
~~~~~~~~
  trait Generic[T] {
    type Repr
    def to(t: T): Repr
    def from(r: Repr): T
  }
  object Generic {
    type Aux[T, R] = Generic[T] { type Repr = R }
    def apply[T](implicit G: Generic[T]): Aux[T, G.Repr] = G
    implicit def materialize[T, R]: Aux[T, R] = macro ...
  }
~~~~~~~~

Wiele z tych typów zawiera abstrakcyjny typ `Repr`, a w swoich obiektach towarzyszących definiują
alias typu `.Aux`, który pozwala go zobaczyć. Umożliwia to nam żądanie `Generic[Foo]` bez podawania
generycznej reprezentacji, która będzie wygenerowana przez makro.

{lang="text"}
~~~~~~~~
  scala> import shapeless._
  scala> final case class Foo(a: String, b: Long)
         Generic[Foo].to(Foo("hello", 13L))
  res: String :: Long :: HNil = hello :: 13 :: HNil
  
  scala> Generic[Foo].from("hello" :: 13L :: HNil)
  res: Foo = Foo(hello,13)
  
  scala> sealed abstract class Bar
         case object Irish extends Bar
         case object English extends Bar
  
  scala> Generic[Bar].to(Irish)
  res: English.type :+: Irish.type :+: CNil.type = Inl(Irish)
  
  scala> Generic[Bar].from(Inl(Irish))
  res: Bar = Irish
~~~~~~~~

Istnieje również komplementarny typ `LabelledGeneric`, który zawiera nazwy pól.

{lang="text"}
~~~~~~~~
  scala> import shapeless._, labelled._
  scala> final case class Foo(a: String, b: Long)
  
  scala> LabelledGeneric[Foo].to(Foo("hello", 13L))
  res: String with KeyTag[Symbol with Tagged[String("a")], String] ::
       Long   with KeyTag[Symbol with Tagged[String("b")],   Long] ::
       HNil =
       hello :: 13 :: HNil
  
  scala> sealed abstract class Bar
         case object Irish extends Bar
         case object English extends Bar
  
  scala> LabelledGeneric[Bar].to(Irish)
  res: Irish.type   with KeyTag[Symbol with Tagged[String("Irish")],     Irish.type] :+:
       English.type with KeyTag[Symbol with Tagged[String("English")], English.type] :+:
       CNil.type =
       Inl(Irish)
~~~~~~~~

Zwróć uwagę, że **wartość** typu `LabelledGeneric` jest taka sama jak `Generic`. Nazwy pól istnieją
jedynie na poziomie typów i są wymazywane w czasie wykonania.

Nie musimy używać typu `KeyTag` bezpośrednio, a zamiast tego możemy użyć aliasu:

{lang="text"}
~~~~~~~~
  type FieldType[K, +V] = V with KeyTag[K, V]
~~~~~~~~

Jeśli chcemy uzyskać dostęp do nazwy pola z `FieldType[K, A]`, musimy poprosić o
niejawny dowód typu `Witness.Aux[K]`, który dostarczy nam wartość `K` w czasie wykonania.

Na pierwszy rzut oka jest to wszystko co musimy wiedzieć, aby móc wyderywować instancję typeklasy
z użyciem Shapelessa. Jednak z czasem wszystko się komplikuje, więc my również przejdziemy przez przykłady
o rosnącym poziomie skomplikowania.

 
### Przykład: `Equal`

Standardowym podejściem jest rozszerzenie typeklasy i umieszczenie jej derywacji z obiekcie towarzyszącym.
W taki sposób znajduje się ona w niejawnym zakresie przeszukiwanym przez kompilator bez dopisywania dodatkowych importów.

{lang="text"}
~~~~~~~~
  trait DerivedEqual[A] extends Equal[A]
  object DerivedEqual {
    ...
  }
~~~~~~~~

Punktem wejścia do derywacji jest metoda `.gen`, wymagająca dwóch parametrów typu: `A`, dla którego derywujemy instancję
oraz `R` czyli jego generycznej reprezentacji. Następnie żądamy wartości `Generic.Aux[A, R]`, która łączy `A` z `R`, oraz
instancji `DerivedEqual` dla `R`. Zacznijmy od takiej właśnie sygnatury i prostej implementacji:

{lang="text"}
~~~~~~~~
  import shapeless._
  
  object DerivedEqual {
    def gen[A, R: DerivedEqual](implicit G: Generic.Aux[A, R]): Equal[A] =
      (a1, a2) => Equal[R].equal(G.to(a1), G.to(a2))
  }
~~~~~~~~

Tym samym zredukowaliśmy problem do dostarczenia `DerivedEqual[R]`, a więc instancji dla generycznej 
reprezentacji `A`. Najpierw rozważmy produkty, czyli sytuację gdzie `R <: HList`. Chcielibyśmy 
zaimplementować taką sygnaturę:

{lang="text"}
~~~~~~~~
  implicit def hcons[H: Equal, T <: HList: DerivedEqual]: DerivedEqual[H :: T]
~~~~~~~~

Jeśli ją zaimplementujemy to kompilator będzie w stanie rekursywnie ją wywoływać aż dotrze do końca listy.
W tym momencie będzie potrzebował instancji dla pustego `HNil`

{lang="text"}
~~~~~~~~
  implicit def hnil: DerivedEqual[HNil]
~~~~~~~~

Zaimplementujmy je

{lang="text"}
~~~~~~~~
  implicit def hcons[H: Equal, T <: HList: DerivedEqual]: DerivedEqual[H :: T] =
    (h1, h2) => Equal[H].equal(h1.head, h2.head) && Equal[T].equal(h1.tail, h2.tail)
  
  implicit val hnil: DerivedEqual[HNil] = (_, _) => true
~~~~~~~~

Dla koproduktów z kolei, chcielibyśmy zaimplementować podobne sygnatury

{lang="text"}
~~~~~~~~
  implicit def ccons[H: Equal, T <: Coproduct: DerivedEqual]: DerivedEqual[H :+: T]
  implicit def cnil: DerivedEqual[CNil]
~~~~~~~~

A> Scalaz i Shapeless współdzielą wiele nazw typów. Gdy używamy ich jednocześnie często musimy wyłączyć niektóre elementy z importów, np.
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   import scalaz.{ Coproduct => _, :+: => _, _ }, Scalaz._
A>   import shapeless._
A> ~~~~~~~~


`.cnil` nie zostanie nigdy zawołany dla typeklas takich jak `Equal`, gdzie parametr typu występuje jedynie w 
pozycji kontrawariantnej, ale kompilator tego nie wie, a więc musimy dostarczyć jakąkolwiek jego implementację:

{lang="text"}
~~~~~~~~
  implicit val cnil: DerivedEqual[CNil] = (_, _) => sys.error("impossible")
~~~~~~~~

W przypadku koproduktów, możemy porównywać jedynie instancje tego samego typu, a więc wtedy, gdy
mamy do czynienia z dwukrotnym `Inl` lub `Inr`

{lang="text"}
~~~~~~~~
  implicit def ccons[H: Equal, T <: Coproduct: DerivedEqual]: DerivedEqual[H :+: T] = {
    case (Inl(c1), Inl(c2)) => Equal[H].equal(c1, c2)
    case (Inr(c1), Inr(c2)) => Equal[T].equal(c1, c2)
    case _                  => false
  }
~~~~~~~~

Warto zaznaczyć, że nasze metody pokrywają się z konceptami `conquer` (`hnil`),
`divide2` (`hlist`) i `alt2` (`coproduct`)! Jedak nic nie zyskamy definiując `Decidable`,
gdyż musielibyśmy zaczynać od zera pisząc testy dla tego kodu.

Przetestujmy więc go prostym ADT

{lang="text"}
~~~~~~~~
  sealed abstract class Foo
  final case class Bar(s: String)          extends Foo
  final case class Faz(b: Boolean, i: Int) extends Foo
  final case object Baz                    extends Foo
~~~~~~~~

Dostarczamy odpowiednie instancje:

{lang="text"}
~~~~~~~~
  object Foo {
    implicit val equal: Equal[Foo] = DerivedEqual.gen
  }
  object Bar {
    implicit val equal: Equal[Bar] = DerivedEqual.gen
  }
  object Faz {
    implicit val equal: Equal[Faz] = DerivedEqual.gen
  }
  final case object Baz extends Foo {
    implicit val equal: Equal[Baz.type] = DerivedEqual.gen
  }
~~~~~~~~

ale kod się nie kompiluje!

{lang="text"}
~~~~~~~~
  [error] shapeless.scala:41:38: ambiguous implicit values:
  [error]  both value hnil in object DerivedEqual of type => DerivedEqual[HNil]
  [error]  and value cnil in object DerivedEqual of type => DerivedEqual[CNil]
  [error]  match expected type DerivedEqual[R]
  [error]     : Equal[Baz.type] = DerivedEqual.gen
  [error]                                      ^
~~~~~~~~

Witaj w Shapelessowym świecie błędów kompilacji!

Problem, który wcale nie jest jasno widoczny w komunikacie błędu, wynika z faktu, że kompilator
nie umie domyślić się czym jest `R`. Musimy więc dostarczyć mu ten parametr wprost:

{lang="text"}
~~~~~~~~
  implicit val equal: Equal[Baz.type] = DerivedEqual.gen[Baz.type, HNil]
~~~~~~~~

lub użyć makra `Generic`, które dostarczy kompilatorowi generyczną reprezentację

{lang="text"}
~~~~~~~~
  final case object Baz extends Foo {
    implicit val generic                = Generic[Baz.type]
    implicit val equal: Equal[Baz.type] = DerivedEqual.gen[Baz.type, generic.Repr]
  }
  ...
~~~~~~~~

A> W tym momencie zacznij ignorować wszelkie podkreślenia i ufaj jedynie kompilatorowi. To jest punkt,
A> w którym Shapeless i wsparcie IDE się rozchodzą.

Powodem, dla którego to rozwiązanie działa, jest sygnatura metody `.gen`

{lang="text"}
~~~~~~~~
  def gen[A, R: DerivedEqual](implicit G: Generic.Aux[A, R]): Equal[A]
~~~~~~~~

która rozwijana jest do

{lang="text"}
~~~~~~~~
  def gen[A, R](implicit R: DerivedEqual[R], G: Generic.Aux[A, R]): Equal[A]
~~~~~~~~

Kompilator Scali rozwiązuje ograniczenia od lewej do prawej, a więc znajduje wiele różnych rozwiązań dla
`DerivedEqual` zanim ograniczy je z użyciem `Generic.Aux[A, R]`. Innym rozwiązaniem jest nie używanie ograniczeń kontekstu.

A> Zamiast prezentować w pełni działającą wersje, uważamy, że ważniejsze jest pokazać kiedy,
A> wydawałoby się, oczywisty kod nie działa, gdyż tak właśnie wygląda rzeczywistość pracy z Shapelessem. 
A> Innym rozwiązaniem, które moglibyśmy tu zastosować, jest użycie `sealed` na `DerivedEqual`
A> sprawiając, że jedynie wyderywowane wersje są poprawne. Ale `sealed trait`y nie są kompatybilne z
A> typami SAM! Żyjąc na krawędzi ostrza spodziewaj się zacięć.

Tym samym nie potrzebujemy już `implicit val generic` ani parametrów typu przekazywanych wprost i możemy
podłączyć `@deriving` dodając wpis w `deriving.conf` (zakładając, że chcemy nadpisać implementację ze `scalaz-deriving`)

{lang="text"}
~~~~~~~~
  scalaz.Equal=fommil.DerivedEqual.gen
~~~~~~~~

i napisać

{lang="text"}
~~~~~~~~
  @deriving(Equal) sealed abstract class Foo
  @deriving(Equal) final case class Bar(s: String)          extends Foo
  @deriving(Equal) final case class Faz(b: Boolean, i: Int) extends Foo
  @deriving(Equal) final case object Baz
~~~~~~~~

Ale zastąpienie wersji ze `scalaz-deriving` oznacza, że zwiększy się czas kompilacji naszego projektu.
Wynika to z faktu, że kompilator musi rozwiązać `N` niejawnych przeszukiwań dla każdego produktu o `N` polach
lub koproduktu o `N` wariantach, podczas gdy `scalaz-deriving` i `Magnolia` nie mają tego problemu.

Zauważ, że używając `scalaz-deriving` lub `Magnolii` wystarczy umieścić anotację `@deriving` na korzeniu ADT,
a w przypadku Shapelessa musi się ona pojawić osobno przy każdym z wariantów.

Jednak taka implementacja nadal jest błędna: nie działa dla rekurencyjnych typów danych i informuje nas o tym
**w czasie wykonania**. Przykład:

{lang="text"}
~~~~~~~~
  @deriving(Equal) sealed trait ATree
  @deriving(Equal) final case class Leaf(value: String)               extends ATree
  @deriving(Equal) final case class Branch(left: ATree, right: ATree) extends ATree
~~~~~~~~

{lang="text"}
~~~~~~~~
  scala> val leaf1: Leaf    = Leaf("hello")
         val leaf2: Leaf    = Leaf("goodbye")
         val branch: Branch = Branch(leaf1, leaf2)
         val tree1: ATree   = Branch(leaf1, branch)
         val tree2: ATree   = Branch(leaf2, branch)
  
  scala> assert(tree1 /== tree2)
  [error] java.lang.NullPointerException
  [error] at DerivedEqual$.shapes$DerivedEqual$$$anonfun$hcons$1(shapeless.scala:16)
          ...
~~~~~~~~

Dzieje się tak, ponieważ `Equal[Tree]` zależy od `Equal[Branch]`, które z kolei zależy od `Equal[Tree]`.
Rekurencja i BUM! Rozwiązaniem jest załadować je leniwie, a nie zachłannie.

Zarówno `scalaz-deriving` jak i Magnolia obsługują ten przypadek automatycznie, lecz tutaj
leży to w gestii programisty.

Typy `Cached`, `Strict` i `Lazy`, oparte o makra, zmieniają zachowanie kompilatora, pozwalając nam na osiągnięcie
potrzebnej leniwości. Generalną zasadą jest użycie `Cached[Strict[_]]` w punkcie wejścia i `Lazy[_]` w okolicach instancji dla typu `H`.

W tym momencie najlepiej będzie jeśli zupełnie zapomnimy o ograniczeniach kontekstu i typach SAM:

{lang="text"}
~~~~~~~~
  sealed trait DerivedEqual[A] extends Equal[A]
  object DerivedEqual {
    def gen[A, R](
      implicit G: Generic.Aux[A, R],
      R: Cached[Strict[DerivedEqual[R]]]
    ): Equal[A] = new Equal[A] {
      def equal(a1: A, a2: A) =
        quick(a1, a2) || R.value.value.equal(G.to(a1), G.to(a2))
    }
  
    implicit def hcons[H, T <: HList](
      implicit H: Lazy[Equal[H]],
      T: DerivedEqual[T]
    ): DerivedEqual[H :: T] = new DerivedEqual[H :: T] {
      def equal(ht1: H :: T, ht2: H :: T) =
        (quick(ht1.head, ht2.head) || H.value.equal(ht1.head, ht2.head)) &&
          T.equal(ht1.tail, ht2.tail)
    }
  
    implicit val hnil: DerivedEqual[HNil] = new DerivedEqual[HNil] {
      def equal(@unused h1: HNil, @unused h2: HNil) = true
    }
  
    implicit def ccons[H, T <: Coproduct](
      implicit H: Lazy[Equal[H]],
      T: DerivedEqual[T]
    ): DerivedEqual[H :+: T] = new DerivedEqual[H :+: T] {
      def equal(ht1: H :+: T, ht2: H :+: T) = (ht1, ht2) match {
        case (Inl(c1), Inl(c2)) => quick(c1, c2) || H.value.equal(c1, c2)
        case (Inr(c1), Inr(c2)) => T.equal(c1, c2)
        case _                  => false
      }
    }
  
    implicit val cnil: DerivedEqual[CNil] = new DerivedEqual[CNil] {
      def equal(@unused c1: CNil, @unused c2: CNil) = sys.error("impossible")
    }
  
    @inline private final def quick(a: Any, b: Any): Boolean =
      a.asInstanceOf[AnyRef].eq(b.asInstanceOf[AnyRef])
  }
~~~~~~~~

Przy okazji dokonaliśmy optymalizacji z użyciem `quick` ze `scalaz-deriving`.

Możemy teraz wywołać

{lang="text"}
~~~~~~~~
  assert(tree1 /== tree2)
~~~~~~~~

bez wyjątków rzucanych w czasie działania.


### Przykład: `Default`

Implementując derywację typeklasy z parametrem typu w pozycji kowariantnej nie natkniemy się na szczęście
na żadne nowe pułapki. Tworzymy instancje dla `HList` i `Coproduct`, pamiętając, że musimy obsłużyć też
przypadek `CNil`, gdyż odpowiada on sytuacji w której żaden z wariantów nie był w stanie dostarczyć wartości.

{lang="text"}
~~~~~~~~
  sealed trait DerivedDefault[A] extends Default[A]
  object DerivedDefault {
    def gen[A, R](
      implicit G: Generic.Aux[A, R],
      R: Cached[Strict[DerivedDefault[R]]]
    ): Default[A] = new Default[A] {
      def default = R.value.value.default.map(G.from)
    }
  
    implicit def hcons[H, T <: HList](
      implicit H: Lazy[Default[H]],
      T: DerivedDefault[T]
    ): DerivedDefault[H :: T] = new DerivedDefault[H :: T] {
      def default =
        for {
          head <- H.value.default
          tail <- T.default
        } yield head :: tail
    }
  
    implicit val hnil: DerivedDefault[HNil] = new DerivedDefault[HNil] {
      def default = HNil.right
    }
  
    implicit def ccons[H, T <: Coproduct](
      implicit H: Lazy[Default[H]],
      T: DerivedDefault[T]
    ): DerivedDefault[H :+: T] = new DerivedDefault[H :+: T] {
      def default = H.value.default.map(Inl(_)).orElse(T.default.map(Inr(_)))
    }
  
    implicit val cnil: DerivedDefault[CNil] = new DerivedDefault[CNil] {
      def default = "not a valid coproduct".left
    }
  }
~~~~~~~~

Analogicznie do relacji pomiędzy `Equal` i `Decidable`, możemy zauważyć relację z `Alt` w
`.point` (`hnil`), `apply2` (`.hcons`), i `.altly2` (`.ccons`).

Niewiele nowego moglibyśmy nauczyć się z `Semigroup`, więc przejdziemy od razu do enkoderów i dekoderów.


### Przykład: `JsEncoder`

Aby odtworzyć nasz enkoder oparty o Magnolię, musimy mieć dostęp do:

1. nazw pól i klas
2. anotacji odzwierciedlających preferencje użytkownika
3. domyślnych wartości pól

Zacznijmy od wersji obsługującej jedynie nasze domyślne zachowania.

Aby uzyskać nazwy pól, użyjemy `LabelledGeneric` zamiast `Generic`, definiując typ 
pierwszego elementu posłużymy się `FieldType[K, H]` zamiast prostym `H`, a wartość 
typu `Witness.Aux[K]` dostarczy nam nazwę pola w czasie wykonania.

Wszystkie nasze metody będą zwracać `JsObject`, więc zamiast uogólniać te wartości do `JsValue`
możemy stworzyć wyspecjalizowaną typeklasę `DerivedJsEncoder` o sygnaturze innej niż
ta w `JsEncoder`.

{lang="text"}
~~~~~~~~
  import shapeless._, labelled._
  
  sealed trait DerivedJsEncoder[R] {
    def toJsFields(r: R): IList[(String, JsValue)]
  }
  object DerivedJsEncoder {
    def gen[A, R](
      implicit G: LabelledGeneric.Aux[A, R],
      R: Cached[Strict[DerivedJsEncoder[R]]]
    ): JsEncoder[A] = new JsEncoder[A] {
      def toJson(a: A) = JsObject(R.value.value.toJsFields(G.to(a)))
    }
  
    implicit def hcons[K <: Symbol, H, T <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[T]
    ): DerivedJsEncoder[FieldType[K, H] :: T] =
      new DerivedJsEncoder[A, FieldType[K, H] :: T] {
        private val field = K.value.name
        def toJsFields(ht: FieldType[K, H] :: T) =
          ht match {
            case head :: tail =>
              val rest = T.toJsFields(tail)
              H.value.toJson(head) match {
                case JsNull => rest
                case value  => (field -> value) :: rest
              }
          }
      }
  
    implicit val hnil: DerivedJsEncoder[HNil] =
      new DerivedJsEncoder[HNil] {
        def toJsFields(h: HNil) = IList.empty
      }
  
    implicit def ccons[K <: Symbol, H, T <: Coproduct](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[T]
    ): DerivedJsEncoder[FieldType[K, H] :+: T] =
      new DerivedJsEncoder[FieldType[K, H] :+: T] {
        private val hint = ("type" -> JsString(K.value.name))
        def toJsFields(ht: FieldType[K, H] :+: T) = ht match {
          case Inl(head) =>
            H.value.toJson(head) match {
              case JsObject(fields) => hint :: fields
              case v                => IList.single("xvalue" -> v)
            }
  
          case Inr(tail) => T.toJsFields(tail)
        }
      }
  
    implicit val cnil: DerivedJsEncoder[CNil] =
      new DerivedJsEncoder[CNil] {
        def toJsFields(c: CNil) = sys.error("impossible")
      }
  
  }
~~~~~~~~


A> Wiele bibliotek dokonujących derywacji w oparciu o Shapelessa używa wzorca, 
A> wg którego derywacją bazuje na "podpowiedziach" dostarczanych za pomocą niejawnej wartości
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   trait ProductHint[A] {
A>     def nulls(field: String): Boolean
A>     def fieldname(field: String): String
A>   }
A>   object ProductHint {
A>     implicit def default[A]: ProductHint[A] = new ProductHint[A] {
A>       def nulls(field: String)     = false
A>       def fieldname(field: String) = field
A>     }
A>   }
A> ~~~~~~~~
A> 
A> Użytkownicy mogą zdefiniować własne instancje `ProductHint` w swoich obiektach towarzyszących
A> lub obiektach pakietu (_package objects_). Jest to **okropny pomysł**, który opiera się na
A> mechanizmie priorytetów wartości niejawnych, który bardzo łatwo jest zepsuć. Jednocześnie
A> łatwo jest doprowadzić do dekoherencji typeklas, gdzie derywacja `JsEncoder[Foo]` zakończy się innym rezultatem
A> zależnie od tego jaka instancja `ProductHint[Foo]` jest dostępna. Najlepiej unikać tego podejścia.

Shapeless obiera ścieżkę wykonania na etapie kompilacji bazując na obecności anotacji, co może prowadzić
do bardziej wydajnego kodu kosztem jego powtarzania. Oznacza to, że liczba anotacji i ich podtypów, z którymi mamy do czynienia
musi być rozsądnie mała, gdyż inaczej okaże się ze jesteśmy zmuszenie pisać 10x więcej kodu. Zamieńmy więc
nasze trzy anotacje na jedną z trzema parametrami:

{lang="text"}
~~~~~~~~
  case class json(
    nulls: Boolean,
    field: Option[String],
    hint: Option[String]
  ) extends Annotation
~~~~~~~~

Każde użycie takiej anotacji wymaga od użytkownika podania wszystkich 3 parametrów, gdyż wartości domyślne nie są dostępne
w konstruktorach anotacji. Możemy napisać własne destruktory, aby nie musieć modyfikować kodu, który napisaliśmy dla Magnolii.

{lang="text"}
~~~~~~~~
  object json {
    object nulls {
      def unapply(j: json): Boolean = j.nulls
    }
    object field {
      def unapply(j: json): Option[String] = j.field
    }
    object hint {
      def unapply(j: json): Option[String] = j.hint
    }
  }
~~~~~~~~

Możemy zażądać `Annotation[json, A]` dla `case class` lub `sealed trait`ów, aby zyskać dostęp do anotacji, 
ale musimy stworzyć warianty `hcons` i `ccons` obsługujące oba przypadki, gdyż wartość taka nie zostanie wygenerowana
gdy anotacja nie jest obecna. Tym samym musimy wprowadzić wartości niejawne o niższym priorytecie i za ich
pomocą obsłużyć brak anotacji.

Możemy też zażądać `Annotations.Aux[json, A, J]`, aby otrzymać `HList`ę anotacji `json` dla typu `A`.
Jednak tak samo musimy powtórzyć `hcons` i `ccons` dla przypadku, gdy anotacja nie jest obecna.

Aby wesprzeć tą jedną anotację musimy napisać czterokrotnie więcej kodu!

Zacznijmy od przepisania derywacji `JsEncoder` tak, aby obsługiwała kod bez jakichkolwiek anotacji.
Teraz kod, który użyje `@json` się nie skompiluje, co jest dobrym zabezpieczeniem.

Musimy dodać `A` i `J` do `DerivedJsEncoder` i przeciągnąć je poprzez metodę `.toJsObject`. Nasze
`.hcons` i `ccons` produkują instancje `DerivedJsEncoder` z anotacja `None.type`. Przeniesiemy je
do zakresu o niższym priorytecie, tak, abyśmy mogli obsłużyć `Annotation[json, A]` w pierwszej kolejności.

Zauważ, że instancje dla `J` pojawiają się przed `R`. Jest to ważne, gdyż kompilator musi najpierw
określić typ `J` zanim będzie w stanie ustalić `R`.

{lang="text"}
~~~~~~~~
  sealed trait DerivedJsEncoder[A, R, J <: HList] {
    def toJsFields(r: R, anns: J): IList[(String, JsValue)]
  }
  object DerivedJsEncoder extends DerivedJsEncoder1 {
    def gen[A, R, J <: HList](
      implicit
      G: LabelledGeneric.Aux[A, R],
      J: Annotations.Aux[json, A, J],
      R: Cached[Strict[DerivedJsEncoder[A, R, J]]]
    ): JsEncoder[A] = new JsEncoder[A] {
      def toJson(a: A) = JsObject(R.value.value.toJsFields(G.to(a), J()))
    }
  
    implicit def hnil[A]: DerivedJsEncoder[A, HNil, HNil] =
      new DerivedJsEncoder[A, HNil, HNil] {
        def toJsFields(h: HNil, a: HNil) = IList.empty
      }
  
    implicit def cnil[A]: DerivedJsEncoder[A, CNil, HNil] =
      new DerivedJsEncoder[A, CNil, HNil] {
        def toJsFields(c: CNil, a: HNil) = sys.error("impossible")
      }
  }
  private[jsonformat] trait DerivedJsEncoder1 {
    implicit def hcons[A, K <: Symbol, H, T <: HList, J <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :: T, None.type :: J] =
      new DerivedJsEncoder[A, FieldType[K, H] :: T, None.type :: J] {
        private val field = K.value.name
        def toJsFields(ht: FieldType[K, H] :: T, anns: None.type :: J) =
          ht match {
            case head :: tail =>
              val rest = T.toJsFields(tail, anns.tail)
              H.value.toJson(head) match {
                case JsNull => rest
                case value  => (field -> value) :: rest
              }
          }
      }
  
    implicit def ccons[A, K <: Symbol, H, T <: Coproduct, J <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :+: T, None.type :: J] =
      new DerivedJsEncoder[A, FieldType[K, H] :+: T, None.type :: J] {
        private val hint = ("type" -> JsString(K.value.name))
        def toJsFields(ht: FieldType[K, H] :+: T, anns: None.type :: J) =
          ht match {
            case Inl(head) =>
              H.value.toJson(head) match {
                case JsObject(fields) => hint :: fields
                case v                => IList.single("xvalue" -> v)
              }
            case Inr(tail) => T.toJsFields(tail, anns.tail)
          }
      }
  }
~~~~~~~~

Teraz możemy dodać sygnatury dla sześciu nowych metod, które pokryją wszystkie możliwe warianty
tego, gdzie może pojawić się anotacja. Zauważ, że wspieramy tylko jedną anotacje w każdej pozycji,
każda następna będzie po cichu zignorowana.

Powoli kończą nam się nazwy, więc arbitralnie dodamy `Annotated`, gdy anotacja jest na typie `A` i
`Custom`, gdy jest ona umieszczona na polu:

{lang="text"}
~~~~~~~~
  object DerivedJsEncoder extends DerivedJsEncoder1 {
    ...
    implicit def hconsAnnotated[A, K <: Symbol, H, T <: HList, J <: HList](
      implicit
      A: Annotation[json, A],
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :: T, None.type :: J]
  
    implicit def cconsAnnotated[A, K <: Symbol, H, T <: Coproduct, J <: HList](
      implicit
      A: Annotation[json, A],
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :+: T, None.type :: J]
  
    implicit def hconsAnnotatedCustom[A, K <: Symbol, H, T <: HList, J <: HList](
      implicit
      A: Annotation[json, A],
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :: T, Some[json] :: J]
  
    implicit def cconsAnnotatedCustom[A, K <: Symbol, H, T <: Coproduct, J <: HList](
      implicit
      A: Annotation[json, A],
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :+: T, Some[json] :: J]
  }
  private[jsonformat] trait DerivedJsEncoder1 {
    ...
    implicit def hconsCustom[A, K <: Symbol, H, T <: HList, J <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :: T, Some[json] :: J] = ???
  
    implicit def cconsCustom[A, K <: Symbol, H, T <: Coproduct, J <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H] :+: T, Some[json] :: J]
  }
~~~~~~~~

Tak naprawdę wcale nie potrzebujemy `.hconsAnnotated` ani `.hconsAnnotatedCustom`, ponieważ
anotacja umieszczona na case klasie nie ma żadnego wpływu na logikę, ma ona jedynie sens w przypadku koproduktów w `.cconsAnnotated`.
Tym samym możemy usunąć dwie metody.

`.cconsAnnotated` i `cconsAnnotatedCustom` mogą być zdefiniowane jako

{lang="text"}
~~~~~~~~
  new DerivedJsEncoder[A, FieldType[K, H] :+: T, None.type :: J] {
    private val hint = A().field.getOrElse("type") -> JsString(K.value.name)
    def toJsFields(ht: FieldType[K, H] :+: T, anns: None.type :: J) = ht match {
      case Inl(head) =>
        H.value.toJson(head) match {
          case JsObject(fields) => hint :: fields
          case v                => IList.single("xvalue" -> v)
        }
      case Inr(tail) => T.toJsFields(tail, anns.tail)
    }
  }
~~~~~~~~

oraz

{lang="text"}
~~~~~~~~
  new DerivedJsEncoder[A, FieldType[K, H] :+: T, Some[json] :: J] {
    private val hintfield = A().field.getOrElse("type")
    def toJsFields(ht: FieldType[K, H] :+: T, anns: Some[json] :: J) = ht match {
      case Inl(head) =>
        val ann = anns.head.get
        H.value.toJson(head) match {
          case JsObject(fields) =>
            val hint = (hintfield -> JsString(ann.hint.getOrElse(K.value.name)))
            hint :: fields
          case v =>
            val xvalue = ann.field.getOrElse("xvalue")
            IList.single(xvalue -> v)
        }
      case Inr(tail) => T.toJsFields(tail, anns.tail)
    }
  }
~~~~~~~~

Użycie metod `.head` i `.get` może być niepokojące, ale zauważmy, że `anns` jest typu `Some[json] :: J`, a więc obie 
są totalne i zupełnie bezpieczne.

`.hconsCustom` i `cconsCustom` zapiszemy jako

{lang="text"}
~~~~~~~~
  new DerivedJsEncoder[A, FieldType[K, H] :: T, Some[json] :: J] {
    def toJsFields(ht: FieldType[K, H] :: T, anns: Some[json] :: J) = ht match {
      case head :: tail =>
        val ann  = anns.head.get
        val next = T.toJsFields(tail, anns.tail)
        H.value.toJson(head) match {
          case JsNull if !ann.nulls => next
          case value =>
            val field = ann.field.getOrElse(K.value.name)
            (field -> value) :: next
        }
    }
  }
~~~~~~~~

oraz

{lang="text"}
~~~~~~~~
  new DerivedJsEncoder[A, FieldType[K, H] :+: T, Some[json] :: J] {
    def toJsFields(ht: FieldType[K, H] :+: T, anns: Some[json] :: J) = ht match {
      case Inl(head) =>
        val ann = anns.head.get
        H.value.toJson(head) match {
          case JsObject(fields) =>
            val hint = ("type" -> JsString(ann.hint.getOrElse(K.value.name)))
            hint :: fields
          case v =>
            val xvalue = ann.field.getOrElse("xvalue")
            IList.single(xvalue -> v)
        }
      case Inr(tail) => T.toJsFields(tail, anns.tail)
    }
  }
~~~~~~~~

Oczywiście, jest tutaj dużo boilerplate'u, ale jeśli przyjrzymy się bliżej, to zobaczymy, że
każda z metod jest zaimplementowana tak wydajnie jak to możliwe biorąc pod uwagę dostępne informacje,
a ścieżki wykonania wybierane są w czasie kompilacji.

Ci z obsesją na punkcie wydajności mogą przerefaktorować ten kod, tak, aby wszystkie anotacje były
dostępne zawczasu, a nie wstrzykiwane przez metodę `.toJsFields`. Dla absolutnej wydajności moglibyśmy
potraktować każdą customizację jako osobną anotację, ale tym samym po raz kolejny kilkukrotnie 
zwiększylibyśmy ilość kodu, wydłużając jeszcze bardziej czas kompilacji dla naszych użytkowników.
Tego typu optymalizacje są poza zakresem tej książki, ale jak najbardziej są one nie tylko możliwe
ale i implementowane w praktyce. Zdolność do przeniesienia pracy z czasu wykonania do czasu kompilacji
jest jedną z najbardziej pociągających rzeczy w programowaniu generycznym.

Dodatkowy haczyk o którym musimy pamiętać, to to, że [`LabelledGeneric` nie jest kompatybilny ze
`scalaz.@@`](https://github.com/milessabin/shapeless/issues/309), ale na szczęście istnieje obejście tego problemu.
Powiedzmy, że chcielibyśmy w wydajny sposób zignorować tagi. Musimy więc dodać dodatkowe reguły derywacji:

{lang="text"}
~~~~~~~~
  object JsEncoder {
    ...
    implicit def tagged[A: JsEncoder, Z]: JsEncoder[A @@ Z] =
      JsEncoder[A].contramap(Tag.unwrap)
  }
  object JsDecoder {
    ...
    implicit def tagged[A: JsDecoder, Z]: JsDecoder[A @@ Z] =
      JsDecoder[A].map(Tag(_))
  }
~~~~~~~~

W tym momencie powinniśmy móc wyderywować instancję `JsDecoder` dla typów podobnych do naszego `TradeTemplate` z Rozdziału 5

{lang="text"}
~~~~~~~~
  final case class TradeTemplate(
    otc: Option[Boolean] @@ Tags.Last
  )
  object TradeTemplate {
    implicit val encoder: JsEncoder[TradeTemplate] = DerivedJsEncoder.gen
  }
~~~~~~~~

Jednak zamiast tego otrzymujemy błąd kompilacji

{lang="text"}
~~~~~~~~
  [error] could not find implicit value for parameter G: LabelledGeneric.Aux[A,R]
  [error]   implicit val encoder: JsEncoder[TradeTemplate] = DerivedJsEncoder.gen
  [error]                                                                     ^
~~~~~~~~

Komunikat błędu jest, tak jak zawsze, niezbyt pomocny. Obejściem jest wprowadzenie dowodu dla `H @@ Z` o niższym priorytecie, a następnie 
ręczne wywołanie kodu, który kompilator powinien był znaleźć na samym początku:

{lang="text"}
~~~~~~~~
  object DerivedJsEncoder extends DerivedJsEncoder1 with DerivedJsEncoder2 {
    ...
  }
  private[jsonformat] trait DerivedJsEncoder2 {
    this: DerivedJsEncoder.type =>
  
    // WORKAROUND https://github.com/milessabin/shapeless/issues/309
    implicit def hconsTagged[A, K <: Symbol, H, Z, T <: HList, J <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H @@ Z]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H @@ Z] :: T, None.type :: J] = hcons(K, H, T)
  
    implicit def hconsCustomTagged[A, K <: Symbol, H, Z, T <: HList, J <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsEncoder[H @@ Z]],
      T: DerivedJsEncoder[A, T, J]
    ): DerivedJsEncoder[A, FieldType[K, H @@ Z] :: T, Some[json] :: J] = hconsCustom(K, H, T)
  }
~~~~~~~~

Na szczęście musimy obsłużyć jedynie produkty, bo tylko one mogą być otagowane.

### `JsDecoder`

Dekodowanie wygląda dokładnie tak jak mogliśmy się tego spodziewać po poprzednich przykładach. 
Możemy tworzyć instancje `FieldType[K, H]` za pomocą funkcji pomocniczej `field[K](h: H)`.
Chcąc obsłużyć jedynie zachowania domyślne musimy napisać:

{lang="text"}
~~~~~~~~
  sealed trait DerivedJsDecoder[A] {
    def fromJsObject(j: JsObject): String \/ A
  }
  object DerivedJsDecoder {
    def gen[A, R](
      implicit G: LabelledGeneric.Aux[A, R],
      R: Cached[Strict[DerivedJsDecoder[R]]]
    ): JsDecoder[A] = new JsDecoder[A] {
      def fromJson(j: JsValue) = j match {
        case o @ JsObject(_) => R.value.value.fromJsObject(o).map(G.from)
        case other           => fail("JsObject", other)
      }
    }
  
    implicit def hcons[K <: Symbol, H, T <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsDecoder[H]],
      T: DerivedJsDecoder[T]
    ): DerivedJsDecoder[FieldType[K, H] :: T] =
      new DerivedJsDecoder[FieldType[K, H] :: T] {
        private val fieldname = K.value.name
        def fromJsObject(j: JsObject) = {
          val value = j.get(fieldname).getOrElse(JsNull)
          for {
            head  <- H.value.fromJson(value)
            tail  <- T.fromJsObject(j)
          } yield field[K](head) :: tail
        }
      }
  
    implicit val hnil: DerivedJsDecoder[HNil] = new DerivedJsDecoder[HNil] {
      private val nil               = HNil.right[String]
      def fromJsObject(j: JsObject) = nil
    }
  
    implicit def ccons[K <: Symbol, H, T <: Coproduct](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsDecoder[H]],
      T: DerivedJsDecoder[T]
    ): DerivedJsDecoder[FieldType[K, H] :+: T] =
      new DerivedJsDecoder[FieldType[K, H] :+: T] {
        private val hint = ("type" -> JsString(K.value.name))
        def fromJsObject(j: JsObject) =
          if (j.fields.element(hint)) {
            j.get("xvalue")
              .into {
                case \/-(xvalue) => H.value.fromJson(xvalue)
                case -\/(_)      => H.value.fromJson(j)
              }
              .map(h => Inl(field[K](h)))
          } else
            T.fromJsObject(j).map(Inr(_))
      }
  
    implicit val cnil: DerivedJsDecoder[CNil] = new DerivedJsDecoder[CNil] {
      def fromJsObject(j: JsObject) = fail(s"JsObject with 'type' field", j)
    }
  }
~~~~~~~~

Dodanie obsługi preferencji użytkownika przebiega podobnie jak w przypadku `DerivedJsEncoder` i jest równie mechaniczne,
więc zostawimy to jako ćwiczenie dla czytelnika.

Brakuje już tylko jednej rzeczy: obsługi domyślnych wartości w case klasach. Możemy zażądać
odpowiedniej wartości, ale większym problemem jest to, że nie będziemy mogli używać tej samej
logiki do derywacji instancji dla produktów i koproduktów, gdyż dla tych drugich taka wartość nigdy nie zostanie 
wygenerowana.

Rozwiązanie jest dość drastyczne: musimy podzielić nasz `DerivedJsDecoder` na `DerivedCoproductJsDecoder`
i `DerivedProductJsDecoder`. Skupimy się na tym drugim i jednocześnie użyjemy typu `Map`
dla szybszego dostępu do pól:

{lang="text"}
~~~~~~~~
  sealed trait DerivedProductJsDecoder[A, R, J <: HList, D <: HList] {
    private[jsonformat] def fromJsObject(
      j: Map[String, JsValue],
      anns: J,
      defaults: D
    ): String \/ R
  }
~~~~~~~~

Możemy zażądać dowodu domyślnych wartości używając `Default.Aux[A, D]` a następnie zduplikować wszystkie
metody tak, aby obsłużyć sytuacje, gdy są i nie są one zdefiniowane. Jednak Shapeless jest litościwy (choć raz)
i dostarcza `Default.AsOptions.Aux[A, D]`, pozwalając nam obsłużyć je w czasie wykonania.

{lang="text"}
~~~~~~~~
  object DerivedProductJsDecoder {
    def gen[A, R, J <: HList, D <: HList](
      implicit G: LabelledGeneric.Aux[A, R],
      J: Annotations.Aux[json, A, J],
      D: Default.AsOptions.Aux[A, D],
      R: Cached[Strict[DerivedProductJsDecoder[A, R, J, D]]]
    ): JsDecoder[A] = new JsDecoder[A] {
      def fromJson(j: JsValue) = j match {
        case o @ JsObject(_) =>
          R.value.value.fromJsObject(o.fields.toMap, J(), D()).map(G.from)
        case other => fail("JsObject", other)
      }
    }
    ...
  }
~~~~~~~~

Musimy przenieść metody `.hcons` i `.hnil` do obiektu towarzyszącego nowej typeklasy, która
potrafi obsłużyć domyślne wartości

{lang="text"}
~~~~~~~~
  object DerivedProductJsDecoder {
    ...
      implicit def hnil[A]: DerivedProductJsDecoder[A, HNil, HNil, HNil] =
      new DerivedProductJsDecoder[A, HNil, HNil, HNil] {
        private val nil = HNil.right[String]
        def fromJsObject(j: StringyMap[JsValue], a: HNil, defaults: HNil) = nil
      }
  
    implicit def hcons[A, K <: Symbol, H, T <: HList, J <: HList, D <: HList](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsDecoder[H]],
      T: DerivedProductJsDecoder[A, T, J, D]
    ): DerivedProductJsDecoder[A, FieldType[K, H] :: T, None.type :: J, Option[H] :: D] =
      new DerivedProductJsDecoder[A, FieldType[K, H] :: T, None.type :: J, Option[H] :: D] {
        private val fieldname = K.value.name
        def fromJsObject(
          j: StringyMap[JsValue],
          anns: None.type :: J,
          defaults: Option[H] :: D
        ) =
          for {
            head <- j.get(fieldname) match {
                     case Maybe.Just(v) => H.value.fromJson(v)
                     case _ =>
                       defaults.head match {
                         case Some(default) => \/-(default)
                         case None          => H.value.fromJson(JsNull)
                       }
                   }
            tail <- T.fromJsObject(j, anns.tail, defaults.tail)
          } yield field[K](head) :: tail
      }
    ...
  }
~~~~~~~~

Niestety nie możemy już używać `@deriving` dla produktów i koproduktów, gdyż w pliku `deriving.conf` może być tylko jeden wpis
dla danej typeklasy.

No i nie zapomnijmy o wsparciu dla `@@`

{lang="text"}
~~~~~~~~
  object DerivedProductJsDecoder extends DerivedProductJsDecoder1 {
    ...
  }
  private[jsonformat] trait DerivedProductJsDecoder2 {
    this: DerivedProductJsDecoder.type =>
  
    implicit def hconsTagged[
      A, K <: Symbol, H, Z, T <: HList, J <: HList, D <: HList
    ](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsDecoder[H @@ Z]],
      T: DerivedProductJsDecoder[A, T, J, D]
    ): DerivedProductJsDecoder[
      A,
      FieldType[K, H @@ Z] :: T,
      None.type :: J,
      Option[H @@ Z] :: D
    ] = hcons(K, H, T)
  
    implicit def hconsCustomTagged[
      A, K <: Symbol, H, Z, T <: HList, J <: HList, D <: HList
    ](
      implicit
      K: Witness.Aux[K],
      H: Lazy[JsDecoder[H @@ Z]],
      T: DerivedProductJsDecoder[A, T, J, D]
    ): DerivedProductJsDecoder[
      A,
      FieldType[K, H @@ Z] :: T,
      Some[json] :: J,
      Option[H @@ Z] :: D
    ] = hconsCustomTagged(K, H, T)
  }
~~~~~~~~


### Skomplikowane Derywacje

Shapeless pozwala na dużo więcej rodzajów derywacji niż jest możliwe do osiągnięcia z użyciem
`scalaz-deriving` lub Magnolii. Jako przykład takiego nieosiągalnego enkodera/dekodera może posłużyć
model XML z  [`xmlformat`](https://github.com/scalaz/scalaz-deriving/tree/master/examples/xmlformat).

{lang="text"}
~~~~~~~~
  @deriving(Equal, Show, Arbitrary)
  sealed abstract class XNode
  
  @deriving(Equal, Show, Arbitrary)
  final case class XTag(
    name: String,
    attrs: IList[XAttr],
    children: IList[XTag],
    body: Maybe[XString]
  )
  
  @deriving(Equal, Show, Arbitrary)
  final case class XAttr(name: String, value: XString)
  
  @deriving(Show)
  @xderiving(Equal, Monoid, Arbitrary)
  final case class XChildren(tree: IList[XTag]) extends XNode
  
  @deriving(Show)
  @xderiving(Equal, Semigroup, Arbitrary)
  final case class XString(text: String) extends XNode
~~~~~~~~

Znając naturę XMLa, sensownym wydaje się mieć osobne pary dekoderów i enkoderów dla `XChildren` i `XString`.
Z użyciem Shapelessa moglibyśmy je wyderywować implementując specjalną obsługę pól zależnie od typeklas jakie są dla nich dostępne oraz
od tego czy jest to `Option` czy nie. Dodatkowo przy dekodowaniu moglibyśmy mieć różne strategie dekodowania
ciał elementów, które mogą być wieloczęściowe, zależnie czy nasz typ ma instancję `Semigroup`, `Monoid` czy też nie ma żadnej z nich.

A> Wielu deweloperów wierzy, że XML to jedynie bardziej rozwlekła forma JSONa z ostrymi nawiasami zamiast klamer.
A> Jednak próba implementacji dwukierunkowego konwertera między `XNode` i `JsValue` szybko udowadnia, że są to dwa kompletnie różne gatunki,
A> a konwersja jest możliwa jedynie dla konkretnych przypadków.

### Przykład: `UrlQueryWriter`

Nasza aplikacja `drone-dynamic-agents` mogłaby skorzystać z derywacji dla typu `UrlQueryWriter`, gdzie
każde pole kodowane jest za pomocą odpowiedniej instancji `UrlEncodedWriter`, a koprodukty nie są wspierane:

{lang="text"}
~~~~~~~~
  @typeclass trait UrlQueryWriter[A] {
    def toUrlQuery(a: A): UrlQuery
  }
  trait DerivedUrlQueryWriter[T] extends UrlQueryWriter[T]
  object DerivedUrlQueryWriter {
    def gen[T, Repr](
      implicit
      G: LabelledGeneric.Aux[T, Repr],
      CR: Cached[Strict[DerivedUrlQueryWriter[Repr]]]
    ): UrlQueryWriter[T] = { t =>
      CR.value.value.toUrlQuery(G.to(t))
    }
  
    implicit val hnil: DerivedUrlQueryWriter[HNil] = { _ =>
      UrlQuery(IList.empty)
    }
    implicit def hcons[Key <: Symbol, A, Remaining <: HList](
      implicit Key: Witness.Aux[Key],
      LV: Lazy[UrlEncodedWriter[A]],
      DR: DerivedUrlQueryWriter[Remaining]
    ): DerivedUrlQueryWriter[FieldType[Key, A] :: Remaining] = {
      case head :: tail =>
        val first =
          Key.value.name -> URLDecoder.decode(LV.value.toUrlEncoded(head).value, "UTF-8")
        val rest = DR.toUrlQuery(tail)
        UrlQuery(first :: rest.params)
    }
  }
~~~~~~~~

Pytanie "Czy te 30 linii kodu jest faktycznie lepsze niż 8 linii dla dwóch ręcznie stworzonych
instancji, których potrzebujemy?" jest całkowicie rozsądne, ale trzeba odpowiedzieć sobie na nie
od nowa w każdym konkretnym przypadku.

Dla kompletności, derywacja `UrlEncodedWriter` może być też zaimplementowana za pomocą Magnolii:

{lang="text"}
~~~~~~~~
  object UrlEncodedWriterMagnolia {
    type Typeclass[a] = UrlEncodedWriter[a]
    def combine[A](ctx: CaseClass[UrlEncodedWriter, A]) = a =>
      Refined.unsafeApply(ctx.parameters.map { p =>
        p.label + "=" + p.typeclass.toUrlEncoded(p.dereference(a))
      }.toList.intercalate("&"))
    def gen[A]: UrlEncodedWriter[A] = macro Magnolia.gen[A]
  }
~~~~~~~~


### Ciemna Strona Derywacji

> "Strzeż się w pełni automatycznej derywacji. Złość, strach, agresja; ciemną stroną derywacji są one.
> Łatwo wypływają, szybko dołączają do ciebie w walce. Gdy raz wstąpisz na ciemną ścieżkę, na zawsze
> zawładną twoim kompilatorem, a ciebie pochłoną.
>
> - starożytny mistrz Shapelessa

W dodatku do wszystkich ostrzeżeń co do w pełni automatycznej derywacji, wspomnianych dla Magnolii,
Shapeless jest **zdecydowanie** gorszy. Taka derywacja z jego użyciem jest nie tylko
[najczęstszym źródłem powolnej kompilacji](https://www.scala-lang.org/blog/2018/06/04/scalac-profiling.html),
ale również źródłem bolesnych błędów w kwestii ich koherencji.

Derywacja w pełni automatyczna ma miejsce wtedy, gdy `def gen` jest opatrzona modyfikatorem `implicit`, sprawiając, 
że wywołanie przejdzie rekurencyjnie przez całe ADT. Z racji tego jak działają niejawne zakresy,
zaimportowany `implicit def` ma wyższy priorytet niż konkretne instancje w obiektach towarzyszących, co
powoduje dekoherencję typeklas. Rozważmy taką właśnie sytuację:

{lang="text"}
~~~~~~~~
  import DerivedJsEncoder._
  
  @xderiving(JsEncoder)
  final case class Foo(s: String)
  final case class Bar(foo: Foo)
~~~~~~~~

Spodziewalibyśmy się, że zakodowana forma `Bar("hello")` będzie wyglądać tak:

{lang="text"}
~~~~~~~~
  {
    "foo":"hello"
  }
~~~~~~~~

ponieważ użyliśmy `xderiving` dla `Foo`. Ale zamiast tego możemy otrzymać 

{lang="text"}
~~~~~~~~
  {
    "foo": {
      "s":"hello"
    }
  }
~~~~~~~~

Sytuacja jest jeszcze gorsza, gdy taka niejawna derywacja jest dodana do obiektu towarzyszącego typeklasy,
gdyż oznacza to, że jej instancje będą **zawsze** derywowane w punkcie użycia a użytkownik nie może
wpłynąć na ten mechanizm.

Zasadniczo pisząc programy generyczne należy przyjąć, że wartości niejawne mogą być ignorowane przez kompilator
zależnie od zakresu, co oznacza, że tracimy bezpieczeństwo w czasie kompilacji, które było naszą główną motywacją
do pisania tego typu programów!

Wszystko jest dużo prostsze po jasnej stronie, gdzie modyfikator `implicit` jest używany jedynie dla
koherentnych, globalnie unikatowych instancji typeklas. Strach przed boilerplatem jest drogą na 
ciemną stronę. Strach prowadzi do złości. Złość prowadzi do nienawiści. Nienawiść prowadzi do cierpienia.


## Wydajność

Nie ma złotego środka w kwestii derywacji typeklas. Aspektem do rozważenia jest wydajność,
zarówno w czasie kompilacji jak i wykonania.

#### Czasy Kompilacji

Kiedy mówimy o czasach kompilacji to Shapeless zdecydowanie wychodzi przed szereg. Nie jest
niczym nadzwyczajnym, aby mały projekt przeszedł od jednej sekundy do jednej minuty czasu kompilacji.
Aby prześledzić przyczyny takich zachowań możemy użyć pluginu `scalac-profiling`

{lang="text"}
~~~~~~~~
  addCompilerPlugin("ch.epfl.scala" %% "scalac-profiling" % "1.0.0")
  scalacOptions ++= Seq("-Ystatistics:typer", "-P:scalac-profiling:no-profiledb")
~~~~~~~~

który wyprodukuje raport mogący posłużyć do wygenerowania *flame grafu*.

Dla typowej derywacji opartej o Shapelessa, dostajemy żywy wykres:

{width=90%}
![](images/implicit-flamegraph-jsonformat-jmh.png)

Niemal cały czas jest poświęcony na niejawne rozstrzyganie. Wprawdzie obejmuje to też kompilacje
instancji tworzonych z użyciem `scalaz-deriving` i Magnolii, ale to Shapeless dominuje.

A wszystko to, gdy wszystko działa. Jeśli zdarzy się problem z Shapelssową derywacją, to kompilator może
się zaciąć w nieskończonej pętli i musi być zabity.

#### Wydajność Czasu Uruchomienia

Kiedy mówimy o wydajności wykonania, odpowiedzią zawsze jest *to zależy*.

Zakładając ze logika derywacji została optymalnie zaimplementowana, to jedynym sposobem
aby dowiedzieć, która jest szybsza jest eksperymentowanie.

Biblioteka `jsonformat` używa [Java Microbenchmark Harness (JMH)](http://openjdk.java.net/projects/code-tools/jmh/)
na modelach pochodzących z API GeoJSONa, Google Maps i Twittera, które zostały skontrybuowane przez Andrity'ego Plokhotnyuka.
Dla każdego modelu mamy trzy testy:

- kodowanie `ADT` do `JsValue`
- pomyślne dekodowanie tego samego `JsValue` z powrotem do ADT
- dekodowanie `JsValue` z błędnymi danymi

zaaplikowane do trzech implementacji:

-   opartych o Magnolię
-   opartych o Shapeless
-   napisanych ręcznie

z odpowiadającymi optymalizacjami w każdej z nich. Wyniki prezentowane są w operacjach na sekundę
(im więcej tym lepiej) i pochodzą z wykonania na mocnej maszynie i jednym wątku:

{lang="text"}
~~~~~~~~
  > jsonformat/jmh:run -i 5 -wi 5 -f1 -t1 -w1 -r1 .*encode*
  Benchmark                                 Mode  Cnt       Score      Error  Units
  
  GeoJSONBenchmarks.encodeMagnolia         thrpt    5   70527.223 ±  546.991  ops/s
  GeoJSONBenchmarks.encodeShapeless        thrpt    5   65925.215 ±  309.623  ops/s
  GeoJSONBenchmarks.encodeManual           thrpt    5   96435.691 ±  334.652  ops/s
  
  GoogleMapsAPIBenchmarks.encodeMagnolia   thrpt    5   73107.747 ±  439.803  ops/s
  GoogleMapsAPIBenchmarks.encodeShapeless  thrpt    5   53867.845 ±  510.888  ops/s
  GoogleMapsAPIBenchmarks.encodeManual     thrpt    5  127608.402 ± 1584.038  ops/s
  
  TwitterAPIBenchmarks.encodeMagnolia      thrpt    5  133425.164 ± 1281.331  ops/s
  TwitterAPIBenchmarks.encodeShapeless     thrpt    5   84233.065 ±  352.611  ops/s
  TwitterAPIBenchmarks.encodeManual        thrpt    5  281606.574 ± 1975.873  ops/s
~~~~~~~~

Widzimy, że przodują implementacje ręczne, za którymi podąża Magnolia. Shapeless
osiągnął od 30% do 70% wydajności ręcznie tworzonych instancji. Teraz spójrzmy na dekodowanie

{lang="text"}
~~~~~~~~
  > jsonformat/jmh:run -i 5 -wi 5 -f1 -t1 -w1 -r1 .*decode.*Success
  Benchmark                                        Mode  Cnt       Score      Error  Units
  
  GeoJSONBenchmarks.decodeMagnoliaSuccess         thrpt    5   40850.270 ±  201.457  ops/s
  GeoJSONBenchmarks.decodeShapelessSuccess        thrpt    5   41173.199 ±  373.048  ops/s
  GeoJSONBenchmarks.decodeManualSuccess           thrpt    5  110961.246 ±  468.384  ops/s
  
  GoogleMapsAPIBenchmarks.decodeMagnoliaSuccess   thrpt    5   44577.796 ±  457.861  ops/s
  GoogleMapsAPIBenchmarks.decodeShapelessSuccess  thrpt    5   31649.792 ±  861.169  ops/s
  GoogleMapsAPIBenchmarks.decodeManualSuccess     thrpt    5   56250.913 ±  394.105  ops/s
  
  TwitterAPIBenchmarks.decodeMagnoliaSuccess      thrpt    5   55868.832 ± 1106.543  ops/s
  TwitterAPIBenchmarks.decodeShapelessSuccess     thrpt    5   47711.161 ±  356.911  ops/s
  TwitterAPIBenchmarks.decodeManualSuccess        thrpt    5   71962.394 ±  465.752  ops/s
~~~~~~~~

Tutaj walka o drugie miejsce między Magnolią i Shapelessem jest bardziej zażarta. W końcu
test dekodujący niepoprawne dane

{lang="text"}
~~~~~~~~
  > jsonformat/jmh:run -i 5 -wi 5 -f1 -t1 -w1 -r1 .*decode.*Error
  Benchmark                                      Mode  Cnt        Score       Error  Units
  
  GeoJSONBenchmarks.decodeMagnoliaError         thrpt    5   981094.831 ± 11051.370  ops/s
  GeoJSONBenchmarks.decodeShapelessError        thrpt    5   816704.635 ±  9781.467  ops/s
  GeoJSONBenchmarks.decodeManualError           thrpt    5   586733.762 ±  6389.296  ops/s
  
  GoogleMapsAPIBenchmarks.decodeMagnoliaError   thrpt    5  1288888.446 ± 11091.080  ops/s
  GoogleMapsAPIBenchmarks.decodeShapelessError  thrpt    5  1010145.363 ±  9448.110  ops/s
  GoogleMapsAPIBenchmarks.decodeManualError     thrpt    5  1417662.720 ±  1197.283  ops/s
  
  TwitterAPIBenchmarks.decodeMagnoliaError      thrpt    5   128704.299 ±   832.122  ops/s
  TwitterAPIBenchmarks.decodeShapelessError     thrpt    5   109715.865 ±   826.488  ops/s
  TwitterAPIBenchmarks.decodeManualError        thrpt    5   148814.730 ±  1105.316  ops/s
~~~~~~~~

Gdy już wydawało się, że widzimy wzór, okazało się, że zarówno Magnolia jak i Shapeless 
wygrały w przypadku danych dla API GeoJSONa, ale ręczne instancje osiągnęły lepszy wyniki
dla Google Maps i Twittera.

Chcielibyśmy dołączyć do porównania `scalaz-deriving`, więc porównamy odpowiadające sobie implementacje
`Equal`, przetestowane na dwóch wartościach które mają tę samą zawartość (`True`) i dwóch o różnej
zawartości (`False`).

{lang="text"}
~~~~~~~~
  > jsonformat/jmh:run -i 5 -wi 5 -f1 -t1 -w1 -r1 .*equal*
  Benchmark                                     Mode  Cnt        Score       Error  Units
  
  GeoJSONBenchmarks.equalScalazTrue            thrpt    5   276851.493 ±  1776.428  ops/s
  GeoJSONBenchmarks.equalMagnoliaTrue          thrpt    5    93106.945 ±  1051.062  ops/s
  GeoJSONBenchmarks.equalShapelessTrue         thrpt    5   266633.522 ±  4972.167  ops/s
  GeoJSONBenchmarks.equalManualTrue            thrpt    5   599219.169 ±  8331.308  ops/s
  
  GoogleMapsAPIBenchmarks.equalScalazTrue      thrpt    5    35442.577 ±   281.597  ops/s
  GoogleMapsAPIBenchmarks.equalMagnoliaTrue    thrpt    5    91016.557 ±   688.308  ops/s
  GoogleMapsAPIBenchmarks.equalShapelessTrue   thrpt    5   107245.505 ±   468.427  ops/s
  GoogleMapsAPIBenchmarks.equalManualTrue      thrpt    5   302247.760 ±  1927.858  ops/s
  
  TwitterAPIBenchmarks.equalScalazTrue         thrpt    5    99066.013 ±  1125.422  ops/s
  TwitterAPIBenchmarks.equalMagnoliaTrue       thrpt    5   236289.706 ±  3182.664  ops/s
  TwitterAPIBenchmarks.equalShapelessTrue      thrpt    5   251578.931 ±  2430.738  ops/s
  TwitterAPIBenchmarks.equalManualTrue         thrpt    5   865845.158 ±  6339.379  ops/s
~~~~~~~~

Tak jak można było się spodziewać, instancje stworzone ręczenie są daleko z przodu. Z kolei
Shapeless prawie zawsze wygrywa wśród automatycznych derywacji. Biblioteka `scalaz-deriving` miała dobry start
z `GeoJSON`, ale nie poradziła sobie w testach Google Maps i Twittera. Wyniki `False` są niemal identyczne

{lang="text"}
~~~~~~~~
  > jsonformat/jmh:run -i 5 -wi 5 -f1 -t1 -w1 -r1 .*equal*
  Benchmark                                     Mode  Cnt        Score       Error  Units
  
  GeoJSONBenchmarks.equalScalazFalse           thrpt    5    89552.875 ±   821.791  ops/s
  GeoJSONBenchmarks.equalMagnoliaFalse         thrpt    5    86044.021 ±  7790.350  ops/s
  GeoJSONBenchmarks.equalShapelessFalse        thrpt    5   262979.062 ±  3310.750  ops/s
  GeoJSONBenchmarks.equalManualFalse           thrpt    5   599989.203 ± 23727.672  ops/s
  
  GoogleMapsAPIBenchmarks.equalScalazFalse     thrpt    5    35970.818 ±   288.609  ops/s
  GoogleMapsAPIBenchmarks.equalMagnoliaFalse   thrpt    5    82381.975 ±   625.407  ops/s
  GoogleMapsAPIBenchmarks.equalShapelessFalse  thrpt    5   110721.122 ±   579.331  ops/s
  GoogleMapsAPIBenchmarks.equalManualFalse     thrpt    5   303588.815 ±  2562.747  ops/s
  
  TwitterAPIBenchmarks.equalScalazFalse        thrpt    5   193930.568 ±  1176.421  ops/s
  TwitterAPIBenchmarks.equalMagnoliaFalse      thrpt    5   429764.654 ± 11944.057  ops/s
  TwitterAPIBenchmarks.equalShapelessFalse     thrpt    5   494510.588 ±  1455.647  ops/s
  TwitterAPIBenchmarks.equalManualFalse        thrpt    5  1631964.531 ± 13110.291  ops/s
~~~~~~~~

Wydajność wykonania `scalaz-deriving`, Magnolii i Shapelessa jest zazwyczaj wystarczająca.
Bądźmy realistami, rzadko kiedy piszemy aplikacje, które muszą kodować do JSONa więcej niż 130 000
wartości na sekundę, na jednym wątku, na JVMie. Jeśli takie jest wymaganie to może warto spojrzeć w stronę C i C++?

Mało prawdopodobne jest, żeby wyderywowane instancje stały się wąskim gardłem aplikacji. Jeśli jednak tak się stanie,
to zawsze istnieje opcja ręcznych instancji, które są bardziej potężne, ale też tym samym bardziej niebezpieczne. Łatwo
jest przy ich tworzeniu popełnić błędy, literówki a nawet przypadkowo obniżyć wydajność.

Podsumowując, derywacje i antyczne makra nie są żadną konkurencją dla dobrych, własnoręcznie napisanych instancji!

A> Moglibyśmy poświęcić życie na badania zużycia CPU i alokacji obiektów używając [`async-profilera`](https://github.com/jvm-profiling-tools/async-profiler)
A> i na próby optymalizacji naszych implementacji. Przykładowo, w samym `jsonformat` jest kilka optymalizacji, których tutaj
A> nie powtórzyliśmy, a które polegają na bardziej zoptymalizowanym dostępie do pól i dodaniu `.xmap`, `.map` oraz `.contramap` w odpowiednich typeklasach.
A> Można uczciwie powiedzieć, że kod tej biblioteki przedkłada czytelność nad optymalizacje, a mimo to nadal
A> osiąga niewiarygodną wydajność.


## Podsumowanie

Gdy musimy zdecydować jakiej technologii użyć do derywacji typeklas, pomocny może okazać się poniższy
wykaz funkcjonalności:

| Funkcjonalność    | Scalaz | Magnolia | Shapeless   | Manual            |
|-------------------|--------|----------|-------------|-------------------|
| `@deriving`       | tak    | tak      | tak         |                   |
| Prawa             | tak    |          |             |                   |
| Szybka kompilacja | tak    | tak      |             | tak               |
| Nazwy pól         |        | tak      | tak         |                   |
| Anotacje          |        | tak      | częściowo   |                   |
| Domyślne wartości |        | tak      | z haczykami |                   |
| Skomplikowanie    |        |          | boleśnie    |                   |
| Wydajność         |        |          |             | potrzymaj mi piwo |

Polecamy używanie `scalaz-deriving`, gdy to tylko możliwe, Magnolii do enkoderów i dekoderów oraz gdy
wydajność jest bardzo istotna, a Shapelessa tam, gdzie derywacje są bardzo skomplikowane a czasy kompilacji
nie mają dużego znaczenia.

Instancje pisane ręcznie pozostają zawsze pod ręką na specjalne okazje oraz gdy trzeba osiągnąć
maksymalną wydajność. Jeśli je piszesz, to staraj się unikać literówek i błędów używając narzędzi do generacji kodu.


# Zmontowanie Aplikacji

Na zakończenie zaaplikujemy zdobytą wiedzę do naszej przykładowej aplikacji i zaimplementujemy klienta oraz serwer
HTTP za pomocą czysto funkcyjnej biblioteki [http4s](https://http4s.org/).

Kod źródłowy `drone-dynamic-agents` jest dostępny wraz z kodem źródłowym tej książki na `https://github.com/fommil/fpmortals`
w folderze `examples`. Obecność przy komputerze w trakcie lektury tego rozdziału nie jest co prawda obowiązkowa,
ale wielu czytelników może zechcieć śledzić kod źródłowy wraz z tekstem tego rozdziału.

Niektóre części aplikacji pozostały niezaimplementowane i pozostawione jako ćwiczenie dla czytelnika. Więcej
instrukcji znajdziesz w `README`.

## Przegląd

Nasza główna aplikacja wymaga jedynie implementacji algebry `DynAgents`.

{lang="text"}
~~~~~~~~
  trait DynAgents[F[_]] {
    def initial: F[WorldView]
    def update(old: WorldView): F[WorldView]
    def act(world: WorldView): F[WorldView]
  }
~~~~~~~~

Mamy już taką implementację w postaci `DynAgentsModule`, ale wymaga ona implementacji algebr `Drone` i `Machines`,
które z kolei wymagają algebr `JsonClient`, `LocalClock` i Oauth2, itd., itd., itd.

Przydatnym bywa spojrzenie z lotu ptaka na wszystkie algebry, moduły i interpretery naszej aplikacji.
Oto jak ułożony jest nasz kod źródłowy:

{lang="text"}
~~~~~~~~
  ├── dda
  │   ├── algebra.scala
  │   ├── DynAgents.scala
  │   ├── main.scala
  │   └── interpreters
  │       ├── DroneModule.scala
  │       └── GoogleMachinesModule.scala
  ├── http
  │   ├── JsonClient.scala
  │   ├── OAuth2JsonClient.scala
  │   ├── encoding
  │   │   ├── UrlEncoded.scala
  │   │   ├── UrlEncodedWriter.scala
  │   │   ├── UrlQuery.scala
  │   │   └── UrlQueryWriter.scala
  │   ├── oauth2
  │   │   ├── Access.scala
  │   │   ├── Auth.scala
  │   │   ├── Refresh.scala
  │   │   └── interpreters
  │   │       └── BlazeUserInteraction.scala
  │   └── interpreters
  │       └── BlazeJsonClient.scala
  ├── os
  │   └── Browser.scala
  └── time
      ├── Epoch.scala
      ├── LocalClock.scala
      └── Sleep.scala
~~~~~~~~

Sygnatury wszystkich algebr możemy podsumować jako

{lang="text"}
~~~~~~~~
  trait Sleep[F[_]] {
    def sleep(time: FiniteDuration): F[Unit]
  }
  
  trait LocalClock[F[_]] {
    def now: F[Epoch]
  }
  
  trait JsonClient[F[_]] {
    def get[A: JsDecoder](
      uri: String Refined Url,
      headers: IList[(String, String)]
    ): F[A]
  
    def post[P: UrlEncodedWriter, A: JsDecoder](
      uri: String Refined Url,
      payload: P,
      headers: IList[(String, String)]
    ): F[A]
  }
  
  trait Auth[F[_]] {
    def authenticate: F[CodeToken]
  }
  trait Access[F[_]] {
    def access(code: CodeToken): F[(RefreshToken, BearerToken)]
  }
  trait Refresh[F[_]] {
    def bearer(refresh: RefreshToken): F[BearerToken]
  }
  trait OAuth2JsonClient[F[_]] {
    // same methods as JsonClient, but doing OAuth2 transparently
  }
  
  trait UserInteraction[F[_]] {
    def start: F[String Refined Url]
    def open(uri: String Refined Url): F[Unit]
    def stop: F[CodeToken]
  }
  
  trait Drone[F[_]] {
    def getBacklog: F[Int]
    def getAgents: F[Int]
  }
  
  trait Machines[F[_]] {
    def getTime: F[Epoch]
    def getManaged: F[NonEmptyList[MachineNode]]
    def getAlive: F[MachineNode ==>> Epoch]
    def start(node: MachineNode): F[Unit]
    def stop(node: MachineNode): F[Unit]
  }
~~~~~~~~

Zauważ, że niektóre sygnatury z poprzednich rozdziałów zostały przerefaktorowane tak, aby
używały typów danych ze Scalaz, skoro już wiemy, że są lepsze od tych z biblioteki standardowej.

Definiowane typy danych to:

{lang="text"}
~~~~~~~~
  @xderiving(Order, Arbitrary)
  final case class Epoch(millis: Long) extends AnyVal
  
  @deriving(Order, Show)
  final case class MachineNode(id: String)
  
  @deriving(Equal, Show)
  final case class CodeToken(token: String, redirect_uri: String Refined Url)
  
  @xderiving(Equal, Show, ConfigReader)
  final case class RefreshToken(token: String) extends AnyVal
  
  @deriving(Equal, Show, ConfigReader)
  final case class BearerToken(token: String, expires: Epoch)
  
  @deriving(ConfigReader)
  final case class OAuth2Config(token: RefreshToken, server: ServerConfig)
  
  @deriving(ConfigReader)
  final case class AppConfig(drone: BearerToken, machines: OAuth2Config)
  
  @xderiving(UrlEncodedWriter)
  final case class UrlQuery(params: IList[(String, String)]) extends AnyVal
~~~~~~~~

Oraz typeklasy:

{lang="text"}
~~~~~~~~
  @typeclass trait UrlEncodedWriter[A] {
    def toUrlEncoded(a: A): String Refined UrlEncoded
  }
  @typeclass trait UrlQueryWriter[A] {
    def toUrlQuery(a: A): UrlQuery
  }
~~~~~~~~

Derywujemy przydatne typeklasy używając `scalaz-deriving` oraz Magnolii. `ConfigReader` pochodzi
z biblioteki `pureconfig` i służy do odczytywania konfiguracji z plików HOCON.

Przeanalizujmy też, bez zaglądania do implementacji, jak kształtuje się graf zależności w `DynAgentsModule`.

{lang="text"}
~~~~~~~~
  final class DynAgentsModule[F[_]: Applicative](
    D: Drone[F],
    M: Machines[F]
  ) extends DynAgents[F] { ... }
  
  final class DroneModule[F[_]](
    H: OAuth2JsonClient[F]
  ) extends Drone[F] { ... }
  
  final class GoogleMachinesModule[F[_]](
    H: OAuth2JsonClient[F]
  ) extends Machines[F] { ... }
~~~~~~~~

Dwa moduły implementują `OAuth2JsonClient`, jeden używa algebry `Refresh` dla usług Google'a, a drugi niewygasającego `BearerToken` dla `Drone'a.

{lang="text"}
~~~~~~~~
  final class OAuth2JsonClientModule[F[_]](
    token: RefreshToken
  )(
    H: JsonClient[F],
    T: LocalClock[F],
    A: Refresh[F]
  )(
    implicit F: MonadState[F, BearerToken]
  ) extends OAuth2JsonClient[F] { ... }
  
  final class BearerJsonClientModule[F[_]: Monad](
    bearer: BearerToken
  )(
    H: JsonClient[F]
  ) extends OAuth2JsonClient[F] { ... }
~~~~~~~~

Do tej pory widzieliśmy wymagania względem `F` mówiące, że musimy dostarczyć `Applicative[F]`, `Monad[F]`
oraz `MonadState[F, BearerToken]`. Wszystkie te wymagania spełnia `StateT[Task, BearerToken, ?]` co pozwala
nam uczynić ten typ kontekstem naszej aplikacji.

Jednak niektóre algebry mają interpretery używające bezpośrednio typu `Task`

{lang="text"}
~~~~~~~~
  final class LocalClockTask extends LocalClock[Task] { ... }
  final class SleepTask extends Sleep[Task] { ... }
~~~~~~~~

Przypomnijmy, że nasze algebry mogą dostarczać `liftM` w swoich obiektach towarzyszących (patrz rozdział
7.4 na temat Biblioteki Transformatorów Monad), co pozwala nam wynieść `LocalClock[Task]` do pożądanego
`StateT[Task, BearerToken, ?]` czyniąc wszystko idealnie spójnym.

Niestety to nie koniec. Sprawy komplikują się na następnej warstwie, gdyż `JsonClient` posiada interpreter używający
innego kontekstu

{lang="text"}
~~~~~~~~
  final class BlazeJsonClient[F[_]](H: Client[Task])(
    implicit
    F: MonadError[F, JsonClient.Error],
    I: MonadIO[F, Throwable]
  ) extends JsonClient[F] { ... }
  object BlazeJsonClient {
    def apply[F[_]](
      implicit
      F: MonadError[F, JsonClient.Error],
      I: MonadIO[F, Throwable]
    ): Task[JsonClient[F]] = ...
  }
~~~~~~~~

Zauważ, że konstruktor `BlazeJsonClient` zwraca `Task[JsonClient[F]]`, a nie `JsonClient[F]`.
Dzieje się tak, ponieważ stworzenie tego klient powoduje efekt w postaci utworzenia mutowalnej puli połączeń
zarządzanej wewnętrznie przez http4s.

A> `OAuth2JsonClientModule` wymaga instancji `MonadState`, a `BlazeJsonClient` instancji
A> `MonadError` i `MonadIO`. Nasz kontekst musi więc przyjąć formę posiadającą ja wszystkie:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   StateT[EitherT[Task, JsonClient.Error, ?], BearerToken, ?]
A> ~~~~~~~~
A> 
A> Stos monad. Stosy monad automatycznie dostarczają odpowiednie instancje `MonadState` i `MonadError` kiedy
A> są zagnieżdżane, więc nie musimy się tym martwić. Gdybyśmy zahardkodowali implementacje w interpreterze i 
A> zwracali `EitherT[Task, Error, ?]` z `BlazeJsonClient` to wszystko stałoby się dużo trudniejsze.

Nie możemy zapomnieć o dostarczeniu `RefreshToken` dla `GoogleMachinesModule`. Moglibyśmy zrzucić to zadanie
na użytkownika, ale jesteśmy mili i dostarczamy osobną aplikację, która używając algebr `Auth` i `Access` rozwiązuje 
ten problem. Implementacje `AuthModule` i `AccessModule` niosą ze sobą kolejne wymagania, ale na szczęście żadnych
zmian co do kontekstu `F[_]`.

{lang="text"}
~~~~~~~~
  final class AuthModule[F[_]: Monad](
    config: ServerConfig
  )(
    I: UserInteraction[F]
  ) extends Auth[F] { ... }
  
  final class AccessModule[F[_]: Monad](
    config: ServerConfig
  )(
    H: JsonClient[F],
    T: LocalClock[F]
  ) extends Access[F] { ... }
  
  final class BlazeUserInteraction private (
    pserver: Promise[Void, Server[Task]],
    ptoken: Promise[Void, String]
  ) extends UserInteraction[Task] { ... }
  object BlazeUserInteraction {
    def apply(): Task[BlazeUserInteraction] = ...
  }
~~~~~~~~

Interpreter algebry `UserInteraction` jest najbardziej skomplikowanym elementem naszego
kodu. Startuje on serwer HTTP, prosi użytkownika o otworzenie strony w przeglądarce,
odbiera wywołanie zwrotne w serwerze i zwraca wynik jednocześnie zakańczając pracę serwera
w bezpieczny sposób.

Zamiast używać `StateT` do zarządzania tym stanem użyliśmy typu `Promise` (pochodzącego z `ioeffect`).
Powinniśmy zawsze używać `Promise` (lub `IORef`) zamiast `StateT`, gdy piszemy interpreter oparty o 
`IO`, gdyż pozwala nam to opanować abstrakcje. Gdybyśmy użyli `StateT`, to nie tylko miałoby to wpływ
na całą aplikacje, ale również powodowałoby wyciek lokalnego stanu do głównej aplikacji, która musiałaby
przejąc odpowiedzialność za dostarczenie inicjalnej wartości. W tym wypadku nie moglibyśmy użyć `StateT`
również dlatego, że potrzebujemy możliwości "czekania", którą daje nam jedynie `Promise`.


## `Main`

Najbrzydsza część FP pojawia się, gdy musimy sprawić by wszystkie monady się zgadzały. Najczęściej ma to miejsce
w punkcie wejściowym naszej aplikacji, czyli klasie `Main`.

Nasza główna pętla wyglądała tak

{lang="text"}
~~~~~~~~
  state = initial()
  while True:
    state = update(state)
    state = act(state)
~~~~~~~~

Dobra wiadomość jest taka, że teraz ten kod będzie wyglądał tak:

{lang="text"}
~~~~~~~~
  for {
    old     <- F.get
    updated <- A.update(old)
    changed <- A.act(updated)
    _       <- F.put(changed)
    _       <- S.sleep(10.seconds)
  } yield ()
~~~~~~~~

gdzie `F` przechowuje stan świata w `MonadState[F, WoldView]`. Możemy zamknąć ten fragment
w metodzie `.step` i powtarzać ją w nieskończoność wywołując `.step[F].forever[Unit]`.

W tym momencie mamy do wyboru dwa podejścia i oba omówimy. Pierwszym i jednocześnie najprostszym
jest skonstruowanie stosu monad kompatybilnego ze wszystkimi algebrami, a każda z nich musi definiować `liftM`, aby
wynieść ją do większego stosu.

Kod, który chcemy napisać dla trybu jednorazowego uwierzytelnienia to

{lang="text"}
~~~~~~~~
  def auth(name: String): Task[Unit] = {
    for {
      config    <- readConfig[ServerConfig](name + ".server")
      ui        <- BlazeUserInteraction()
      auth      = new AuthModule(config)(ui)
      codetoken <- auth.authenticate
      client    <- BlazeJsonClient
      clock     = new LocalClockTask
      access    = new AccessModule(config)(client, clock)
      token     <- access.access(codetoken)
      _         <- putStrLn(s"got token: $token")
    } yield ()
  }.run
~~~~~~~~

gdzie `.readConfig` i `.putStrLn` to wywołania funkcji z bibliotek. Możemy potraktować je jako interpretery
oparte o `Task` dla algebr odczytujących konfigurację i wypisująca ciąg znaków.

Ten kod jednak się nie kompiluje z dwóch powodów. Po pierwsze, musimy zdecydować jak będzie wyglądał nasz
stos monad. Konstruktor `BlazeJsonClient` zwraca `Task`, ale `JsonClient`wymaga `MonadError[..., JsonClient.Error]`,
co można rozwiązać za pomocą `EitherT`. Możemy więc skonstruować nasz stos dla całej konstrukcji `for` jako

{lang="text"}
~~~~~~~~
  type H[a] = EitherT[Task, JsonClient.Error, a]
~~~~~~~~

Niestety, oznacza to, że musimy wywołać `.liftM` dla wszystkiego co zwraca `Task`,
co dodaje dość dużo boilerplate'u. Niestety metoda `liftM` nie przyjmuje typów o kształcie
`H[_]` tylko `H[_[_]. _]`, więc musimy stworzyć alias, który pomoże kompilatorowi:

{lang="text"}
~~~~~~~~
  type HT[f[_], a] = EitherT[f, JsonClient.Error, a]
  type H[a]        = HT[Task, a]
~~~~~~~~

możemy teraz wywołać `.liftM[HT]` kiedy dostajemy `Task`

{lang="text"}
~~~~~~~~
  for {
    config    <- readConfig[ServerConfig](name + ".server").liftM[HT]
    ui        <- BlazeUserInteraction().liftM[HT]
    auth      = new AuthModule(config)(ui)
    codetoken <- auth.authenticate.liftM[HT]
    client    <- BlazeJsonClient[H].liftM[HT]
    clock     = new LocalClockTask
    access    = new AccessModule(config)(client, clock)
    token     <- access.access(codetoken)
    _         <- putStrLn(s"got token: $token").liftM[HT]
  } yield ()
~~~~~~~~

Ale nasz kod nadal się nie kompiluje. Tym razem dlatego, że `clock` jest typu `LocalClock[Task]` a `AccessModule` wymaga `LocalClock[H]`. 
Dodajmy więc potrzebny boilerplate `.liftM` do obiektu towarzyszącego `LocalClock` i wynieśmy całą algebrę

{lang="text"}
~~~~~~~~
  clock     = LocalClock.liftM[Task, HT](new LocalClockTask)
~~~~~~~~

Wreszcie wszystko się kompiluje!

Drugie podejście do zmontowywania aplikacji jest bardziej złożone, ale niezbędne, gdy pojawiają się
konflikty w stosie monad, tak jak w naszej głównej pętli. Jeśli przeanalizujemy wymagania,
zobaczymy, że potrzebujemy poniższych instancji:

-   `MonadError[F, JsonClient.Error]` w `JsonClient`
-   `MonadState[F, BearerToken]` w `OAuth2JsonClient`
-   `MonadState[F, WorldView]` w głównej pętli

Niestety, dwa wymagania na `MonadState` są ze sobą sprzeczne. Moglibyśmy
skonstruować typ danych, który przechowuje cały stan aplikacji, ale byłaby to
cieknąca abstrakcja. Zamiast tego zagnieździmy konstrukcję `for` i dostarczymy stan tam gdzie jest potrzebny

Musimy teraz przemyśleć trzy warstwy, które nazwiemy `F`, `G` i `H`

{lang="text"}
~~~~~~~~
  type HT[f[_], a] = EitherT[f, JsonClient.Error, a]
  type GT[f[_], a] = StateT[f, BearerToken, a]
  type FT[f[_], a] = StateT[f, WorldView, a]
  
  type H[a]        = HT[Task, a]
  type G[a]        = GT[H, a]
  type F[a]        = FT[G, a]
~~~~~~~~

Teraz złe wieści: `liftM` obsługuje tylko jedną warstwę na raz. Jeśli mamy `Task[A]`, a chcemy
uzyskać `F[A]` to musimy przejść przez wszystkie kroki i wywołać `ta.liftM[HT].liftM[GT].liftM[FT]`.
Podobnie, gdy wynosimy algebry, musimy zawołać `liftM` wielokrotnie. Aby uzyskać `Sleep[F]`, musimy napisać

{lang="text"}
~~~~~~~~
  val S: Sleep[F] = {
    import Sleep.liftM
    liftM(liftM(liftM(new SleepTask)))
  }
~~~~~~~~

a żeby dostać `LocalClock[G]` robimy dwa wyniesienia

{lang="text"}
~~~~~~~~
  val T: LocalClock[G] = {
    import LocalClock.liftM
    liftM(liftM(new LocalClockTask))
  }
~~~~~~~~

Główna aplikacja wygląda więc tak:

{lang="text"}
~~~~~~~~
  def agents(bearer: BearerToken): Task[Unit] = {
    ...
    for {
      config <- readConfig[AppConfig]
      blaze  <- BlazeJsonClient[G]
      _ <- {
        val bearerClient = new BearerJsonClientModule(bearer)(blaze)
        val drone        = new DroneModule(bearerClient)
        val refresh      = new RefreshModule(config.machines.server)(blaze, T)
        val oauthClient =
          new OAuth2JsonClientModule(config.machines.token)(blaze, T, refresh)
        val machines = new GoogleMachinesModule(oauthClient)
        val agents   = new DynAgentsModule(drone, machines)
        for {
          start <- agents.initial
          _ <- {
            val fagents = DynAgents.liftM[G, FT](agents)
            step(fagents, S).forever[Unit]
          }.run(start)
        } yield ()
      }.eval(bearer).run
    } yield ()
  }
~~~~~~~~

gdzie zewnętrzna pętla używa `Task`, środkowa `G` a wewnętrzna `F`.

Wywołania `.run(start)` oraz `.eval(bearer)` dostarczają inicjalny stan dla części bazujących na `StateT`.
`.run` z kolei pokazuje błędy zgromadzone w `EitherT`.

Na koniec wołamy te dwie aplikacji z naszej instancji `SafeApp`

{lang="text"}
~~~~~~~~
  object Main extends SafeApp {
    def run(args: List[String]): IO[Void, ExitStatus] = {
      if (args.contains("--machines")) auth("machines")
      else agents(BearerToken("<invalid>", Epoch(0)))
    }.attempt[Void].map {
      case \/-(_)   => ExitStatus.ExitNow(0)
      case -\/(err) => ExitStatus.ExitNow(1)
    }
  }
~~~~~~~~

i uruchamiamy ją!

{lang="text"}
~~~~~~~~
  > runMain fommil.dda.Main --machines
  [info] Running (fork) fommil.dda.Main --machines
  ...
  [info] Service bound to address /127.0.0.1:46687
  ...
  [info] Created new window in existing browser session.
  ...
  [info] Headers(Host: localhost:46687, Connection: keep-alive, User-Agent: Mozilla/5.0 ...)
  ...
  [info] POST https://www.googleapis.com/oauth2/v4/token
  ...
  [info] got token: "<elided>"
~~~~~~~~

Hurra!


## Blaze

Server i klienta HTTP zaimplementujemy z użyciem zewnętrznej biblioteki `http4s`. Interpretery
dla odpowiednich algebr dostaną w związku z tym prefiks *Blaze*, gdyż tak też nazywa się 
właściwy komponent tej biblioteki.

Dodajemy poniższe zależności

{lang="text"}
~~~~~~~~
  val http4sVersion = "0.18.16"
  libraryDependencies ++= Seq(
    "org.http4s"            %% "http4s-dsl"          % http4sVersion,
    "org.http4s"            %% "http4s-blaze-server" % http4sVersion,
    "org.http4s"            %% "http4s-blaze-client" % http4sVersion
  )
~~~~~~~~


### `BlazeJsonClient`

Będziemy potrzebować kilku dodatkowych importów

{lang="text"}
~~~~~~~~
  import org.http4s
  import org.http4s.{ EntityEncoder, MediaType }
  import org.http4s.headers.`Content-Type`
  import org.http4s.client.Client
  import org.http4s.client.blaze.{ BlazeClientConfig, Http1Client }
~~~~~~~~

Moduł `Client` może być podsumowany jako

{lang="text"}
~~~~~~~~
  final class Client[F[_]](
    val shutdown: F[Unit]
  )(implicit F: MonadError[F, Throwable]) {
    def fetch[A](req: Request[F])(f: Response[F] => F[A]): F[A] = ...
    ...
  }
~~~~~~~~

gdzie `Request` i `Response` to typy danych:

{lang="text"}
~~~~~~~~
  final case class Request[F[_]](
    method: Method
    uri: Uri,
    headers: Headers,
    body: EntityBody[F]
  ) {
    def withBody[A](a: A)
                   (implicit F: Monad[F], A: EntityEncoder[F, A]): F[Request[F]] = ...
    ...
  }
  
  final case class Response[F[_]](
    status: Status,
    headers: Headers,
    body: EntityBody[F]
  )
~~~~~~~~

składające się z 

{lang="text"}
~~~~~~~~
  final case class Headers(headers: List[Header])
  final case class Header(name: String, value: String)
  
  final case class Uri( ... )
  object Uri {
    // not total, only use if `s` is guaranteed to be a URL
    def unsafeFromString(s: String): Uri = ...
    ...
  }
  
  final case class Status(code: Int) {
    def isSuccess: Boolean = ...
    ...
  }
  
  type EntityBody[F[_]] = fs2.Stream[F, Byte]
~~~~~~~~

`EntityBody` jest aliasem na typ `Stream` z biblioteki [`fs2`](https://github.com/functional-streams-for-scala/fs2). Możemy rozumieć go jako
leniwy strumień danych wykonujący efekty, bazujący na wyciąganiu danych (_pull-based_). Zaimplementowany jest jako monada `Free` z
dodatkowym łapaniem wyjątków i obsługą przerwań. `Stream` przyjmuje dwa parametry typu: typ efektów i typ zawartości. Dodatkowo posiada
wewnątrz wydajną reprezentację pozwalającą na łączenie danych (_batching_), więc przykładowo, używając `Stream[F, Byte]` tak naprawdę mamy do czynienia
z opakowaną tablicą `Array[Byte]`, która przybywa do nas za pośrednictwem sieci.

Musimy przekonwertować nasze reprezentacje nagłówków i URLi na wersje wymagane przez http4s:

{lang="text"}
~~~~~~~~
  def convert(headers: IList[(String, String)]): http4s.Headers =
    http4s.Headers(
      headers.foldRight(List[http4s.Header]()) {
        case ((key, value), acc) => http4s.Header(key, value) :: acc
      }
    )
  
  def convert(uri: String Refined Url): http4s.Uri =
    http4s.Uri.unsafeFromString(uri.value) // we already validated our String
~~~~~~~~

Obie nasze metody `.get` i `.post` muszą przekonwertować instancję `Response` pochodząca z `http4s` na typ `A`. 
Możemy wydzielić tę logikę do pojedynczej funkcji `.handler`

{lang="text"}
~~~~~~~~
  import JsonClient.Error
  
  final class BlazeJsonClient[F[_]] private (H: Client[Task])(
    implicit
    F: MonadError[F, Error],
    I: MonadIO[F, Throwable]
  ) extends JsonClient[F] {
    ...
    def handler[A: JsDecoder](resp: http4s.Response[Task]): Task[Error \/ A] = {
      if (!resp.status.isSuccess)
        Task.now(JsonClient.ServerError(resp.status.code).left)
      else
        for {
          text <- resp.body.through(fs2.text.utf8Decode).compile.foldMonoid
          res = JsParser(text)
            .flatMap(_.as[A])
            .leftMap(JsonClient.DecodingError(_))
        } yield res
    }
  }
~~~~~~~~


`through(fs2.text.utf8Decode)` pozwala przekonwertować `Stream[Task, Byte]` na `Stream[Task, String]`.
`compile.foldMonoid` interpretuje strumień z użyciem naszego `Task`a i łączy wyniki przy pomocy
`Monoid[String]`, zwracając `Task[String]`.

Następnie parsujemy string do JSONa, a `JsDecoder[A]`dostarcza potrzebny rezultat.

Oto nasza implementacja `.get`

{lang="text"}
~~~~~~~~
  def get[A: JsDecoder](
    uri: String Refined Url,
    headers: IList[(String, String)]
  ): F[A] =
    I.liftIO(
        H.fetch(
          http4s.Request[Task](
            uri = convert(uri),
            headers = convert(headers)
          )
        )(handler[A])
      )
      .emap(identity)
~~~~~~~~

Trzeba przyznać, że jest to w 100% łączenie istniejących kawałków. Konwertujemy nasze typy wejściowe
do `http4s.Request`, wołamy `.fetch` na kliencie przekazując nasz `handler`, w odpowiedzi dostajemy
`Task[Error \/ A]`. Musimy jednak zwrócić `F[A]`, więc używamy `MonadIO.liftIO` do stworzenia
`F[Error \/ ]`, na którym z kolei wywołujemy `emap` umieszczając błąd wewnątrz `F`.

Niestety, próba skompilowania tego kodu zakończy się porażką, a błąd będzie wyglądał mniej więcej tak:

{lang="text"}
~~~~~~~~
  [error] BlazeJsonClient.scala:95:64: could not find implicit value for parameter
  [error]  F: cats.effect.Sync[scalaz.ioeffect.Task]
~~~~~~~~

Coś na temat zaginionego kota?

Dzieje się tak, gdyż `http4s` używa innej biblioteki wspomagającej FP niż Scalaz. Na szczęście `scalaz-ioeffect` dostarcza
warstwę dodającą kompatybilność z tą biblioteką, a projekt [shims](https://github.com/djspiewak/shims) definiuje
niezauważalne (zazwyczaj) niejawne konwersje. Tak więc możemy sprawić, że nasz kod zacznie się kompilować dodając zależności

{lang="text"}
~~~~~~~~
  libraryDependencies ++= Seq(
    "com.codecommit" %% "shims"                % "1.4.0",
    "org.scalaz"     %% "scalaz-ioeffect-cats" % "2.10.1"
  )
~~~~~~~~

i importy

{lang="text"}
~~~~~~~~
  import shims._
  import scalaz.ioeffect.catz._
~~~~~~~~

Implementacja `.post` jest podobna, ale musimy jeszcze dostarczyć instancję

{lang="text"}
~~~~~~~~
  EntityEncoder[Task, String Refined UrlEncoded]
~~~~~~~~

Na szczęście typeklasa `EntityEncoder` pozwala nam łatwo ją wyderywować z istniejącego
enkodera dla typu `String`

{lang="text"}
~~~~~~~~
  implicit val encoder: EntityEncoder[Task, String Refined UrlEncoded] =
    EntityEncoder[Task, String]
      .contramap[String Refined UrlEncoded](_.value)
      .withContentType(
        `Content-Type`(MediaType.`application/x-www-form-urlencoded`)
      )
~~~~~~~~

Jedyną różnicą między `.get` i `.post` jest sposób w jaki konstruujemy `http4s.Request`

{lang="text"}
~~~~~~~~
  http4s.Request[Task](
    method = http4s.Method.POST,
    uri = convert(uri),
    headers = convert(headers)
  )
  .withBody(payload.toUrlEncoded)
~~~~~~~~

Ostatnim fragmentem układanki jest konstruktor, w którym wywołujemy `Http1Client` przekazując obiekt konfiguracyjny

{lang="text"}
~~~~~~~~
  object BlazeJsonClient {
    def apply[F[_]](
      implicit
      F: MonadError[F, JsonClient.Error],
      I: MonadIO[F, Throwable]
    ): Task[JsonClient[F]] =
      Http1Client(BlazeClientConfig.defaultConfig).map(new BlazeJsonClient(_))
  }
~~~~~~~~


### `BlazeUserInteraction`

Musimy uruchomić serwer HTTP, co jest dużo łatwiejsze niż może się wydawać. Po pierwsze, importy

{lang="text"}
~~~~~~~~
  import org.http4s._
  import org.http4s.dsl._
  import org.http4s.server.Server
  import org.http4s.server.blaze._
~~~~~~~~

Następnie musimy utworzyć `dsl` dla naszego typu efektów, z którego zaimportujemy zawartość

{lang="text"}
~~~~~~~~
  private val dsl = new Http4sDsl[Task] {}
  import dsl._
~~~~~~~~

Teraz możemy używać [dsla http4s](https://http4s.org/v0.18/dsl/) do obsługi żądań HTTP. Zamiast opisywać wszystko
co jest możliwe zaimplementujemy po prostu pojedynczą końcówkę (_endpoint_), która przypomina
każdy inny DSL HTTP

{lang="text"}
~~~~~~~~
  private object Code extends QueryParamDecoderMatcher[String]("code")
  private val service: HttpService[Task] = HttpService[Task] {
    case GET -> Root :? Code(code) => ...
  }
~~~~~~~~

Każde dopasowanie musi zwrócić `Task[Response[Task]]`. W naszym przypadku chcemy wziąć `code` i 
ukończyć obietnicę `ptoken`:

{lang="text"}
~~~~~~~~
  final class BlazeUserInteraction private (
    pserver: Promise[Throwable, Server[Task]],
    ptoken: Promise[Throwable, String]
  ) extends UserInteraction[Task] {
    ...
    private val service: HttpService[Task] = HttpService[Task] {
      case GET -> Root :? Code(code) =>
        ptoken.complete(code) >> Ok(
          "That seems to have worked, go back to the console."
        )
    }
    ...
  }
~~~~~~~~

ale zdefiniowanie logiki nie wystarczy, musimy jeszcze uruchomić nasz serwer, co też zrobimy
używając `BlazeBuilder`

{lang="text"}
~~~~~~~~
  private val launch: Task[Server[Task]] =
    BlazeBuilder[Task].bindHttp(0, "localhost").mountService(service, "/").start
~~~~~~~~

Przypisanie do portu `0` sprawia, że system operacyjny użyje tymczasowego portu, który możemy
odczytać z pola `server.address`.

Nasza implementacja `.start` i `.stop` jest więc bardzo prosta

{lang="text"}
~~~~~~~~
  def start: Task[String Refined Url] =
    for {
      server  <- launch
      updated <- pserver.complete(server)
      _ <- if (updated) Task.unit
           else server.shutdown *> fail("server was already running")
    } yield mkUrl(server)
  
  def stop: Task[CodeToken] =
    for {
      server <- pserver.get
      token  <- ptoken.get
      _      <- IO.sleep(1.second) *> server.shutdown
    } yield CodeToken(token, mkUrl(server))
  
  private def mkUrl(s: Server[Task]): String Refined Url = {
    val port = s.address.getPort
    Refined.unsafeApply(s"http://localhost:${port}/")
  }
  private def fail[A](s: String): String =
    Task.fail(new IOException(s) with NoStackTrace)
~~~~~~~~

Uśpienie wątku na `1.second` jest niezbędne, aby uniknąć wyłączenia serwera zanim odpowiedź trafi z powrotem
do przeglądarki. Z wydajnością współbieżności `IO` nie ma żartów!

W końcu, aby utworzyć `BlazeUserInteraction` potrzebuje jedynie dwóch niezainicjalizowanych obietnic

{lang="text"}
~~~~~~~~
  object BlazeUserInteraction {
    def apply(): Task[BlazeUserInteraction] = {
      for {
        p1 <- Promise.make[Void, Server[Task]].widenError[Throwable]
        p2 <- Promise.make[Void, String].widenError[Throwable]
      } yield new BlazeUserInteraction(p1, p2)
    }
  }
~~~~~~~~

Mogliśmy użyć `IO[Void, ?]`, ale skoro reszta naszej aplikacji używa `Task` (czyli `IO[Throwable, ?]`), wywołujemy
`.widenError`, aby nie wprowadzać zbędnego boilerplate'u.


## Podziękowania

I to tyle! Gratulujemy dotarcia do końca podróży.

Jeśli w trakcie jej trwania nauczyłeś się czegoś, to proszę, powiedz o tym swoim znajomym. 
Ta książka nie ma działu marketingu, więc jest to jedyny sposób w jaki potencjalni czytelnicy mogą się o niej dowiedzieć.

Aby zaangażować się w rozwój Scalaz wystarczy dołączyć do [pokoju na gitterze](https://gitter.im/scalaz/scalaz). Stamtąd
możesz zadawać pytania, pomagać innym (teraz jesteś ekspertem!) i pomagać w tworzeniu kolejnych wersji biblioteki.

