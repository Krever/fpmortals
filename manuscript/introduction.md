
# Wprowadzenie

To normalne, że do nowego paradygmatu podchodzimy sceptycznie.
Aby zarysować nieco drogę, jaką już przeszliśmy i zmiany, jakie udało nam się zaakceptować 
w JVMie, zacznijmy od szybkiej powtórki z ostatnich 20 lat tej platformy.

Java 1.2 wprowadziła _Collections API_, pozwalające nam pisać metody mogące
abstrahować nad[^absover] mutowalnymi kolekcjami. Była to zmiana pomocna w pisaniu 
algorytmów ogólnego przeznaczenia, która stała się podwaliną dla wielu systemów i bibliotek.

[^absover]: Jest to tłumaczenie angielskiego _abstract over_, które w języku polskim nie ma dobrego odpowiednika.
    Zwrot ten oznacza zrobienie czegoś bez brania pod uwagę szczegółów, np. "abstrahować nad mutowalnymi kolekcjami"
    oznacza  używać ich ogólnej abstrakcji (interfejsu) zamiast konkretnych implementacji.

Niestety, API to miało jeden problem, zmuszało nas do rzutowania w czasie wykonania (_runtime casting_):

{lang="text"}
~~~~~~~~
  public String first(Collection collection) {
    return (String)(collection.get(0));
  }
~~~~~~~~

W odpowiedzi na ten problem deweloperzy definiowali obiekty domenowe, które przyjmowały formę `CollectionOfThing`, czyli były kolekcjami konkretnych typów, z ich własnym silnie typowanym interfejsem,
a Collection API stało się jedynie szczegółem implementacyjnym.

W 2005 Java 5 wprowadziła *typy generyczne* (_generics_), pozwalające nam definiować `Collection<Thing>`,
abstrahując nad konkretną kolekcją **oraz** typem jej elementów. Typy generyczne po raz kolejny zmieniły sposób, 
w jaki pisaliśmy kod w Javie.

Autor Javowego kompilatora typów generycznych, Martin Odersky, niedługo później stworzył Scalę, język z silniejszym 
systemem typów, niemutowalnymi kolekcjami oraz wielokrotnym dziedziczeniem. Wprowadziło to fuzję pomiędzy programowaniem
obiektowym (OOP) oraz programowaniem funkcyjnym (FP).

Dla większości programistów FP oznacza używanie niemutowalnych struktur danych tak często jak to możliwe,
ale mutowalny stan jest nadal złem koniecznym, które musi być wyizolowane i zarządzane, np. przy użyciu aktorów z `Akki` lub
klas używających `synchronized`. Ten styl FP skutkuje prostszymi programami, które łatwiej zrównoleglić i rozproszyć, 
stawiając zdecydowany krok naprzód względem Javy. Jest to jednak niewielka część zalet i korzyści płynących z programowania funkcyjnego, 
które odkryjemy w tej książce.

Scala wprowadza również typ `Future`, sprawiając, że pisanie aplikacji asynchronicznych staje się dużo łatwiejsze.
Jednak gdy tylko `Future` pojawi się w typie zwracanym z funkcji, *wszystko* musi zostać przepisane i dostosowane,
wliczając testy, które teraz narażone są na arbitralne _timeouty_[^timeout].

[^timeout]: Wielokrotnie w tej książce pojawią się spolszczone wyrażenia angielskie w miejscach w których nie ma dla nich dobrego
    polskiego odpowiednika. Uznaliśmy że dużo lepiej użyć wyrażenia które być może brzmi dziwnie, ale pozwala w łatwy sposób zrozumieć
    niesione znaczenie, niż wymyślać nową nazwę, której znaczenia trzeba się domyślać.

Mamy więc problem podobny to tego z Javy 1.0: brakuje nam możliwości abstrahowania nad wykonaniem programu, tak samo,
jak brakowało nam możliwości abstrahowania nad używanymi kolekcjami.


## Abstrahowanie nad wykonaniem

Wyobraźmy sobie, że chcemy komunikować się z użytkownikiem poprzez wiersz poleceń. Możemy czytać (`.read`),
to co użytkownik napisał i pisać (`.write`) wiadomości, które będzie mógł przeczytać.

{lang="text"}
~~~~~~~~
  trait TerminalSync {
    def read(): String
    def write(t: String): Unit
  }
  
  trait TerminalAsync {
    def read(): Future[String]
    def write(t: String): Future[Unit]
  }
~~~~~~~~

Jak możemy napisać generyczny kod, który zrobi coś tak prostego, jak powtórzenie (`echo`) wiadomości
wpisanej przez użytkownika w sposób synchroniczny bądź asynchroniczny w zależności od naszego środowiska uruchomieniowego?

Moglibyśmy napisać wersję synchroniczną i owinąć ją typem `Future`, ale zmusiłoby nas to do zdecydowania, jakiej puli wątków
powinniśmy użyć. Alternatywnie moglibyśmy zawołać `Await.result` na `Future` i wprowadzić tym samym blokowanie wątku. 
W obu przypadkach sprowadza się to do napisanie dużej ilości _boilerplate'u_ i utrzymywania dwóch różnych API, które nie są
w żaden sposób zunifikowane.

Możemy też rozwiązać ten problem, podobnie jak w Javie 1.2, używając wspólnego interfejsu bazującego na 
*typach wyższego rodzaju* (_higher kinded types_, HKT) dostępnych w Scali.

A> **Typy wyższego rzędu** pozwalają nam na używanie  *konstruktorów typów* (_type constructors_) przy definiowaniu 
A> parametrów typów (_type parameters_), które wyglądają tak: `C[_]`. Jest to sposób na wyrażenie:
A> czymkolwiek jest `C`, musi ono przyjmować jeden parametr typu (_type parameter_). Na przykład:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   trait Foo[C[_]] {
A>     def create(i: Int): C[Int]
A>   }
A> ~~~~~~~~
A> 
A> `List` jest _konstruktorem typu_, ponieważ przyjmuje on typ (np. `Int`) i tworzy nowy typ
A> (`List[Int]`). Możemy więc zaimplementować `Foo`, używając `List`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooList extends Foo[List] {
A>     def create(i: Int): List[Int] = List(i)
A>   }
A> ~~~~~~~~
A> 
A> Możemy zaimplementować `Foo`, używając dowolnego typu z pojedynczym brakującym parametrem typu, np.
A> `Either[String, _]`. Niestety jest to dość uciążliwe, ponieważ musimy zdefiniować alias typu (_type alias_), aby
A> zmusić kompilator do zaakceptowania tego, co chcemy zrobić:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   type EitherString[T] = Either[String, T]
A> ~~~~~~~~
A> 
A> Aliasy typów nie definiują nowych typów ani nie zwiększają bezpieczeństwa ich używania (_type safety_), a jedynie pozwalają na proste podstawienia.
A> Kompilator zamienia `EitherString[T]` na `Either[String, T]` gdziekolwiek to pierwsze jest użyte. 
A> Technika ta może być użyta do oszukiwania kompilatora gdy chcemy użyć typu z dwoma parametrami w miejscu, gdzie kompilator oczekuje tylko jednego,
A> tak jak, gdy chcieliśmy implementować `Foo` przy użyciu `EitherString`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooEitherString extends Foo[EitherString] {
A>     def create(i: Int): Either[String, Int] = Right(i)
A>   }
A> ~~~~~~~~
A> 
A> Alternatywnie, możemy użyć pluginu kompilatora [kind projector](https://github.com/non/kind-projector/), która pozwala na 
A> uniknąć definiowania aliasów typów, a zamiast nich możemy użyć `?` aby przekazać kompilatorowi odpowiednią informację:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooEitherString extends Foo[Either[String, ?]] {
A>     def create(i: Int): Either[String, Int] = Right(i)
A>   }
A> ~~~~~~~~
A> 
A> Na koniec został nam jeszcze jeden trik, którego możemy użyć, aby zignorować konstruktor typu, definiując alias 
A> tak, aby był równoważny ze swoim parametrem:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   type Id[T] = T
A> ~~~~~~~~
A>
A> Nim przejdziemy dalej, ważne jest, by zrozumieć, że `Id[Int]` jest dokładnie tym samym co `Int`, ale ponieważ `Id` jest
A> poprawnym konstruktorem typu, możemy go użyć, aby zaimplementować `Foo`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooId extends Foo[Id] {
A>     def create(i: Int): Int = i
A>   }
A> ~~~~~~~~

Chcielibyśmy zdefiniować `Terminal` dla dowolnego konstruktora typu `C[_]`. Poprzez zdefiniowanie `Now` 
jako równoznacznego ze swoim parametrem (analogicznie do `Id`), możemy zaimplementować ten wspólny interfejs dla terminali
synchronicznych i asynchronicznych:

{lang="text"}
~~~~~~~~
  trait Terminal[C[_]] {
    def read: C[String]
    def write(t: String): C[Unit]
  }
  
  type Now[X] = X
  
  object TerminalSync extends Terminal[Now] {
    def read: String = ???
    def write(t: String): Unit = ???
  }
  
  object TerminalAsync extends Terminal[Future] {
    def read: Future[String] = ???
    def write(t: String): Future[Unit] = ???
  }
~~~~~~~~

Niestety nie wiemy nic o `C` i nic nie jesteśmy w stanie zrobić z `C[String]`.
Potrzebujemy środowiska wykonania (_execution environment_), które pozwoli nam zawołać metodę zwracającą `C[T]` a później
zrobić coś z `T`, np. zawołać kolejną metodę z interfejsu `Terminal`.  Potrzebujemy również możliwości owinięcia prostej wartości 
typem `C[_]`. Poniższa sygnatura dobrze spełnia nasze wymagania:

{lang="text"}
~~~~~~~~
  trait Execution[C[_]] {
    def chain[A, B](c: C[A])(f: A => C[B]): C[B]
    def create[B](b: B): C[B]
  }
~~~~~~~~

pozwalając nam na napisanie:

{lang="text"}
~~~~~~~~
  def echo[C[_]](t: Terminal[C], e: Execution[C]): C[String] =
    e.chain(t.read) { in: String =>
      e.chain(t.write(in)) { _: Unit =>
        e.create(in)
      }
    }
~~~~~~~~

Możemy teraz współdzielić implementację `echo` pomiędzy synchroniczną i asynchroniczną wersją naszego programu.
Możemy napisać sztuczną (_mock_) implementację `Terminal[Now]` i użyć jej w naszych testach bez zagrożenia ze strony _timeoutów_. 

Implementacje `Execution[Now]` oraz `Execution[Future]` mogą być reużywane przez generyczne metody takie jak `echo`.

Ale kod implementujący `echo` jest okropny!

Używając mechanizmu `implicit class` w Scali, możemy dodać metody do `C`.
Nazwijmy te metody `flatMap` i `map` z powodów, które staną się jasne już niedługo. Każda z metod przyjmuje
`implicit Execution[C]`, ale oprócz tego są to dokładnie takie same `flatMap` i `map`, jakie znamy z typów `Seq`, `Option` czy `Future`. 

{lang="text"}
~~~~~~~~
  object Execution {
    implicit class Ops[A, C[_]](c: C[A]) {
      def flatMap[B](f: A => C[B])(implicit e: Execution[C]): C[B] =
            e.chain(c)(f)
      def map[B](f: A => B)(implicit e: Execution[C]): C[B] =
            e.chain(c)(f andThen e.create)
    }
  }
  
  def echo[C[_]](implicit t: Terminal[C], e: Execution[C]): C[String] =
    t.read.flatMap { in: String =>
      t.write(in).map { _: Unit =>
        in
      }
    }
~~~~~~~~

Możemy teraz zdradzić, dlaczego użyliśmy `flatMap` jako nazwy metody: pozwala nam to używać *for comprehension*, czyli 
lepszej składni dla zagnieżdżonych wywołań `flatMap` i `map`.

{lang="text"}
~~~~~~~~
  def echo[C[_]](implicit t: Terminal[C], e: Execution[C]): C[String] =
    for {
      in <- t.read
       _ <- t.write(in)
    } yield in
~~~~~~~~

Nasze `Execution` ma taką samą sygnaturę jak trait w Scalaz zwany `Monad`,
z ta różnicą, że `chain` to `bind` and `create` to `pure`. Mówimy, że `C` jest *monadyczne* (_monadic_),
gdy dostępna jest niejawna (_implicit_) instancja `Monad[C]`. Dodatkowo Scalaz definiuje również alias typu `Id`.

Podsumowując: jeśli piszemy metody operujące na typach monadycznych, wówczas możemy 
pisać sekwencyjny kod, który abstrahuje nad swoim środowiskiem wykonania. Pokazaliśmy jak zrobić to dla 
synchronicznego i asynchronicznego wykonania programu, ale tej samej techniki możemy użyć dla innych kontekstów, np.
statycznie deklarowanych błędów (gdzie `C[_]` stanie się `Either[Error, _]`), zarządzania dostępem do ulotnego stanu aplikacji (_volatile state_),
wykonywania operacji wejścia/wyjścia albo audytowalnej sesji.

## Programowanie czysto funkcyjne[^purefp]

[^purefp]: _Pure Functional Programming_

Programowanie Funkcyjne to akt tworzenia programów przy użyciu *czystych funkcji* (_pure functions_).
Czyste funkcje mają trzy właściwości:

-  **Totalność**: zwracają wartość dla każdego możliwego argumentu (_total_)
-  **Deterministyczność**: za każdym razem zwracają tę samą wartość dla tego samego argumentu (_deterministic_)
-  **Niewinność**: brak (bezpośrednich) interakcji ze światem lub wewnętrznym stanem programu (_inculpable_)

Razem te właściwości dają nam bezprecedensową zdolność do rozumowania o naszym kodzie. Na przykład, walidacja
wejścia jest łatwiejsza do wyizolowania z totalnością, caching jest możliwy, gdy funkcje są deterministyczne, a
interagowanie ze światem jest łatwiejsze do kontrolowania i testowania, gdy funkcje są niewinne.

Rzeczy, które łamią te właściwości, nazywamy *efektami ubocznymi* (_side effects_): bezpośredni dostęp lub zmiana
mutowalnego stanu aplikacji (np. `var` wewnątrz klasy), komunikowanie się z zewnętrznymi zasobami (np. plikami lub siecią) lub
rzucanie i łapanie wyjątków.

Piszemy czyste funkcje przez unikanie wyjątków i komunikowanie się ze światem jedynie poprzez bezpieczny kontekst wywołania `F[_]`.

W poprzedniej sekcji abstrahowaliśmy nad wykonaniem programu i definiowaliśmy `echo[Id]` oraz `echo[Future]`.
Możemy oczekiwać, że wywołanie jakiegokolwiek `echo` nie spowoduje żadnych efektów ubocznych, ponieważ jest to czysta funkcja.
Jednak jeśli używamy `Future` lub `Id` jako kontekstu wykonania, nasza aplikacja zacznie nasłuchiwać na standardowym strumieniu wejścia (_stdin_):

{lang="text"}
~~~~~~~~
  val futureEcho: Future[String] = echo[Future]
~~~~~~~~

Zaburzyliśmy czystość i tym samym nie piszemy już kodu funkcyjnego: `futureEcho` jest rezultatem wykonania `echo` jeden raz. 
`Future` łączy definicję programu z jego *interpretacją* (uruchomieniem). Tym samym, trudnym staje się rozumowanie o 
aplikacjach zbudowanych przy użyciu `Future`.

A> Wyrażenie jest *referencyjnie transparentne* (_referentially transparent_), jeśli może ono być zastąpione
A> jego wartością bez zmieniania zachowania programu.
A>
A> Czyste funkcje są referencyjnie transparentne, pozwalając na daleko idące reużycie kodu, 
A> optymalizacje wydajności, zrozumienie i kontrolę nad programem.
A> 
A> Nieczyste funkcje nie są referencyjnie transparentne. Nie możemy zastąpić wywołania `echo[Future]` jego wartością,
A> ponieważ ten nieznośny użytkownik za drugim razem może wpisać coś zupełnie innego.

Możemy zdefiniować prosty i bezpieczny kontekst wykonania `F[_]`

{lang="text"}
~~~~~~~~
  final class IO[A](val interpret: () => A) {
    def map[B](f: A => B): IO[B] = IO(f(interpret()))
    def flatMap[B](f: A => IO[B]): IO[B] = IO(f(interpret()).interpret())
  }
  object IO {
    def apply[A](a: =>A): IO[A] = new IO(() => a)
  }
~~~~~~~~

który leniwie wykonuje thunk[^thunk]. `IO` jest zwyczajną strukturą danych, która zawiera kawałek (potencjalnie)
nieczystego kodu, ale go nie wykonuje. Możemy zaimplementować `Terminal[IO]`

[^thunk]: kawałek kodu. Jedno z wielu wyrażeń bez odpowiednika w języku polskim.

{lang="text"}
~~~~~~~~
  object TerminalIO extends Terminal[IO] {
    def read: IO[String]           = IO { io.StdIn.readLine }
    def write(t: String): IO[Unit] = IO { println(t) }
  }
~~~~~~~~

i wywołać `echo[IO]` aby dostać z powrotem wartość

{lang="text"}
~~~~~~~~
  val delayed: IO[String] = echo[IO]
~~~~~~~~

Taka wartość `delayed` może być reużywana, gdyż jest to tylko definicja pracy, która musi zostać wykonana. Możemy 
przemapować `String` i tworzyć kolejne programy, podobnie jak mapowalibyśmy `Future`. `IO` pozwala nam zachować szczerość
co do tego, że zależymy od pewnych interakcji ze światem zewnętrznym, ale nie pozbawia nas dostępu do wyniku tej interakcji.

Nieczysty kod wewnątrz `IO` jest ewaluowany, kiedy wywołamy `.interpret()` na zwróconej wartości. Wywołanie to jest oczywiście 
również nieczystą akcją

{lang="text"}
~~~~~~~~
  delayed.interpret()
~~~~~~~~

Aplikacja złożona z programów opartych o `IO` jest interpretowana jedynie raz, wewnątrz metody `main`, która jest
również zwana *końcem świata* (_the end of the world_).

W następnych rozdziałach rozszerzymy wprowadzone tutaj koncepcje i pokażemy jak pisać utrzymywalne czyste funkcje, które
rozwiązują stawiane przed nimi problemy.
