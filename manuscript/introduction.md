
# Wprowadzenie

To normalne, że gdy poznajemy nowy paradygmat robimy to sceptycznie.
Aby zarysować nieco drogę jaką przeszliśmy i zmiany jakie zaakceptowaliśmy 
w JVMie, zacznijmy od szybkiej powtórki z ostanich 20 lat tej platformy.

Java 1.2 wprowadziła _Collections API_, pozwalające nam pisac metody które mogły
abstrahować nad[^absover]??? mutowalnymi kolekcjami. Była to zmiana pomocna w pisaniu 
algorytmów ogólnego przeznaczenia, która stała się podwaliną dla naszego kodu.

[^absover]: Jest to tłumaczenie angielskiego _abstract over_, które w języku polskim nie ma dobrego tłumaczenia.
    Zwrot ten oznacza zrobienie czegoś bez brania pod uwagę szczegółów, np. "abstrahować nad mutowalnymi kolekcjami"
    oznacza  używać ich ogólnej abstrakcji (interfejsu) zamiast konkretnych implementacji. (przyp. tłum.)???

Niestety, API to miało jeden problem, zmuszało nas do rzutowania w czasie wykonania (runtime casting)???:

{lang="text"}
~~~~~~~~
  public String first(Collection collection) {
    return (String)(collection.get(0));
  }
~~~~~~~~

W odpowiedzi na ten problem, developerzy definiowali obiekty domenowe, które były 
efektywnie `CollcetionOfThing`, czyli kolekcjami konkretnych typów, z ich własnym silnie typowanym interfejsem,
a Collection API stało się szczegółem implementacyjnym.

W 2005 Java 5 wprowadziła *typy generyczne* (generics)???, pozwalające nam defniować `Collection<Thing>`,
abstrahując nad konkretną kolekjcę **oraz** jej elementami. Typy generyczne zmieniły sposób w jaki pisaliśmy kod w Javie.

Autor javowego kompilatora typów generycznych, Martin Odersky, niedługo później stworzył Scalę, język z silniejszym 
systemem typów, niemutowalnymi kolekcjami oraz wielokrotnym dziedziczeniem. Sprowadziło to fuzję pomiędzy programowaniem
zorientowanym obiektowo (OOP) oraz programowniem funkcyjnym (FP).

Dla większości programistów FP oznacza używanie niemutowalnych struktur danych tak często jak to możliwe,
ale mutowalny stan jest nadal złem koniecznym które musi być wyizolowane i zarządzane, np. przy użyciu aktorów z `Akki` lub
klas używających `synchronized`. Ten styl FP skutkuje prostszymi programami które łatwiej zrównoleglić i rozproszyć, 
stawiając zdecydowany krok naprzód względem Javy. Jest to jednak niewielka częśc zalet i korzyści płynących z programowa funkcyjnego, 
które odkryjemy w tej książce.

Scala wprowadza również typ `Future`, sprawiając że pisanie aplikacji asynchonicznych staje się dużo łatwiejsze.
Jendak gdy tylko `Future` pojawi się w typie zwracanym z funkcji, *wszystko* musi zostać przepisane i dostosowane,
wliczając testy, które teraz narażone są na arbitralne _timeouty_[^timeout]

[^timeout]: Wielokrotnie w tej książce pojawią się spolszczone wyrażenia angielskie w miejscach w których nie ma dla nich dobrego
    polskiego odpowiednika. Uznaliśmy że dużo lepiej użyć wyrażenia które być może brzmi dziwnie, ale pozwala w łatwy sposób zrozumieć
    niesione znaczenie, niż wymyślać nową nazwę, której znaczenia trzba się domyślać.

Mamy więc problem podobny to tego z Javy 1.0: brakuje nam możliwości abstrahowania nad wykonaniem programu, tak samo
jak brakowało nam możliwość abstrahowania nad używanymi kolekcjami.


## Abstrahowanie nad Wykonaniem

Powiedzmy, że chcemy komunikować się z użytkownikiem poprzed interjs wiersza poleceń. Możemy czytać (`read`)
to co uzytkownik napisał i pisać (`write`) wiadomośći które będzie mógł przeczytać.

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

Jak możemy napisać generyczny kod, który zrobić coś tak prostego jak powtórzenie (`echo`) wiadomości
wpisanej przez użytkownia, w sposób synchroniczny bądz asynchroniczny w zależności do naszego środowiska uruchomieniowego?

Moglibyśmy napisać wersję synchroniczą i owinąć ją typem `Future` ale zmusiłoby nas to do zdecydowania jakiej puli wątków
powinnismy użyć. Alternatywnie moglibyśmy zawołać `Await.result` na `Future` i wprowadzić tym samym blokowanie wątku. 
W obu przypadkach sprowadza się to do napisanie dużej ilości _boilerplate'u_ i utrzymywania dwóch różnych API które nie są
w żaden sposób zunifikowane.

Możemy rozwiązać ten problem, podobnie jak w Javie 1.2, używając wspólnego interfejsu bazującego na 
*typach wyższego rodzaju* (higher kinded types, HKT) dostępnych w Scali.

A> **Higher Kinded Types** pozwalają nam na używnie  *konstruktorów typów* (_type constructors_) przy definiowaniu 
A> parametrów typów (_type parameters_), które wygladają tak: `C[_]`. Jest to spósb na wyrażenie:
A> czymkolwiek jest `C`, musi ono przyjmowac jeden _type parameter_. Na przykład:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   trait Foo[C[_]] {
A>     def create(i: Int): C[Int]
A>   }
A> ~~~~~~~~
A> 
A> `List` jest _type constructor'em_ ponieważ przyjmuje on typ (np. `Int`) i tworzy nowy typ
A> (`List[Int]`). Możemu zaimplementować `Foo` używając `List`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooList extends Foo[List] {
A>     def create(i: Int): List[Int] = List(i)
A>   }
A> ~~~~~~~~
A> 
A> Możemy zaimplementować `Foo` używając dowolnego typu z pojedynczym brakującym parametrem typu, np.
A> `Either[String, _]`. Niestety jest to dość uciążliwe, ponieważ musimy zdefiniować alias typu (_type alias_) aby
A> zmusic kompilator do zaakceptwania tego co chcemy zrobić:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   type EitherString[T] = Either[String, T]
A> ~~~~~~~~
A> 
A> Aliasy typów nie denfiują nowych typów ani nie zwiększają bezpieczeństwa ich używania (_type safety_), a jedynie pozwalają na proste podstawienia.
A> Kompilator zamienia `EitherString[T]` na `Either[String, T]` gdziekolwiek to pierwsze jest użyte. 
A> Technika ta może być użyta do oszukiwania kompilatora gdy chcemy użyć typu z dwoma parametrami tam gdzie kompilator oczekuje jednego,
A> tak jak gdy implementowaliśmy `Foo` przy użyciu `EitherString`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooEitherString extends Foo[EitherString] {
A>     def create(i: Int): Either[String, Int] = Right(i)
A>   }
A> ~~~~~~~~
A> 
A> Alternatywnie, możemy uzyć pluginu do kompilatora [kind projector](https://github.com/non/kind-projector/), która pozwala na 
A> uniknąć definiowania aliasów typów, a zamiast nich możemy użyć `?` aby przekazać kompilatorowi odpowiednią informacje:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooEitherString extends Foo[Either[String, ?]] {
A>     def create(i: Int): Either[String, Int] = Right(i)
A>   }
A> ~~~~~~~~
A> 
A> Na koniec został nam jeszcze jeden trik, którego możemy użyć aby zignorować konstruktor typu. 
A> Możemy zdefiniować alias typu tak, aby był równoważny ze swoim parametrem:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   type Id[T] = T
A> ~~~~~~~~
A>
A> Nim przejdziemy dalej, musisz zrozumieć, że `Id[Int]` jest dokładnie tym samym co `Int`. Ponieważ `Id` jest
A> poprawnym konstruktorem typu możemy użyć `Id` aby zaimplementować `Foo`:
A> 
A> {lang="text"}
A> ~~~~~~~~
A>   object FooId extends Foo[Id] {
A>     def create(i: Int): Int = i
A>   }
A> ~~~~~~~~

Chcemy zdefiniowac `Terminal` dla dowolnego konstruktora typu `C[_]`. Poprzez zdefiniowanie `Now` 
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
Potrzebujemy środowiska wykoniania (_execution environment_), które pozwoli nam zawołać metodę zwracającą `C[T]` a póżniej
zrobić coś z `T`, np zawołać kolejną metodę z interfejsu `Terminal`.  Potrzebujemy również możliwość owinięcia wartośći 
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
Możemy napisać sztuczną (_mock_) implementację `Terminal[Now]` i użyć jej w naszych testach beż zagrożenia ze strony _timeoutów_. 

Implementacje `Execution[Now]` oraz `Execution[Future]` moga być reużywane przez generyczne metody takie jak `echo`.

Ale kod implementujący `echo` jest okropny!

Używając mechnizmu `implicit class` w Scali, możemy dodać metody do `C`.
Nazwijmy te metody `flatMap` i `map` z powodów, które staną sie jasne już niedługo. Każda z metod przyjmuje
`implicit Execution[C]`, ale oprócz tego są to dokładnie takie same `flatMap` i `map` jakie znamy z typów `Seq`, `Option` czy `Future`. 

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

Możemy teraz zdradzić dlaczego użyliśmy `flatMap` jako nazwy metody: pozwala nam to używać *for comprehension*, czyli 
lepszej składni dla zagnieżdżonych wywowałań `flatMap` i `map`.

{lang="text"}
~~~~~~~~
  def echo[C[_]](implicit t: Terminal[C], e: Execution[C]): C[String] =
    for {
      in <- t.read
       _ <- t.write(in)
    } yield in
~~~~~~~~

Nasze `Execution` ma taką samą sygnaturę jak trait w Scalaz zwany `Monad`,
z ta różnicą że `chain` to `bind` and `create` to `pure`. Mówimy, że `C` jest *monadyczne* (_monadic_)
gdy dostępna jest implicit instancja `Monad[C]`. Dodatkow Scalaz ma również alias typu `Id`.

Podsumowując: jeśli piszemy metody operujące na typach moandycznych, wówczas możemy 
pisać sekwencyjny kod który abstrahuje nad swoim środowiskiem wykonania. Pokazaliśmy jak zrobić to dla 
synchronicznego i asynchronicznego wykonania programu ale tej samej techniki możemy użyć dla innych kontekstów, np.
statycznego deklarowania błedów (gdzie `C[_]` stanie się `Either[Error, _]`), zarządzania dostępem do ulotnego stanu aplikacji (_volatile state_),
wykonywania operacji wejścia/wyjścia albo audytowalnej sesji.

## Programowanie Czysto Funkcyjne[^purefp]

[^purefp]: _Pure Functional Programming_

Programowanie Funkcyjne to akt tworzenia programów przy użyciu *czystych funkcji* (_pure functions_).
Czyste funkcje mają trzy własciwości:

-  **Totalność**: zwracają wartość dla każdego możliwego argumentu (_total_)
-  **Deterministyczność**: za kazdym razem zwracają tę samą wartość dla tego samego argumentu (_deterministic_)
-  **Niewinność**: brak (bezpośrednich) interakcji ze światem lub wewnętrznym stanem programu (_inculpable_)

Razem te właściwości dają nam bezprecensową zdolność do rozumowania o naszym kodzie. Na przykład, walidacja
wejścia jest łatwiejsza do wyizolowania z totalnością, caching jest możliwy gdy funkcje są deterministyczne a
interagowanie ze światem jest łatwiejsze do kontrolowania i testowania gdy funkcje są niewinne.

Rzeczy które łamią te właściwośći nazywamy *efektami ubocznymi* (_side effects_): bezpośredni dostęp lub zmiana
mutowalnego stanu aplikacji (np. `var` wewnątrz klasy), komunikowanie się z zewnętrznymi zasobami (np. plikami lub siecią) lub
rzucanie i łapanie wyjątków.

Piszemy czyste funkcje przez unikanie wyjątkow i komunikowanie się ze światem jedynie poprzez bezpieczny kontekst wywołania `F[_]`.

W poprzedniej sekcji abstrahowaliśmy nad wykonianiem programu i definiowaliśmy `echo[Id]` oraz `echo[Future]`.
Możemy oczekiwać że wywołanie jakiegokolwiek `echo` nie spowoduje żadnych efektów ubocznych, ponieważ jest to czysta funkcja.
Jednak jeśli używamy `Future` lub `Id` jako konktekstu wykonania, nasza aplikacjia zacznie nasłuchiwać na standardowym stumieniu wejścia (_stdin_):

{lang="text"}
~~~~~~~~
  val futureEcho: Future[String] = echo[Future]
~~~~~~~~

Zaburzyliśmy czystość in tym samym nie piszemy kodu funkcyjnego: `futureEcho` jest rezultate wykonania `echo` raz. 
`Future` łączy defnicje programu z jego *interpretacją* (uruchomieniem). Tym samym, trudnym staje się rozumowanie o 
aplikacjach zbudowanych przy użyciu `Future`.

A> Wyrażenie jest *referencyjnie transparentne* (_referentially transparent_) jeśli może ono być zastąpione
A> jego wartośćia bez zmieniania zachowania programu.
A>
A> Czyste funkcje są referenycjnie transparentne, pozwalając na szeroko zakrojone reużycie kodu, 
A> optymalizacje wydajności, zrozumienie i kontrolę nad programem.
A> 
A> Nieczyste funkcje nie są referencyjnie transparentne. Nie możemy zastapić wywołania `echo[Future]` jego wartością
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

który leniwie wykonuje thunk[^thunk]. `IO` jest jest zwyczajną struktura danych która odnosi się do (potencjalnie)
nieczystego kodu ale nic nie wykonuje. Możemy zaimplementować `Terminal[IO]`

[^thunk]: kawałek kodu. Jedno z wyrażeń bez odpowiednika w języku polskim. (przyp. tłum.)

{lang="text"}
~~~~~~~~
  object TerminalIO extends Terminal[IO] {
    def read: IO[String]           = IO { io.StdIn.readLine }
    def write(t: String): IO[Unit] = IO { println(t) }
  }
~~~~~~~~

i wywołać `echo[IO]` aby dostać spowrotem wartość

{lang="text"}
~~~~~~~~
  val delayed: IO[String] = echo[IO]
~~~~~~~~

Ta `val delayed` może być reużywana, gdyż jest to tylko definicja pracy która musi zostać wykonana. Możemy 
przemapować `String` i tworzyć kolejne programy, podobnie jak mapowalibyśmy `Future`. `IO` pozwala nam zachować szczerość
co do tego, że zależymy od pewnych interakcji ze światem zewnętrznym, ale nie pozbawia nas dostępu do wyniku tej interakcji.

Nieczysty kod wewnątrz `IO` jest ewaluowany kiedy wywołamy `.interpret()` na zwróconej wartości. Wywoałnie to jest oczywiście 
również nieczystą akcją

{lang="text"}
~~~~~~~~
  delayed.interpret()
~~~~~~~~

Aplikacja złożona z programów opartych o `IO` jest interpretowana jedynie raz, wewnątrz metody `main`, która jest
również zwana *końcem świata* (_the end of the world_).

W tej książce rozszerzamy koncepcje wprowadzone w tym rozdziale i pokazujemy jak pisać utrzymywalne, czyste funkcje które
rozwiązują stawiane przed nimi problemy.


