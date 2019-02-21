{backmatter}


# Skrót Typeklas

| Typeklasa          | Metoda          | Z               | Mając                  | Do             |
|--------------------|-----------------|-----------------|------------------------|----------------|
| `InvariantFunctor` | `xmap`          | `F[A]`          | `A => B, B => A`       | `F[B]`         |
| `Contravariant`    | `contramap`     | `F[A]`          | `B => A`               | `F[B]`         |
| `Functor`          | `map`           | `F[A]`          | `A => B`               | `F[B]`         |
| `Apply`            | `ap` / `<*>`    | `F[A]`          | `F[A => B]`            | `F[B]`         |
|                    | `apply2`        | `F[A], F[B]`    | `(A, B) => C`          | `F[C]`         |
| `Alt`              | `altly2`        | `F[A], F[B]`    | `(A \/ B) => C`        | `F[C]`         |
| `Divide`           | `divide2`       | `F[A], F[B]`    | `C => (A, B)`          | `F[C]`         |
| `Decidable`        | `choose2`       | `F[A], F[B]`    | `C => (A \/ B)`        | `F[C]`         |
| `Bind`             | `bind` / `>>=`  | `F[A]`          | `A => F[B]`            | `F[B]`         |
|                    | `join`          | `F[F[A]]`       |                        | `F[A]`         |
| `Cobind`           | `cobind`        | `F[A]`          | `F[A] => B`            | `F[B]`         |
|                    | `cojoin`        | `F[A]`          |                        | `F[F[A]]`      |
| `Applicative`      | `point`         | `A`             |                        | `F[A]`         |
| `Divisible`        | `conquer`       |                 |                        | `F[A]`         |
| `Comonad`          | `copoint`       | `F[A]`          |                        | `A`            |
| `Semigroup`        | `append`        | `A, A`          |                        | `A`            |
| `Plus`             | `plus` / `<+>`  | `F[A], F[A]`    |                        | `F[A]`         |
| `MonadPlus`        | `withFilter`    | `F[A]`          | `A => Boolean`         | `F[A]`         |
| `Align`            | `align`         | `F[A], F[B]`    |                        | `F[A \&/ B]`   |
|                    | `merge`         | `F[A], F[A]`    |                        | `F[A]`         |
| `Zip`              | `zip`           | `F[A], F[B]`    |                        | `F[(A, B)]`    |
| `Unzip`            | `unzip`         | `F[(A, B)]`     |                        | `(F[A], F[B])` |
| `Cozip`            | `cozip`         | `F[A \/ B]`     |                        | `F[A] \/ F[B]` |
| `Foldable`         | `foldMap`       | `F[A]`          | `A => B`               | `B`            |
|                    | `foldMapM`      | `F[A]`          | `A => G[B]`            | `G[B]`         |
| `Traverse`         | `traverse`      | `F[A]`          | `A => G[B]`            | `G[F[B]]`      |
|                    | `sequence`      | `F[G[A]]`       |                        | `G[F[A]]`      |
| `Equal`            | `equal` / `===` | `A, A`          |                        | `Boolean`      |
| `Show`             | `shows`         | `A`             |                        | `String`       |
| `Bifunctor`        | `bimap`         | `F[A, B]`       | `A => C, B => D`       | `F[C, D]`      |
|                    | `leftMap`       | `F[A, B]`       | `A => C`               | `F[C, B]`      |
|                    | `rightMap`      | `F[A, B]`       | `B => C`               | `F[A, C]`      |
| `Bifoldable`       | `bifoldMap`     | `F[A, B]`       | `A => C, B => C`       | `C`            |
| (z `MonadPlus`)    | `separate`      | `F[G[A, B]]`    |                        | `(F[A], F[B])` |
| `Bitraverse`       | `bitraverse`    | `F[A, B]`       | `A => G[C], B => G[D]` | `G[F[C, D]]`   |
|                    | `bisequence`    | `F[G[A], G[B]]` |                        | `G[F[A, B]]`   |


# Haskell

Dokumentacja Scalaz często odwołuje się do bibliotek lub artykułów używających Haskella jako języka programowania.
W tym krótkim rozdziale poznamy jego podstawy, tak, aby móc zrozumieć wspomniane materiały oraz móc uczestniczyć
w Haskellowych prezentacjach na konferencjach o programowaniu funkcyjnym.


## Dane

Haskell ma bardzo schludną składnię dla ADT. Oto tradycyjna lista:

{lang="text"}
~~~~~~~~
  data List a = Nil | Cons a (List a)
~~~~~~~~

`List` jest *konstruktorem typu*, `a` to *parametr typu*, a `|` rozdziela *konstruktory danych*, które w tym wypadku to:
`Nil` czyli pusta lista oraz `Cons` czyli komórka listy. `Cons` przyjmuje dwa parametry, które są rozdzielone białym znakiem. Nie ma
tu przecinków ani nawiasów. 

W Haskellu nie ma też podtypowania, więc nie ma czegoś takiego jak typ `Nil`
lub `Cons`, oba tworzą typ `List`.

Przybliżone tłumaczenie na Scalę:

{lang="text"}
~~~~~~~~
  sealed abstract class List[A]
  object Nil {
    def apply[A]: List[A] = ...
    def unapply[A](as: List[A]): Option[Unit] = ...
  }
  object Cons {
    def apply[A](head: A, tail: List[A]): List[A] = ...
    def unapply[A](as: List[A]): Option[(A, List[A])] = ...
  }
~~~~~~~~

A więc, konstruktor typu to odpowiednik `sealed abstract class` a każdy z konstruktorów danych
to para `.apply`/`.unapply`. Warto zauważyć, że przy takim kodowaniu Scala nie jest w stanie sprawdzić
czy pattern matching jest wyczerpujący, i dlatego też nie jest ono używane w Scalaz.

Możemy też użyć infiksu, tworząc ładniejszą definicję z `:.` zamiast `Cons`

{lang="text"}
~~~~~~~~
  data List t = Nil | t :. List t
  infixr 5 :.
~~~~~~~~

Specyfikujemy tutaj *fixity*, które może przyjąć jedną z wartości `infix`, `infixl` lub `infixr`, które oznaczają odpowiednio
brak łączności, łączność lewostronną i prawostronną. Liczby od 0 do 9 określają priorytet operacji.
Możemy teraz stworzyć listę liczb całkowitych za pomocą

{lang="text"}
~~~~~~~~
  1 :. 2 :. Nil
~~~~~~~~

Haskell posiada już definicję listy i jest ona na tyle ważna dla programowania funkcyjnego, że zasłużyła
na osobną składnię zdefiniowaną na poziomie języka: `[a]`.

{lang="text"}
~~~~~~~~
  data [] a = [] | a : [a]
  infixr 5 :
~~~~~~~~

oraz wygodny wielowartościowy konstruktor `[1, 2, 3]` zamiast `1 : 2 : 3 : []`.

Koniec końców nasze ADT musi przechowywać wartości prymitywne. Najpopularniejsze z nich to:

-   `Char` - znak unikodu
-   `Text` - blok tekstu opartego o unikod
-   `Int` - zależna od sprzętu liczba całkowita ze znakiem o stałej precyzji
-   `Word` - liczba całkowita bez znaku z wariantami o stałym rozmiarze `Word8` / `Word16` / `Word32` / `Word64`
-   `Float` / `Double` - liczby zmiennoprzecinkowe o pojedynczej i podwójnej precyzji, zgodne z IEEE
-   `Integer` / `Natural` - liczba całkowita o arbitralnej precyzji. Ze znakiem oraz dodatnia.
-   `(,)` - tuple o rozmiarach od 0 do 62
-   `IO` - inspiracja dla `IO` w Scalaz, implementowana na poziomie środowiska uruchomieniowego

z honorowym miejscem dla

{lang="text"}
~~~~~~~~
  data Bool       = True | False
  data Maybe a    = Nothing | Just a
  data Either a b = Left a  | Right b
  data Ordering   = LT | EQ | GT
~~~~~~~~

Haskell, podobnie jak Scala, pozwala na definiowanie aliasów typów. Alias i jego rozwiniętą
forma mogą być używane zamiennie. Z powodów historycznych `String` zdefiniowany jest alias na listę
`Char`ów

{lang="text"}
~~~~~~~~
  type String = [Char]
~~~~~~~~

co jest reprezentacją bardzo niewydajną i dlatego właśnie powinniśmy używać typu `Text`.

Możemy też definiować nazwy pól w ADT używając *składni rekordów*, co oznacza umieszczenie konstruktorów danych
w klamrach i dodanie do pól *anotacji typów* za podwójnym dwukropkiem aby określić ich typ.

{lang="text"}
~~~~~~~~
  -- raw ADT
  data Resource = Human Int String
  data Company  = Company String [Resource]
  
  -- with record syntax
  data Resource = Human
                  { serial    :: Int
                  , humanName :: String
                  }
  data Company  = Company
                  { companyName :: String
                  , employees   :: [Resource]
                  }
~~~~~~~~

Zauważ, że konstruktor danych `Human` i typ `Resource` nie muszą mieć tej samej nazwy. 
Rekordy generują dla nas metody pozwalające na dostęp do pól i łatwe kopiowanie danych.

{lang="text"}
~~~~~~~~
  -- construct
  adam = Human 0 Adam
  -- field access
  serial adam
  -- copy
  eve = adam { humanName = "Eve" }
~~~~~~~~

Bardziej wydajną alternatywą dla pojedynczych definicji danych jest użycie słowa kluczowego
`newtype`, które nie niesie ze sobą żadnego narzutu wydajnościowego:

{lang="text"}
~~~~~~~~
  newtype Alpha = Alpha { underlying :: Double }
~~~~~~~~

Jest to odpowiednik `extends AnyVal`, tyle że bez żadnych haczyków.

A> Ograniczeniem Haskellowych rekordów jest to, że nazwy pól nie mogą się powtarzać.
A> Możemy to jednak obejść stosując rozszerzenie języka, które pozwoli nam użyć `name`
A> zarówno w `Human` jak i `Company`:
A>
A> {lang="text"}
A> ~~~~~~~~
A>   {-# LANGUAGE DuplicateRecordFields #-}
A>   
A>   data Resource = Human
A>                   { serial :: Int
A>                   , name   :: String
A>                   }
A>   data Company  = Company
A>                   { name      :: String
A>                   , employees :: [Resource]
A>                   }
A> ~~~~~~~~
A> 
A> Istnieje wiele takich rozszerzeń i nie jest niczym nadzwyczajnym aby mały projekt korzystał
A> z 20 albo i więcej z nich. Haskell jest bardzo konserwatywnym językiem i nowe funkcjonalności
A> są domyślnie wyłączone przez długi czas zanim zostaną zaakceptowane do standardu języka.


## Funkcje

Mimo że nie jest to konieczne, to dobrą praktyką jest opatrywanie funkcji sygnaturami typu,
co wyrażane jest jako nazwa funkcji za którą podąża jej typ. Dla przykładu, oto `foldl` wyspecjalizowany
dla listy

{lang="text"}
~~~~~~~~
  foldl :: (b -> a -> b) -> b -> [a] -> b
~~~~~~~~

Wszystkie funkcje w Haskellu są domyślnie *rozwinięte* (_curried_), parametry rozdzielone są
`->, a ostatni typ to typ zwracany przez funkcję. Powyższy przykład to odpowiednik Scalowej sygnatury

{lang="text"}
~~~~~~~~
  def foldLeft[A, B](f: (B, A) => B)(b: B)(as: List[A]): B
~~~~~~~~

Tyle, że:

- bez słów kluczowych
- bez deklaracji typów które wyprowadzamy
- bez nazywania parametrów

Wszystko to sprawia, że kod jest bardziej zwięzły.

Funkcje infiksowe definiowane są w nawiasach i wymagają określenia fixity:

{lang="text"}
~~~~~~~~
  (++) :: [a] -> [a] -> [a]
  infixr 5 ++
~~~~~~~~

Zwykłe funkcje mogą być wołane w pozycji infiksowej poprzez otoczenie nazwy apostrofami,
a infiksowe możemy wywoływać tak jak normalne jeśli pozostawimy nawiasy wokół nazwy. Poniższe wywołania są 
równoznaczne:

{lang="text"}
~~~~~~~~
  a `foo` b
  foo a b
~~~~~~~~

Funkcja infiksowa może być rozwinięta z lewej bądź prawej strony, często dając różną
semantykę:

{lang="text"}
~~~~~~~~
  invert = (1.0 /)
  half   = (/ 2.0)
~~~~~~~~

Funkcje zazwyczaj pisane są tak, aby najbardziej ogólny parametr był na początku, co pozwala zmaksymalizować
reużywalność domyślnej rozwiniętej formy.

Definicje funkcji mogą używać dopasowywania wzorców z jedną linią na wariant. W tym miejscu możemy
nazwać nasze parametry używając konstruktorów danych do ich wyekstrahowania, podobnie jak w Scalowej 
klauzuli `case`:

{lang="text"}
~~~~~~~~
  fmap :: (a -> b) -> Maybe a -> Maybe b
  fmap f (Just a) = Just (f a)
  fmap _ Nothing  = Nothing
~~~~~~~~

Podkreślenie służy do ignorowania nieistotnych parametrów. Nazwy funkcji mogą
występować w pozycji infiksowej również w definicjach:

{lang="text"}
~~~~~~~~
  (<+>) :: Maybe a -> Maybe a -> Maybe a
  Just a <+> _      = Just a
  Empty  <+> Just a = Just a
  Empty  <+> Empty  = Empty
~~~~~~~~

Funkcje anonimowe (lambdy) definiujemy z pomocą odwrotnego ukośnika, co przypomina grecką literę λ. Poniższe definicje są
równoznaczne:

{lang="text"}
~~~~~~~~
  (*)
  (\a1 -> \a2 -> a1 * a2)
  (\a1 a2     -> a1 * a2)
~~~~~~~~

Funkcje używające dopasowań w Haskellu to tak naprawdę jedynie syntax sugar ponad zagnieżdżonymi
lambdami. Rozważmy prostą funkcję, która tworzy tuple z 3 argumentów:

{lang="text"}
~~~~~~~~
  tuple :: a -> b -> c -> (a, b, c)
~~~~~~~~

Jej implementacja

{lang="text"}
~~~~~~~~
  tuple a b c = (a, b, c)
~~~~~~~~

jest rozwijana przez kompilator do 

{lang="text"}
~~~~~~~~
  tuple = \a -> \b -> \c -> (a, b, c)
~~~~~~~~

W ciele funkcji możemy tworzyć lokalne przypisania za pomocą klauzul `let` i `where`.
Poniższe definicje `map` dla listy są równoznaczne (apostrof jest poprawnym identyfikatorem):

{lang="text"}
~~~~~~~~
  map :: (a -> b) -> [a] -> [b]
  
  -- explicit
  map f as = foldr map' [] as
             where map' a bs = f a : bs
  
  -- terser, making use of currying
  map f    = foldr map' []
             where map' a = (f a :)
  
  -- let binding
  map f    = let map' a = (f a :)
             in foldr map' []
  
  -- actual implementation
  map _ []       = []
  map f (x : xs) = f x : map f xs
~~~~~~~~

`if` / `then` / `else` to słowa kluczowe do definiowania wyrażeń warunkowych:

{lang="text"}
~~~~~~~~
  filter :: (a -> Bool) -> [a] -> [a]
  filter _ [] = []
  filter f (head : tail) = if f head
                           then head : filter f tail
                           else filter f tail
~~~~~~~~

Alternatywnie możemy użyć *ograniczeń wariantów* (_case guards_)

{lang="text"}
~~~~~~~~
  filter f (head : tail) | f head    = head : filter f tail
                         | otherwise = filter f tail
~~~~~~~~

Dopasowania dla dowolnego wyrażenia definiujemy używają `case ... of`

{lang="text"}
~~~~~~~~
  unfoldr :: (a -> Maybe (b, a)) -> a -> [b]
  unfoldr f b = case f b of
                  Just (b', a') -> b' : unfoldr f a'
                  Nothing       -> []
~~~~~~~~

Ograniczenia mogą być używane wewnątrz dopasowań. Możemy, na przykład, chcieć
potraktować zera w specjalny sposób:

{lang="text"}
~~~~~~~~
  unfoldrInt :: (a -> Maybe (Int, a)) -> a -> [Int]
  unfoldrInt f b = case f b of
                     Just (i, a') | i == 0    -> unfoldrInt f a'
                                  | otherwise -> i : unfoldrInt f a'
                     Nothing                  -> []
~~~~~~~~

Na koniec dwie funkcje warte wspomnienia: `($)` i `(.)`

{lang="text"}
~~~~~~~~
  -- application operator
  ($) :: (a -> b) -> a -> b
  infixr 0
  
  -- function composition
  (.) :: (b -> c) -> (a -> b) -> a -> c
  infixr 9
~~~~~~~~

Obie są stylistycznymi alternatywami dla zagnieżdżonych nawiasów.

Poniższe wywołania są równoznaczne

{lang="text"}
~~~~~~~~
  Just (f a)
  Just $ f a
~~~~~~~~

tak jak i

{lang="text"}
~~~~~~~~
  putStrLn (show (1 + 1))
  putStrLn $ show $ 1 + 1
~~~~~~~~

Składanie funkcji za pomocą `.` jest przez wielu preferowane ponad wielokrotne użycie `$`

{lang="text"}
~~~~~~~~
  (putStrLn . show) $ 1 + 1
~~~~~~~~


## Typeklasy

Aby zdefiniować typeklasę używamy słowa kluczowego `class`, za którym podąża jej nazwa oraz parametry typu, a wymagane
metody trafiają do klauzuli `where`. Jeśli między typeklasami istnieje zależność, jak np. w przypadku `Applicative` i
`Functor`, to może być ona wyrażona za pomocą notacji `=>`

{lang="text"}
~~~~~~~~
  class Functor f where
    (<$>) :: (a -> b) -> f a -> f b
    infixl 4 <$>
  
  class Functor f => Applicative f where
    pure  :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b
    infixl 4 <*>
  
  class Applicative f => Monad f where
    (=<<) :: (a -> f b) -> f a -> f b
    infixr 1 =<<
~~~~~~~~

Implementację danej typeklasy możemy dostarczyć za pomocą słowa kluczowego `instance`. Jeśli chcielibyśmy
powtórzyć sygnatury metod, co dodaje nieco czytelności, musimy włączyć rozszerzenie języka `InstanceSigs`.

{lang="text"}
~~~~~~~~
  {-# LANGUAGE InstanceSigs #-}
  
  data List a = Nil | a :. List a
  
  -- defined elsewhere
  (++) :: List a -> List a -> List a
  map :: (a -> b) -> List a -> List b
  flatMap :: (a -> List b) -> List a -> List b
  foldLeft :: (b -> a -> b) -> b -> List a -> b
  
  instance Functor List where
    (<$>) :: (a -> b) -> List a -> List b
    f <$> as = map f as
  
  instance Applicative List where
    pure a = a :. Nil
  
    Nil <*> _  = Nil
    fs  <*> as = foldLeft (++) Nil $ (<$> as) <$> fs
  
  instance Monad List where
    f =<< list = flatMap f list
~~~~~~~~

Gdy chcemy skorzystać z typeklasy w funkcji, deklarujemy to za pomocą `=>`. Możemy na przykład
zdefiniować odpowiednik `Apply.apply2` ze Scalaz

{lang="text"}
~~~~~~~~
  apply2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
  apply2 f fa fb = f <$> fa <*> fb
~~~~~~~~

Skoro wprowadziliśmy już typeklasę `Monad` to jest to dobry moment na omówienie notacji `do`,
która była inspiracją dla Scalowej konstrukcji `for`:

{lang="text"}
~~~~~~~~
  do
    a <- f
    b <- g
    c <- h
    pure (a, b, c)
~~~~~~~~

Powyższy kod rozwijany jest do

{lang="text"}
~~~~~~~~
  f >>= \a ->
    g >>= \b ->
      h >>= \c ->
        pure (a, b, c)
~~~~~~~~

gdzie `>>=` to `=<<` z parametrami zamienionymi miejscami

{lang="text"}
~~~~~~~~
  (>>=) :: Monad f => f a -> (a -> f b) -> f b
  (>>=) = flip (=<<)
  infixl 1 >>=
  
  -- from the stdlib
  flip :: (a -> b -> c) -> b -> a -> c
~~~~~~~~

a `return` to synonim do `pure`.

W przeciwieństwie do Scali, nie musimy przypisywać pustych wartości ani używać `yield` gdy zwracamy `()`.

{lang="text"}
~~~~~~~~
  for {
    _ <- putStr("hello")
    _ <- putStr(" world")
  } yield ()
~~~~~~~~

jest odpowiednikiem

{lang="text"}
~~~~~~~~
  do putStr "hello"
     putStr " world"
~~~~~~~~

Niemonadyczne wartości mogą być przypisywane z użyciem słowa kluczowego `let`:

{lang="text"}
~~~~~~~~
  nameReturn :: IO String
  nameReturn = do putStr "What is your first name? "
                  first <- getLine
                  putStr "And your last name? "
                  last  <- getLine
                  let full = first ++ " " ++ last
                  putStrLn ("Pleased to meet you, " ++ full ++ "!")
                  pure full
~~~~~~~~

Na koniec, Haskell pozwala na derywację typeklas za pomocą słowa kluczowego `deriving`, a mechanizm ten
był inspiracją dla poznanego przez nas `@scalaz.deriving`. Definiowanie zasad derywacji to dość zaawansowany
temat, ale sama derywacja dla ADT jest bardzo prosta:

{lang="text"}
~~~~~~~~
  data List a = Nil | a :. List a
                deriving (Eq, Ord)
~~~~~~~~


## Algebras

In Scala, typeclasses and algebras are both defined as a `trait` interface.
Typeclasses are injected by the `implicit` feature and algebras are passed as
explicit parameters. There is no language-level support in Haskell for algebras:
they are just data!

Consider the simple `Console` algebra from the introduction. We can rewrite it
into Haskell as a *record of functions*:

{lang="text"}
~~~~~~~~
  data Console m = Console
                    { println :: Text -> m ()
                    , readln  :: m Text
                    }
~~~~~~~~

with business logic using a `Monad` constraint

{lang="text"}
~~~~~~~~
  echo :: (Monad m) => Console m -> m ()
  echo c = do line <- readln c
              println c line
~~~~~~~~

A production implementation of `Console` would likely have type `Console IO`.
The Scalaz `liftIO` function is inspired by a Haskell function of the same name
and can lift `Console IO` into any Advanced Monad stack.

Two additional language extensions make the business logic even cleaner. For
example, `RecordWildCards` allows us to import all the fields of a data type by
using `{..}`:

{lang="text"}
~~~~~~~~
  echo :: (Monad m) => Console m -> m ()
  echo Console{..} = do line <- readln
                        println line
~~~~~~~~

`NamedFieldPuns` requires each imported field to be listed explicitly, which is
more boilerplate but makes the code easier to read:

{lang="text"}
~~~~~~~~
  echo :: (Monad m) => Console m -> m ()
  echo Console{readln, println} = do line <- readln
                                     println line
~~~~~~~~

Whereas in Scala this encoding may be called *Finally Tagless*, in Haskell it is
known as MTL style. Without going into details, some Scala developers didn't
understand a research paper about the performance benefits of [Generalised ADTs
in Haskell](http://okmij.org/ftp/tagless-final/index.html#tagless-final).

An alternative to MTL style are *Extensible Effects*, also known as [Free Monad
style](http://okmij.org/ftp/Haskell/extensible/more.pdf).


## Moduły

Kod źródłowy napisany w Haskellu układa się w hierarchiczne moduły, a kod każdego z nich musi być zawarty z jednym pliku.
Pierwsza linia w pliku określa jego nazwę

{lang="text"}
~~~~~~~~
  module Silly.Tree where
~~~~~~~~

Kod organizowany jest według konwencji za pomocą katalogów, tak więc plik ten znajdzie się w `Silly/Tree.hs`.

Domyślnie wszystkie symbole w pliku są eksportowane, ale możemy kontrolować to zachowanie. 
Dla przykładu wyeksportujmy typ `Tree` wraz z konstruktorami danych i funkcje `fringe`, a ominiemy
funkcję `sapling`:

{lang="text"}
~~~~~~~~
  module Silly.Tree (Tree(..), fringe) where
  
  data Tree a = Leaf a | Branch (Tree a) (Tree a)
  
  fringe :: Tree a -> [a]
  fringe (Leaf x)            = [x]
  fringe (Branch left right) = fringe left ++ fringe right
  
  sapling :: Tree String
  sapling = Leaf ""
~~~~~~~~

Co ciekawe, możemy eksportować symbole, które są zaimportowane z zewnątrz. Pozwala to autorom bibliotek
spakować całe API do jednego modułu niezależnie od tego jak zostało zaimplementowane.

W innym pliku możemy zaimportować wcześniej zdefiniowane `Silly.Tree`.

{lang="text"}
~~~~~~~~
  import Silly.Tree
~~~~~~~~

co jest równoznaczne ze Scalowym `import silly.tree._`. Jeśli chcielibyśmy ograniczyć symbole,
które są importowane to wystarczy wymienić je w nawiasach zaraz za nazwą importowanego modułu:

{lang="text"}
~~~~~~~~
  import Silly.Tree (Tree, fringe)
~~~~~~~~

Tutaj importujemy jedynie kontruktor typu `Tree` (bez konstruktorów danych)
i funkcję `fringe`. Jeśli chcielibyśmy zaimportować wszystkie konstruktory danych możemy
użyć `Tree(..)`. Jeśli potrzebujemy jedynie `Branch` to wystarczy to zadeklarować:

Here we only import the `Tree` type constructor (not the data constructors) and
the `fringe` function. If we want to import all the data constructors (and
pattern matchers) we can use `Tree(..)`. If we only want to import the `Branch`
constructor we can list it explicitly:

{lang="text"}
~~~~~~~~
  import Silly.Tree (Tree(Branch), fringe)
~~~~~~~~

Jeśli okaże się że nazwy importowanych symboli kolidują ze sobą możemy rozwiązać ten problem używając importu kwalifikowanego
(`qualified`) z opcjonalną listą importowanych symboli

{lang="text"}
~~~~~~~~
  import qualified Silly.Tree (fringe)
~~~~~~~~

Teraz by wywołać `fringe` musimy posłużyć się identyfikatorem `Silly.Tree.fringe` zamiast zwykłego `fringe`. Podczas importowania
możemy też zmienić nazwę modułu

{lang="text"}
~~~~~~~~
  import qualified Silly.Tree as T
~~~~~~~~

tym samym `fringe` jest teraz dostępne jako`T.fringe`.

Alternatywnie, zamiast deklarować importowane symbole możemy wybrać to czego **nie** chcemy importować

{lang="text"}
~~~~~~~~
  import Silly.Tree hiding (fringe)
~~~~~~~~

Domyślnie moduł `Prelude` jest niejawnie importowany, ale jeśli zaimportujemy go wprost, to tylko
nasza wersja będzie użyta. Możemy użyć tego triku aby ukryć niebezpieczne funkcje

{lang="text"}
~~~~~~~~
  import Prelude hiding ((!!), head)
~~~~~~~~

Możemy też całkowicie się go pozbyć za pomocą rozszerzenia języka `NoImplicitPrelude`.


## Ewaluacja

Haskell kompiluje się do kodu natywnego, nie ma więc maszyny wirtualnej, ale nadal jest garbage collector.
Podstawową właściwością Haskellowego środowiska uruchomieniowego, jest to, że wszystkie parametry są domyślnie
**leniwie ewaluowane**. Wyrażenia traktowane są jako "thunki", czyli obietnice dostarczenia wartości gdy będzie ona potrzebna.
Thunki są redukowane tylko gdy jest to absolutnie niezbędne do kontynuowania obliczeń.

Dużą zaletą leniwej ewaluacji jest to, że zdecydowanie trudniej jest przepełnić stos! Wadą jest nieuchronny
narzut wydajnościowy, dlatego też Haskell pozwala nam przełączyć się na ścisłą ewaluację dla wybranych przez
nas parametrów.

Nie jest też takie oczywiste co tak na prawdę oznacza ścisła ewaluacja. Określa się, że wyrażenie jest w *słabej czołowej postaci normalnej* (WHNF, _weak head normal form_)
jeśli najbardziej zewnętrzne bloki nie mogą być bardziej zredukowane, oraz w *postaci normalnej* jeśli wyrażenie jest w pełni wyewaluowane.
Domyślna strategia ewaluacji w Scali odpowiada właśnie postaci normalnej.

Dla przykładu, te wyrażenia są w postaci normalnej:

{lang="text"}
~~~~~~~~
  42
  (2, "foo")
  \x -> x + 1
~~~~~~~~

natomiast poniższe nie są (mogą być dalej redukowane):

{lang="text"}
~~~~~~~~
  1 + 2            -- reduces to 3
  (\x -> x + 1) 2  -- reduces to 3
  "foo" ++ "bar"   -- reduces to "foobar"
  (1 + 1, "foo")   -- reduces to (2, "foo")
~~~~~~~~

Następujące wyrażenia są w WHNF ponieważ zewnętrzny kod nie może być zredukowany (mimo że
części wewnętrzne mogą):

{lang="text"}
~~~~~~~~
  (1 + 1, "foo")
  \x -> 2 + 2
  'f' : ("oo" ++ "bar")
~~~~~~~~

a te wyrażenia już w WHNF nie są

{lang="text"}
~~~~~~~~
  1 + 1              -- reduces to 2
  (\x y -> x + y) 2  -- reduces to \y -> 2 + y
  "foo" ++ "bar"     -- reduces to "foobar"
~~~~~~~~

Domyślną strategią ewaluacji jest niewykonywanie żadnych redukcji gdy wyrażenie przekazywane jest jako parametr.
Wsparcie na poziomie języka pozwala nam wymusić WHNF dla dowolnego wyrażenia za pomocą `($!)`

{lang="text"}
~~~~~~~~
  -- evaluates `a` to WHNF, then calls the function with that value
  ($!) :: (a -> b) -> a -> b
  infixr 0
~~~~~~~~

Możemy też użyć wykrzyknika na parametrach konstruktorów danych:

{lang="text"}
~~~~~~~~
  data StrictList t = StrictNil | !t :. !(StrictList t)
  
  data Employee = Employee
                    { name :: !Text
                    , age :: !Int
                    }
~~~~~~~~

Rozszerzenie języka `StrictData` sprawia, że wszystkie parametry danych w danym module są ściśle ewaluowane.

Kolejne rozszerzenie, `BangPattern`, pozwala na używanie `!` na argumentach funkcji. Z kolei rozszerzenie
`Strict` zamienia wszystkie argumenty funkcji na ściśle ewaluowane.

W ekstremalnym przypadku możemy użyć `($!!)` i typeklasy `NFData` do wymuszenia ewaluacji do postaci normalnej

{lang="text"}
~~~~~~~~
  class NFData a where
    rnf :: a -> ()
  
  ($!!) :: (NFData a) => (a -> b) -> a -> b
~~~~~~~~

jeśli tylko istnieje instancja tej typeklasy.

Kosztem ścisłej ewaluacji jest to, że Haskell zaczyna zachowywać się podobnie jak inne ścisłe języki
i może wykonywać niepotrzebną pracę. Tym samym przełączanie się w ten tryb musi być wykonane
z wielką uwagą i tylko gdy mamy do czynienia z mierzalnym wzrostem wydajności. Jeśli masz wątpliwości
to lepiej zostać przy domyślnej leniwej ewaluacji.

A> Istnieje groźna pułapka dotycząca leniwej ewaluacji: jeśli akcja typu I/O populuje leniwą strukturę danych,
A> to będzie ona wykonana gdy dana struktura jest ewaluowana, grożąc tym samym błędami pochodzącymi
A> z zupełnie nieoczekiwanych miejsc oraz tym, że wymknie się ona z logiki obsługi zasobów. Aby uniknąć
A> takich problemów powinniśmy zawsze wczytywać dane z I/O do ścisłych struktur danych.
A>
A> Na szczęście dotyczy to jedynie deweloperów piszących niskopoziomowy kod oparty o I/O. Zewnętrzne biblioteki,
A> takie jak `pipes-safe` lub `conduits` dostarczają bezpieczne abstrakcje dla zwykłego Haskellera.


## Kolejne kroki

Haskell jest językiem często szybszym, bezpieczniejszym i prostszym niż Scala, który używany jest również
w biznesie. Rozważ [kurs programowania funkcyjnego od data61](https://github.com/data61/fp-course), a ewentualne
pytania możesz zawsze zadać w pokoju `#qfpl` na `freenode.net`.

O to parę dodatkowych materiałów, które mogą być pomocne w nauce:

-   [Programming in Haskell](http://www.cs.nott.ac.uk/~pszgmh/pih.html) nauczy nas języka od podstaw
-   [Parallel and Concurrent Programming in Haskell](http://shop.oreilly.com/product/0636920026365.do) oraz [What I Wish I Knew When
    Learning Haskell](http://dev.stephendiehl.com/hask/#data-kinds) dostarczają wiedzy na poziomie zaawansowanym.
-   [Glasgow Haskell Compiler User Guide](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/) i [HaskellWiki](https://wiki.haskell.org) to z kolei same twarde fakty.
-   [Eta](https://eta-lang.org/), czyli Haskell na JVMie.

Jeśli podoba Ci się Haskell i doceniasz wartość jaką może przynieść twojej firmie, to powiedz to swoim przełożonym! W ten sposób
ci nieliczni managerowie, którzy zdecydują się na ten krok mogą przyciągnąć utalentowanych programistów funkcyjnych
z miejsc, które nie były dość odważne, a wszyscy będą szczęśliwi.

# Licencje

Niektóre części kodu źródłowego w tej książce zostały skopiowane z wolnego (_free / libre_) oprogramowania.
Licencje tych projektów wymagają, aby poniższe licencje były rozprowadzane wraz ze wspomnianym kodem.


## Licencja Scali

{lang="text"}
~~~~~~~~
  Copyright (c) 2002-2017 EPFL
  Copyright (c) 2011-2017 Lightbend, Inc.
  
  All rights reserved.
  
  Redistribution and use in source and binary forms, with or without modification,
  are permitted provided that the following conditions are met:
  
    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Neither the name of the EPFL nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.
  
  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
~~~~~~~~


## Licencja Scalaz

{lang="text"}
~~~~~~~~
  Copyright (c) 2009-2014 Tony Morris, Runar Bjarnason, Tom Adams,
                          Kristian Domagala, Brad Clow, Ricky Clarkson,
                          Paul Chiusano, Trygve Laugstøl, Nick Partridge,
                          Jason Zaugg
  All rights reserved.
  
  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:
  
  1. Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
  2. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
  3. Neither the name of the copyright holder nor the names of
     its contributors may be used to endorse or promote products derived from
     this software without specific prior written permission.
  
  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
~~~~~~~~


