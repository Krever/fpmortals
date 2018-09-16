{frontmatter}

> "Miłość jest mądra, nienawiść jest głupia. W tym świecie, który staje się
> coraz bardziej wewnętrznie połączony, musimy nauczyć się tolerować się 
> wzajemnie, musimy nauczyć się znosić to że niektórzy ludzie mówią rzeczy,
> które nam się nie podobają. Tylko w ten sposób możemy żyć razem. Ale jeśli
> mamy żyć razem i nie umierać razem, musimy nauczyć się rodzaju dobroci
> i tolerancji, który jest absolutnie konieczny do przetrwania ludzkiego życia
> na tej planecie."
> 
> ― Bertrand Russell


# O niniejszej książce

Książka ta jest kierowana do typowego programisty Scali, prawdopodobnie z
doświadczenie Javowym, który zaciekawiony jest pradygmatem **Programowania Funkcyjnego** (FP).
Książka ta uzasadnia każdy koncept praktycznym przykładem, wliczacjąc stworzenie aplikacji
webowej.

Ninejsza książka używa [Scalaz 7.2](https://github.com/scalaz/scalaz), najpopularniejszej, najstabilniejszej,
najpryncypialnej[^principled] i najbardziej kompleksowej biblioteki do Programowania Funkcyjnego w Scali.

[^principled]: _the most principled_

Książka ta została napisana z myślą o czytaniu jej od deski do deski, w zaprezentowanej kolejności i z 
przerwami na odpoczynek między rozdziałami. Początkowe rozdziały zachęcaj do programowania w sposób, który
w późniejszych rozdziałach zdyskredytujemy: podobnie jak uczymy się teori grawitacji Newtona jako dzieci
aby później przejść do Riemanna / Einsteina / Maxwella jeśli zechcemy studiować fizykę.

Komputer nie jest niezbędny aby podążać za treścią, ale zachęcamy do zgłebienia źródeł Scalaz. Niektóre z bardziej
skomplikowanych fagmentów kodu są dostępne wraz z [źródłami tej książki](https://github.com/fommil/fpmortals/)  a
ci, którzy rządni sa praktycznych ćwiczeń powinni spróbować (zre-)implementować Scalaz (oraz przykładową aplikację)
używając częsciowych opisów zaprezentowanych w tej książce.

Polecamy również [Czerwoną Książkę](https://www.manning.com/books/functional-programming-in-scala)[^redbook] jako kolejny krok. 
Pokazuje ona jak stworzyć bibliotekę wspierającą programowanie funkcyjne od podstaw.

[^redbook]: _The Red Book_


# Nota lewa autorskiego[^copyleft]

[^copleft]: _Copyleft notice_. Nie mogliśmy się powstrzymać.

Ta książka jest **Wolna**[^libre] i podąża za filozofią [Wolnego Oprogramowania](https://www.gnu.org/philosophy/free-sw.en.html):
możesz używac jej jak tylko chcesz, [źródła są dostępne](https://github.com/fommil/fpmortals/), możesz ją redystrybuować 
oraz dystrybuować swoją własną wersję. Oznacza to że możesz ja wydrukować, fotokopiować, wysyłać mailem, uploadować 
na strony internetowe, zmieniać, tłumaczyć, pobierać opłaty, remiksować, usuwać kawałki i malowac po dowolnych fragmentach.

[^libre]: _Libre_

Ta książka jest objęta **Lewem autorskim**: jeśli zmienisz i udostępnisz swoją własną wersję, musisz równieżnież przekazać
wspomniane uprawnienia swoim odbiorcom.

Książka ta używa licencji [Creative Commons Attribution ShareAlike 4.0 International](https://creativecommons.org/licenses/by-sa/4.0/legalcode) 
(CC BY-SA 4.0).

Wszystkie oryginalne fragmenty kodu w tej książce są osobno licencjonowane na podstawie [CC0](https://wiki.creativecommons.org/wiki/CC0),
możesz używać ich bez żadnych ograniczeń. Fragmenty ze Scalaz i pokrewnych bibliotek zachowują swoje licencje, powtórzone w pełni w załączniku.

Przykładowa aplikacja `drone-dynamic-agents` udostępniona jest na zasadach [GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html):
jedynie fragmenty zawarte w książce dostępne sa bez ograniczeń. 


# Podziękowania

Dla Diego Esteban Alonso Blas, Raúl Raja Martínez i Peter Neyens z 47
degrees, Rúnar Bjarnason, Tony Morris, John de Goes i Edward Kmett
za ich pomoc w tłumaczeniu zasad FP. Kenji Yoshida i
Jason Zaugg za stworzenie pierwszej wersji Scalaz, oraz Paul Chuisano /
Miles Sabin naprawienie krytycznego błedu w kompilatorze Scali([SI-2712](https://issues.scala-lang.org/browse/SI-2712)).

Dziękuje też czytelnikom, którzy doradzali przy pierwszych szkicach tej książki.

Niektóre materiały były szczególnie pomocne dla mojego własnego zrozumienia konceptów opisanych w tej książce.
Podziękowania dla Juana Manuela Serrano za [All Roads Lead to Lambda](https://skillsmatter.com/skillscasts/9904-london-scala-march-meetup#video), 
Pere'a Villega za [On Free Monads](http://perevillega.com/understanding-free-monads), 
Dicka Wall oraz Josha Suereth za [For: What is it Good For?](https://www.youtube.com/watch?v=WDaw2yXAa50), 
Erika Bakker za [Options in Futures, how to unsuck them](https://www.youtube.com/watch?v=hGMndafDcc8),
Noela Markham za [ADTs for the Win!](https://www.47deg.com/presentations/2017/06/01/ADT-for-the-win/), 
Sukanta Hajra za [Classy Monad Transformers](https://www.youtube.com/watch?v=QtZJATIPB0k),
Luki Jacobowitz za [Optimizing Tagless Final](https://lukajcb.github.io/blog/functional/2018/01/03/optimizing-tagless-final.html), 
Vincenta Marquez za [Index your State](https://www.youtube.com/watch?v=JPVagd9W4Lo), 
Gabriela Gonzalez za [The Continuation Monad](http://www.haskellforall.com/2012/12/the-continuation-monad.html), 
oraz Yi Lin Wei / Zainab Ali za ich tutoriale w trakcie spotkań Hack The Tower.

Pomocne dusze, które cierpliwe tłumaczyły mi kolejne rzeczy: Merlin Göttlinger, Edmund
Noble, Fabio Labella, Adelbert Chang, Michael Pilquist, Paul Snively, Daniel
Spiewak, Stephen Compall, Brian McKenna, Ryan Delucchi, Pedro Rodriguez, Emily
Pillmore, Aaron Vargo, Tomas Mikula, Jean-Baptiste Giraudeau, Itamar Ravid, Ross
A. Baker, Alexander Konovalov, Harrison Houghton, Alexandre Archambault,
Christopher Davenport, Jose Cardona, Isaac Elliott.

# Nota tłumacza

Angielski stał się _de facto_ uniwersalnym językiem programistów, a zarówno dostepność jak i konsumpcja treśći 
technicznych w innych językach jest bardzo niewielka. Niesie to ze sobą implikacje również i dla tej książki 
oraz jej tłumaczenia. Przy tłumaczeniu staraliśmy sie brać pod uwagę, że wszelkie następne kroki czytelnika, 
takie jak wyszukiwanie dodatkowych materiałów, zadawanie pytań lub zwykła komunikacja z innymi programistami
najprawdopodobniej odbywać się będą z użyciem języka angielskiego. Dlatego też staraliśmy się używać tłumaczeń jak 
najbardziej zbliżonych do wersji oryginalnych, co poskutkowało tym że duża ich część może brzmieć śmiesznie, dziwnie lub
nawet absurdalnie. W wielu miejscach używamy form potocznych i słowotwórstwa, które nie znalazły by miejsca w 
poważnej literaturzetechnicznej. Dodatkowo, w momencie gdy wprowadzamy tłumaczenie, dla którego odtworzenie 
wersji oryginalnej może być nieoczywiste, podajemy tęże wersje wprost, w nawiasach bądź przypisach.

Należy również pamiętać, że jest to tłumaczenie amatorskie, motywowane jedynie chęcią popularyzacji Scali i 
programowania funkcyjnego, a nie zyskiem, dlatego też w wielu miejscach odbiegać ono może od profesjonalnych
standardów. Użycie liczby mnogiej, w tej nocie i późniejszych przypisach, wynika z kolei jedynie z megalomanii 
tłumacza a nie z faktu że stoi za nimi zespół profesjonalistów.



# Aspekty praktyczne

Aby skonfigurować projekt używający bibliotek prezentowanych w tej książce użyj aktualnej wersji Scali wraz
z opcjami specyficznymi dla Programowania Funkcyjnego (np. w `build.sbt`):

{lang="text"}
~~~~~~~~
  scalaVersion in ThisBuild := "2.12.6"
  scalacOptions in ThisBuild ++= Seq(
    "-language:_",
    "-Ypartial-unification",
    "-Xfatal-warnings"
  )
  
  libraryDependencies ++= Seq(
    "com.github.mpilquist" %% "simulacrum"     % "0.13.0",
    "org.scalaz"           %% "scalaz-core"    % "7.2.26"
  )
  
  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.7")
  addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.1" cross CrossVersion.full)
~~~~~~~~

Aby fragmenty kodu były krótkie, ominiemy sekcje `import`ów. Jeśli nie zaznaczono inaczej,
można przyjąć że wszystkie fragmenty mają poniższe importy:

{lang="text"}
~~~~~~~~
  import scalaz._, Scalaz._
  import simulacrum._
~~~~~~~~


