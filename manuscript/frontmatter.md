{frontmatter}

> "Miłość jest mądra, nienawiść jest głupia. W tym świecie, który staje się
> coraz bardziej połączony wewnętrznie, musimy nauczyć się tolerować się 
> wzajemnie. Musimy nauczyć się znosić to, że niektórzy ludzie mówią rzeczy,
> które nam się nie podobają. Tylko w ten sposób możemy żyć razem. Ale jeśli
> mamy razem żyć, ale nie umierać, musimy nauczyć się dobroci
> i tolerancji, które są absolutnie niezbędne do przetrwania ludzi na tej planecie."
> 
> ― Bertrand Russell


# O niniejszej książce

Książka ta jest kierowana do zwykłego programisty Scali, prawdopodobnie z
doświadczeniem Javowym, który zaciekawiony jest paradygmatem **Programowania Funkcyjnego**.
Każdy koncept, który przedstawiamy uzasadniany jest praktycznym przykładem, a cała książka
zwięczona jest stworzeniem w pełni funkcjonalnej aplikacji webowej.

Niniejsza książka używa [Scalaz 7.2](https://github.com/scalaz/scalaz), najpopularniejszej, najstabilniejszej,
najbardziej pryncypialnej[^principled] i najbardziej kompleksowej biblioteki do Programowania Funkcyjnego w Scali.

[^principled]: _the most principled_

Książka ta została napisana z myślą o czytaniu jej od deski do deski, w zaprezentowanej kolejności i z 
przerwami na odpoczynek między rozdziałami. Początkowe rozdziały zachęcają do programowania w sposób, który
w później zdyskredytujemy: podobnie jak uczymy się teorii grawitacji Newtona jako dzieci
aby później przejść do Riemanna / Einsteina / Maxwella jeśli zechcemy studiować fizykę.

Komputer nie jest niezbędny aby podążać za treścią, ale zachęcamy do zgłębienia kodu źródłowego Scalaz. Niektóre z bardziej
skomplikowanych fragmentów kodu są dostępne wraz z [źródłami tej książki](https://github.com/fommil/fpmortals/), a
ci, którzy żądni są praktycznych ćwiczeń powinni spróbować (zre)implementować Scalaz (oraz naszą przykładową aplikację)
używając częściowych opisów, które zaprezentujemy.

Jako kolejny krok polecamy również [Czerwoną Książkę](https://www.manning.com/books/functional-programming-in-scala)[^redbook]. 
Pokazuje ona jak stworzyć bibliotekę wspierającą programowanie funkcyjne, taką jak na przykład Scalaz, od zupełnych podstaw.

[^redbook]: _The Red Book_


# Nota lewa autorskiego[^copyleft]

[^copyleft]: _Copyleft notice_.

Ta książka jest **Wolna**[^libre] i podąża za filozofią [Wolnego Oprogramowania](https://www.gnu.org/philosophy/free-sw.en.html):
możesz używać jej jak tylko chcesz, [źródła są dostępne](https://github.com/fommil/fpmortals/), możesz ją redystrybuować 
oraz dystrybuować swoją własną wersję. Oznacza to że możesz ja wydrukować, fotokopiować, wysyłać mailem, uploadować 
na strony internetowe, zmieniać, tłumaczyć, pobierać opłaty, remiksować, usuwać kawałki i malować po dowolnych fragmentach.

[^libre]: _Libre_

Ta książka jest objęta **Lewem autorskim**: jeśli ją zmienisz i udostępnisz swoją własną wersję, musisz również przekazać
wspomniane uprawnienia swoim odbiorcom.

Książka ta używa licencji [Creative Commons Attribution ShareAlike 4.0 International](https://creativecommons.org/licenses/by-sa/4.0/legalcode) 
(CC BY-SA 4.0).

Wszystkie oryginalne fragmenty kodu są osobno licencjonowane na podstawie [CC0](https://wiki.creativecommons.org/wiki/CC0),
co oznacza, że możesz używać ich bez żadnych ograniczeń. Fragmenty ze Scalaz i pokrewnych bibliotek zachowują swoje licencje, powtórzone w pełni w załączniku.

Przykładowa aplikacja `drone-dynamic-agents` udostępniona jest na zasadach [GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html), 
a jedynie fragmenty zawarte w książce dostępne są bez ograniczeń. 


# Podziękowania

Dla Diego Estebana Alonso Blasa, Raúla Raja Martíneza i Petera Neyensa z 47
degrees, Rúnara Bjarnasona, Tonego Morrisa, Johna de Goes i Edwarda Kmetta
za ich pomoc w tłumaczeniu zasad FP. Kenji Yoshidzie i
Jasonowi Zauggowi za stworzenie pierwszej wersji Scalaz, oraz Paulowi Chiusano /
Milesowi Sabinowi za naprawienie krytycznego błędu w kompilatorze Scali ([SI-2712](https://issues.scala-lang.org/browse/SI-2712)).

Dziękuje też czytelnikom, którzy doradzali przy pierwszych szkicach tej książki.

Niektóre materiały były szczególnie pomocne dla mojego własnego zrozumienia konceptów opisanych w tej książce.
Podziękowania dla Juana Manuela Serrano za [All Roads Lead to Lambda](https://skillsmatter.com/skillscasts/9904-london-scala-march-meetup#video), 
Pere'a Villega za [On Free Monads](http://perevillega.com/understanding-free-monads), 
Dicka Walla oraz Josha Sueretha za [For: What is it Good For?](https://www.youtube.com/watch?v=WDaw2yXAa50), 
Erika Bakkera za [Options in Futures, how to unsuck them](https://www.youtube.com/watch?v=hGMndafDcc8),
Noela Markhama za [ADTs for the Win!](https://www.47deg.com/presentations/2017/06/01/ADT-for-the-win/), 
Sukanta Hajra za [Classy Monad Transformers](https://www.youtube.com/watch?v=QtZJATIPB0k),
Luki Jacobowitz za [Optimizing Tagless Final](https://lukajcb.github.io/blog/functional/2018/01/03/optimizing-tagless-final.html), 
Vincenta Marqueza za [Index your State](https://www.youtube.com/watch?v=JPVagd9W4Lo), 
Gabriela Gonzaleza za [The Continuation Monad](http://www.haskellforall.com/2012/12/the-continuation-monad.html), 
oraz Yi Lin Wei / Zainab Ali za ich tutoriale w trakcie spotkań Hack The Tower.

Pomocne dusze, które cierpliwe tłumaczyły mi kolejne koncepty: Merlin Göttlinger, Edmund
Noble, Fabio Labella, Adelbert Chang, Michael Pilquist, Paul Snively, Daniel
Spiewak, Stephen Compall, Brian McKenna, Ryan Delucchi, Pedro Rodriguez, Emily
Pillmore, Aaron Vargo, Tomas Mikula, Jean-Baptiste Giraudeau, Itamar Ravid, Ross
A. Baker, Alexander Konovalov, Harrison Houghton, Alexandre Archambault,
Christopher Davenport, Jose Cardona, Isaac Elliott.

# Nota tłumacza

Angielski stał się _de facto_ uniwersalnym językiem programistów, a zarówno dostępność jak i konsumpcja treści 
technicznych w innych językach jest bardzo niewielka. Niesie to ze sobą implikacje również i dla tej książki 
oraz jej tłumaczenia. Przy tłumaczeniu staraliśmy się brać pod uwagę, że wszelkie kroki po przeczytaniu tej książki, 
takie jak wyszukiwanie dodatkowych materiałów, zadawanie pytań lub zwykła komunikacja z innymi programistami,
najprawdopodobniej odbywać się będą z użyciem języka angielskiego. Dlatego też staraliśmy się używać tłumaczeń jak 
najbardziej zbliżonych do wersji oryginalnych, co poskutkowało tym, że duża ich część może brzmieć śmiesznie, dziwnie lub
nawet absurdalnie. W wielu miejscach używamy form potocznych i słowotwórstwa, które nie znalazły by miejsca w 
poważnej literaturze technicznej. Dodatkowo, w momencie gdy wprowadzamy tłumaczenie, dla którego odtworzenie 
wersji oryginalnej może być nieoczywiste, podajemy tę wersję wprost, w nawiasach bądź przypisach.

Pamiętajmy również, że jest to tłumaczenie amatorskie, motywowane jedynie chęcią popularyzacji Scali i 
programowania funkcyjnego, a nie zyskiem, dlatego też w wielu miejscach może ono odbiegać od profesjonalnych
standardów. Z kolei użycie liczby mnogiej w tej nocie i późniejszych przypisach, wynika z kolei jedynie z megalomanii 
tłumacza, a nie z faktu że była to praca zespółu profesjonalistów.

Chcielibyśmy również uprzedzić, że część tłumaczeń może nie pokrywać się (z różnych powodów) z tłumaczeniami tych samych terminów
wprowadzonymi przez innych autorów. Wynika to z 2 rzeczy. Po pierwsze, jak wspomniano wyżej, wierzymy że
to wersje oryginalne są najistotniejsze, a polskie tłumaczenie jest tutaj jedynie pomocą obniżającą próg wejścia. Po drugie,
jak również wspomniano powyżej, jest to tłumaczenie realizowane minimalnym wysiłkiem i bez zasobów potrzebnych na analizę
wcześniejszych prac i tłumaczeń. Mimo to mamy nadzieję, że lektura sprawi wam przyjemność.


# Aspekty praktyczne

Aby skonfigurować projekt używający bibliotek prezentowanych w tej książce użyjemy aktualnej wersji Scali wraz
z opcjami specyficznymi dla Programowania Funkcyjnego. Oto `build.sbt`:

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

Aby fragmenty kodu były krótkie, ominiemy sekcje `import`ów i jeeśli nie zaznaczono inaczej,
to należy przyjąć, że wszystkie fragmenty zawierają:

{lang="text"}
~~~~~~~~
  import scalaz._, Scalaz._
  import simulacrum._
~~~~~~~~


