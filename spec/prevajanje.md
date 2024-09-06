## Millet prevajalnik 

## predstavitev milleta 

razpisal sem sistem tipov in izračunov, da lahko kasneje utemeljim prevode 

## predstavitev wasm gc

v nalogi bo potrebno tudi opisati, wasm ukaze, ki se uporabljajo in kako deluje wasm 

za wasm bi bilo dobro opisati stack machine in validacijo

Iz wasm gc se uporabljajo naslednji tipi in ukazi
```
i8
anyref  eqref  i31ref  (ref $t)  (ref null $t)
struct  array

ref.eq
ref.is_null  ref.as_non_null  ref.as_i31  ref.as_data  ref.cast
i31.new  
struct.new  struct.get  struct.get_u  struct.set
array.new  array.new_default  array.get  array.get_u  array.set  array.lens
```


## Abstraktno sintaksno dreko spremeni v bolj primereno predstavitev za prevajanje:

k vsakemu vozlišču se doda tip 

## predstava tipov v wasmu 

`bool, int` -> `i32`, `i31ref`, `i8`

`float` -> `f64`, `ref (struct f64)`, `f64`

`tuple` -> `ref (struct (ref eq))` s primernim številom polj 

`tyapply` -> za `tyinline` uporablja `ref (struct (ref eq))`. Za `tysum` pa `ref (struct (i32))`, `ref (struct (i32 ref eq))`. i32 predstavlja tag

`tyarrow` -> ustrezen wasm funkcijski tip

`typaram` -> `(ref eq)`

## currying eval/apply

prevajalnik uporablja eval/apply za currying 

## polimorfizem

Prevajalnik uporablja `(ref eq)`, da lahko generira validen wasm. Ujemanje tipov zagotovi z uporabo  pretvorb me tipi

## compile coerce

funkcija, ki vzame vrednost in v spremenljivko, ki bo shrenjena in odda primerne ukaze, da se tipi skladajo


## prevajanje vzorcev

`PNonbinding, Typed.PTuple []` vrednosti se znebi

`PVar var` nastavi local z vrednostjo spremenljivke

`PAnnotated (p, _)` prevede vzorec 

`PAs (p, var)` prevede vzorec in potem rezultatu priredi spremenljivko

`PTuple ps` nastavi local z tipom n-terke, ki ga potem uporabi, ko prevaja posamezne vzorce n-terke

`PVariant (lbl, p)` poišče varianto v kontekstu in ustvari primerne ukaze za preverjanje variante

`PConst const` preveri, če je na skladu pravilna konstanta, če ni br 

## prevajanje izrazov

`Typed.Var var` poišče tip spremenljivke (global, local) in odda primeren ukaz

`Const c` odda ukaz, ki ustreza spremenljivki

`Annotated (exp1, _)` prevede izraz in izvede coerce

`Tuple []` drop 

`Tuple es` prevede ukaze in rezultate zapakira v struct

`Variant (lbl, e)` prevede ukaz in rezultat zapakira v struct z oznako

`Lambda _` prevede funkcijo 

`RecLambda (var, abs)` prevede funkcijo

## prevajanje funkcij

izračuna parametre za zaprtje 

če je funkcija rekurzivna nastavi local z zaprtjem funkcije

Po prevajanju funkcije odda še eno zaprtje, da ga lahko uporabijo kasnejši deli programa.

## prevajanje izračunov

`Typed.Return exp` prevede izraz, ki pripada return-u

`Do (compute, {it = (pat, cont); _})` glede na vrsto vzorce odda različne ukaze. Če je vzorec nepomemben 
samo izvede izračun in nato prevede naslednji izračun. Če je vzorec popoln prevede prevede izračun in 
vzorec. Če je vzorec delen prevede v `block ( block ( prevod izračuna, prevod vzorca, br (1), prevod nadaljevanja) unreachable)`

`Match (exp, [])` prevde izraz in nato odda unreachable

`Match (exp, abs_ls)` odda local, kamor shrani rezulat exp izraza, nato odda block, v katerem preveri vsak vzorec 

`Apply (exp1, exp2)` preveri, če je `exp1` spremenljivka ali lambda, nato preveri število argumentov funkcije, in preveri koliko argumentov je, če se ujemajo potem prevede argumente in pokliče funkcijo, sicer naredi closure in ga pokliče

## prevajanje tipov 

`TySum` prevede vsako definicijo in ji določi tag, potem doda vse skupaj kot eno definico v kontekst

`TyInline` prevede definicijo in jo doda v kontekst

## prevajanje TopLet in TopDo

`TopLet` prevede izraz in ga shrani v primerno spremenljivko

`TopDo` preveden izračun odda kot `export` funkcijo, ki ne sprejema argumentov

## prevajanje primitivnih funkcij

matematične operacije se prevedejo v funkcijo, ki sprejme struct in izvede primeren ukaz 

operacije, ki delujejo na eni spremenljivki, sprejmejo kar vrednost samo 