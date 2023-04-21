on veut représenter le model mémoire par l'ensemble de ses états possibles, pour l'instant avec ST ce n'est pas possible (on ne peut retourner qu'un seul état), il faut donc un effet pour manipuler les ensemble d'états


## effet custom
faire un effet custom
```ocaml
ST (a:Type) (state:Type0)
  (pre:(state -> prop) -> prop)
  (post:(state -> prop) -> a -> state -> prop)
```
(voir `fstar/Effect.fst`)

- problème: avec l'implémentation actuelle le type checking est lent
## utiliser STATE\_h

on peut utiliser des `STATE_h (state -> prop)`
peut-être ajouter une notion de préorder
