on veut représenter le model mémoire par l'ensemble de ses états possibles, pour l'instant avec ST ce n'est pas possible (on ne peut retourner qu'un seul état), il faut donc un effet pour manipuler les ensemble d'états


Puis on a deux préordres, un qui représente les actions des autres process et un pour représenter les actions du processus courant

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
peut-être ajouter une notion de préorder et de witness pour montrer les propriétés plus facilement
