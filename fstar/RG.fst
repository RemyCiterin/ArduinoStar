module RG

module Map = FStar.Map
module P = FStar.Preorder

let st_pre (state:Type0) (rely guarantee:P.relation state) =
  p:(state -> Type0){P.stable p rely}
