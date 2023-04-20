let get_some #a (x: (option a){Some? x})=
    match x with
    | Some _x -> x
