let rec lookup: int -> (int * int) list -> maybe in  = 
  fn k:int => fn l: (int*int) list =>
    match l with 
      nil      -> nothing 
    | x :: xs -> if (fst x) = k 
        then just (snd x)
        else lookup k xs  in 

let base_dados : (int * int) list =  [(1,10), (2,20), (3,30), (4,40), (5,50)] in

let key:int = 3 in 

match lookup key base_dados with
  noting -> 0
| just n -> n


let rec list_max: int list -> maybe int  = 
  fn l:int list =>
    match l with 
    | nil -> nothing
    | h :: t -> (
        match list_max t with
        | noting -> just h
        | just m -> just (if h >= m then h else m))
