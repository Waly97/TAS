type ptype = 
  | Var of string 
  | Arr of ptype * ptype 
  | Nat