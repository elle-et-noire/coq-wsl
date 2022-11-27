Section uo.
  Definition fct := nat -> nat.
  Parameter incr_fct : Set.
  Parameter fct_of_incr_fct : incr_fct -> fct.
  
  Fail Coercion fct_of_incr_fct : incr_fct >-> Funclass.
  Coercion fct_of_incr_fct : incr_fct >-> fct.
  Parameter f' : incr_fct.
  Check f' : fct.
  Fail Check f' 0.

  Identity Coercion uo_fct_Funclass : fct >-> Funclass.
  Check f' 0.