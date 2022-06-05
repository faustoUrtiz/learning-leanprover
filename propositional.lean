variables A B C : Prop 

example : A ∧ ¬ B → ¬ B ∧ A  :=
assume h : A ∧ ¬ B,
and.intro (and.right h) (and.left h)

example : true := trivial

section
  variable h : false
  #check h

  theorem t : A := false.elim h 

  #check t

end


theorem AimpBnotBThennotA (hpq : A → B) (hnq : ¬ B) : ¬ A :=
assume hp : A,
show false, from hnq (hpq hp)

#check AimpBnotBThennotA




