section
  variable A : Type
  variable f : A → A
  variable P : A → Prop
  variable h : ∀ x, P x → P (f x)

-- Show the following:
  example : ∀ y, P y → P (f(f(y))):=
  assume y : A,
  assume py : P y,
  have hpf : P y → P (f (y)), from h y,
  have hpff : P (f(y)) → P (f (f(y))), from h (f(y)),
  hpff (hpf (py)) 
end

section
  variable U : Type
  variables A B : U → Prop

  example : (∀ x, A x ∧ B x) → ∀ x, A x :=  
  assume h : (∀ x, A x ∧ B x),
  assume y,
  show A y, from and.left (h y) 
end

section
  variable U : Type
  variables A B C : U → Prop
  variable h1 : ∀ x, A x ∨ B x
  variable h2 : ∀ x, A x → C x
  variable h3 : ∀ x, B x → C x
  
  example : ∀ x, C x :=
  assume y,
  or.elim (h1 y) 
    (assume ha : A y ,  (h2 y) ha)  
    (assume hb : B y, (h3 y) hb)
end

section
  variable U : Type
  variables A B : U → Prop
  example : (∃ x, A x) → ∃ x, A x ∨ B x :=
  assume h,
  exists.elim h 
    (assume y (h1 : A y),
    show ∃ x, A x ∨ B x, from exists.intro y (or.inl h1))
end

section 
  variable U : Type
  variables A B C : U → Prop
  
  example : (¬ ∃ x, A x) → ∀ x, ¬ A x :=
  sorry

  example : (∀ x, ¬ A x) → ¬ ∃ x, A x :=
  sorry
end