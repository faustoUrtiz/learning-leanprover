open classical
variables (A B : Prop)

example : A ∨ ¬ A :=
by_contradiction
  (assume h1 : ¬ (A ∨ ¬ A),
    have h2 : ¬ A, from
      assume h3 : A,
      have h4 : A ∨ ¬ A, from or.inl h3,
      show false, from h1 h4,
    have h5 : A ∨ ¬ A, from or.inr h2,
    show false, from h1 h5)

  

example (p : Prop) : p ∨ ¬ p :=
em p

example (h : ¬ B → ¬ A) : A → B :=
assume h1 : A,
show B, from
  by_contradiction
    (assume h2 : ¬ B,
      have h3 : ¬ A, from h h2,
      show false, from h3 h1)

example (h : ¬ (A ∧ ¬ B)) : A → B :=
assume : A,
show B, from
  by_contradiction
    (assume : ¬ B,
      have A ∧ ¬ B, from and.intro ‹A› this,
      show false, from h this)