open classical
variables {A B C : Prop}
-- Prove ¬ (A ∧ B) → ¬ A ∨ ¬ B by replacing the sorry's below
-- by proofs.

lemma step1 (h1 : ¬ (A ∧ B)) (h2 : A) : ¬ A ∨ ¬ B :=
have ¬ B, from (assume g1 : B, show false, from h1 (and.intro h2 g1)),
show ¬ A ∨ ¬ B, from or.inr this


lemma step2 (h1 : ¬ (A ∧ B)) (h2 : ¬ (¬ A ∨ ¬ B)) : false :=
have ¬ A, from
  assume : A,
  have ¬ A ∨ ¬ B, from step1 h1 ‹A›,
  show false, from h2 this,
show false, from h2 (or.inl this)


theorem step3 (h : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
by_contradiction
  (assume h' : ¬ (¬ A ∨ ¬ B),
  show false, from step2 h h')


example (h : ¬ B → ¬ A) : A → B :=
assume ha : A,
by_contradiction
  (assume hnb : ¬ B,
    have hna : ¬ A, from h hnb,
    show false, from hna ha)


example (h : A → B) : ¬ A ∨ B :=
have t : A ∨ ¬ A, from em A,
or.elim t
  (assume ha : A,
    have hb : B, from h ha,
    show ¬ A ∨ B, from or.inr hb)
  (assume hna : ¬ A,  show ¬ A ∨ B, from or.inl hna)
