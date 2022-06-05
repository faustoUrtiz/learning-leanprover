section

variables A B C D : Prop

example : A ∧ (A → B) → B :=
assume h : A ∧ (A → B),
have g : A, from and.left h,
have i : A → B, from and.right h,
show B, from i g

theorem nny (ha : A) : ¬ (¬ A) :=
assume hna : ¬ A,
show false, from hna ha

#check nny

theorem notAnotB (h : ¬ A ∨ ¬ B) : ¬ (A ∧ B) :=
or.elim h
  (assume hna : ¬ A,
    assume hn : A ∧ B,
    show false, from hna (and.left hn))
  (assume hnb : ¬ B,
    assume hn : A ∧ B,
    show false, from hnb (and.right hn))

#check notAnotB

  
example : A → ¬ (¬ A ∧ B) :=
assume ha : A,
assume hnab : ¬ A ∧ B,
show false, from and.left hnab ha

example : ¬ (A ∧ B) → (A → ¬ B) :=
assume hnanb : ¬ (A ∧ B),
assume ha : A,
assume hb : B,
show false, from hnanb (and.intro ha hb)


example (h1 : A ∨ B) (h2 : A → C) (h3 : B → D) : C ∨ D :=
or.elim h1
  (assume h1a : A,
    show C ∨ D, from or.inl (h2 h1a))
  (assume h1b : B,
    show C ∨ D, from or.inr (h3 h1b))



example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
assume g : A ∨ B,
or.elim g 
  (assume ga : A,
    show false, from (and.left h) ga)
  (assume gb : B,
    show false, from (and.right h) gb)


example : ¬ (A ∧ ¬ A) :=
assume h : A ∧ ¬ A,
show false, from and.right h (and.left h)


lemma AimpNotA (h : A → ¬ A) : ¬ A :=
assume g : A,
show false, from (h g) g

#check AimpNotA



example : ¬ (A ↔ ¬ A) :=
assume hiff : A ↔ ¬ A,
have hl : A → ¬ A, from iff.elim_left hiff,
have hr : ¬ A → A, from iff.elim_right hiff,
have hna : ¬ A, from 
  assume h : A, 
  show false, from (hl h) h,
have ha : A, from hr hna,
show false, from hna ha



end
