variables (α : Type*) (p q : α → Prop)

theorem thml : (∀ x, p x ∧ q x) → (∀ x, p x) :=
assume h, 
assume y,
show p y, from and.elim_left(h y)

theorem thmr : (∀ x, p x ∧ q x) →  (∀ x, q x) :=
assume h, 
assume y,
show q y, from and.elim_right(h y)


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro 
  (assume h : (∀ x, p x ∧ q x),
  and.intro (assume t : α, and.left (h t)) (assume t : α, and.right (h t)))
  (assume h, assume t, and.intro ((and.left h) t) ((and.right h) t))
  
  
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
assume h : (∀ x, p x → q x),
assume g : (∀ x, p x),
assume y : α,
(h y) (g y) 

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
assume h,
or.elim h 
  (assume g, assume t, or.inl (g t)) (assume g, assume t, or.inr (g t))