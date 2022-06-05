open classical

variables A B C D: Prop

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
begin
  intro,
  cases ᾰ,
    apply h.left,
      assumption,
    apply h.right,
      assumption
end

