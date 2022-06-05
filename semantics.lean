-- Define your truth assignment here
def A := tt
def B := ff
def C := tt
def D := tt
def E := ff

def test (p : Prop) [decidable p] : string :=
if p then "true" else "false"

#eval test ((A ∧ B) ∨ ¬ C)

#eval test (A → D)

#eval test (C → (D ∨ ¬E))

#eval test (¬(A ∧ B ∧ C ∧ D))