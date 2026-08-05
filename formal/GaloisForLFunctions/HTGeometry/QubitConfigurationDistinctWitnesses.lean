import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

/-!
# Distinct qubit configurations exist

A finite qubit configuration is a Boolean assignment to the sites.  As soon as there is a site the
all-zero and all-one assignments differ, so the configuration space is nontrivial and every law
conditioned on two distinct configurations has instances.
-/

namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*}

/-- **The all-zero and all-one configurations differ on a nonempty site set.** -/
theorem const_false_ne_const_true [Nonempty σ] :
    (fun _ => false : FiniteQubitConfiguration σ) ≠ (fun _ => true) := by
  intro h
  have := congrFun h (Classical.arbitrary σ)
  exact Bool.noConfusion this

/-- Hence the configuration space is nontrivial. -/
instance [Nonempty σ] : Nontrivial (FiniteQubitConfiguration σ) :=
  ⟨_, _, const_false_ne_const_true (σ := σ)⟩

/-- Two configurations differing at one site are distinct. -/
theorem ne_of_apply_ne {x y : FiniteQubitConfiguration σ} {i : σ} (h : x i ≠ y i) : x ≠ y :=
  fun hxy => h (congrFun hxy i)

end GaloisForLFunctions.HTGeometry
