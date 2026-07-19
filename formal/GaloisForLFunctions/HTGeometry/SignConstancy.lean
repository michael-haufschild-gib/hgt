import GaloisForLFunctions.HTGeometry.NodeGap

/-!
# Constancy of sign on a zero-free interval

A continuous function without zeros on `[a, b]` takes the same sign at both endpoints: otherwise the
intermediate value theorem would produce a zero inside.  This is the contrapositive of the step used
in link 92, and it is what lets the cofactor's sign at a node be read off at any interior point of
the adjacent gap.
-/

open scoped BigOperators
open Polynomial Set

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Sign constancy.**  A continuous function with no zero on `[a, b]` has `f a` and `f b` of the
same sign. -/
theorem mul_pos_of_ne_zero_on_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    0 < f a * f b := by
  rcases lt_trichotomy (f a * f b) 0 with hlt | heq | hgt
  · exfalso
    rcases mul_neg_iff.mp hlt with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo' hab hcont ⟨hnb, hpa⟩
      exact hne z ⟨le_of_lt hz.1, le_of_lt hz.2⟩ hfz
    · obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo hab hcont ⟨hna, hpb⟩
      exact hne z ⟨le_of_lt hz.1, le_of_lt hz.2⟩ hfz
  · exfalso
    rcases mul_eq_zero.mp heq with h0 | h0
    · exact hne a ⟨le_refl a, hab⟩ h0
    · exact hne b ⟨hab, le_refl b⟩ h0
  · exact hgt

/-- Away from a root of `Q_{n+1}`, the cofactor cannot vanish. -/
theorem cofactor_eval_ne_zero {n : ℕ} {xi y : ℝ} {G : Polynomial ℝ}
    (hG : monicOrtho s (n + 1) = (X - C xi) * G)
    (hy : (monicOrtho s (n + 1)).eval y ≠ 0) : G.eval y ≠ 0 := by
  intro h0
  refine hy ?_
  rw [hG]
  simp [h0]

/-- A polynomial is continuous on any set. -/
theorem continuousOn_eval (p : Polynomial ℝ) (t : Set ℝ) :
    ContinuousOn (fun x => p.eval x) t :=
  p.continuous_aeval.continuousOn

end HTGeometry
