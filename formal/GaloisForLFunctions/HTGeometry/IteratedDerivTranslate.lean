import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# Iterated derivatives and translation

Differentiating a translated function is translating its derivative, at every order.  Mathlib has
this for a single derivative (`deriv_comp_add_const`) but not for `iteratedDeriv`.

The consequence recorded here is the identification between two ways of describing a translated
family: as `m` separate functions each differentiated at the same point, or as one function
differentiated at `m` translated points.  The packet formalism uses the second, the family gauge the
first.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Iterated derivatives commute with translation.**  Absent from mathlib for `iteratedDeriv`,
though the single-derivative case is `deriv_comp_add_const`. -/
theorem iteratedDeriv_comp_add_right (f : ℂ → ℂ) (c : ℂ) :
    ∀ (n : ℕ) (z : ℂ), iteratedDeriv n (fun w => f (w + c)) z = iteratedDeriv n f (z + c) := by
  intro n
  induction n generalizing f with
  | zero => intro z; simp
  | succ k ih =>
      intro z
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hderiv : deriv (fun w => f (w + c)) = fun w => deriv f (w + c) := by
        funext w
        exact deriv_comp_add_const f c w
      rw [hderiv, ih (deriv f)]

/-- The family jet vector of a translated family is the jet vector of the single function read at
the translated nodes.  This is the identification between the family formalism and the packet
formalism, where one function is evaluated at shifted nodes. -/
theorem familyJetVec_translates {m n : ℕ} (f : ℂ → ℂ) (h : Fin m → ℂ) (z : ℂ) :
    familyJetVec (n := n) (fun i w => f (w + h i)) z
      = Sum.elim (fun _ => z) (fun p => iteratedDeriv (p.2 : ℕ) f (z + h p.1)) := by
  funext s
  cases s with
  | inl x => cases x; rfl
  | inr p =>
      obtain ⟨i, j⟩ := p
      show iteratedDeriv (j : ℕ) (fun w => f (w + h i)) z = _
      rw [iteratedDeriv_comp_add_right]
      rfl

end

end GaloisForLFunctions.HTGeometry
