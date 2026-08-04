import GaloisForLFunctions.HTGeometry.CascadeExactOrderFromSeparation

/-!
# Order recession along the Poincaré approximants

A cascade whose constituents are all the same function is the iterate, so the unit-cost law reads
`ord_DA(f^{[n]}) = n`.  The normalized Poincaré approximants `g_n(z) = f^{[n]}(ζ + z/λ^n)` differ from
the iterate by an invertible affine precomposition, which does not move the minimal order.

Hence the approximants have exact orders `1, 2, 3, …`, a strictly receding sequence, while their
locally uniform limit is the Poincaré function.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- A cascade with a single repeated constituent is the iterate. -/
theorem entireCascade_const (f : ℂ → ℂ) (n : ℕ) :
    entireCascade (fun _ : ℕ => f) n = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply']
      show f (entireCascade (fun _ : ℕ => f) n z) = f (f^[n] z)
      rw [ih]

/-- **Order is unchanged along an affine reparametrisation of an iterate.** -/
theorem exactDifferentialOrder_iterate_affine {f : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0) {n : ℕ}
    (h : ExactDifferentialOrder (f^[n]) n) :
    ExactDifferentialOrder (fun z => f^[n] (a * z + b)) n :=
  (exactDifferentialOrder_affine_precomp ha).mpr h

/-- **The Poincaré approximants recede in order.**  With a repelling multiplier `λ ≠ 0`, the
normalized approximant `z ↦ f^{[n]}(ζ + z/λ^n)` has exact differential order `n`. -/
theorem exactDifferentialOrder_poincareApprox {f : ℂ → ℂ} {ζ lam : ℂ} (hlam : lam ≠ 0) {n : ℕ}
    (h : ExactDifferentialOrder (f^[n]) n) :
    ExactDifferentialOrder (fun z => f^[n] (ζ + z / lam ^ n)) n := by
  have ha : (lam ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hlam)
  have hfun : (fun z : ℂ => f^[n] (ζ + z / lam ^ n))
      = fun z : ℂ => f^[n] ((lam ^ n)⁻¹ * z + ζ) := by
    funext z
    congr 1
    rw [div_eq_inv_mul]
    ring
  rw [hfun]
  exact exactDifferentialOrder_iterate_affine ha h

/-- **The unit-cost law for iterates.**  Stated on the iterate rather than the cascade. -/
theorem exactDifferentialOrder_iterate_of_separation {f : ℂ → ℂ}
    (hfan : AnalyticOnNhd ℂ f Set.univ) {n : ℕ}
    (hall : TranscendentalEntire f)
    (h1 : DifferentiallyAlgebraicOfOrder f 1)
    (hsep : ∀ m : ℕ,
      StepSeparation (prefixFamily (entireCascade (fun _ : ℕ => f)) m)
        (entireCascade (fun _ : ℕ => f) m))
    (helim : ∀ m, m < n →
      DifferentiallyAlgebraicOfOrder (entireCascade (fun _ : ℕ => f) n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily (fun _ : ℕ => f) n) P z = 0) :
    ExactDifferentialOrder (f^[n]) n := by
  have h := exactDifferentialOrder_entireCascade_of_separation
    (f := fun _ : ℕ => f) (fun _ => hfan) (fun _ => hall) (fun _ _ => h1) hsep helim
  rwa [entireCascade_const] at h

end GaloisForLFunctions.HTGeometry
