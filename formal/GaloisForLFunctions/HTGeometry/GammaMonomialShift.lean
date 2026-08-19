import GaloisForLFunctions.HTGeometry.RationalShiftRatio

/-!
# The functional equation of a Gamma monomial

`M_n(s) = ∏_k Γ(s+λ_k)^{n_k}` satisfies

`M_n(s+1) = (∏_k (s+λ_k)^{n_k}) · M_n(s)`,

so its shift ratio is the *rational* function whose second logarithmic derivative
`SignedShiftProductLogDeriv` computes and `RationalShiftRatio` forbids a rational solution for.

This is the bridge between the arithmetic of exponent vectors and the shift obstruction, and it is
the base of the linear independence of Gamma monomials that
`archimedean-relative-prime-cocycle-curvature` consumes.  The identity needs the arguments to avoid
the poles of `Γ` and the origin, which a right half plane arranges uniformly.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The Gamma monomial with integer exponents. -/
def gammaMonomial {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) (s : ℂ) : ℂ :=
  ∏ k, (Complex.Gamma (s + lam k)) ^ (n k)

/-- **The functional equation of a Gamma monomial.** -/
theorem gammaMonomial_shift {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) {s : ℂ}
    (hz : ∀ k, s + lam k ≠ 0) :
    gammaMonomial lam n (s + 1) = (∏ k, (s + lam k) ^ (n k)) * gammaMonomial lam n s := by
  rw [gammaMonomial, gammaMonomial, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hgam : Complex.Gamma (s + 1 + lam k) = (s + lam k) * Complex.Gamma (s + lam k) := by
    have hrw : s + 1 + lam k = (s + lam k) + 1 := by ring
    rw [hrw]
    exact Complex.Gamma_add_one _ (hz k)
  rw [hgam, mul_zpow]

/-- On a right half plane every shifted argument has positive real part. -/
theorem re_pos_of_gt_sum_abs {r : ℕ} (lam : Fin r → ℂ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) (k : Fin r) : 0 < (s + lam k).re := by
  have hle : |(lam k).re| ≤ ∑ j, |(lam j).re| :=
    Finset.single_le_sum (f := fun j => |(lam j).re|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ k)
  have hneg : -(lam k).re ≤ |(lam k).re| := neg_le_abs _
  rw [Complex.add_re]
  linarith

/-- The Gamma monomial is nonvanishing on a right half plane. -/
theorem gammaMonomial_ne_zero {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) {s : ℂ}
    (hre : ∀ k, 0 < (s + lam k).re) : gammaMonomial lam n s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ ?_
  refine Complex.Gamma_ne_zero fun m => ?_
  intro hcon
  have h1 : (s + lam k).re = -(m : ℝ) := by
    rw [hcon]
    simp
  have h2 := hre k
  have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [h1] at h2
  linarith

/-- **The functional equation on a right half plane.** -/
theorem gammaMonomial_shift_of_re {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) :
    gammaMonomial lam n (s + 1) = (∏ k, (s + lam k) ^ (n k)) * gammaMonomial lam n s := by
  refine gammaMonomial_shift lam n fun k => ?_
  intro hcon
  have := re_pos_of_gt_sum_abs lam hs k
  rw [hcon] at this
  simp at this

/-- The half plane on which the functional equation holds is nonempty and unbounded to the right. -/
theorem exists_re_gt_sum_abs {r : ℕ} (lam : Fin r → ℂ) (t : ℝ) :
    ∃ s : ℂ, (∑ j, |(lam j).re|) < s.re ∧ t < s.re := by
  refine ⟨((max (∑ j, |(lam j).re|) t + 1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_re]
    have := le_max_left (∑ j, |(lam j).re|) t
    linarith
  · rw [Complex.ofReal_re]
    have := le_max_right (∑ j, |(lam j).re|) t
    linarith

end

end GaloisForLFunctions.HTGeometry
