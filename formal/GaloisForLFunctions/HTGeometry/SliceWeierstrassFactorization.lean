import GaloisForLFunctions.HTGeometry.WeierstrassPolynomial

/-!
# The slice factors through the monic polynomial of its roots

The multiset attached to a slice by the argument principle is determined by its power sums, and the
factorization produced by eliminating the zeros has exactly those power sums; so the two agree, and
the slice is the monic product of the linear factors at its roots times a nowhere vanishing
holomorphic factor.

In particular the zeros of the slice inside the circle are exactly the roots of that monic
polynomial, with multiplicity — the conclusion of Weierstrass' preparation theorem in the
distinguished variable, for one fixed value of the parameters.

* `HTGeometry.exists_slice_factorization`;
* `HTGeometry.slice_eq_zero_iff`.
-/

open Complex Metric
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- **The slice factors through the monic polynomial of its root multiset.** -/
theorem exists_slice_factorization {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) :
    ∃ (t₁ : ℝ) (g : ℂ → ℂ), t < t₁ ∧ DifferentiableOn ℂ g (ball (0 : ℂ) t₁) ∧
      (∀ z ∈ ball (0 : ℂ) t₁, g z ≠ 0) ∧
      ∀ z ∈ ball (0 : ℂ) t₁,
        f (Fin.cons z y) = multisetLinearProd (sliceRoots f t y) z * g z := by
  obtain ⟨U, hU, hsub, hfd, hne⟩ := hy
  obtain ⟨M, t₁, g, hM, ht₁, hballU, hgd, hgne, heq, hpow⟩ :=
    exists_rootMultiset_factorization ht hU hsub hfd hne
  have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hMroots : M = sliceRoots f t y := by
    refine GaloisForLFunctions.multiset_eq_of_powerSum_eq fun p => ?_
    have hmom : sliceMoment f t p y = (M.map (fun x => x ^ p)).sum := by
      rw [sliceMoment, hpow p]
      field_simp
    rw [← hmom, sliceMoment_eq_powerSum ht ⟨U, hU, hsub, hfd, hne⟩ p]
  refine ⟨t₁, g, ht₁, hgd, hgne, fun z hz => ?_⟩
  have := heq hz
  rw [hMroots] at this
  exact this

/-- **The zeros of a slice are the roots of the monic polynomial of its root multiset.** -/
theorem slice_eq_zero_iff {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) {z : ℂ} (hz : ‖z‖ < t) :
    f (Fin.cons z y) = 0 ↔ multisetLinearProd (sliceRoots f t y) z = 0 := by
  obtain ⟨t₁, g, ht₁, hgd, hgne, hfact⟩ := exists_slice_factorization ht hy
  have hzball : z ∈ ball (0 : ℂ) t₁ := by
    rw [mem_ball_zero_iff]
    exact lt_trans hz ht₁
  rw [hfact z hzball]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h2
    · exact h1
    · exact absurd h2 (hgne z hzball)
  · intro h
    rw [h, zero_mul]

end HTGeometry
