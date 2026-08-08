import GaloisForLFunctions.HTGeometry.AffineGaussianSemidefinite

/-!
# Positivity of the Hermitian form of a nondegenerate theta function

The chain assembled here is the necessary direction of the Capocasa--Catanese criterion, in the
form a quasi-Abelian facet certificate needs.  Given a Hermitian form `H`, a unitary semicharacter,
and an entire function transforming by the Appell--Humbert factor of that pair:

* if the function is nonzero at a single point and the period group has a compact covering set,
  then `H` is positive **semi**-definite;
* if in addition `H` is nondegenerate, then `H` is positive definite.

The real part `(u, v) -> Re H (u,v)` is a symmetric real bilinear form whose diagonal is
`Re H (x,x)`, so the degenerate Cauchy--Schwarz lemma applies to it verbatim.  Applying it both to
`x` and to `i x` kills the real and imaginary parts of `H (x, -)` separately.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The real part of a Hermitian form, as a symmetric real bilinear form. -/
def hermitianRe (H : W → W → ℂ) (u v : W) : ℝ := (H u v).re

namespace IsHermitianForm

variable {H : W → W → ℂ} (hH : IsHermitianForm H)

include hH

theorem hermitianRe_real_smul (t : ℝ) (u v : W) :
    hermitianRe H u (((t : ℝ) : ℂ) • v) = t * hermitianRe H u v := by
  have h : H u (((t : ℝ) : ℂ) • v) = ((t : ℝ) : ℂ) * H u v := by
    rw [hH.symm (((t : ℝ) : ℂ) • v) u, hH.smul_left, star_mul, hH.symm u v, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj, mul_comm]
  rw [hermitianRe, h, Complex.re_ofReal_mul, hermitianRe]

/-- The quadratic expansion of the real part along a real direction. -/
theorem hermitianRe_expand (t : ℝ) (u v : W) :
    hermitianRe H (u + ((t : ℝ) : ℂ) • v) (u + ((t : ℝ) : ℂ) • v)
      = hermitianRe H u u + 2 * t * hermitianRe H u v + t ^ 2 * hermitianRe H v v := by
  have hsq : hermitianRe H (((t : ℝ) : ℂ) • v) (((t : ℝ) : ℂ) • v) = t ^ 2 * hermitianRe H v v := by
    rw [hermitianRe, hermitianForm_smul_self hH, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      hermitianRe]
  have hsym : hermitianRe H (((t : ℝ) : ℂ) • v) u = hermitianRe H u (((t : ℝ) : ℂ) • v) :=
    hH.re_symm u (((t : ℝ) : ℂ) • v)
  have hexpand : hermitianRe H (u + ((t : ℝ) : ℂ) • v) (u + ((t : ℝ) : ℂ) • v)
      = hermitianRe H u u + hermitianRe H u (((t : ℝ) : ℂ) • v)
        + (hermitianRe H (((t : ℝ) : ℂ) • v) u
          + hermitianRe H (((t : ℝ) : ℂ) • v) (((t : ℝ) : ℂ) • v)) := by
    simp only [hermitianRe, hH.add_left, hH.add_right, Complex.add_re]
  rw [hexpand, hsym, hH.hermitianRe_real_smul, hsq]
  ring

/-- **The radical of a positive semi-definite Hermitian form.**  A null vector is annihilated by
the form entirely, not only in its real part. -/
theorem eq_zero_of_self_re_eq_zero (hpsd : ∀ x : W, 0 ≤ (H x x).re) {u : W}
    (hu : (H u u).re = 0) (v : W) : H u v = 0 := by
  have hpsd' : ∀ x : W, 0 ≤ hermitianRe H x x := hpsd
  have hre : hermitianRe H u v = 0 :=
    symmBilin_eq_zero_of_self_eq_zero (comb := fun t x y => x + ((t : ℝ) : ℂ) • y)
      (fun t x y => hH.hermitianRe_expand t x y) hpsd' hu v
  have hIu : hermitianRe H (Complex.I • u) (Complex.I • u) = 0 := by
    rw [hermitianRe, hermitianForm_smul_self hH, hu, mul_zero]
  have him : hermitianRe H (Complex.I • u) v = 0 :=
    symmBilin_eq_zero_of_self_eq_zero (comb := fun t x y => x + ((t : ℝ) : ℂ) • y)
      (fun t x y => hH.hermitianRe_expand t x y) hpsd' hIu v
  have hIv : (H (Complex.I • u) v).re = -(H u v).im := by
    rw [hH.smul_left]
    simp [Complex.mul_re]
  rw [hermitianRe, hIv] at him
  rw [Complex.ext_iff]
  constructor
  · exact hre
  · simpa using neg_eq_zero.mp him

end IsHermitianForm

/-- **Semi-definiteness of the Appell--Humbert form of a nonvanishing theta function.** -/
theorem hermitianForm_nonneg_of_theta {H : W → W → ℂ} (hH : IsHermitianForm H)
    {χ : W → ℂ} (hχ : ∀ γ, ‖χ γ‖ = 1) {θ : W → ℂ} (hdiff : Differentiable ℂ θ)
    (hHc : Continuous fun z => (H z z).re)
    (hθ : ∀ γ z : W, θ (z + γ) = appellHumbertFactor H χ γ z * θ z)
    {Γ : AddSubgroup W} {K : Set W} (hK : IsCompact K)
    (hcov : ∀ z : W, ∃ γ ∈ Γ, z - γ ∈ K) {z₀ : W} (hne : θ z₀ ≠ 0) (v : W) :
    0 ≤ (H v v).re := by
  obtain ⟨M, hM⟩ :=
    exists_bound_thetaNorm_of_compact_cover hH hχ hdiff.continuous hHc hθ hK hcov
  exact nonneg_re_of_thetaNorm_bounded_of_exists_ne_zero hH hdiff hM hne v

/-- **The necessary direction, assembled.**  A nondegenerate Hermitian form carrying a nonvanishing
theta function over a period group with a compact covering set is positive definite. -/
theorem hermitianForm_pos_of_theta_of_nondegenerate {H : W → W → ℂ} (hH : IsHermitianForm H)
    {χ : W → ℂ} (hχ : ∀ γ, ‖χ γ‖ = 1) {θ : W → ℂ} (hdiff : Differentiable ℂ θ)
    (hHc : Continuous fun z => (H z z).re)
    (hθ : ∀ γ z : W, θ (z + γ) = appellHumbertFactor H χ γ z * θ z)
    {Γ : AddSubgroup W} {K : Set W} (hK : IsCompact K)
    (hcov : ∀ z : W, ∃ γ ∈ Γ, z - γ ∈ K) {z₀ : W} (hne : θ z₀ ≠ 0)
    (hnd : ∀ x : W, x ≠ 0 → ∃ y, H x y ≠ 0) {x : W} (hx : x ≠ 0) :
    0 < (H x x).re := by
  have hpsd : ∀ v : W, 0 ≤ (H v v).re :=
    hermitianForm_nonneg_of_theta hH hχ hdiff hHc hθ hK hcov hne
  rcases (hpsd x).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy⟩ := hnd x hx
    exact hy (hH.eq_zero_of_self_re_eq_zero hpsd h.symm y)

end GaloisForLFunctions.HTGeometry
