import GaloisForLFunctions.ArithmeticPolarization.TheFejerBarrierForCoupledContraction
import GaloisForLFunctions.HTGeometry.BohrAPWitnesses

/-!
# The leading line is positive

For a conjugation-symmetric polar configuration `G(s) = Σ_z c(z)/(s − z)` whose vertical sections
are positive definite, the rightmost line `Re z = σ_max` carries the trigonometric sum
`T(t) = Σ_{Re z = σ_max} c(z) cos(Im z · t)`.

* **The leading-line law** (`leadingSum_nonneg`): `T(t) ≥ 0` for every `t`, with no condition on
  the ordinates. The scale weight is `e^{σ_max t}(T(t) + o(1))` and nonnegative (Post–Widder); `T`
  is the real part of the trigonometric polynomial `Σ c(z) e^{i Im z · t}`, which is Bohr almost
  periodic, so every value of `T` returns at arbitrarily large `t` (`bohrAP_exists_large_return`).
* This removes the periodicity hypothesis of `leadingSum_nonneg_of_periodic`: the positive cone of
  polar configurations constrains its leading line by exactly the nonnegativity of an almost
  periodic trigonometric sum, for couplings by any finite set of ordinates.
-/

open Complex Finset Filter Topology Real BoundedContinuousFunction
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry

/-- Finite sums of characters are Bohr almost periodic. -/
theorem isBohrAP_finsetSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) :
    IsBohrAP (∑ i ∈ s, a i • bcfChar (lam i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert isBohrAP_const (0 : ℂ) using 1
    ext s; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ((isBohrAP_bcfChar (lam i)).smul (a i)).add ih

/-- The leading trigonometric polynomial `Σ_{Re z = σ} c(z) e^{i Im z · t}`. -/
def leadingPoly (S : Finset ℂ) (c : ℂ → ℝ) (σ : ℝ) : ℝ →ᵇ ℂ :=
  ∑ z ∈ S.filter (fun z => z.re = σ), ((c z : ℂ)) • bcfChar z.im

theorem re_leadingPoly (S : Finset ℂ) (c : ℂ → ℝ) (σ t : ℝ) :
    (leadingPoly S c σ t).re = leadingSum S c σ t := by
  rw [leadingPoly, leadingSum, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, bcfChar_apply,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **The leading-line law.** For a conjugation-symmetric polar configuration with positive-definite
vertical sections and no weighted point right of `σ_max`, the leading-line sum is nonnegative. -/
theorem leadingSum_nonneg {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σmax : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σmax) (t : ℝ) :
    0 ≤ leadingSum S c σmax t := by
  by_contra hneg
  rw [not_le] at hneg
  set δ := -leadingSum S c σmax t with hδ
  have hδ0 : 0 < δ := by linarith
  -- the remainder is eventually below `δ/2`, and the scale weight is nonnegative for `u > 0`
  have hev := (tendsto_offLeadingSum hmax).eventually (gt_mem_nhds (half_pos hδ0))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  -- a large return of the leading polynomial
  obtain ⟨τ, hτ, hdist⟩ := bohrAP_exists_large_return
    (isBohrAP_finsetSum (S.filter fun z => z.re = σmax) (fun z => (c z : ℂ)) fun z => z.im)
    (half_pos hδ0) (max N₀ 1 + |t|)
  set u := t + τ
  have hu₀ : N₀ ≤ u := by
    have := le_max_left N₀ 1; have := neg_abs_le t; simp only [u]; linarith
  have hu₁ : 0 < u := by
    have := le_max_right N₀ 1; have := neg_abs_le t; simp only [u]; linarith
  have hclose : |leadingSum S c σmax u - leadingSum S c σmax t| < δ / 2 := by
    rw [← re_leadingPoly, ← re_leadingPoly, ← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans_lt ?_
    have h := (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hdist
    rw [dist_eq_norm, bcfTranslate_apply] at h
    simpa [leadingPoly, u, add_comm] using h
  have hw := posDef_polarSum_laplaceWeight_nonneg hS_conj hc_conj hS_re hpd hu₁
  rw [polarScaleWeight_eq_leading] at hw
  have hR := hN₀ u hu₀
  have hT : leadingSum S c σmax u < -δ / 2 := by
    have := (abs_lt.mp hclose).2; linarith
  have : leadingSum S c σmax u + offLeadingSum S c σmax u < 0 := by linarith
  have := mul_neg_of_pos_of_neg (Real.exp_pos (σmax * u)) this
  linarith

end GaloisForLFunctions.ArithmeticPolarization
