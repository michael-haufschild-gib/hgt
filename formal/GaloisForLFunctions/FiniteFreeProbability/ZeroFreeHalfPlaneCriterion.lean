import GaloisForLFunctions.FiniteFreeProbability.ImaginaryPartDichotomy
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Finite free detection of zero-free half-planes

Expand the completed zeta function on a vertical line `Re s = σ`: `G_σ(w) = ξ(σ + iw)`. A zero `ρ`
of `ξ` becomes the zero `w_ρ = (ρ − σ)/i` of `G_σ`, with `Im w_ρ = σ − Re ρ`; so the zeros of `ξ`
to the right of `Re s = σ` are exactly the zeros of `G_σ` in the open lower half-plane.

**Theorem.** Let `R_d` be the reversed Jensen polynomials of the Taylor series of `G_σ` at `0`.

* If, for some `K` and infinitely many `d`, every root of `R_d` has imaginary part `≤ K`, then `ξ`
  has no zero with `Re ρ > σ`.
* If `ξ` has a zero with `Re ρ > σ`, there is `κ > 0` such that, for all large `d`, some root has
  imaginary part `≥ κ d`.

So a zero to the right of `Re s = σ` is visible as linear growth of the imaginary parts of the roots
of `R_d(G_σ)`, and sublinear growth along infinitely many degrees certifies the zero-free half-plane.
At `σ = 1/2` this is the Riemann hypothesis.
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- The Taylor coefficients at `0` of `w ↦ ξ(σ + iw)`. -/
def xiShiftCoeff (σ : ℝ) (k : ℕ) : ℂ :=
  iteratedDeriv k (fun w : ℂ => xi ((σ : ℂ) + I * w)) 0 / (k.factorial : ℂ)

theorem differentiable_xi_shift (σ : ℝ) : Differentiable ℂ fun w : ℂ => xi ((σ : ℂ) + I * w) :=
  xi_differentiable.comp (by fun_prop)

theorem hasSum_xiShiftCoeff (σ : ℝ) (z : ℂ) :
    HasSum (fun k => xiShiftCoeff σ k * z ^ k) (xi ((σ : ℂ) + I * z)) := by
  have h := Complex.hasSum_taylorSeries_of_entire (differentiable_xi_shift σ) 0 z
  refine h.congr_fun fun k => ?_
  simp only [xiShiftCoeff, sub_zero, smul_eq_mul]
  ring

theorem xiShiftCoeff_zero_ne (σ : ℝ) : xiShiftCoeff σ 0 ≠ 0 := by
  simpa [xiShiftCoeff] using xi_ne_zero_of_real σ

theorem summable_xiShiftCoeff (σ : ℝ) (R : ℝ) :
    Summable fun k => ‖xiShiftCoeff σ k‖ * R ^ k :=
  summable_norm_mul_pow_of_summable (fun z => (hasSum_xiShiftCoeff σ z).summable) R

/-- **Sublinear imaginary parts give a zero-free half-plane.** -/
theorem re_le_of_frequently_im_le {σ K : ℝ}
    (h : ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im ≤ K)
    {ρ : ℂ} (hρ : xi ρ = 0) : ρ.re ≤ σ := by
  have hw : ∑' k, xiShiftCoeff σ k * (-I * (ρ - σ)) ^ k = 0 := by
    rw [(hasSum_xiShiftCoeff σ _).tsum_eq,
      show (σ : ℂ) + I * (-I * (ρ - σ)) = ρ by ring_nf; rw [I_sq]; ring, hρ]
  have := im_nonneg_of_frequently_im_le (summable_xiShiftCoeff σ) (xiShiftCoeff_zero_ne σ) h hw
  simp only [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, sub_re,
    ofReal_re] at this
  linarith

/-- **A zero to the right of `Re s = σ` forces linear growth.** -/
theorem exists_linear_im_of_xi_zero {σ : ℝ} {ρ : ℂ} (hρ : xi ρ = 0) (hre : σ < ρ.re) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ d : ℕ in atTop,
      ∃ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x ∧ κ * d ≤ x.im := by
  have hw : ∑' k, xiShiftCoeff σ k * (-I * (ρ - σ)) ^ k = 0 := by
    rw [(hasSum_xiShiftCoeff σ _).tsum_eq,
      show (σ : ℂ) + I * (-I * (ρ - σ)) = ρ by ring_nf; rw [I_sq]; ring, hρ]
  refine eventually_exists_root_im_ge (summable_xiShiftCoeff σ) (xiShiftCoeff_zero_ne σ) hw ?_
  simp only [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, sub_re, ofReal_re]
  linarith

/-- **Sublinear growth gives a zero-free half-plane.** If for every `ε > 0`, along infinitely many
degrees, the roots of `R_d(ξ(σ + i·))` have imaginary parts `≤ εd`, then `ξ` has no zero with
`Re ρ > σ`. -/
theorem zeroFree_of_forall_frequently_im_le_mul {σ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im ≤ ε * d) :
    ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ := by
  intro ρ hρ
  by_contra hre
  push Not at hre
  obtain ⟨κ, hκ, hev⟩ := exists_linear_im_of_xi_zero hρ hre
  obtain ⟨d, hd, hall⟩ := ((h (κ / 2) (by positivity)).and_eventually
    (hev.and (eventually_gt_atTop 0))).exists
  obtain ⟨⟨x, hx, hxim⟩, hd0⟩ := hall
  have := hd x hx
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  nlinarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.re_le_of_frequently_im_le
#print axioms FiniteFreeProbability.zeroFree_of_forall_frequently_im_le_mul
