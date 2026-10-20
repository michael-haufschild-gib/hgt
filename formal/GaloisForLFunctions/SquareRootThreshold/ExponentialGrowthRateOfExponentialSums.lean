import GaloisForLFunctions.SquareRootThreshold.BoundedExponentialSumsHaveNoTopPole

/-!
# The growth rate of an exponential sum is the abscissa of its top poles

Let `F(v) = Σ_t q_t e^{λ_t v}` with `Σ_t |q_t| < ∞` and `Re λ_t ≤ A`. If `|F(v)| ≤ K e^{σv}` for
`v ≥ 0`, then `q_{t₁} = 0` for every exponent `λ_{t₁}` with `Re λ_{t₁} > σ` that is rightmost on its
horizontal line and separated from the other lines (`eq_zero_of_norm_tsum_exp_le_exp`).

The terms with `Re λ_t ≤ σ` contribute at most `Σ|q_t| e^{σv}`. What remains, multiplied by
`e^{−σv}`, is a bounded exponential sum with exponents `λ_t − σ` of positive real part, to which
`eq_zero_of_norm_tsum_exp_le` applies.

So the exponential growth rate `limsup (1/v) log |F(v)|` lies between the largest real part of a top
pole with nonzero coefficient and `sup Re λ_t`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

/-- **No top pole beyond the growth rate.** If `Σ_t |q_t| < ∞`, `Re λ_t ≤ A`, and
`|Σ_t q_t e^{λ_t v}| ≤ K e^{σv}` for `v ≥ 0`, then `q_{t₁} = 0` for every `t₁` with
`Re λ_{t₁} > σ` whose exponent is rightmost on its horizontal line, not shared, and `η`-separated
from the other lines. -/
theorem eq_zero_of_norm_tsum_exp_le_exp {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) {A : ℝ} (hA : ∀ t, (lam t).re ≤ A) {σ : ℝ} (t₁ : ι)
    (hσ : σ < (lam t₁).re) (htop : ∀ t, (lam t).im = (lam t₁).im → (lam t).re ≤ (lam t₁).re)
    (hinj : ∀ t, lam t = lam t₁ → t = t₁) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t, |(lam t).im - (lam t₁).im| < η → (lam t).im = (lam t₁).im) {K : ℝ}
    (hK : ∀ v : ℝ, 0 ≤ v → ‖∑' t, q t * cexp (lam t * v)‖ ≤ K * Real.exp (σ * v)) :
    q t₁ = 0 := by
  set S : Set ι := {t | σ < (lam t).re} with hS
  have ht₁S : t₁ ∈ S := hσ
  have hsum : ∀ v : ℝ, 0 ≤ v → Summable fun t => q t * cexp ((lam t - σ) * v) := fun v hv =>
    Summable.of_norm_bounded (hq.mul_left (Real.exp ((A - σ) * v))) fun t => by
      rw [norm_mul, Complex.norm_exp, mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have : ((lam t - σ) * (v : ℂ)).re = ((lam t).re - σ) * v := by simp
      rw [this]
      nlinarith [hA t]
  -- the shifted sum over `S` is bounded
  have hbound : ∀ v : ℝ, 0 ≤ v →
      ‖∑' t : S, q t * cexp ((lam t - σ) * v)‖ ≤ K + ∑' t, ‖q t‖ := by
    intro v hv
    have hsplit := (hsum v hv).tsum_subtype_add_tsum_subtype_compl S
    have htot : ∑' t, q t * cexp ((lam t - σ) * v) =
        cexp (-(σ * v)) * ∑' t, q t * cexp (lam t * v) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun t => ?_
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    have hnorm : ‖∑' t, q t * cexp ((lam t - σ) * v)‖ ≤ K := by
      rw [htot, norm_mul, Complex.norm_exp]
      have : (-((σ : ℂ) * v)).re = -(σ * v) := by simp
      rw [this]
      have h := hK v hv
      calc Real.exp (-(σ * v)) * ‖∑' t, q t * cexp (lam t * v)‖
          ≤ Real.exp (-(σ * v)) * (K * Real.exp (σ * v)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = K := by rw [mul_comm K, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
            one_mul]
    have hcompl : ‖∑' t : (Sᶜ : Set ι), q t * cexp ((lam t - σ) * v)‖ ≤ ∑' t, ‖q t‖ := by
      have hb : ∀ t : (Sᶜ : Set ι), ‖q t * cexp ((lam t - σ) * v)‖ ≤ ‖q t‖ := fun t => by
        rw [norm_mul, Complex.norm_exp]
        have : ((lam t - σ) * (v : ℂ)).re = ((lam t).re - σ) * v := by simp
        rw [this]
        have hle : (lam t).re ≤ σ := not_lt.mp t.2
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
      have hs : Summable fun t : (Sᶜ : Set ι) => ‖q t‖ := hq.subtype _
      refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs)).trans ?_
      exact (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs)
        hs).trans (hq.tsum_subtype_le _ _ fun _ => norm_nonneg _)
    have := norm_sub_le (∑' t, q t * cexp ((lam t - σ) * v))
      (∑' t : (Sᶜ : Set ι), q t * cexp ((lam t - σ) * v))
    rw [← hsplit, add_sub_cancel_right] at this
    rw [← hsplit] at hnorm
    linarith
  -- apply the bounded case to `S` with shifted exponents
  have h := eq_zero_of_norm_tsum_exp_le (ι := S) (lam := fun t => lam t - σ) (q := fun t => q t)
    (hq.subtype _) (A := A - σ)
    (fun t => ⟨by simpa using sub_pos.mpr (show σ < (lam t).re from t.2), by simpa using hA t⟩)
    ⟨t₁, ht₁S⟩ (fun t him => by
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero] at him ⊢
      linarith [htop t him])
    (fun t hl => Subtype.ext (hinj t (by simpa using hl))) hη
    (fun t hlt => by simpa using hsep t (by simpa using hlt)) hbound
  exact h

end GaloisForLFunctions.SquareRootThreshold
