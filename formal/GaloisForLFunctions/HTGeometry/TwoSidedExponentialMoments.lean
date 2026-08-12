import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# Two-sided exponential moments

This module evaluates the elementary bilateral Gamma moments needed when an exponential tail
lower bound is converted into a lower bound for an even moment sequence.  For `r > 0`,

`∫ℝ |x|^(2n) exp (-r |x|) dx = 2 (2n)! / r^(2n+1)`.

The result is analytic: it uses the Euler Gamma integral on the positive ray and reflection of the
even integrand.  No numerical evaluation is involved.
-/

noncomputable section

open MeasureTheory Real Set

namespace HTGeometry

/-- Every natural power times a two-sided decaying exponential is integrable. -/
theorem integrable_abs_pow_mul_exp_neg_abs (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => |x| ^ n * Real.exp (-r * |x|)) := by
  let f : ℝ → ℝ := fun x => |x| ^ n * Real.exp (-r * |x|)
  have hpos : IntegrableOn f (Ioi 0) := by
    have h := GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi
      (σ := (n : ℝ)) (a := r)
      (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hr
    apply h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only [f]
    rw [abs_of_pos hx, Real.rpow_natCast]
    congr 2
    ring
  have hposClosed : IntegrableOn f (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hpos
  have hposClosed' : IntegrableOn f (Ici (-(0 : ℝ))) := by
    simpa only [neg_zero] using hposClosed
  have hnegRaw := hposClosed'.comp_neg_Iic (c := (0 : ℝ))
  have hneg : IntegrableOn f (Iic 0) := by
    apply hnegRaw.congr_fun (fun x _ => ?_) measurableSet_Iic
    simp only [f, abs_neg]
  have hunion : IntegrableOn f (Iic 0 ∪ Ioi 0) := hneg.union hpos
  rw [Iic_union_Ioi] at hunion
  simpa only [integrableOn_univ, f] using hunion

/-- Exact bilateral even moment of the two-sided exponential density. -/
theorem integral_abs_evenPow_mul_exp_neg_abs (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, |x| ^ (2 * n) * Real.exp (-r * |x|)) =
      2 * (2 * n).factorial / r ^ (2 * n + 1) := by
  let f : ℝ → ℝ := fun x => |x| ^ (2 * n) * Real.exp (-r * |x|)
  have hf : Integrable f := integrable_abs_pow_mul_exp_neg_abs (2 * n) hr
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    simp only [f, abs_neg]
  have hsplit : (∫ x : ℝ, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
    have h1 : (∫ x in Ioi (0 : ℝ), f (-x)) = ∫ x in Iic (0 : ℝ), f x := by
      have h := integral_comp_neg_Ioi (0 : ℝ) f
      rwa [neg_zero] at h
    have h2 : (∫ x in Ioi (0 : ℝ), f (-x)) = ∫ x in Ioi (0 : ℝ), f x :=
      setIntegral_congr_fun measurableSet_Ioi fun x _ => heven x
    have h3 := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (f := f) (b := 0)
      hf.integrableOn hf.integrableOn
    rw [← h3, ← h1, h2]
    ring
  rw [hsplit]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 * n : ℝ) + 1) (r := r) (by positivity) hr
  have hIoi : (∫ x in Ioi (0 : ℝ), f x) =
      (2 * n).factorial / r ^ (2 * n + 1) := by
    rw [show (∫ x in Ioi (0 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ), x ^ ((2 * n : ℝ) + 1 - 1) *
          Real.exp (-(r * x)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only [f]
      rw [abs_of_pos hx]
      have hexponent : ((2 * n : ℝ) + 1 - 1) = ((2 * n : ℕ) : ℝ) := by
        norm_num
      rw [hexponent, Real.rpow_natCast]
      congr 2
      ring]
    rw [hgamma]
    have hGammaArg : (2 * (n : ℝ) + 1) = ((2 * n : ℕ) : ℝ) + 1 := by
      norm_num
    rw [hGammaArg, Real.Gamma_nat_eq_factorial]
    have hpow : (1 / r) ^ (((2 * n : ℕ) : ℝ) + 1) =
        (1 / r) ^ (2 * n + 1 : ℕ) := by
      rw [show (((2 * n : ℕ) : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) by norm_num]
      exact Real.rpow_natCast _ _
    rw [hpow, one_div, inv_pow, div_eq_mul_inv]
    ring
  rw [hIoi]
  ring

end HTGeometry
