import GaloisForLFunctions.RHTower.EisensteinHeckeOperator
import GaloisForLFunctions.RHTower.EisensteinLineZeroMean
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineEigenEquation
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Full Hecke growth beyond cusp-decay hypotheses

The actual positive-frequency Eisenstein Fourier-Bessel tail is nonzero,
periodic, mean zero, and uniformly decaying at the infinity cusp. It obeys
the local Laplace equation and the complete normalized Hecke equation.

At real parameter u = 1/4 its Laplace eigenvalue is 3/16, while every prime
Hecke eigenvalue is p^u + p^(-u) > 2. Its Hecke iterates have the exact
corresponding exponential growth. Thus these analytic and arithmetic
conditions without global modular invariance do not imply Ramanujan.

No function here is supplied as a level-one Maass cusp form. The final
existence theorem is a counterexample to the weakened sufficient conditions,
not to Ramanujan-Petersson. The separate inversion-defect identity concerns
the two-sign tail in the absolutely convergent parameter sector.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.EisensteinTailSpectrum

noncomputable section

def tail (u : ℝ) (x y : ℝ) : ℂ :=
  ∑' N : ℕ, eisensteinTailTerm false x y N (u : ℂ)

private def realTerm (u y : ℝ) (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) ^ u *
    (∑ d ∈ (N + 1).divisors, (d : ℝ) ^ (-2 * u)) * Real.sqrt y *
      realModifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * y) u

private theorem term_zero_eq (u : ℝ) {y : ℝ} (hy : 0 < y) (N : ℕ) :
    eisensteinTailTerm false 0 y N (u : ℂ) = (realTerm u y N : ℂ) := by
  rw [eisensteinTailTerm_eq_whittaker_mul_base]
  unfold whittakerCoeff divisorPowerSum baseTerm
  simp only [d4BMCompletedEisensteinFourierPhase, mul_zero, ofReal_zero,
    zero_mul, Complex.exp_zero, one_mul]
  have harg : 0 < 2 * Real.pi * ((N : ℝ) + 1) * y := by positivity
  rw [modifiedBesselKOrder_ofReal harg]
  rw [show (-2 * (u : ℂ)) = ((-2 * u : ℝ) : ℂ) by push_cast; ring]
  have hc (n : ℕ) (v : ℝ) : (n : ℂ) ^ (v : ℂ) = (((n : ℝ) ^ v : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_cpow (Nat.cast_nonneg n) v).symm
  simp_rw [hc]
  simp only [realTerm, Complex.ofReal_mul, Complex.ofReal_sum]
  ring

private theorem realTerm_pos (u : ℝ) {y : ℝ} (hy : 0 < y) (N : ℕ) :
    0 < realTerm u y N := by
  have hsum : 0 < ∑ d ∈ (N + 1).divisors, (d : ℝ) ^ (-2 * u) := by
    apply Finset.sum_pos'
    · intro d hd
      exact (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_mem_divisors hd) _).le
    · exact ⟨1, Nat.one_mem_divisors.mpr (Nat.succ_ne_zero N), by simp⟩
  exact mul_pos
    (mul_pos (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hsum)
      (Real.sqrt_pos.mpr hy))
    (realModifiedBesselKOrder_pos (by positivity) u)

theorem tail_re_pos (u : ℝ) {y : ℝ} (hy : 0 < y) : 0 < (tail u 0 y).re := by
  have hs := summable_eisensteinTailTerm false 0 hy (u : ℂ)
  have hsreal := hs.mapL Complex.reCLM
  simp only [term_zero_eq u hy, Complex.reCLM_apply, Complex.ofReal_re] at hsreal
  change 0 < Complex.reCLM (∑' N : ℕ, eisensteinTailTerm false 0 y N (u : ℂ))
  rw [Complex.reCLM.map_tsum hs]
  simp only [term_zero_eq u hy, Complex.reCLM_apply, Complex.ofReal_re]
  exact hsreal.tsum_pos (fun N => (realTerm_pos u hy N).le) 0 (realTerm_pos u hy 0)

theorem tail_periodic (u y : ℝ) : Function.Periodic (fun x => tail u x y) 1 := by
  intro x
  apply tsum_congr
  intro N
  simp only [eisensteinTailTerm, fourierPhase_add_one]

theorem tail_mean_zero (u : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ioc (0 : ℝ) 1, tail u x y = 0 :=
  setIntegral_Ioc_signedSqrtWhittakerTail false hy (u : ℂ)

theorem tail_rapid_decay (u x : ℝ) (w : ℂ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ w * tail u x y) atTop (𝓝 0) :=
  tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
    (u : ℂ) (u : ℂ) w false x 0 0

theorem tail_norm_le_exp (u x : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖tail u x y‖ ≤ Real.exp ((‖(u : ℂ)‖ + 1) ^ 2 / (2 * Real.pi)) *
      Real.exp (-(2 * Real.pi * y)) * tailSeriesSum (u : ℂ) := by
  simpa only [signedSqrtWhittakerTail_eq_tsum_term, tail] using
    norm_signedSqrtWhittakerTail_le_exp false x hy (u : ℂ)

theorem tail_zero_at_im_infty (u : ℝ) :
    UpperHalfPlane.IsZeroAtImInfty (fun z : UpperHalfPlane => tail u z.re z.im) := by
  have him : Tendsto (fun z : UpperHalfPlane => z.im) UpperHalfPlane.atImInfty atTop :=
    tendsto_comap
  have harg := him.const_mul_atTop (by positivity : 0 < 2 * Real.pi)
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
  have hlim := (hexp.const_mul (Real.exp ((‖(u : ℂ)‖ + 1) ^ 2 / (2 * Real.pi)))).mul_const
    (tailSeriesSum (u : ℂ))
  simp only [mul_zero, zero_mul] at hlim
  have hbound : ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖tail u z.re z.im‖ ≤ Real.exp ((‖(u : ℂ)‖ + 1) ^ 2 / (2 * Real.pi)) *
        Real.exp (-(2 * Real.pi * z.im)) * tailSeriesSum (u : ℂ) := by
    filter_upwards [him.eventually (eventually_ge_atTop (1 / 2 : ℝ))] with z hz
    exact tail_norm_le_exp u z.re hz
  change Tendsto (fun z : UpperHalfPlane => tail u z.re z.im)
    UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun z : UpperHalfPlane => norm_nonneg (tail u z.re z.im)) hbound hlim

private theorem tail_eq_weightedTail (u x y : ℝ) :
    tail u x y = weightedTail (u : ℂ) false x y := by
  rw [weightedTail_eq_signedSqrtWhittakerTail, signedSqrtWhittakerTail_eq_tsum_term]
  rfl

theorem tail_laplace_equation (u x : ℝ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 *
      (deriv (fun t => deriv (fun s => tail u s y) t) x +
        deriv (fun t => deriv (fun s => tail u x s) t) y) =
      ((1 / 4 - u ^ 2 : ℝ) : ℂ) * tail u x y := by
  simp_rw [tail_eq_weightedTail]
  have hx : (fun t => deriv (fun s => weightedTail (u : ℂ) false s y) t) =
      fun t => weightedTailX (u : ℂ) false t y := by
    funext t
    exact (hasDerivAt_weightedTail_x (u : ℂ) false t hy).deriv
  have hv : (fun t => deriv (fun s => weightedTail (u : ℂ) false x s) t) =ᶠ[𝓝 y]
      fun t => weightedTailY (u : ℂ) false x t := by
    filter_upwards [eventually_gt_nhds hy] with t ht
    exact (hasDerivAt_weightedTail_y (u : ℂ) false x ht).deriv
  rw [hx, (hasDerivAt_weightedTailX_x (u : ℂ) false x hy).deriv,
    hv.deriv_eq, (hasDerivAt_weightedTailY_y (u : ℂ) false x hy).deriv]
  have h := weightedTail_eigen (u : ℂ) false x hy
  push_cast
  linear_combination -h

def eigenvalue (p : ℕ) (u : ℝ) : ℝ := (p : ℝ) ^ u + (p : ℝ) ^ (-u)

theorem hecke_tail (u : ℝ) {p : ℕ} (hp : p.Prime) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeOp p (tail u) x y = (eigenvalue p u : ℂ) * tail u x y := by
  change heckeOp p (fun x y => ∑' N : ℕ, eisensteinTailTerm false x y N (u : ℂ)) x y = _
  rw [heckeOp_tail false hp x hy]
  congr 1
  simp only [eigenvalue, Complex.ofReal_add, Complex.ofReal_cpow (Nat.cast_nonneg p),
    Complex.ofReal_neg, Complex.ofReal_natCast]

theorem eigenvalue_gt_two {p : ℕ} (hp : 1 < p) {u : ℝ} (hu : 0 < u) :
    2 < eigenvalue p u := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have ha := Real.one_lt_rpow hpR hu
  have ha0 : 0 < (p : ℝ) ^ u := zero_lt_one.trans ha
  have hid : (p : ℝ) ^ u * ((p : ℝ) ^ u)⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
  have hsq : 0 < ((p : ℝ) ^ u - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr ha)
  rw [eigenvalue, Real.rpow_neg (le_trans zero_le_one hpR.le)]
  nlinarith

theorem hecke_iterate_tail (u : ℝ) {p : ℕ} (hp : p.Prime)
    (k : ℕ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (heckeOp p)^[k] (tail u) x y = (eigenvalue p u : ℂ) ^ k * tail u x y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hpy : 0 < p * y := mul_pos hpR hy
      have hyp : 0 < y / p := div_pos hy hpR
      rw [Function.iterate_succ_apply', heckeOp, ih _ hpy]
      simp_rw [ih _ hyp, ← Finset.mul_sum]
      calc
        _ = (eigenvalue p u : ℂ) ^ k * heckeOp p (tail u) x y := by
          unfold heckeOp
          ring
        _ = _ := by rw [hecke_tail u hp x hy]; ring

theorem hecke_iterate_div_pow_tendsto_atTop (u : ℝ) {p : ℕ} (hp : p.Prime)
    {r : ℝ} (hr : 0 < r) (hrmu : r < eigenvalue p u) :
    Tendsto (fun k : ℕ => ‖(heckeOp p)^[k] (tail u) 0 1‖ / r ^ k)
      atTop atTop := by
  have hmu0 : 0 < eigenvalue p u := hr.trans hrmu
  have hf : 0 < ‖tail u 0 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hpos := tail_re_pos u zero_lt_one
    rw [h, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  have hrate : 1 < eigenvalue p u / r := (lt_div_iff₀ hr).mpr (by simpa using hrmu)
  have hlim := (tendsto_pow_atTop_atTop_of_one_lt hrate).atTop_mul_const hf
  convert hlim using 1
  ext k
  rw [hecke_iterate_tail u hp k 0 zero_lt_one, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmu0, div_pow]
  ring

theorem normalized_hecke_iterate_tendsto_atTop {u : ℝ} (hu : 0 < u)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun k : ℕ => ‖(heckeOp p)^[k] (tail u) 0 1‖ / (2 : ℝ) ^ k)
      atTop atTop :=
  hecke_iterate_div_pow_tendsto_atTop u hp (by norm_num) (eigenvalue_gt_two hp.one_lt hu)

theorem symmetric_tail_inversion_defect {u : ℂ} (hu : 1 / 2 < u.re)
    (z : UpperHalfPlane) :
    d4BMCompletedEisensteinCuspTailPart .scalar u (ModularGroup.S • z).re
        (ModularGroup.S • z).im -
      d4BMCompletedEisensteinCuspTailPart .scalar u z.re z.im =
    d4BMCompletedEisensteinCuspConstantPart .scalar u z.im -
      d4BMCompletedEisensteinCuspConstantPart .scalar u (ModularGroup.S • z).im := by
  have h := eisensteinLineModel_S_of_re hu z
  unfold eisensteinLineModel d4BMCompletedEisensteinCuspLeg at h
  linear_combination h

/-- A closed witness that cusp decay, zero mean, the local Laplace equation,
and the full prime Hecke eigen-equations do not suffice without automorphy. -/
theorem exists_mean_zero_rapid_decay_supercritical_hecke_family :
    ∃ F : ℝ → ℝ → ℂ, ∃ mu : ℕ → ℝ,
      F 0 1 ≠ 0 ∧
      (∀ y : ℝ, Function.Periodic (fun x => F x y) 1) ∧
      (∀ y : ℝ, 0 < y → ∫ x in Ioc (0 : ℝ) 1, F x y = 0) ∧
      (∀ x : ℝ, ∀ w : ℂ,
        Tendsto (fun y : ℝ => (y : ℂ) ^ w * F x y) atTop (𝓝 0)) ∧
      UpperHalfPlane.IsZeroAtImInfty (fun z : UpperHalfPlane => F z.re z.im) ∧
      (∀ x y : ℝ, 0 < y → -(y : ℂ) ^ 2 *
        (deriv (fun t => deriv (fun s => F s y) t) x +
          deriv (fun t => deriv (fun s => F x s) t) y) = (3 / 16 : ℂ) * F x y) ∧
      (∀ p : ℕ, p.Prime → 2 < mu p ∧
        (∀ x y : ℝ, 0 < y → heckeOp p F x y = (mu p : ℂ) * F x y) ∧
        Tendsto (fun k : ℕ => ‖(heckeOp p)^[k] F 0 1‖ / (2 : ℝ) ^ k) atTop atTop) := by
  refine ⟨tail (1 / 4), fun p => eigenvalue p (1 / 4), ?_,
    tail_periodic _, fun y hy => tail_mean_zero _ hy, tail_rapid_decay _,
    tail_zero_at_im_infty _, ?_, ?_⟩
  · intro h
    have hpos := tail_re_pos (1 / 4) zero_lt_one
    rw [h, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  · intro x y hy
    convert tail_laplace_equation (1 / 4) x hy using 1
    norm_num
  · intro p hp
    exact ⟨eigenvalue_gt_two hp.one_lt (by norm_num),
      fun x y hy => hecke_tail _ hp x hy,
      normalized_hecke_iterate_tendsto_atTop (by norm_num) hp⟩

end
end RHTower.EisensteinTailSpectrum
