import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The literal integer-grid pole defect

The left endpoint rule for `2 cosh(y/2)` on logarithmic integer cells has
weights `n⁻¹ᐟ² + δₙ`, with strictly positive summable `δₙ`. Its full spectral
defect tends to the real part of critical-line zeta plus the bounded cosine
correction. The error is at most `(6 + 2 |τ|) / sqrt(K+1)` for every cutoff
and frequency, so pairing with a finite first spectral moment is justified.

This is an Euler-summation bridge, not an energy-sign theorem. The external
positive-real zeta large-value obstruction is not formalized in this file.
Paper: docs/reports/weil-work/results/02-exposing-ray/GRID-DEFECT-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Complex
noncomputable section
namespace RHTower.ExposingRayGrid

/-- Exact pole mass of the cell `[log(j+1), log(j+2)]`. -/
def cellWeight (j : ℕ) : ℝ :=
  2*(Real.sqrt (j+2)-Real.sqrt (j+1)) +
    2*(1/Real.sqrt (j+1)-1/Real.sqrt (j+2))

/-- The positive difference from the critical Dirichlet coefficient. -/
def correctionCoeff (j : ℕ) : ℝ := cellWeight j-1/Real.sqrt (j+1)

private theorem sqrt_gap (j : ℕ) :
    Real.sqrt (j+2)-Real.sqrt (j+1) =
      1/(Real.sqrt (j+1)+Real.sqrt (j+2)) := by
  have ha : 0 < Real.sqrt (j+1) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < Real.sqrt (j+2) := Real.sqrt_pos.2 (by positivity)
  apply (eq_div_iff (ne_of_gt (add_pos ha hb))).2
  nlinarith [Real.sq_sqrt (show 0 ≤ (j:ℝ)+1 by positivity),
    Real.sq_sqrt (show 0 ≤ (j:ℝ)+2 by positivity)]

theorem correctionCoeff_eq (j : ℕ) :
    correctionCoeff j =
      (1+Real.sqrt (j+1)/(Real.sqrt (j+1)+Real.sqrt (j+2))) /
      (Real.sqrt (j+1)*Real.sqrt (j+2)*(Real.sqrt (j+1)+Real.sqrt (j+2))) := by
  have ha : 0 < Real.sqrt (j+1) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < Real.sqrt (j+2) := Real.sqrt_pos.2 (by positivity)
  have hab := sqrt_gap j
  unfold correctionCoeff cellWeight
  rw [hab]
  field_simp
  nlinarith [mul_self_nonneg (Real.sqrt (j+2)-Real.sqrt (j+1)),
    Real.sq_sqrt (show 0 ≤ (j:ℝ)+1 by positivity),
    Real.sq_sqrt (show 0 ≤ (j:ℝ)+2 by positivity)]

theorem correctionCoeff_pos (j : ℕ) : 0 < correctionCoeff j := by
  rw [correctionCoeff_eq]
  positivity

theorem correctionCoeff_le (j : ℕ) :
    correctionCoeff j ≤ 2*(1/Real.sqrt (j+1)-1/Real.sqrt (j+2)) := by
  have ha : 0 < Real.sqrt (j+1) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < Real.sqrt (j+2) := Real.sqrt_pos.2 (by positivity)
  have hab : Real.sqrt (j+1) ≤ Real.sqrt (j+2) := Real.sqrt_le_sqrt (by linarith)
  have h : 2/(Real.sqrt (j+1)+Real.sqrt (j+2)) ≤ 1/Real.sqrt (j+1) := by
    apply (div_le_div_iff₀ (add_pos ha hb) ha).2
    linarith
  unfold correctionCoeff cellWeight
  rw [sqrt_gap]
  simp only [div_eq_mul_inv] at h ⊢
  linarith

theorem summable_correctionCoeff : Summable correctionCoeff := by
  apply summable_of_sum_range_le (fun j => (correctionCoeff_pos j).le) (c := 2)
  intro K
  calc
    ∑ j ∈ Finset.range K, correctionCoeff j ≤
        ∑ j ∈ Finset.range K, 2*(1/Real.sqrt (j+1)-1/Real.sqrt (j+2)) :=
      Finset.sum_le_sum (fun j _ => correctionCoeff_le j)
    _ = 2*(1-1/Real.sqrt (K+1)) := by
      rw [← Finset.mul_sum]
      convert congrArg (fun x : ℝ => 2*x)
        (Finset.sum_range_sub' (fun j : ℕ => 1/Real.sqrt ((j:ℝ)+1)) K) using 1 <;>
        norm_num [Nat.cast_add, add_assoc]
    _ ≤ 2 := by
      have h : 0 ≤ 1/Real.sqrt ((K:ℝ)+1) := by positivity
      linarith

/-- An absolutely convergent cosine series with positive coefficients. -/
def correction (τ : ℝ) : ℝ :=
  ∑' j : ℕ, correctionCoeff j * Real.cos (τ*Real.log (j+1))

theorem summable_correction (τ : ℝ) :
    Summable (fun j : ℕ => correctionCoeff j * Real.cos (τ*Real.log (j+1))) := by
  apply Summable.of_norm_bounded summable_correctionCoeff
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (correctionCoeff_pos j)]
  exact mul_le_of_le_one_right (correctionCoeff_pos j).le (Real.abs_cos_le_one _)

theorem abs_correction_le (τ : ℝ) : |correction τ| ≤ correction 0 := by
  unfold correction
  simp only [zero_mul, Real.cos_zero, mul_one]
  refine (norm_tsum_le_tsum_norm (summable_correction τ).norm).trans ?_
  apply Summable.tsum_le_tsum _ (summable_correction τ).norm summable_correctionCoeff
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (correctionCoeff_pos j)]
  exact mul_le_of_le_one_right (correctionCoeff_pos j).le (Real.abs_cos_le_one _)

def criticalPoint (τ : ℝ) : ℂ := 1/2+(τ:ℂ)*Complex.I

private theorem criticalPoint_re (τ : ℝ) : (criticalPoint τ).re = 1/2 := by
  simp [criticalPoint]

private theorem criticalPoint_ne_zero (τ : ℝ) : criticalPoint τ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [criticalPoint_re] at this
  norm_num at this

private theorem one_sub_criticalPoint_ne_zero (τ : ℝ) : 1-criticalPoint τ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, criticalPoint_re, Complex.zero_re] at this
  norm_num at this

private theorem cpow_critical_re {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ((x:ℂ)^(-criticalPoint τ)).re =
      1/Real.sqrt x * Real.cos (τ*Real.log x) := by
  have hr : Real.exp (Real.log x/2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Complex.exp_re]
  simp only [criticalPoint, Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.one_re, Complex.one_im]
  norm_num
  rw [show Real.log x * (1/2:ℝ) = Real.log x/2 by ring, Real.exp_neg, hr,
    mul_comm (Real.log x) τ]

def polePrimitive (τ x : ℝ) : ℝ :=
  (((x:ℂ)^(1-criticalPoint τ))/(1-criticalPoint τ) -
    ((x:ℂ)^(-criticalPoint τ))/(criticalPoint τ)).re

/-- The actual quadrature defect, including the whole continuous pole integral. -/
def defect (K : ℕ) (τ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range K, cellWeight j * Real.cos (τ*Real.log (j+1))) -
    ∫ y in 0..Real.log (K+1), 2*Real.cosh (y/2)*Real.cos (τ*y)

private theorem critical_cpow_tendsto_zero (τ : ℝ) :
    Tendsto (fun K : ℕ => (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun K : ℕ => ((K:ℝ)+1)^(-(1/2:ℝ)))
  · intro K
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
      criticalPoint_re]
  · exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp
      (by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

private theorem polePrimitive_one (τ : ℝ) : polePrimitive τ 1 = 0 := by
  simp only [polePrimitive, Complex.ofReal_one, Complex.one_cpow, Complex.sub_re]
  simp [criticalPoint, Complex.normSq_apply]
  ring

theorem polePrimitive_eq_integral {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    polePrimitive τ x =
      ∫ y in 0..Real.log x, 2*Real.cosh (y/2)*Real.cos (τ*y) := by
  let s := criticalPoint τ
  let G : ℝ → ℂ := fun y => Complex.exp ((1-s)*(y:ℂ)) + Complex.exp ((-s)*(y:ℂ))
  have hg : ∀ y : ℝ, (G y).re = 2*Real.cosh (y/2)*Real.cos (τ*y) := by
    intro y
    simp [G, s, criticalPoint, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Real.cosh_eq, div_eq_mul_inv]
    ring_nf
  have hG : IntervalIntegrable G volume 0 (Real.log x) :=
    (show Continuous G by dsimp [G]; fun_prop).intervalIntegrable _ _
  have he : (∫ y in 0..Real.log x, G y) =
      ((x:ℂ)^(1-s)-1)/(1-s) + ((x:ℂ)^(-s)-1)/(-s) := by
    change (∫ y in 0..Real.log x, Complex.exp ((1-s)*(y:ℂ)) +
        Complex.exp ((-s)*(y:ℂ))) = _
    rw [intervalIntegral.integral_add
        (by exact (show Continuous (fun y : ℝ => Complex.exp ((1-s)*(y:ℂ))) by
          fun_prop).intervalIntegrable _ _)
        (by exact (show Continuous (fun y : ℝ => Complex.exp ((-s)*(y:ℂ))) by
          fun_prop).intervalIntegrable _ _),
      integral_exp_mul_complex (one_sub_criticalPoint_ne_zero τ),
      integral_exp_mul_complex (neg_ne_zero.mpr (criticalPoint_ne_zero τ))]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le]
    dsimp only [s]
    simp only [mul_comm]
  have hcomm := Complex.reCLM.intervalIntegral_comp_comm hG
  change (∫ y in 0..Real.log x, (G y).re) = (∫ y in 0..Real.log x, G y).re at hcomm
  simp_rw [hg] at hcomm
  rw [hcomm, he]
  have hp := polePrimitive_one τ
  simp only [polePrimitive, Complex.ofReal_one, Complex.one_cpow] at hp
  have ha : ((x:ℂ)^(1-s)-1)/(1-s) + ((x:ℂ)^(-s)-1)/(-s) =
      ((x:ℂ)^(1-s)/(1-s)-(x:ℂ)^(-s)/s) - (1/(1-s)-1/s) := by ring
  rw [ha, Complex.sub_re]
  change polePrimitive τ x = polePrimitive τ x - (1/(1-criticalPoint τ)-1/criticalPoint τ).re
  rw [hp, sub_zero]

private theorem sum_principal (K : ℕ) (τ : ℝ) :
    (∑ j ∈ Finset.range K, 1/Real.sqrt (j+1)*Real.cos (τ*Real.log (j+1))) =
      (∑ n ∈ Finset.Icc 1 K, ((n:ℝ):ℂ)^(-criticalPoint τ)).re := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), Complex.add_re, ← ih]
    congr 1
    rw [cpow_critical_re (by positivity)]
    simp

private theorem defect_eq (K : ℕ) (τ : ℝ) :
    defect K τ =
      ((∑ n ∈ Finset.Icc 1 (K+1), ((n:ℝ):ℂ)^(-criticalPoint τ)) -
        (((K:ℝ)+1:ℝ):ℂ)^(1-criticalPoint τ)/(1-criticalPoint τ)).re +
      ((((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ -
        (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)).re +
      ∑ j ∈ Finset.range K, correctionCoeff j * Real.cos (τ*Real.log (j+1)) := by
  have hsum : (∑ j ∈ Finset.range K, cellWeight j*Real.cos (τ*Real.log (j+1))) =
      (∑ j ∈ Finset.range K, 1/Real.sqrt (j+1)*Real.cos (τ*Real.log (j+1))) +
      ∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold correctionCoeff
    ring
  unfold defect
  rw [← polePrimitive_eq_integral (by positivity), hsum, sum_principal,
    Finset.sum_Icc_succ_top (by omega)]
  simp only [polePrimitive, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
    Complex.ofReal_one, Complex.sub_re, Complex.add_re]
  ring

/-- The pole-grid defect contains critical-line zeta, with an exact bounded correction. -/
theorem tendsto_defect (τ : ℝ) :
    Tendsto (fun K => defect K τ) atTop
      (𝓝 ((riemannZeta (criticalPoint τ)).re + correction τ)) := by
  have hs0 : 0 < (criticalPoint τ).re := by rw [criticalPoint_re]; norm_num
  have hs1 : criticalPoint τ ≠ 1 := by
    intro h
    exact one_sub_criticalPoint_ne_zero τ (by rw [h, sub_self])
  have hE := (tendsto_sum_cpow_sub_pow hs0 hs1).comp
    (tendsto_add_atTop_nat 1)
  have hZ := critical_cpow_tendsto_zero τ
  have hR := (hZ.div_const (criticalPoint τ)).sub hZ
  have hC := (summable_correction τ).hasSum.tendsto_sum_nat
  have h := ((Complex.continuous_re.continuousAt.tendsto.comp hE).add
    (Complex.continuous_re.continuousAt.tendsto.comp hR)).add hC
  simp only [zero_div, sub_zero, Complex.zero_re, add_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun K => by
    dsimp only [Function.comp_apply]
    rw [defect_eq K τ]
    simp [Nat.cast_add, Nat.cast_one]

private theorem polePrimitive_zero {x : ℝ} (hx : 0 < x) :
    polePrimitive 0 x = 2*Real.sqrt x-2/Real.sqrt x := by
  have hp : (x:ℂ)^(1/2:ℂ) = (Real.sqrt x:ℂ) := by
    simpa only [Real.sqrt_eq_rpow, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using (Complex.ofReal_cpow hx.le (1/2)).symm
  have hm := Complex.cpow_neg (x:ℂ) (1/2)
  simp only [polePrimitive, criticalPoint, Complex.ofReal_zero, zero_mul, add_zero]
  norm_num only at *
  rw [hp] at hm
  rw [hp, hm]
  simp [Complex.normSq_apply]
  field_simp

theorem cellWeight_eq_integral (j : ℕ) :
    cellWeight j = ∫ y in Real.log (j+1)..Real.log (j+2), 2*Real.cosh (y/2) := by
  have hcont : Continuous (fun y : ℝ => 2*Real.cosh (y/2)) := by fun_prop
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 (Real.log ((j:ℝ)+1)))
    (hcont.intervalIntegrable (Real.log ((j:ℝ)+1)) (Real.log ((j:ℝ)+2)))
  have h1 := polePrimitive_eq_integral (x := (j:ℝ)+1) (by positivity) 0
  have h2 := polePrimitive_eq_integral (x := (j:ℝ)+2) (by positivity) 0
  simp only [zero_mul, Real.cos_zero, mul_one] at h1 h2
  rw [← h1, ← h2, polePrimitive_zero (by positivity),
    polePrimitive_zero (by positivity)] at h
  unfold cellWeight
  simp only [div_eq_mul_inv] at h ⊢
  linarith

theorem defect_zero (K : ℕ) : defect K 0 = 0 := by
  have ht : (∑ j ∈ Finset.range K, cellWeight j) =
      2*Real.sqrt (K+1)-2/Real.sqrt (K+1) := by
    induction K with
    | zero => norm_num
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, cellWeight]
      push_cast
      ring_nf
  unfold defect
  simp only [zero_mul, Real.cos_zero, mul_one]
  have hp := polePrimitive_eq_integral (x := (K:ℝ)+1) (by positivity) 0
  simp only [zero_mul, Real.cos_zero, mul_one] at hp
  rw [← hp, polePrimitive_zero (by positivity), ht, sub_self]

/-- The total correction mass is fixed by the zeta value at one half. -/
theorem correction_zero_eq : correction 0 = -(riemannZeta (1/2)).re := by
  have h := tendsto_defect 0
  simp only [defect_zero, criticalPoint, Complex.ofReal_zero, zero_mul, add_zero] at h
  have he := tendsto_nhds_unique h tendsto_const_nhds
  linarith

theorem abs_correction_le_zeta (τ : ℝ) :
    |correction τ| ≤ -(riemannZeta (1/2)).re := by
  rw [← correction_zero_eq]
  exact abs_correction_le τ

theorem correctionCoeff_tail_le (K : ℕ) :
    (∑' j : ℕ, correctionCoeff (j+K)) ≤ 2/Real.sqrt (K+1) := by
  apply Real.tsum_le_of_sum_range_le (fun j => (correctionCoeff_pos (j+K)).le)
  intro M
  calc
    ∑ j ∈ Finset.range M, correctionCoeff (j+K) ≤
        ∑ j ∈ Finset.range M, 2*(1/Real.sqrt ((j+K:ℕ)+1)-
          1/Real.sqrt ((j+K:ℕ)+2)) :=
      Finset.sum_le_sum (fun j _ => correctionCoeff_le (j+K))
    _ = 2*(1/Real.sqrt (K+1)-1/Real.sqrt ((M+K:ℕ)+1)) := by
      rw [← Finset.mul_sum]
      convert congrArg (fun x : ℝ => 2*x)
        (Finset.sum_range_sub' (fun j : ℕ => 1/Real.sqrt ((j+K:ℕ)+1)) M) using 1 <;>
        norm_num [Nat.cast_add, add_assoc]
      simp only [add_left_comm]
      norm_num
    _ ≤ 2/Real.sqrt (K+1) := by
      have h : 0 ≤ 1/Real.sqrt ((M+K:ℕ)+1) := by positivity
      simp only [div_eq_mul_inv] at h ⊢
      linarith

theorem correction_tail_le (K : ℕ) (τ : ℝ) :
    |(∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1))) -
      correction τ| ≤ 2/Real.sqrt (K+1) := by
  have hs := (summable_correction τ).sum_add_tsum_nat_add K
  have htail := (summable_nat_add_iff K).2 (summable_correction τ)
  have he : (∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1))) -
      correction τ = -(∑' j : ℕ, correctionCoeff (j+K)*Real.cos (τ*Real.log ((j+K:ℕ)+1))) := by
    unfold correction
    linarith
  rw [he, abs_neg]
  calc
    _ ≤ ∑' j : ℕ, ‖correctionCoeff (j+K)*Real.cos (τ*Real.log ((j+K:ℕ)+1))‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' j : ℕ, correctionCoeff (j+K) := by
      apply Summable.tsum_le_tsum _ htail.norm ((summable_nat_add_iff K).2 summable_correctionCoeff)
      intro j
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (correctionCoeff_pos (j+K))]
      exact mul_le_of_le_one_right (correctionCoeff_pos (j+K)).le (Real.abs_cos_le_one _)
    _ ≤ _ := correctionCoeff_tail_le K

private def eulerError (K : ℕ) (τ : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 (K+1), ((n:ℝ):ℂ)^(-criticalPoint τ)) -
    (((K:ℝ)+1:ℝ):ℂ)^(1-criticalPoint τ)/(1-criticalPoint τ) -
    riemannZeta (criticalPoint τ)

private theorem norm_eulerError_le (K : ℕ) (τ : ℝ) :
    ‖eulerError K τ‖ ≤ 2*‖criticalPoint τ‖/Real.sqrt (K+1) := by
  have hs0 : 0 < (criticalPoint τ).re := by rw [criticalPoint_re]; norm_num
  have hs1 : criticalPoint τ ≠ 1 := by
    intro h
    exact one_sub_criticalPoint_ne_zero τ (by rw [h, sub_self])
  have he : eulerError K τ = criticalPoint τ *
      ∫ t in Ioi ((K+1:ℕ):ℝ), ((Int.fract t:ℝ):ℂ)*(t:ℂ)^(-(criticalPoint τ+1)) := by
    unfold eulerError
    rw [Sieve.riemannZeta_eq_sum_add_tail hs0 hs1 (show 1 ≤ K+1 by omega),
      show criticalPoint τ-1 = -(1-criticalPoint τ) by ring, div_neg]
    push_cast
    ring
  rw [he, norm_mul]
  calc
    _ ≤ ‖criticalPoint τ‖ * (((K+1:ℕ):ℝ)^(-(criticalPoint τ).re)/(criticalPoint τ).re) :=
      mul_le_mul_of_nonneg_left (Sieve.norm_integral_Ioi_fract_cpow_le hs0 (by omega))
        (norm_nonneg _)
    _ = _ := by
      rw [criticalPoint_re, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
      push_cast
      ring

private theorem norm_critical_bounds (τ : ℝ) :
    1/2 ≤ ‖criticalPoint τ‖ ∧ ‖criticalPoint τ‖ ≤ 1/2+|τ| := by
  constructor
  · have h := Complex.abs_re_le_norm (criticalPoint τ)
    rw [criticalPoint_re, abs_of_pos (by norm_num : (0:ℝ)<1/2)] at h
    exact h
  · simpa [criticalPoint, norm_mul] using
      (norm_add_le (1/2:ℂ) ((τ:ℂ)*Complex.I))

private theorem pole_endpoint_le (K : ℕ) (τ : ℝ) :
    |((((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ -
      (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)).re| ≤ 3/Real.sqrt (K+1) := by
  have hn : ‖(((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)‖ = 1/Real.sqrt (K+1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
      criticalPoint_re, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
  have hs : 0 < ‖criticalPoint τ‖ := lt_of_lt_of_le (by norm_num) (norm_critical_bounds τ).1
  have hi : 1/‖criticalPoint τ‖ ≤ 2 := by
    apply (div_le_iff₀ hs).2
    linarith [(norm_critical_bounds τ).1]
  calc
    _ ≤ ‖(((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ -
      (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ‖ +
      ‖(((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)‖ := norm_sub_le _ _
    _ = (1/Real.sqrt (K+1))*(1/‖criticalPoint τ‖)+1/Real.sqrt (K+1) := by
      rw [norm_div, hn]
      ring
    _ ≤ (1/Real.sqrt (K+1))*2+1/Real.sqrt (K+1) :=
      add_le_add (mul_le_mul_of_nonneg_left hi
        (show 0 ≤ 1/Real.sqrt ((K:ℝ)+1) by positivity)) le_rfl
    _ = _ := by ring

/-- Weighted uniform convergence, sufficient for integration against a finite first moment. -/
theorem defect_error_le (K : ℕ) (τ : ℝ) :
    |defect K τ - ((riemannZeta (criticalPoint τ)).re + correction τ)| ≤
      (6+2*|τ|)/Real.sqrt (K+1) := by
  have he := (Complex.abs_re_le_norm (eulerError K τ)).trans (norm_eulerError_le K τ)
  have hid : defect K τ - ((riemannZeta (criticalPoint τ)).re + correction τ) =
      (eulerError K τ).re +
      ((((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ -
        (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)).re +
      ((∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1))) - correction τ) := by
    rw [defect_eq]
    simp only [eulerError, Complex.sub_re]
    ring
  rw [hid]
  calc
    _ ≤ |(eulerError K τ).re +
        ((((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ -
          (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)).re| +
        |(∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1))) - correction τ| :=
      abs_add_le _ _
    _ ≤ (|(eulerError K τ).re| +
        |((((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)/criticalPoint τ -
          (((K:ℝ)+1:ℝ):ℂ)^(-criticalPoint τ)).re|) +
        |(∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1))) - correction τ| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (2*‖criticalPoint τ‖/Real.sqrt (K+1) + 3/Real.sqrt (K+1)) +
        2/Real.sqrt (K+1) :=
      add_le_add (add_le_add he (pole_endpoint_le K τ)) (correction_tail_le K τ)
    _ = (2*‖criticalPoint τ‖+5)/Real.sqrt (K+1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [(norm_critical_bounds τ).2])
      (Real.sqrt_nonneg _)

end RHTower.ExposingRayGrid
