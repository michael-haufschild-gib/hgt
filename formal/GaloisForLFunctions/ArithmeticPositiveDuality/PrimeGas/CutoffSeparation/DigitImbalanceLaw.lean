import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.RadixShellExpansion
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Centered base-`C` digit-imbalance remainder law and sharp oscillation envelope

For arbitrary integer cutoffs `X ≥ 1` with radix `C = tailRadix t j > 1` and `L = ⌊log_C X⌋`,
unrolling the shell recursion through depth `L` expresses `renormalizedCutoff t j X w` modulo
`O(X^(-Re w))` as `2 ζ(w) / (C^w - 1) + Δ_C(X) X^(-w)`, where

`Δ_C(X) = (⌊log_C X⌋ + 1) - 2 s_C(X) / (C - 1)`

is minus twice the mean-centered base-`C` digit sum of `X`.

Subtracting `Δ_C(X) X^(-w)` eliminates the logarithmic truncation loss uniformly across all `X ≥ 1`.
Conversely, explicit alternating-digit cutoffs `X_m → ∞` satisfy `Δ_C(X_m) = 0` for every radix
`C ≥ 2`, so at every zero of `ζ(w)` in `Re w > 0` the normalized cutoff modulus
`‖renormalizedCutoff t j X w‖ / (X^(-Re w) log_C X)` has upper limit `1` (attained along `C^K` and
`C^K - 1`) and lower limit `0` (attained along `X_m`).
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Filter MeasureTheory Set
open scoped Topology

/-- Mean-centered base-`C` digit imbalance `(⌊log_C X⌋ + 1) - 2 s_C(X) / (C - 1)`. -/
def digitImbalance (C X : ℕ) : ℝ :=
  ((Nat.log C X + 1 : ℕ) : ℝ) - 2 * ((C.digits X).sum : ℝ) / ((C : ℝ) - 1)

/-- Digit-balanced prime-gas cutoff, removing the base-`C` carry oscillation `Δ_C(X) X^(-w)`. -/
def digitBalancedCutoff (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℂ :=
  renormalizedCutoff t j X w - (digitImbalance (tailRadix t j).val X : ℂ) * (X : ℂ) ^ (-w)

private theorem shellCutoff_unroll (t : ExceptionalTime) (j M X : ℕ) (w : ℂ) :
    let C := tailRadix t j
    let q := heat w C
    shellCutoff t j X w =
      2 * (∑ i ∈ Finset.range M, q ^ (i + 1) * radialCutoff (X / C.val ^ (i + 1)) w) +
        q ^ M * shellCutoff t j (X / C.val ^ M) w := by
  dsimp only
  set C := tailRadix t j with hCdef
  set q := heat w C with hqdef
  induction M with
  | zero => simp
  | succ M ih =>
    have hrec := shell_cutoff_recursion t j (X / C.val ^ M) w
    dsimp only at hrec
    have hdiv : X / C.val ^ M / C.val = X / C.val ^ (M + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [ih, hrec, ← hCdef, ← hqdef, hdiv, Finset.sum_range_succ, pow_succ]
    ring

/-- Exact finite-row sum for `shellCutoff` at every integer cutoff `X`. -/
theorem shellCutoff_eq_sum_log (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    let C := tailRadix t j
    let q := heat w C
    shellCutoff t j X w =
      2 * ∑ i ∈ Finset.range (Nat.log C.val X),
        q ^ (i + 1) * radialCutoff (X / C.val ^ (i + 1)) w := by
  dsimp only
  let C := tailRadix t j
  have hC1 : 1 < C.val := radix_gt_one t j
  let L := Nat.log C.val X
  have hlt : X < C.val ^ (L + 1) := Nat.lt_pow_succ_log_self hC1 X
  have hdiv : X / C.val ^ (L + 1) = 0 := Nat.div_eq_of_lt hlt
  have hunroll := shellCutoff_unroll t j (L + 1) X w
  dsimp only at hunroll
  rw [hunroll, hdiv, shellCutoff_zero, mul_zero, add_zero, Finset.sum_range_succ,
    hdiv, radialCutoff_zero, mul_zero, add_zero]

/-- Exact base-`C` fractional remainder sum in terms of the digit sum `s_C(X)`. -/
theorem sum_mod_div_pow_eq {C : ℕ} (hC : 1 < C) (X : ℕ) :
    let L := Nat.log C X
    (∑ i ∈ Finset.range L, ((X % C ^ (i + 1) : ℕ) : ℝ) / (C : ℝ) ^ (i + 1)) =
      (((C.digits X).sum : ℝ) - (X : ℝ) * ((C : ℝ)⁻¹) ^ L) / ((C : ℝ) - 1) := by
  dsimp only
  let L := Nat.log C X
  have hCr1 : (1 : ℝ) < C := by exact_mod_cast hC
  have hC0 : (0 : ℝ) < C := by positivity
  have hc_sub : (C : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hCr1.ne'
  have hlt : X < C ^ (L + 1) := Nat.lt_pow_succ_log_self hC X
  have hdiv0 : X / C ^ (L + 1) = 0 := Nat.div_eq_of_lt hlt
  have hleg := Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := C) X
  rw [Finset.sum_range_succ, hdiv0, add_zero] at hleg
  have hleg_r : ((C : ℝ) - 1) * (∑ i ∈ Finset.range L, ((X / C ^ (i + 1) : ℕ) : ℝ)) =
      (X : ℝ) - ((C.digits X).sum : ℝ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hleg
    simp only [Nat.cast_mul, Nat.cast_sub hC.le, Nat.cast_one, Nat.cast_sum,
      Nat.cast_sub (Nat.digit_sum_le C X)] at hcast
    exact hcast
  have hmod : ∀ i ∈ Finset.range L,
      ((X % C ^ (i + 1) : ℕ) : ℝ) / (C : ℝ) ^ (i + 1) =
        (X : ℝ) * ((C : ℝ)⁻¹) ^ (i + 1) - ((X / C ^ (i + 1) : ℕ) : ℝ) := by
    intro i _
    have hpow_ne : (C : ℝ) ^ (i + 1) ≠ 0 := pow_ne_zero _ hC0.ne'
    have hdm : ((C ^ (i + 1) * (X / C ^ (i + 1)) + X % C ^ (i + 1) : ℕ) : ℝ) = (X : ℝ) := by
      exact_mod_cast Nat.div_add_mod X (C ^ (i + 1))
    push_cast at hdm
    rw [inv_pow]
    field_simp [hpow_ne]
    linarith
  have hgeom : (∑ i ∈ Finset.range L, ((C : ℝ)⁻¹) ^ (i + 1)) =
      (1 - ((C : ℝ)⁻¹) ^ L) / ((C : ℝ) - 1) := by
    simp_rw [pow_succ', ← Finset.mul_sum]
    have hinv_ne : (C : ℝ)⁻¹ - 1 ≠ 0 := by
      intro h; have := sub_eq_zero.mp h; exact hCr1.ne' (inv_eq_one.mp this)
    have hc_sub' : (1 : ℝ) - C ≠ 0 := sub_ne_zero.mpr hCr1.ne
    have hg := geom_sum_mul (C : ℝ)⁻¹ L
    have hsum : (∑ i ∈ Finset.range L, ((C : ℝ)⁻¹) ^ i) =
        (((C : ℝ)⁻¹) ^ L - 1) / ((C : ℝ)⁻¹ - 1) := (eq_div_iff hinv_ne).mpr hg
    rw [hsum]
    field_simp [hC0.ne', hc_sub, hc_sub', hinv_ne]
    ring
  rw [Finset.sum_congr rfl hmod, Finset.sum_sub_distrib, ← Finset.mul_sum, hgeom]
  field_simp [hc_sub]
  linear_combination -hleg_r

/-- Mean-value bound on `u^(-w) - a^(-w)` valid for all `0 < a ≤ u` and `Re w ≥ -1`, with no
size condition comparing `‖w‖` to `a`. -/
private theorem norm_cpow_neg_sub_le {a u : ℝ} (ha : 0 < a) (hau : a ≤ u)
    {w : ℂ} (hw : -1 ≤ w.re) :
    ‖(u : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ ≤ ‖w‖ * a ^ (-w.re - 1) * (u - a) := by
  by_cases hw0 : w = 0
  · subst w; simp
  have hwn : -w ≠ 0 := neg_ne_zero.mpr hw0
  have hz : (0 : ℝ) ∉ Set.uIcc a u := by
    rw [Set.uIcc_of_le hau]; intro h; linarith [h.1]
  have hexp_ne : -w - 1 ≠ -1 := fun h => hw0 (by linear_combination -h)
  have hprim : (∫ v in a..u, (v : ℂ) ^ (-w - 1)) =
      ((u : ℂ) ^ (-w) - (a : ℂ) ^ (-w)) / (-w) := by
    rw [integral_cpow (Or.inr ⟨hexp_ne, hz⟩), show -w - 1 + 1 = -w by ring]
  have hdiff : (u : ℂ) ^ (-w) - (a : ℂ) ^ (-w) = -w * ∫ v in a..u, (v : ℂ) ^ (-w - 1) := by
    rw [hprim]; field_simp [hwn]
  rw [hdiff, norm_mul, norm_neg, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg w)
  have hbd : ∀ v ∈ Set.uIoc a u, ‖(v : ℂ) ^ (-w - 1)‖ ≤ a ^ (-w.re - 1) := by
    intro v hv
    rw [Set.uIoc_of_le hau] at hv
    have hv0 : 0 < v := ha.trans hv.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv0, show (-w - 1).re = -w.re - 1 by simp]
    exact Real.rpow_le_rpow_of_nonpos ha hv.1.le (by linarith)
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rwa [abs_of_nonneg (sub_nonneg.mpr hau)] at hle

/-- Quadratic remainder bound for `(b^(1-w) - a^(1-w)) / (1 - w) - (b - a) a^(-w)`. -/
private theorem norm_cpow_one_sub_div_sub_linear_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {w : ℂ} (hw : -1 ≤ w.re) (hw1 : w ≠ 1) :
    ‖((b : ℂ) ^ (1 - w) - (a : ℂ) ^ (1 - w)) / (1 - w) - ((b - a : ℝ) : ℂ) * (a : ℂ) ^ (-w)‖ ≤
      ‖w‖ * a ^ (-w.re - 1) * (b - a) ^ 2 := by
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]
  have hprim : (∫ u in a..b, (u : ℂ) ^ (-w)) =
      ((b : ℂ) ^ (1 - w) - (a : ℂ) ^ (1 - w)) / (1 - w) := by
    rw [integral_cpow (Or.inr ⟨neg_injective.ne hw1, hz⟩), show -w + 1 = 1 - w by ring]
  have hconst : (∫ _u in a..b, (a : ℂ) ^ (-w)) = ((b - a : ℝ) : ℂ) * (a : ℂ) ^ (-w) := by
    rw [intervalIntegral.integral_const, Complex.real_smul]
  have hi1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-w)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro u hu
    exact (Complex.continuousAt_ofReal_cpow_const u (-w)
      (Or.inr (ha.trans_le hu.1).ne')).continuousWithinAt
  rw [← hprim, ← hconst, ← intervalIntegral.integral_sub hi1 intervalIntegrable_const]
  have hbd : ∀ u ∈ Set.uIoc a b,
      ‖(u : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ ≤ ‖w‖ * a ^ (-w.re - 1) * (b - a) := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    refine (norm_cpow_neg_sub_le ha hu.1.le hw).trans ?_
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2 a) (by positivity)
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hle
  calc ‖∫ x in a..b, ((x : ℂ) ^ (-w) - (a : ℂ) ^ (-w))‖
      ≤ ‖w‖ * a ^ (-w.re - 1) * (b - a) * (b - a) := hle
    _ = ‖w‖ * a ^ (-w.re - 1) * (b - a) ^ 2 := by ring

/-- Explicit `X`-independent constant bounding `‖digitBalancedCutoff - limit‖ · X^(Re w)`. -/
def digitImbalanceErrorConst (t : ExceptionalTime) (j : ℕ) (w : ℂ) : ℝ :=
  let C : ℝ := (tailRadix t j).val
  let q := heat w (tailRadix t j)
  ‖2 * q * riemannZeta w / (1 - q)‖ * C ^ w.re +
    2 * C / ((C - 1) * ‖1 - w‖) +
    (2 * C / (C - 1) + 1) +
    (C / (C - 1)) * (2 : ℝ) ^ (w.re + 1) *
      (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1)))

/-- All-cutoff centered digit-imbalance law: uniformly for every integer `X ≥ 1` and every
`Re w > 0`, `w ≠ 1`, subtracting `Δ_C(X) X^(-w)` reduces the truncation remainder to `O(X^(-Re w))`. -/
theorem norm_renormalizedCutoff_sub_digitImbalance_le (t : ExceptionalTime) (j : ℕ)
    {X : ℕ} (hX : 1 ≤ X) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let q := heat w (tailRadix t j)
    ‖digitBalancedCutoff t j X w - 2 * q * riemannZeta w / (1 - q)‖ ≤
      digitImbalanceErrorConst t j w * (X : ℝ) ^ (-w.re) := by
  dsimp only
  set C := tailRadix t j with hCdef
  set Cr : ℝ := (C.val : ℝ) with hCrdef
  set q := heat w C with hqdef
  set L := Nat.log C.val X with hLdef
  set Z := 2 * q * riemannZeta w / (1 - q) with hZdef
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < Cr := by rw [hCrdef]; exact_mod_cast hC1
  have hCr0 : (0 : ℝ) < Cr := by positivity
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hq_lt : ‖q‖ < 1 := heat_contraction C hC1 w hw
  have h1q : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr fun he => hq_lt.ne (by rw [← he, norm_one])
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have hc1_c : (C.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hC1.ne')
  have hc1_r : Cr - 1 ≠ 0 := sub_ne_zero.mpr hCr1.ne'
  have hCL_le : C.val ^ L ≤ X := Nat.pow_log_le_self C.val (by omega)
  have hX_lt_CL1 : X < C.val ^ (L + 1) := Nat.lt_pow_succ_log_self hC1 X
  -- Decompose each row `0 ≤ i < L`.
  let α (i : ℕ) : ℝ := ((X % C.val ^ (i + 1) : ℕ) : ℝ) / Cr ^ (i + 1)
  let remRow (i : ℕ) : ℂ :=
    2 * (q ^ (i + 1) * radialCutoff (X / C.val ^ (i + 1)) w) -
      (2 * riemannZeta w * q ^ (i + 1) +
        (2 * (X : ℂ) ^ (1 - w) / (1 - w)) * ((C.val : ℂ)⁻¹) ^ (i + 1) +
        ((1 - 2 * α i : ℝ) : ℂ) * (X : ℂ) ^ (-w))
  have hrow_bound : ∀ i ∈ Finset.range L,
      ‖remRow i‖ ≤
        (2 : ℝ) ^ (w.re + 1) * (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1))) *
          Cr ^ (i + 1) * (X : ℝ) ^ (-w.re - 1) := by
    intro i hi
    have hiL : i + 1 ≤ L := Finset.mem_range.mp hi
    set P : ℕ := C.val ^ (i + 1)
    have hP_pos : 0 < P := pow_pos C.pos (i + 1)
    have hPr_pos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_pos
    have hPr_eq : (P : ℝ) = Cr ^ (i + 1) := by simp [P, Cr]
    have hP_le_X : P ≤ X := (Nat.pow_le_pow_right C.pos hiL).trans hCL_le
    set Y : ℕ := X / P
    have hY1 : 1 ≤ Y := (Nat.le_div_iff_mul_le hP_pos).mpr (by omega)
    have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
    set b : ℝ := (X : ℝ) / (P : ℝ)
    have hdm : ((P * Y + X % P : ℕ) : ℝ) = (X : ℝ) := by exact_mod_cast Nat.div_add_mod X P
    push_cast at hdm
    have hb_eq : b = (Y : ℝ) + α i := by
      dsimp only [b, α]; rw [← hPr_eq]; field_simp [hPr_pos.ne']; linarith
    have hα0 : 0 ≤ α i := by dsimp only [α]; positivity
    have hα1 : α i ≤ 1 := by
      dsimp only [α]; rw [← hPr_eq, div_le_one hPr_pos]
      exact_mod_cast (Nat.mod_lt X hP_pos).le
    have hab : (Y : ℝ) ≤ b := by linarith
    have hb_sub : b - (Y : ℝ) = α i := by linarith
    -- Centred Bernoulli representation at `Y`.
    have hzeta := RHTower.zeta_eq_centredTruncated_of_re_pos hY1 hw hw1
    unfold RHTower.zetaCentredTruncated at hzeta
    have hws : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    have hw_div : (Y : ℂ) ^ (1 - w) / (w - 1) = -((Y : ℂ) ^ (1 - w) / (1 - w)) := by
      rw [ ← neg_div, div_eq_div_iff hws h1w ]; ring
    have hrad : radialCutoff Y w =
        riemannZeta w + (Y : ℂ) ^ (1 - w) / (1 - w) + (Y : ℂ) ^ (-w) / 2 +
          w * (w + 1) * RHTower.zetaBernoulliTail Y w := by
      rw [hw_div] at hzeta
      unfold radialCutoff
      linear_combination -hzeta
    -- Relate `q^(i+1) * b^(1-w)` to `P⁻¹ * X^(1-w)` and `q^(i+1) * Y^(-w)` to `(P*Y)^(-w)`.
    have hqi : q ^ (i + 1) = ((P : ℝ) : ℂ) ^ (-w) := by
      rw [Complex.ofReal_natCast]
      exact (nat_pow_cpow_neg C (i + 1) w).symm
    have hcancel := RHTower.cpow_neg_mul_div_cpow hPr_pos hXpos w
    have hPinv : ((P : ℝ) : ℂ)⁻¹ = ((C.val : ℂ)⁻¹) ^ (i + 1) := by
      rw [Complex.ofReal_natCast, show (P : ℂ) = (C.val : ℂ) ^ (i + 1) by simp [P], inv_pow]
    have hPY : q ^ (i + 1) * ((Y : ℝ) : ℂ) ^ (-w) = (((P * Y : ℕ) : ℝ) : ℂ) ^ (-w) := by
      rw [hqi, Nat.cast_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hPr_pos.le hYpos.le]
    have hsplit_rem : remRow i =
        -(2 * q ^ (i + 1) * (((b : ℂ) ^ (1 - w) - ((Y : ℝ) : ℂ) ^ (1 - w)) / (1 - w) -
            (α i : ℂ) * ((Y : ℝ) : ℂ) ^ (-w))) +
        ((1 - 2 * α i : ℝ) : ℂ) * ((((P * Y : ℕ) : ℝ) : ℂ) ^ (-w) - ((X : ℝ) : ℂ) ^ (-w)) +
        2 * q ^ (i + 1) * (w * (w + 1) * RHTower.zetaBernoulliTail Y w) := by
      dsimp only [remRow]
      change 2 * (q ^ (i + 1) * radialCutoff Y w) - _ = _
      rw [hrad]
      have hYcast : (Y : ℂ) = ((Y : ℝ) : ℂ) := by simp
      have hXcast : (X : ℂ) = ((X : ℝ) : ℂ) := by simp
      rw [hYcast, hXcast, ← hPinv]
      have hqb : q ^ (i + 1) * (b : ℂ) ^ (1 - w) = ((P : ℝ) : ℂ)⁻¹ * ((X : ℝ) : ℂ) ^ (1 - w) := by
        rw [hqi]; exact hcancel
      simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
      linear_combination (2 / (1 - w)) * hqb + (1 - 2 * (α i : ℂ)) * hPY
    -- Bound the three pieces using `X / 2 ≤ P * Y ≤ X`.
    have hPY_pos : (0 : ℝ) < (P * Y : ℕ) := by exact_mod_cast Nat.mul_pos hP_pos hY1
    have hPY_le : ((P * Y : ℕ) : ℝ) ≤ (X : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) (X % P)]
    have hPY_sub : (X : ℝ) - ((P * Y : ℕ) : ℝ) ≤ (P : ℝ) := by
      have hmod_lt : ((X % P : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast Nat.mod_lt X hP_pos
      push_cast; linarith
    have hX_le_2PY : (X : ℝ) / 2 ≤ ((P * Y : ℕ) : ℝ) := by
      have hmod_lt : ((X % P : ℕ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast (Nat.mod_lt X hP_pos).le
      have hPY_ge_P : (P : ℝ) ≤ ((P * Y : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_right P hY1
      push_cast at hPY_ge_P ⊢; linarith
    have hPY_rpow : (((P * Y : ℕ) : ℝ)) ^ (-w.re - 1) ≤
        (2 : ℝ) ^ (w.re + 1) * (X : ℝ) ^ (-w.re - 1) := by
      calc (((P * Y : ℕ) : ℝ)) ^ (-w.re - 1)
          ≤ ((X : ℝ) / 2) ^ (-w.re - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hX_le_2PY (by linarith)
        _ = (2 : ℝ) ^ (w.re + 1) * (X : ℝ) ^ (-w.re - 1) := by
            rw [Real.div_rpow hXpos.le (by norm_num), div_eq_mul_inv,
              ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              show -(-w.re - 1) = w.re + 1 by ring, mul_comm]
    have hqY_rpow : ‖q ^ (i + 1)‖ * (Y : ℝ) ^ (-w.re - 1) ≤
        (2 : ℝ) ^ (w.re + 1) * (P : ℝ) * (X : ℝ) ^ (-w.re - 1) := by
      have hqn : ‖q ^ (i + 1)‖ = (P : ℝ) ^ (-w.re) := by
        rw [hqi, Complex.norm_cpow_eq_rpow_re_of_pos hPr_pos, Complex.neg_re]
      have hfac : (P : ℝ) ^ (-w.re) * (Y : ℝ) ^ (-w.re - 1) =
          (P : ℝ) * (((P * Y : ℕ) : ℝ)) ^ (-w.re - 1) := by
        rw [Nat.cast_mul, Real.mul_rpow hPr_pos.le hYpos.le, ← mul_assoc,
          ← Real.rpow_one_add' hPr_pos.le (by linarith), show 1 + (-w.re - 1) = -w.re by ring]
      rw [hqn, hfac, mul_comm ((2 : ℝ) ^ (w.re + 1)) (P : ℝ), mul_assoc]
      exact mul_le_mul_of_nonneg_left hPY_rpow hPr_pos.le
    have hE1 : ‖-(2 * q ^ (i + 1) * (((b : ℂ) ^ (1 - w) - ((Y : ℝ) : ℂ) ^ (1 - w)) / (1 - w) -
          (α i : ℂ) * ((Y : ℝ) : ℂ) ^ (-w)))‖ ≤
        2 * (2 : ℝ) ^ (w.re + 1) * ‖w‖ * (P : ℝ) * (X : ℝ) ^ (-w.re - 1) := by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_ofNat]
      have hquad := norm_cpow_one_sub_div_sub_linear_le hYpos hab (by linarith) hw1
      rw [hb_sub] at hquad
      have hα2 : (α i) ^ 2 ≤ 1 := by nlinarith
      calc 2 * ‖q ^ (i + 1)‖ * _
          ≤ 2 * ‖q ^ (i + 1)‖ * (‖w‖ * (Y : ℝ) ^ (-w.re - 1) * 1) :=
            mul_le_mul_of_nonneg_left
              (hquad.trans (mul_le_mul_of_nonneg_left hα2 (by positivity))) (by positivity)
        _ = 2 * ‖w‖ * (‖q ^ (i + 1)‖ * (Y : ℝ) ^ (-w.re - 1)) := by ring
        _ ≤ 2 * ‖w‖ * ((2 : ℝ) ^ (w.re + 1) * (P : ℝ) * (X : ℝ) ^ (-w.re - 1)) :=
            mul_le_mul_of_nonneg_left hqY_rpow (by positivity)
        _ = _ := by ring
    have hE2 : ‖((1 - 2 * α i : ℝ) : ℂ) *
          ((((P * Y : ℕ) : ℝ) : ℂ) ^ (-w) - ((X : ℝ) : ℂ) ^ (-w))‖ ≤
        (2 : ℝ) ^ (w.re + 1) * ‖w‖ * (P : ℝ) * (X : ℝ) ^ (-w.re - 1) := by
      have h12 : |1 - 2 * α i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
      have hmv := norm_cpow_neg_sub_le hPY_pos hPY_le (w := w) (by linarith)
      calc |1 - 2 * α i| * ‖((X : ℝ) : ℂ) ^ (-w) - (((P * Y : ℕ) : ℝ) : ℂ) ^ (-w)‖
          ≤ 1 * (‖w‖ * (((P * Y : ℕ) : ℝ)) ^ (-w.re - 1) * (P : ℝ)) := by
            refine mul_le_mul h12 (hmv.trans ?_) (norm_nonneg _) zero_le_one
            exact mul_le_mul_of_nonneg_left hPY_sub (by positivity)
        _ ≤ 1 * (‖w‖ * ((2 : ℝ) ^ (w.re + 1) * (X : ℝ) ^ (-w.re - 1)) * (P : ℝ)) := by gcongr
        _ = _ := by ring
    have hE3 : ‖2 * q ^ (i + 1) * (w * (w + 1) * RHTower.zetaBernoulliTail Y w)‖ ≤
        (2 : ℝ) ^ (w.re + 1) * (‖w * (w + 1)‖ / (4 * (w.re + 1))) *
          (P : ℝ) * (X : ℝ) ^ (-w.re - 1) := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_mul]
      have hbY := norm_zetaBernoulliTail_le hY1 (w := w) (by linarith)
      have hwpos1 : 0 < w.re + 1 := by linarith
      calc 2 * ‖q ^ (i + 1)‖ * (‖w * (w + 1)‖ * ‖RHTower.zetaBernoulliTail Y w‖)
          ≤ 2 * ‖q ^ (i + 1)‖ * (‖w * (w + 1)‖ * ((Y : ℝ) ^ (-w.re - 1) / (8 * (w.re + 1)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hbY (norm_nonneg _)) (by positivity)
        _ = (‖w * (w + 1)‖ / (4 * (w.re + 1))) * (‖q ^ (i + 1)‖ * (Y : ℝ) ^ (-w.re - 1)) := by
            field_simp [hwpos1.ne']; ring
        _ ≤ (‖w * (w + 1)‖ / (4 * (w.re + 1))) *
              ((2 : ℝ) ^ (w.re + 1) * (P : ℝ) * (X : ℝ) ^ (-w.re - 1)) :=
            mul_le_mul_of_nonneg_left hqY_rpow (by positivity)
        _ = _ := by ring
    rw [hsplit_rem, ← hPr_eq]
    refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
    refine (add_le_add (add_le_add hE1 hE2) hE3).trans_eq ?_
    ring
  -- Sum the geometric series and combine with the boundary pieces.
  have hsum_P : (∑ i ∈ Finset.range L, Cr ^ (i + 1)) ≤ Cr / (Cr - 1) * (X : ℝ) := by
    simp_rw [pow_succ', ← Finset.mul_sum]
    have hg : (∑ i ∈ Finset.range L, Cr ^ i) = (Cr ^ L - 1) / (Cr - 1) :=
      (eq_div_iff hc1_r).mpr (geom_sum_mul Cr L)
    rw [hg]
    have hCL_r : Cr ^ L ≤ (X : ℝ) := by rw [hCrdef]; exact_mod_cast hCL_le
    have hpos_den : 0 < Cr - 1 := sub_pos.mpr hCr1
    calc Cr * ((Cr ^ L - 1) / (Cr - 1))
        ≤ Cr * (Cr ^ L / (Cr - 1)) := by gcongr; linarith
      _ ≤ Cr * ((X : ℝ) / (Cr - 1)) := by gcongr
      _ = Cr / (Cr - 1) * (X : ℝ) := by ring
  have hgeom_q : (∑ i ∈ Finset.range L, q ^ (i + 1)) = q * (1 - q ^ L) / (1 - q) := by
    simp_rw [pow_succ', ← Finset.mul_sum]
    have hg := geom_sum_mul q L
    have h1 : (∑ i ∈ Finset.range L, q ^ i) = (1 - q ^ L) / (1 - q) := by
      rw [eq_div_iff h1q]; linear_combination -hg
    rw [h1, mul_div_assoc]
  have hgeom_Cinv : (∑ i ∈ Finset.range L, ((C.val : ℂ)⁻¹) ^ (i + 1)) =
      (1 - ((C.val : ℂ)⁻¹) ^ L) / ((C.val : ℂ) - 1) := by
    simp_rw [pow_succ', ← Finset.mul_sum]
    have hc0 : (C.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
    have hc1_c_rev : (1 : ℂ) - C.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (by exact_mod_cast hC1.ne'))
    have hinv1 : (C.val : ℂ)⁻¹ - 1 ≠ 0 := by
      intro h; exact hc1_c (by have := sub_eq_zero.mp h; exact (inv_eq_one.mp this).symm ▸ sub_self 1)
    have hg := geom_sum_mul (C.val : ℂ)⁻¹ L
    rw [(eq_div_iff hinv1).mpr hg]
    field_simp [hc0, hc1_c, hc1_c_rev, hinv1]
    ring
  have hα_sum : ((∑ i ∈ Finset.range L, (1 - 2 * α i) : ℝ) : ℂ) =
      (digitImbalance C.val X : ℂ) +
        (((2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) - 1 : ℝ)) : ℂ) := by
    have hmod_sum := sum_mod_div_pow_eq hC1 X
    dsimp only at hmod_sum
    have hlin : (∑ i ∈ Finset.range L, (1 - 2 * α i)) =
        (L : ℝ) - 2 * ∑ i ∈ Finset.range L, α i := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        ← Finset.mul_sum]
    have hreal_eq : (∑ i ∈ Finset.range L, (1 - 2 * α i)) =
        digitImbalance C.val X + (2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) - 1) := by
      rw [hlin, show (∑ i ∈ Finset.range L, α i) =
        (((C.val.digits X).sum : ℝ) - (X : ℝ) * (Cr⁻¹) ^ L) / (Cr - 1) by
          simpa only [← hCrdef, ← hLdef] using hmod_sum]
      unfold digitImbalance
      rw [← hCrdef, ← hLdef, Nat.cast_add, Nat.cast_one]
      field_simp [hc1_r]
      ring
    rw [hreal_eq, Complex.ofReal_add]
  -- Assemble the algebraic identity for `digitBalancedCutoff - Z`.
  have halg : digitBalancedCutoff t j X w - Z =
      -Z * q ^ L -
        (2 / (((C.val : ℂ) - 1) * (1 - w))) * ((X : ℂ) ^ (1 - w) * ((C.val : ℂ)⁻¹) ^ L) +
        (((2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) - 1 : ℝ)) : ℂ) * (X : ℂ) ^ (-w) +
        ∑ i ∈ Finset.range L, remRow i := by
    have hshell := shellCutoff_eq_sum_log t j X w
    dsimp only at hshell
    rw [← hCdef, ← hqdef, ← hLdef] at hshell
    have hsum_rows : (∑ i ∈ Finset.range L, remRow i) =
        shellCutoff t j X w -
          (2 * riemannZeta w * (∑ i ∈ Finset.range L, q ^ (i + 1)) +
            (2 * (X : ℂ) ^ (1 - w) / (1 - w)) * (∑ i ∈ Finset.range L, ((C.val : ℂ)⁻¹) ^ (i + 1)) +
            ((∑ i ∈ Finset.range L, (1 - 2 * α i) : ℝ) : ℂ) * (X : ℂ) ^ (-w)) := by
      dsimp only [remRow]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hshell]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Complex.ofReal_sum]
    rw [hgeom_q, hgeom_Cinv, hα_sum] at hsum_rows
    rw [digitBalancedCutoff, renormalizedCutoff_eq, ← hCdef]
    have hz1 : 2 * riemannZeta w * (q * (1 - q ^ L) / (1 - q)) = Z * (1 - q ^ L) := by
      dsimp only [Z]; ring
    have hz2 : (2 / ((C.val : ℂ) - 1)) * ((X : ℂ) ^ (1 - w) / (1 - w)) -
        (2 * (X : ℂ) ^ (1 - w) / (1 - w)) * ((1 - ((C.val : ℂ)⁻¹) ^ L) / ((C.val : ℂ) - 1)) =
        (2 / (((C.val : ℂ) - 1) * (1 - w))) * ((X : ℂ) ^ (1 - w) * ((C.val : ℂ)⁻¹) ^ L) := by
      field_simp [hc1_c, h1w]; ring
    rw [hz1] at hsum_rows
    linear_combination -hsum_rows - hz2
  -- Bound each of the four pieces by `const * X^(-w.re)`.
  have hX_invL : (X : ℝ) * (Cr⁻¹) ^ L ≤ Cr := by
    have hlt' : (X : ℝ) ≤ Cr ^ (L + 1) := by rw [hCrdef]; exact_mod_cast hX_lt_CL1.le
    rw [inv_pow, mul_inv_le_iff₀ (pow_pos hCr0 L)]
    simpa only [pow_succ'] using hlt'
  have hqL_le : ‖q ^ L‖ ≤ Cr ^ w.re * (X : ℝ) ^ (-w.re) := by
    have hqn : ‖q ^ L‖ = (Cr ^ L) ^ (-w.re) := by
      rw [norm_pow, norm_heat, energy, ← hCrdef, ← Real.rpow_natCast,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        Real.rpow_def_of_pos (pow_pos hCr0 L), Real.log_pow]
      congr 1; ring
    have hX_div_C : (X : ℝ) / Cr ≤ Cr ^ L := by
      rw [div_le_iff₀ hCr0]
      have hlt' : (X : ℝ) ≤ Cr ^ (L + 1) := by rw [hCrdef]; exact_mod_cast hX_lt_CL1.le
      simpa only [pow_succ] using hlt'
    rw [hqn]
    calc (Cr ^ L) ^ (-w.re) ≤ ((X : ℝ) / Cr) ^ (-w.re) :=
          Real.rpow_le_rpow_of_nonpos (div_pos hXpos hCr0) hX_div_C (neg_nonpos.mpr hw.le)
      _ = Cr ^ w.re * (X : ℝ) ^ (-w.re) := by
          rw [Real.div_rpow hXpos.le hCr0.le, div_eq_mul_inv, ← Real.rpow_neg hCr0.le,
            neg_neg, mul_comm]
  have hB1 : ‖-Z * q ^ L‖ ≤ ‖Z‖ * Cr ^ w.re * (X : ℝ) ^ (-w.re) := by
    rw [norm_mul, norm_neg, mul_assoc]
    exact mul_le_mul_of_nonneg_left hqL_le (norm_nonneg Z)
  have hB2 : ‖(2 / (((C.val : ℂ) - 1) * (1 - w))) *
        ((X : ℂ) ^ (1 - w) * ((C.val : ℂ)⁻¹) ^ L)‖ ≤
      (2 * Cr / ((Cr - 1) * ‖1 - w‖)) * (X : ℝ) ^ (-w.re) := by
    have hnorm_c1 : ‖(C.val : ℂ) - 1‖ = Cr - 1 := by
      have : (C.val : ℂ) - 1 = ((Cr - 1 : ℝ) : ℂ) := by simp [Cr]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hCr1)]
    have hnorm_X1w : ‖(X : ℂ) ^ (1 - w)‖ = (X : ℝ) * (X : ℝ) ^ (-w.re) := by
      rw [show (X : ℂ) = ((X : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hXpos,
        show (1 - w).re = 1 + (-w.re) by simp; ring,
        Real.rpow_add hXpos, Real.rpow_one]
    have hnorm_invL : ‖((C.val : ℂ)⁻¹) ^ L‖ = (Cr⁻¹) ^ L := by
      rw [norm_pow, norm_inv, Complex.norm_natCast]
    rw [norm_mul, norm_div, norm_mul, Complex.norm_ofNat, hnorm_c1, norm_mul, hnorm_X1w, hnorm_invL]
    have hden_pos : 0 < (Cr - 1) * ‖1 - w‖ := mul_pos (sub_pos.mpr hCr1) (norm_pos_iff.mpr h1w)
    calc 2 / ((Cr - 1) * ‖1 - w‖) * ((X : ℝ) * (X : ℝ) ^ (-w.re) * (Cr⁻¹) ^ L)
        = (2 / ((Cr - 1) * ‖1 - w‖)) * ((X : ℝ) * (Cr⁻¹) ^ L) * (X : ℝ) ^ (-w.re) := by ring
      _ ≤ (2 / ((Cr - 1) * ‖1 - w‖)) * Cr * (X : ℝ) ^ (-w.re) := by gcongr
      _ = _ := by ring
  have hB3 : ‖(((2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) - 1 : ℝ)) : ℂ) * (X : ℂ) ^ (-w)‖ ≤
      (2 * Cr / (Cr - 1) + 1) * (X : ℝ) ^ (-w.re) := by
    have hnorm_Xw : ‖(X : ℂ) ^ (-w)‖ = (X : ℝ) ^ (-w.re) := by
      rw [show (X : ℂ) = ((X : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hXpos, Complex.neg_re]
    have habs : |2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) - 1| ≤ 2 * Cr / (Cr - 1) + 1 := by
      have hnonneg : 0 ≤ 2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) :=
        div_nonneg (by positivity) (sub_pos.mpr hCr1).le
      have hup : 2 * (X : ℝ) * (Cr⁻¹) ^ L / (Cr - 1) ≤ 2 * Cr / (Cr - 1) := by
        rw [mul_assoc 2]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX_invL zero_le_two) (sub_pos.mpr hCr1).le
      rw [abs_le]; constructor <;> linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnorm_Xw]
    exact mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg hXpos.le _)
  have hB4 : ‖∑ i ∈ Finset.range L, remRow i‖ ≤
      (Cr / (Cr - 1)) * (2 : ℝ) ^ (w.re + 1) *
        (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1))) * (X : ℝ) ^ (-w.re) := by
    let Krow := (2 : ℝ) ^ (w.re + 1) * (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1)))
    have hKrow0 : 0 ≤ Krow := by positivity
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hrow_bound).trans ?_
    have hpull : (∑ i ∈ Finset.range L, Krow * Cr ^ (i + 1) * (X : ℝ) ^ (-w.re - 1)) =
        Krow * (∑ i ∈ Finset.range L, Cr ^ (i + 1)) * (X : ℝ) ^ (-w.re - 1) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    change (∑ i ∈ Finset.range L, Krow * Cr ^ (i + 1) * (X : ℝ) ^ (-w.re - 1)) ≤ _
    rw [hpull]
    have hXrpow : (X : ℝ) * (X : ℝ) ^ (-w.re - 1) = (X : ℝ) ^ (-w.re) := by
      rw [← Real.rpow_one_add' hXpos.le (by linarith), show 1 + (-w.re - 1) = -w.re by ring]
    calc Krow * (∑ i ∈ Finset.range L, Cr ^ (i + 1)) * (X : ℝ) ^ (-w.re - 1)
        ≤ Krow * (Cr / (Cr - 1) * (X : ℝ)) * (X : ℝ) ^ (-w.re - 1) := by gcongr
      _ = (Cr / (Cr - 1)) * Krow * ((X : ℝ) * (X : ℝ) ^ (-w.re - 1)) := by ring
      _ = _ := by rw [hXrpow]; ring
  rw [halg]
  refine (((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl)).trans ?_
  have hB12 : ‖-Z * q ^ L‖ + ‖(2 / (((C.val : ℂ) - 1) * (1 - w))) *
        ((X : ℂ) ^ (1 - w) * ((C.val : ℂ)⁻¹) ^ L)‖ ≤
      (‖Z‖ * Cr ^ w.re + 2 * Cr / ((Cr - 1) * ‖1 - w‖)) * (X : ℝ) ^ (-w.re) := by
    linarith [hB1, hB2]
  refine (add_le_add (add_le_add hB12 hB3) hB4).trans_eq ?_
  unfold digitImbalanceErrorConst
  dsimp only [Z, q, Cr, C]
  ring

/-- Uniform bound on `|digitImbalance C X|`: at most the base-`C` digit length `⌊log_C X⌋ + 1`. -/
theorem abs_digitImbalance_le {C : ℕ} (hC : 1 < C) {X : ℕ} (hX : 1 ≤ X) :
    |digitImbalance C X| ≤ (Nat.log C X : ℝ) + 1 := by
  have hCr1 : (1 : ℝ) < C := by exact_mod_cast hC
  have hsum_le : ((C.digits X).sum : ℝ) ≤ ((C : ℝ) - 1) * ((Nat.log C X : ℝ) + 1) := by
    have hcard : (C.digits X).sum ≤ (C - 1) * (C.digits X).length := by
      have h := (C.digits X).sum_le_card_nsmul (C - 1) fun d hd => by
        have := Nat.digits_lt_base hC hd; omega
      exact le_trans h (by simp [nsmul_eq_mul, Nat.mul_comm])
    rw [Nat.length_digits _ _ hC (by omega)] at hcard
    have hc : ((C.digits X).sum : ℝ) ≤ (((C - 1) * (Nat.log C X + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    simpa only [Nat.cast_mul, Nat.cast_sub hC.le, Nat.cast_add, Nat.cast_one] using hc
  have hdiv_le : 2 * ((C.digits X).sum : ℝ) / ((C : ℝ) - 1) ≤ 2 * ((Nat.log C X : ℝ) + 1) := by
    rw [div_le_iff₀ (sub_pos.mpr hCr1)]
    linarith
  have hdiv_nn : 0 ≤ 2 * ((C.digits X).sum : ℝ) / ((C : ℝ) - 1) :=
    div_nonneg (by positivity) (sub_pos.mpr hCr1).le
  unfold digitImbalance
  rw [Nat.cast_add, Nat.cast_one, abs_le]
  constructor <;> linarith

/-- Explicit all-`X` truncation error bound for `renormalizedCutoff` on `Re w > 0`, `w ≠ 1`. -/
theorem norm_renormalizedCutoff_sub_limit_le (t : ExceptionalTime) (j : ℕ)
    {X : ℕ} (hX : 1 ≤ X) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    ‖renormalizedCutoff t j X w - 2 * q * riemannZeta w / (1 - q)‖ ≤
      (Real.logb C.val X + 1 + digitImbalanceErrorConst t j w) * (X : ℝ) ^ (-w.re) := by
  dsimp only
  let C := tailRadix t j
  let q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hbal := norm_renormalizedCutoff_sub_digitImbalance_le t j hX hw hw1
  dsimp only at hbal
  have hlog : (Nat.log C.val X : ℝ) ≤ Real.logb C.val X := Real.natLog_le_logb X C.val
  have hdimb : ‖(digitImbalance C.val X : ℂ) * (X : ℂ) ^ (-w)‖ ≤
      (Real.logb C.val X + 1) * (X : ℝ) ^ (-w.re) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, show (X : ℂ) = ((X : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hXpos, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right
      ((abs_digitImbalance_le hC1 hX).trans (by linarith)) (Real.rpow_nonneg hXpos.le _)
  have hsplit : renormalizedCutoff t j X w - 2 * q * riemannZeta w / (1 - q) =
      (digitBalancedCutoff t j X w - 2 * q * riemannZeta w / (1 - q)) +
        (digitImbalance C.val X : ℂ) * (X : ℂ) ^ (-w) := by
    unfold digitBalancedCutoff; dsimp only [C, q]; ring
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hbal hdimb).trans_eq (by ring))

/-- Explicit alternating-digit cutoff `X_m` in base `C` whose digits pair to `C - 1`. -/
def balancedCutoff (C : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (C - 1 - C / 2) + C * (C / 2 + C * balancedCutoff C m)

theorem balancedCutoff_bounds {C : ℕ} (hC : 1 < C) {m : ℕ} (hm : 1 ≤ m) :
    C ^ (2 * m - 1) ≤ balancedCutoff C m ∧ balancedCutoff C m < C ^ (2 * m) := by
  induction m with
  | zero => omega
  | succ m ih =>
    set d₁ := C / 2
    set d₀ := C - 1 - d₁
    have hd1_pos : 1 ≤ d₁ := Nat.div_pos (by omega) (by norm_num)
    have hd1_lt : d₁ < C := Nat.div_lt_self (by omega) (by norm_num)
    have hd0_lt : d₀ < C := by omega
    rcases m with _ | m
    · change C ^ 1 ≤ d₀ + C * (d₁ + C * 0) ∧ d₀ + C * (d₁ + C * 0) < C ^ 2
      rw [pow_one, mul_zero, add_zero]
      constructor
      · exact le_trans (by simpa only [mul_one] using Nat.mul_le_mul_left C hd1_pos)
          (Nat.le_add_left _ d₀)
      · calc d₀ + C * d₁ < C + C * d₁ := by omega
          _ = C * (d₁ + 1) := by ring
          _ ≤ C * C := Nat.mul_le_mul_left C hd1_lt
          _ = C ^ 2 := (sq C).symm
    · obtain ⟨hlo, hhi⟩ := ih (Nat.succ_pos m)
      change C ^ (2 * (m + 2) - 1) ≤ d₀ + C * (d₁ + C * balancedCutoff C (m + 1)) ∧
        d₀ + C * (d₁ + C * balancedCutoff C (m + 1)) < C ^ (2 * (m + 2))
      have hexp1 : 2 * (m + 2) - 1 = (2 * (m + 1) - 1) + 2 := by omega
      have hexp2 : 2 * (m + 2) = 2 * (m + 1) + 2 := by omega
      constructor
      · rw [hexp1, pow_add]
        have hm1 : C ^ (2 * (m + 1) - 1) * C ^ 2 ≤ balancedCutoff C (m + 1) * C ^ 2 :=
          Nat.mul_le_mul_right _ hlo
        nlinarith
      · rw [hexp2, pow_add]
        have hstep : balancedCutoff C (m + 1) + 1 ≤ C ^ (2 * (m + 1)) := hhi
        have hm2 : (balancedCutoff C (m + 1) + 1) * C ^ 2 ≤ C ^ (2 * (m + 1)) * C ^ 2 :=
          Nat.mul_le_mul_right _ hstep
        have htop : d₀ + C * d₁ < C ^ 2 := by
          calc d₀ + C * d₁ < C + C * d₁ := by omega
            _ = C * (d₁ + 1) := by ring
            _ ≤ C * C := Nat.mul_le_mul_left C hd1_lt
            _ = C ^ 2 := (sq C).symm
        nlinarith

theorem digitImbalance_balancedCutoff_eq_zero {C : ℕ} (hC : 1 < C) {m : ℕ} (hm : 1 ≤ m) :
    digitImbalance C (balancedCutoff C m) = 0 := by
  have hdsum : ∀ k : ℕ, (C.digits (balancedCutoff C k)).sum = k * (C - 1) := by
    intro k
    induction k with
    | zero => simp [balancedCutoff]
    | succ k ih =>
      set d₁ := C / 2
      set d₀ := C - 1 - d₁
      have hd1_pos : 1 ≤ d₁ := Nat.div_pos (by omega) (by norm_num)
      have hd1_lt : d₁ < C := Nat.div_lt_self (by omega) (by norm_num)
      have hd0_lt : d₀ < C := by omega
      have hinner_ne : d₁ + C * balancedCutoff C k ≠ 0 := by omega
      have hdig1 : C.digits (d₀ + C * (d₁ + C * balancedCutoff C k)) =
          d₀ :: C.digits (d₁ + C * balancedCutoff C k) :=
        Nat.digits_add C hC d₀ _ hd0_lt (Or.inr hinner_ne)
      have hdig2 : C.digits (d₁ + C * balancedCutoff C k) =
          d₁ :: C.digits (balancedCutoff C k) :=
        Nat.digits_add C hC d₁ _ hd1_lt (Or.inl (by omega))
      change (C.digits (d₀ + C * (d₁ + C * balancedCutoff C k))).sum = (k + 1) * (C - 1)
      rw [hdig1, hdig2, List.sum_cons, List.sum_cons, ih]
      have hd01 : d₀ + d₁ = C - 1 := by omega
      calc d₀ + (d₁ + k * (C - 1)) = (d₀ + d₁) + k * (C - 1) := by ring
        _ = (C - 1) + k * (C - 1) := by rw [hd01]
        _ = (k + 1) * (C - 1) := by ring
  obtain ⟨hlo, hhi⟩ := balancedCutoff_bounds hC hm
  have hlog : Nat.log C (balancedCutoff C m) = 2 * m - 1 := by
    rw [Nat.log_eq_iff (Or.inr ⟨hC, by
      have : 1 ≤ C ^ (2 * m - 1) := Nat.one_le_pow _ _ (by omega)
      omega⟩)]
    exact ⟨hlo, by simpa only [show 2 * m - 1 + 1 = 2 * m by omega] using hhi⟩
  have hCr1 : (1 : ℝ) < C := by exact_mod_cast hC
  have hc_sub : (C : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hCr1.ne'
  unfold digitImbalance
  rw [hlog, show 2 * m - 1 + 1 = 2 * m by omega, hdsum m]
  simp only [Nat.cast_mul, Nat.cast_sub hC.le, Nat.cast_one, Nat.cast_ofNat]
  field_simp [hc_sub]
  ring

/-- Sharp oscillation envelope at every zero of `ζ(w)` in `Re w > 0`: normalized by
`X^(-Re w) log_C X`, `‖renormalizedCutoff‖` is asymptotically bounded above by `1`, attains `1`
along `C^K`, and tends to `0` along `balancedCutoff C (m + 1)`. -/
theorem sharp_oscillation_envelope_at_zeta_zero (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hz : riemannZeta w = 0) :
    let C := tailRadix t j
    let normScale (X : ℕ) : ℝ := (X : ℝ) ^ (-w.re) * Real.logb C.val X
    (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ‖renormalizedCutoff t j X w‖ / normScale X ≤ 1 + ε) ∧
    Tendsto (fun K : ℕ => ‖renormalizedCutoff t j (C.val ^ K) w‖ / normScale (C.val ^ K))
      atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ =>
        ‖renormalizedCutoff t j (balancedCutoff C.val (m + 1)) w‖ /
          normScale (balancedCutoff C.val (m + 1)))
      atTop (𝓝 0) := by
  dsimp only
  let C := tailRadix t j
  let normScale (X : ℕ) : ℝ := (X : ℝ) ^ (-w.re) * Real.logb C.val X
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hCr0 : (0 : ℝ) < C.val := by positivity
  let E := digitImbalanceErrorConst t j w
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have hlog_top : Tendsto (fun X : ℕ => Real.logb C.val X) atTop atTop := by
      have hdiv : Tendsto (fun X : ℕ => Real.log X / Real.log C.val) atTop atTop :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
          (Real.log_pos hCr1)
      exact hdiv
    filter_upwards [eventually_ge_atTop C.val,
      hlog_top.eventually_ge_atTop (max 1 ((1 + |E|) / ε))] with X hXC hlogX
    have hX1 : 1 ≤ X := le_trans C.pos hXC
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have hlog_pos : 0 < Real.logb C.val X := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hlogX)
    have hb := norm_renormalizedCutoff_sub_limit_le t j hX1 hw hw1
    dsimp only at hb
    rw [hz, mul_zero, zero_div, sub_zero] at hb
    have hden_pos : 0 < normScale X := mul_pos (Real.rpow_pos_of_pos hXpos _) hlog_pos
    rw [div_le_iff₀ hden_pos]
    refine hb.trans ?_
    have hε_le : 1 + E ≤ ε * Real.logb C.val X := by
      have h1 : (1 + |E|) / ε ≤ Real.logb C.val X := (le_max_right _ _).trans hlogX
      have h2 : 1 + |E| ≤ ε * Real.logb C.val X := by
        rwa [div_le_iff₀ hε, mul_comm] at h1
      linarith [le_abs_self E]
    have hrpow_nn : 0 ≤ (X : ℝ) ^ (-w.re) := Real.rpow_nonneg hXpos.le _
    dsimp only [normScale]
    nlinarith
  · have hspike := ((zeta_zero_iff_radix_pow_spike t j hw hw1).mp hz).norm
    rw [norm_one] at hspike
    refine hspike.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK0
    have hqK_norm : ‖(heat w C) ^ K‖ = ((C.val ^ K : ℕ) : ℝ) ^ (-w.re) := by
      rw [norm_pow, norm_heat, energy, ← Real.rpow_natCast,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hCr0 K), Real.log_pow]
      ring_nf
    have hlogK : Real.logb C.val (C.val ^ K : ℕ) = (K : ℝ) := by
      rw [Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one hCr1, mul_one]
    rw [norm_div, norm_mul, Complex.norm_natCast, hqK_norm, hlogK, mul_comm (K : ℝ)]
  · -- Along `balancedCutoff C (m + 1)`, `digitImbalance = 0`, leaving `O(X^(-w.re))`, hence `O(1/m)`.
    have h0 : Tendsto (fun m : ℕ => E / (2 * (m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop.const_mul_atTop two_pos).atTop_add tendsto_const_nhds)
    refine squeeze_zero' (Eventually.of_forall fun m => by
      obtain ⟨hlo, _⟩ := balancedCutoff_bounds hC1 (Nat.succ_pos m)
      have hX1 : 1 ≤ balancedCutoff C.val (m + 1) :=
        (Nat.one_le_pow _ _ C.pos).trans hlo
      have hXpos : (0 : ℝ) < balancedCutoff C.val (m + 1) := by exact_mod_cast hX1
      have hlog_ge : (1 : ℝ) ≤ Real.logb C.val (balancedCutoff C.val (m + 1)) := by
        have hlo_r : (C.val : ℝ) ^ (2 * (m + 1) - 1) ≤ balancedCutoff C.val (m + 1) := by
          exact_mod_cast hlo
        have h1 : (C.val : ℝ) ≤ (C.val : ℝ) ^ (2 * (m + 1) - 1) := by
          simpa only [pow_one] using pow_le_pow_right₀ hCr1.le (by omega : 1 ≤ 2 * (m + 1) - 1)
        calc (1 : ℝ) = Real.logb C.val C.val := (Real.logb_self_eq_one hCr1).symm
          _ ≤ Real.logb C.val (balancedCutoff C.val (m + 1)) :=
            Real.logb_le_logb_of_le hCr1 hCr0 (h1.trans hlo_r)
      exact div_nonneg (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hXpos.le _) (zero_le_one.trans hlog_ge))) ?_ h0
    refine Eventually.of_forall fun m => ?_
    set X := balancedCutoff C.val (m + 1)
    obtain ⟨hlo, _⟩ := balancedCutoff_bounds hC1 (Nat.succ_pos m)
    have hX1 : 1 ≤ X := (Nat.one_le_pow _ _ C.pos).trans hlo
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have hbal := norm_renormalizedCutoff_sub_digitImbalance_le t j hX1 hw hw1
    dsimp only at hbal
    have hdimb0 := digitImbalance_balancedCutoff_eq_zero hC1 (Nat.succ_pos m)
    unfold digitBalancedCutoff at hbal
    rw [hdimb0, Complex.ofReal_zero, zero_mul, sub_zero, hz, mul_zero, zero_div, sub_zero] at hbal
    have hlog_ge : 2 * (m : ℝ) + 1 ≤ Real.logb C.val X := by
      have hlo_r : (C.val : ℝ) ^ (2 * m + 1) ≤ (X : ℝ) := by
        have hexp : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [← hexp]; exact_mod_cast hlo
      calc 2 * (m : ℝ) + 1
          = Real.logb C.val ((C.val : ℝ) ^ (2 * m + 1)) := by
              rw [Real.logb_pow, Real.logb_self_eq_one hCr1, mul_one]; push_cast; ring
        _ ≤ Real.logb C.val (X : ℝ) :=
            Real.logb_le_logb_of_le hCr1 (pow_pos hCr0 _) hlo_r
    have hE0 : 0 ≤ E := by
      have hrp : 0 < (X : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos hXpos _
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hbal) hrp
    calc ‖renormalizedCutoff t j X w‖ / ((X : ℝ) ^ (-w.re) * Real.logb C.val X)
        ≤ (E * (X : ℝ) ^ (-w.re)) / ((X : ℝ) ^ (-w.re) * (2 * (m : ℝ) + 1)) := by
          refine div_le_div₀ (mul_nonneg hE0 (Real.rpow_nonneg hXpos.le _)) hbal
            (mul_pos (Real.rpow_pos_of_pos hXpos _) (by positivity))
            (mul_le_mul_of_nonneg_left hlog_ge (Real.rpow_nonneg hXpos.le _))
      _ = E / (2 * (m : ℝ) + 1) := by
          have hrp : (X : ℝ) ^ (-w.re) ≠ 0 := (Real.rpow_pos_of_pos hXpos _).ne'
          field_simp [hrp]

#print axioms shellCutoff_eq_sum_log
#print axioms sum_mod_div_pow_eq
#print axioms norm_renormalizedCutoff_sub_digitImbalance_le
#print axioms norm_renormalizedCutoff_sub_limit_le
#print axioms digitImbalance_balancedCutoff_eq_zero
#print axioms sharp_oscillation_envelope_at_zeta_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
