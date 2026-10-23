import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingCenteredSemigroup
import GaloisForLFunctions.BezoutValuationIncidence.ResidueModeCompleteness
import Mathlib.Analysis.PSeries

/-!
# Residue modes in the receiver norm, and why continuation must read the source

The normalized residue modes `v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d` are total in `c₀`
(`BezoutValuationIncidence.normalizedResidueMode_dense_span`).  This module puts them in the
receiver norm `ℓ²` and reads off two consequences for damping continuation.

* **Eigenmodes** (`centeredOperator_normalizedResidueMode`): `C_η v_d = d^{−η} v_d` for every
  `η > 0`; the modes diagonalize the centered damping chain.
* **Receiver size** (`tsum_sq_normalizedResidueProfile_le`, `..._ge`): `ℓ²`-norm squares satisfy
  `(d − 1)/d² ≤ ‖v_d‖² ≤ 2/d`.  A mode carries mass `≍ 1/d` in the receiver norm against sup norm
  `1/d` in `c₀`.
* **Backward continuation is ill-posed** (`not_backward_stable_l2`, `not_backward_stable_c0`): for
  every `t > 0` no inequality `‖b‖ ≤ K ‖C_t b‖` holds, in `ℓ²` or in `c₀`; on `v_d` the ratio is
  `d^t`.  Transporting admission from a larger damping to a smaller one can therefore never be an
  operator estimate on the chain: it must use the specific source vector (the reciprocal `1/k`,
  `TheReceiverIsTheChainOrbitOfTheReciprocal`) and its Möbius coefficients.
* **The sign-blind threshold** (`summable_signBlind_iff`): `Σ_d d^{−ε} ‖v_d‖_{ℓ²}` converges exactly
  for `ε > 1/2`.  Summing the damped Möbius residue series with absolute values — the triangle
  inequality in the receiver norm — admits the source precisely above half damping and nowhere
  below: below half damping the signs of `μ` are the estimate.
-/

open Finset Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

private theorem c0_tendsto_zero (b : C₀(ℕ, ℝ)) : Tendsto (fun n => b n) atTop (𝓝 0) := by
  have h := b.zero_at_infty'
  rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at h

/-! ### Eigenmodes of the chain -/

theorem normalizedResidueProfile_eq_floor (d n : ℕ) :
    normalizedResidueProfile d n = arithmeticDampingFloorProfile d (n + 1) - 1 / (d : ℝ) := rfl

private theorem finiteAction_floor (η : ℝ) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    arithmeticDampingFiniteAction η (fun k => arithmeticDampingFloorProfile d (k + 1)) n =
      (d : ℝ) ^ (-η) * arithmeticDampingFloorProfile d (n + 1) := by
  have h := arithmeticDampingTransition_floorProfile η (Nat.succ_pos n) hd
  rw [RHTower.sum_Icc_eq_sum_range_shift] at h
  exact h

/-- **Residue modes are eigenvectors**: `C_η v_d = d^{−η} v_d`. -/
theorem centeredOperator_normalizedResidueMode {η : ℝ} (hη : 0 < η) {d : ℕ} (hd : 0 < d) :
    arithmeticDampingCenteredOperator hη (normalizedResidueMode d) =
      (d : ℝ) ^ (-η) • normalizedResidueMode d := by
  set c := ((d : ℝ) ^ (-η) - 1) / d - arithmeticDampingEntrancePair η (normalizedResidueMode d)
    with hc
  have hdiff : ∀ n, arithmeticDampingCenteredOperator hη (normalizedResidueMode d) n -
      (d : ℝ) ^ (-η) * normalizedResidueMode d n = c := by
    intro n
    rw [arithmeticDampingCenteredOperator_eq_finiteAction]
    have hb : (fun k => normalizedResidueMode d k) =
        fun k => arithmeticDampingFloorProfile d (k + 1) - 1 / (d : ℝ) := rfl
    change arithmeticDampingFiniteAction η (fun k => normalizedResidueMode d k) n - _ - _ = c
    rw [hb, arithmeticDampingFiniteAction_sub_const, finiteAction_floor η hd,
      normalizedResidueMode_apply, normalizedResidueProfile_eq_floor, hc]
    ring
  -- both sides vanish at infinity, so the constant difference is zero
  have ht : Tendsto (fun n => arithmeticDampingCenteredOperator hη (normalizedResidueMode d) n -
      (d : ℝ) ^ (-η) * normalizedResidueMode d n) atTop (𝓝 0) := by
    have := (c0_tendsto_zero (arithmeticDampingCenteredOperator hη (normalizedResidueMode d))).sub
      ((c0_tendsto_zero (normalizedResidueMode d)).const_mul ((d : ℝ) ^ (-η)))
    simpa using this
  have hc0 : c = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hdiff n).symm) ht
  ext n
  have := hdiff n
  rw [hc0, sub_eq_zero] at this
  simpa using this

/-! ### Receiver size of a mode -/

theorem abs_normalizedResidueProfile_le_inv_d {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |normalizedResidueProfile d n| ≤ 1 / (d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have he : (((n + 1) % d : ℕ) : ℝ) + (d : ℝ) * ((n + 1) / d : ℕ) = (n + 1 : ℕ) := by
    exact_mod_cast Nat.mod_add_div (n + 1) d
  have hform : normalizedResidueProfile d n =
      -(((n + 1) % d : ℕ) : ℝ) / ((d : ℝ) * (n + 1 : ℕ)) := by
    unfold normalizedResidueProfile
    field_simp
    nlinarith
  rw [hform, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (mul_pos hd' hn')]
  rw [div_le_div_iff₀ (mul_pos hd' hn') hd', one_mul]
  have : (((n + 1) % d : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.mod_le _ _
  nlinarith

theorem abs_normalizedResidueProfile_le_inv_n (d n : ℕ) :
    |normalizedResidueProfile d n| ≤ 1 / ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [normalizedResidueProfile_zero, abs_zero]; positivity
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have he : (((n + 1) % d : ℕ) : ℝ) + (d : ℝ) * ((n + 1) / d : ℕ) = (n + 1 : ℕ) := by
    exact_mod_cast Nat.mod_add_div (n + 1) d
  have hform : normalizedResidueProfile d n =
      -(((n + 1) % d : ℕ) : ℝ) / ((d : ℝ) * (n + 1 : ℕ)) := by
    unfold normalizedResidueProfile
    field_simp
    nlinarith
  rw [hform, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (mul_pos hd' hn')]
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hn' ⊢
  rw [div_le_div_iff₀ (mul_pos hd' hn') hn', one_mul]
  have : (((n + 1) % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt _ hd).le
  nlinarith

/-- Below its modulus a mode is the constant `−1/d`. -/
theorem normalizedResidueProfile_of_lt {d n : ℕ} (h : n + 1 < d) :
    normalizedResidueProfile d n = -1 / (d : ℝ) := by
  unfold normalizedResidueProfile
  rw [Nat.div_eq_of_lt h]
  simp only [Nat.cast_zero, zero_div, zero_sub]
  ring

/-- The comparison weight `1/d²` below the modulus and `1/(n(n+1))` above it. -/
private def modeMajorant (d n : ℕ) : ℝ :=
  if n + 1 ≤ d then 1 / (d : ℝ) ^ 2 else 1 / ((n : ℝ) * ((n : ℝ) + 1))

private theorem sq_le_modeMajorant {d : ℕ} (hd : 0 < d) (n : ℕ) :
    normalizedResidueProfile d n ^ 2 ≤ modeMajorant d n := by
  unfold modeMajorant
  split_ifs with h
  · have := abs_normalizedResidueProfile_le_inv_d hd n
    rw [← sq_abs, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have h1 := abs_normalizedResidueProfile_le_inv_n d n
    have h2 : normalizedResidueProfile d n ^ 2 ≤ (1 / ((n : ℝ) + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [div_pow, one_pow, one_div_le_one_div (by positivity) (by positivity)]
    nlinarith

private theorem sum_modeMajorant_le {d : ℕ} (hd : 0 < d) (N : ℕ) :
    ∑ n ∈ range N, modeMajorant d n ≤ 2 / (d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  -- below the modulus the sum is `N/d²`; above it, it telescopes to `2/d − 1/N`
  have hlow : ∀ N, N ≤ d → ∑ n ∈ range N, modeMajorant d n = N / (d : ℝ) ^ 2 := by
    intro N hN
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [modeMajorant, show N + 1 ≤ d by omega, if_true]
      push_cast
      ring
  have hhigh : ∀ k, ∑ n ∈ range (d + k), modeMajorant d n = 2 / (d : ℝ) - 1 / ((d + k : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero =>
      rw [add_zero, hlow d le_rfl]
      field_simp
      ring
    | succ k ih =>
      rw [← add_assoc, Finset.sum_range_succ, ih]
      simp only [modeMajorant, show ¬ (d + k + 1 ≤ d) by omega, if_false]
      have hk : (0 : ℝ) < ((d + k : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < d + k by omega)
      push_cast at hk ⊢
      field_simp
      ring
  rcases le_or_gt N d with hN | hN
  · rw [hlow N hN]
    rw [div_le_div_iff₀ (by positivity) hd']
    have : (N : ℝ) ≤ d := by exact_mod_cast hN
    nlinarith
  · obtain ⟨k, rfl⟩ : ∃ k, N = d + k := ⟨N - d, by omega⟩
    rw [hhigh k]
    have : (0 : ℝ) ≤ 1 / ((d + k : ℕ) : ℝ) := by positivity
    linarith

theorem summable_sq_normalizedResidueProfile (d : ℕ) :
    Summable fun n => normalizedResidueProfile d n ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  exact summable_of_sum_range_le (fun n => sq_nonneg _) fun N =>
    (sum_le_sum fun n _ => sq_le_modeMajorant hd n).trans (sum_modeMajorant_le hd N)

/-- **Upper receiver size**: `‖v_d‖²_{ℓ²} ≤ 2/d`. -/
theorem tsum_sq_normalizedResidueProfile_le {d : ℕ} (hd : 0 < d) :
    ∑' n, normalizedResidueProfile d n ^ 2 ≤ 2 / (d : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) fun N =>
    (sum_le_sum fun n _ => sq_le_modeMajorant hd n).trans (sum_modeMajorant_le hd N)

/-- **Lower receiver size**: `(d − 1)/d² ≤ ‖v_d‖²_{ℓ²}`. -/
theorem tsum_sq_normalizedResidueProfile_ge {d : ℕ} (hd : 1 ≤ d) :
    ((d : ℝ) - 1) / (d : ℝ) ^ 2 ≤ ∑' n, normalizedResidueProfile d n ^ 2 := by
  have h := (summable_sq_normalizedResidueProfile d).sum_le_tsum (range (d - 1))
    fun n _ => sq_nonneg _
  refine le_trans (le_of_eq ?_) h
  rw [sum_congr rfl fun n hn => by
    rw [normalizedResidueProfile_of_lt (by simp at hn; omega)]]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [Nat.cast_sub hd]
  push_cast
  field_simp

/-! ### Backward continuation is ill-posed -/

theorem normalizedResidueMode_ne_zero {d : ℕ} (hd : 2 ≤ d) : normalizedResidueMode d ≠ 0 := by
  intro h
  have := congrArg (fun b : C₀(ℕ, ℝ) => b 0) h
  simp only [normalizedResidueMode_apply, ZeroAtInftyContinuousMap.zero_apply] at this
  rw [normalizedResidueProfile_of_lt (by omega)] at this
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have : (-1 : ℝ) / d < 0 := div_neg_of_neg_of_pos (by norm_num) hd'
  linarith

private theorem exists_rpow_gt {t : ℝ} (ht : 0 < t) (K : ℝ) : ∃ d : ℕ, 2 ≤ d ∧ K < (d : ℝ) ^ t := by
  have h := tendsto_rpow_atTop ht
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((tendsto_atTop.mp (h.comp tendsto_natCast_atTop_atTop)) (K + 1))
  refine ⟨max M 2, le_max_right _ _, ?_⟩
  have := hM (max M 2) (le_max_left _ _)
  simp only [Function.comp_apply] at this
  linarith

/-- **No backward stability in `ℓ²`**: for every `t > 0` and every `K` some receiver-square-summable
`b` has `K Σ (C_t b)² < Σ b²`. -/
theorem not_backward_stable_l2 {t : ℝ} (ht : 0 < t) (K : ℝ) :
    ∃ b : C₀(ℕ, ℝ), Summable (fun n => b n ^ 2) ∧
      K * ∑' n, arithmeticDampingCenteredOperator ht b n ^ 2 < ∑' n, b n ^ 2 := by
  obtain ⟨d, hd2, hK⟩ := exists_rpow_gt (by linarith : (0 : ℝ) < 2 * t) K
  have hd : 0 < d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨normalizedResidueMode d, summable_sq_normalizedResidueProfile d, ?_⟩
  rw [centeredOperator_normalizedResidueMode ht hd]
  simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, normalizedResidueMode_apply, mul_pow]
  rw [tsum_mul_left]
  set S := ∑' n, normalizedResidueProfile d n ^ 2 with hS
  have hSpos : 0 < S := by
    have := tsum_sq_normalizedResidueProfile_ge (show 1 ≤ d by omega)
    have h1 : (0 : ℝ) < ((d : ℝ) - 1) / (d : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      exact div_pos (by linarith) (by positivity)
    linarith
  have hpow : ((d : ℝ) ^ (-t)) ^ 2 * (d : ℝ) ^ (2 * t) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le, ← Real.rpow_add hdpos]
    convert Real.rpow_zero (d : ℝ) using 2
    push_cast
    ring
  have hq : 0 < ((d : ℝ) ^ (-t)) ^ 2 := by positivity
  have : K * ((d : ℝ) ^ (-t)) ^ 2 < 1 := by
    calc K * ((d : ℝ) ^ (-t)) ^ 2 < (d : ℝ) ^ (2 * t) * ((d : ℝ) ^ (-t)) ^ 2 :=
          mul_lt_mul_of_pos_right hK hq
      _ = 1 := by rw [mul_comm]; exact hpow
  nlinarith

/-- **No backward stability in `c₀`**: for every `t > 0` and every `K` some `b` has
`K ‖C_t b‖ < ‖b‖`. -/
theorem not_backward_stable_c0 {t : ℝ} (ht : 0 < t) (K : ℝ) :
    ∃ b : C₀(ℕ, ℝ), K * ‖arithmeticDampingCenteredOperator ht b‖ < ‖b‖ := by
  obtain ⟨d, hd2, hK⟩ := exists_rpow_gt ht K
  have hd : 0 < d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨normalizedResidueMode d, ?_⟩
  rw [centeredOperator_normalizedResidueMode ht hd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hb : 0 < ‖normalizedResidueMode d‖ := norm_pos_iff.mpr (normalizedResidueMode_ne_zero hd2)
  have hpow : (d : ℝ) ^ (-t) * (d : ℝ) ^ t = 1 := by
    rw [← Real.rpow_add hdpos]; norm_num
  have hq : 0 < (d : ℝ) ^ (-t) := by positivity
  have : K * (d : ℝ) ^ (-t) < 1 := by
    calc K * (d : ℝ) ^ (-t) < (d : ℝ) ^ t * (d : ℝ) ^ (-t) := mul_lt_mul_of_pos_right hK hq
      _ = 1 := by rw [mul_comm]; exact hpow
  nlinarith

/-! ### The sign-blind threshold -/

/-- **Sign-blind threshold.**  `Σ_d d^{−ε} ‖v_d‖_{ℓ²}` converges exactly for `ε > 1/2`. -/
theorem summable_signBlind_iff (ε : ℝ) :
    Summable (fun d : ℕ => (d : ℝ) ^ (-ε) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) ↔
      1 / 2 < ε := by
  set a := fun d : ℕ => (d : ℝ) ^ (-ε) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)
    with ha
  have hnn : ∀ d, 0 ≤ a d := fun d => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  -- `a d ≍ d^{−ε−1/2}`
  have hupper : ∀ d : ℕ, 1 ≤ d → a d ≤ Real.sqrt 2 * (d : ℝ) ^ (-ε - 1 / 2) := by
    intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have h1 := tsum_sq_normalizedResidueProfile_le (show 0 < d by omega)
    have h2 : Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2) ≤
        Real.sqrt 2 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc _ ≤ Real.sqrt (2 / d) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 2 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_div' _ hdpos.le, Real.sqrt_eq_rpow (d : ℝ), Real.rpow_neg hdpos.le,
            div_eq_mul_inv]
    calc a d ≤ (d : ℝ) ^ (-ε) * (Real.sqrt 2 * (d : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.sqrt 2 * (d : ℝ) ^ (-ε - 1 / 2) := by
          rw [mul_left_comm, ← Real.rpow_add hdpos]; ring_nf
  have hlower : ∀ d : ℕ, 2 ≤ d → (d : ℝ) ^ (-ε - 1 / 2) / Real.sqrt 2 ≤ a d := by
    intro d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 := tsum_sq_normalizedResidueProfile_ge (show 1 ≤ d by omega)
    have h3 : 1 / (2 * (d : ℝ)) ≤ ∑' n, normalizedResidueProfile d n ^ 2 := by
      refine le_trans ?_ h1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (d : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt 2 ≤
        Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2) := by
      calc (d : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt 2 = Real.sqrt (1 / (2 * d)) := by
            rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_mul (by norm_num),
              Real.sqrt_eq_rpow (d : ℝ), Real.rpow_neg hdpos.le]
            field_simp
        _ ≤ _ := Real.sqrt_le_sqrt h3
    calc (d : ℝ) ^ (-ε - 1 / 2) / Real.sqrt 2 =
          (d : ℝ) ^ (-ε) * ((d : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt 2) := by
          rw [mul_div_assoc', ← Real.rpow_add hdpos]; ring_nf
      _ ≤ a d := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hp : Summable (fun d : ℕ => (d : ℝ) ^ (-ε - 1 / 2)) ↔ 1 / 2 < ε := by
    rw [Real.summable_nat_rpow]
    constructor <;> intro h <;> linarith
  constructor
  · intro hs
    rw [← hp]
    -- compare with `√2 · a d` from `d ≥ 2`
    have hs2 : Summable (fun d : ℕ => Real.sqrt 2 * a (d + 2)) :=
      ((summable_nat_add_iff 2).mpr hs).mul_left _
    have hc : Summable (fun d : ℕ => ((d + 2 : ℕ) : ℝ) ^ (-ε - 1 / 2)) := by
      refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_) hs2
      have := hlower (d + 2) (by omega)
      have hs2pos : 0 < Real.sqrt 2 := by positivity
      rw [div_le_iff₀ hs2pos] at this
      linarith
    exact (summable_nat_add_iff 2).mp hc
  · intro hε
    have hm : Summable (fun d : ℕ => Real.sqrt 2 * ((d + 1 : ℕ) : ℝ) ^ (-ε - 1 / 2)) :=
      ((summable_nat_add_iff 1).mpr (hp.mpr hε)).mul_left _
    have : Summable (fun d : ℕ => a (d + 1)) :=
      Summable.of_nonneg_of_le (fun d => hnn _) (fun d => hupper (d + 1) (by omega)) hm
    exact (summable_nat_add_iff 1).mp this

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
