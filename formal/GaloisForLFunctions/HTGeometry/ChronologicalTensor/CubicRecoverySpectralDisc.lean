import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryUniformGrowth
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryCommutator
import Mathlib.Analysis.Normed.Algebra.Spectrum
import GaloisForLFunctions.HTGeometry.VectorSequenceShift

/-!
# The spectrum of the complexified recovery multiplier

In the physical Hilbert basis `b_k`, the recovery multiplier acts by `U b_k = w_k b_{k+1}`,
`w_k = δ_{k+1}/δ_k`.  Its complexification is the weighted shift on `ℓ²(ℕ, ℂ)`,
`(U x)_0 = 0`, `(U x)_{k+1} = w_k x_k`: the coordinate map of the real Hilbert basis intertwines it
with the real multiplier, and `(x, y) ↦ ι x + i ι y` identifies `ℓ²(ℕ, ℂ)` with the
complexification.  Its powers are `(U^d x)_{j+d} = (δ_{j+d}/δ_j) x_j`, so

  `‖U^d‖ = sup_k δ_{k+d}/δ_k`,

and the uniform growth theorem with Gelfand's formula gives spectral radius `ρ`.  For `|μ| < ρ`
the vector `v = Σ μ^k (δ_0/δ_k) e_k` lies in `ℓ²` and `U^* v = μ v`; equivalently `U - μ̄` is not
surjective.  Hence the spectrum is exactly the closed disc `{|z| ≤ ρ}`.
-/

open Set Filter Metric
open scoped Real Topology ENNReal NNReal ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

/-- `ℓ²(ℕ, ℂ)`. -/
abbrev RecoveryL2 := VecSeq ℂ

theorem recoveryL2_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

/-- The shifted sums: `Σ_n (if d ≤ n then g(n - d) else 0) = Σ_j g j`. -/
theorem tsum_shift_eq {g : ℕ → ℝ} (hg : Summable g) (d : ℕ) :
    (Summable fun n => if d ≤ n then g (n - d) else 0) ∧
      ∑' n, (if d ≤ n then g (n - d) else 0) = ∑' j, g j := by
  induction d with
  | zero => simpa using hg
  | succ d ih =>
    have hs : Summable fun n => if d + 1 ≤ n then g (n - (d + 1)) else 0 := by
      refine (summable_nat_add_iff 1).mp ?_
      refine ih.1.congr fun n => ?_
      simp only [show n + 1 - (d + 1) = n - d by omega]
      by_cases h : d ≤ n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    refine ⟨hs, ?_⟩
    rw [hs.tsum_eq_zero_add, ← ih.2]
    simp only [show ¬ (d + 1 ≤ 0) by omega, if_false, zero_add]
    congr 1; ext n
    simp only [show n + 1 - (d + 1) = n - d by omega]
    by_cases h : d ≤ n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-! ### The weighted shift -/

/-- The weighted shift of sequences, `(x_k) ↦ (0, w_0 x_0, w_1 x_1, …)`. -/
def recoveryShiftSeq (x : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => (cubicRecoveryShiftWeight k : ℂ) * x k

theorem norm_recoveryShiftSeq_succ (x : ℕ → ℂ) (k : ℕ) :
    ‖recoveryShiftSeq x (k + 1)‖ = cubicRecoveryShiftWeight k * ‖x k‖ := by
  rw [recoveryShiftSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cubicRecoveryShiftWeight_bounds k).1]

theorem summable_recoveryShiftSeq (x : RecoveryL2) :
    Summable fun n => ‖recoveryShiftSeq x n‖ ^ 2 := by
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    (vecSeq_summable_sq x)
  rw [norm_recoveryShiftSeq_succ]
  have hw := cubicRecoveryShiftWeight_bounds n
  have hx := norm_nonneg (x n)
  exact pow_le_pow_left₀ (mul_nonneg hw.1.le hx) (mul_le_of_le_one_left hx (by linarith [hw.2])) 2

theorem tsum_recoveryShiftSeq (x : RecoveryL2) :
    ∑' n, ‖recoveryShiftSeq x n‖ ^ 2 = ∑' k, (cubicRecoveryShiftWeight k * ‖x k‖) ^ 2 := by
  rw [(summable_recoveryShiftSeq x).tsum_eq_zero_add]
  simp only [recoveryShiftSeq, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  congr 1; ext k
  rw [← norm_recoveryShiftSeq_succ]; rfl

/-- The underlying linear map of the complexified recovery shift. -/
def recoveryShiftLinear : RecoveryL2 →ₗ[ℂ] RecoveryL2 where
  toFun x := ⟨recoveryShiftSeq x, memℓp_of_summable_sq (summable_recoveryShiftSeq x)⟩
  map_add' x y := by
    ext n
    cases n with
    | zero => simp [recoveryShiftSeq]
    | succ k => simp [recoveryShiftSeq, mul_add]
  map_smul' c x := by
    ext n
    cases n with
    | zero => simp [recoveryShiftSeq]
    | succ k => simp [recoveryShiftSeq]; ring

theorem recoveryShiftLinear_apply (x : RecoveryL2) (n : ℕ) :
    (recoveryShiftLinear x : ℕ → ℂ) n = recoveryShiftSeq x n := rfl

theorem norm_recoveryShiftLinear_le (x : RecoveryL2) :
    ‖recoveryShiftLinear x‖ ≤ 1 / 4 * ‖x‖ := by
  have hsq : ‖recoveryShiftLinear x‖ ^ 2 ≤ (1 / 4 * ‖x‖) ^ 2 := by
    rw [vecSeq_norm_sq, mul_pow, vecSeq_norm_sq, ← tsum_mul_left]
    change ∑' n, ‖recoveryShiftSeq x n‖ ^ 2 ≤ _
    rw [tsum_recoveryShiftSeq]
    have hs : Summable fun k => (cubicRecoveryShiftWeight k * ‖x k‖) ^ 2 := by
      refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
        (vecSeq_summable_sq x)
      have hw := cubicRecoveryShiftWeight_bounds k
      have hx := norm_nonneg (x k)
      exact pow_le_pow_left₀ (mul_nonneg hw.1.le hx)
        (mul_le_of_le_one_left hx (by linarith [hw.2])) 2
    refine hs.tsum_le_tsum (fun k => ?_) ((vecSeq_summable_sq x).mul_left _)
    have hw := cubicRecoveryShiftWeight_bounds k
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hw.1]) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **The complexified recovery shift** `U` on `ℓ²(ℕ, ℂ)`. -/
def complexRecoveryShift : RecoveryL2 →L[ℂ] RecoveryL2 :=
  recoveryShiftLinear.mkContinuous (1 / 4) norm_recoveryShiftLinear_le

theorem complexRecoveryShift_apply_zero (x : RecoveryL2) :
    (complexRecoveryShift x : ℕ → ℂ) 0 = 0 := rfl

theorem complexRecoveryShift_apply_succ (x : RecoveryL2) (k : ℕ) :
    (complexRecoveryShift x : ℕ → ℂ) (k + 1) = (cubicRecoveryShiftWeight k : ℂ) * x k := rfl

/-! ### Powers and their norms -/

/-- The block weight `π(j,d) = δ_{j+d}/δ_j`. -/
def recoveryBlockWeight (j d : ℕ) : ℝ := cubicGradedRecoveryGap (j + d) / cubicGradedRecoveryGap j

theorem recoveryBlockWeight_pos (j d : ℕ) : 0 < recoveryBlockWeight j d :=
  div_pos (cubicGradedRecoveryGap_positive _) (cubicGradedRecoveryGap_positive _)

theorem recoveryBlockWeight_succ (j d : ℕ) :
    recoveryBlockWeight j (d + 1) = cubicRecoveryShiftWeight (j + d) * recoveryBlockWeight j d := by
  unfold recoveryBlockWeight cubicRecoveryShiftWeight
  rw [← add_assoc]
  field_simp [(cubicGradedRecoveryGap_positive (j + d)).ne']

theorem complexRecoveryShift_pow_apply (d : ℕ) (x : RecoveryL2) (n : ℕ) :
    ((complexRecoveryShift ^ d) x : ℕ → ℂ) n =
      if d ≤ n then (recoveryBlockWeight (n - d) d : ℂ) * x (n - d) else 0 := by
  induction d generalizing n with
  | zero => simp [recoveryBlockWeight, (cubicGradedRecoveryGap_positive n).ne']
  | succ d ih =>
    rw [pow_succ']
    change (complexRecoveryShift ((complexRecoveryShift ^ d) x) : ℕ → ℂ) n = _
    cases n with
    | zero => rw [complexRecoveryShift_apply_zero, if_neg (by omega)]
    | succ m =>
      rw [complexRecoveryShift_apply_succ, ih m]
      by_cases h : d ≤ m
      · rw [if_pos h, if_pos (by omega), show m + 1 - (d + 1) = m - d by omega,
          recoveryBlockWeight_succ, show m - d + d = m by omega]
        push_cast; ring
      · rw [if_neg h, if_neg (by omega), mul_zero]

theorem recoveryBlockWeight_le_one (j d : ℕ) : recoveryBlockWeight j d ≤ 1 := by
  induction d with
  | zero => simp [recoveryBlockWeight, (cubicGradedRecoveryGap_positive j).ne']
  | succ d ih =>
    rw [recoveryBlockWeight_succ]
    have hw := cubicRecoveryShiftWeight_bounds (j + d)
    have hp := recoveryBlockWeight_pos j d
    nlinarith

theorem norm_complexRecoveryShift_pow_sq (d : ℕ) (x : RecoveryL2) :
    ‖(complexRecoveryShift ^ d) x‖ ^ 2 = ∑' j, (recoveryBlockWeight j d * ‖x j‖) ^ 2 := by
  have hg : Summable fun j => (recoveryBlockWeight j d * ‖x j‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
      (vecSeq_summable_sq x)
    have h1 := recoveryBlockWeight_le_one j d
    have h0 := recoveryBlockWeight_pos j d
    have hx := norm_nonneg (x j)
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  rw [vecSeq_norm_sq, ← (tsum_shift_eq hg d).2]
  congr 1; ext n
  rw [complexRecoveryShift_pow_apply]
  split_ifs with h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (recoveryBlockWeight_pos _ _)]
  · simp

/-- **`‖U^d‖ = sup_k δ_{k+d}/δ_k`.** -/
theorem norm_complexRecoveryShift_pow {d : ℕ} (hd : 1 ≤ d) :
    ‖complexRecoveryShift ^ d‖ = cubicRecoveryUniformGrowth d := by
  have hG := cubicRecoveryUniformGrowth_pos hd
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ hG.le fun x => ?_
    have hsq : ‖(complexRecoveryShift ^ d) x‖ ^ 2 ≤ (cubicRecoveryUniformGrowth d * ‖x‖) ^ 2 := by
      rw [norm_complexRecoveryShift_pow_sq, mul_pow, vecSeq_norm_sq, ← tsum_mul_left]
      have hs : Summable fun j => (recoveryBlockWeight j d * ‖x j‖) ^ 2 := by
        refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
          (vecSeq_summable_sq x)
        have h1 := recoveryBlockWeight_le_one j d
        have h0 := recoveryBlockWeight_pos j d
        rw [mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
      refine hs.tsum_le_tsum (fun j => ?_) ((vecSeq_summable_sq x).mul_left _)
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := le_cubicRecoveryUniformGrowth hd j
      have h0 := recoveryBlockWeight_pos j d
      exact pow_le_pow_left₀ h0.le h1 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  · refine ciSup_le fun j => ?_
    have hx : ‖(lp.single 2 j (1 : ℂ) : RecoveryL2)‖ = 1 := by
      rw [lp.norm_single (by norm_num), norm_one]
    have hle := (complexRecoveryShift ^ d).le_opNorm (lp.single 2 j (1 : ℂ))
    rw [hx, mul_one] at hle
    have hval : ‖(complexRecoveryShift ^ d) (lp.single 2 j (1 : ℂ))‖ = recoveryBlockWeight j d := by
      have h := norm_complexRecoveryShift_pow_sq d (lp.single 2 j (1 : ℂ))
      have hsum : ∑' i, (recoveryBlockWeight i d * ‖(lp.single 2 j (1 : ℂ) : RecoveryL2) i‖) ^ 2 =
          recoveryBlockWeight j d ^ 2 := by
        rw [tsum_eq_single j (fun i hi => by
          rw [lp.single_apply, Pi.single_eq_of_ne hi, norm_zero, mul_zero]; norm_num)]
        rw [lp.single_apply, Pi.single_eq_same, norm_one, mul_one]
      rw [hsum] at h
      exact (pow_left_inj₀ (norm_nonneg _) (recoveryBlockWeight_pos j d).le two_ne_zero).mp h
    rw [hval] at hle
    exact hle

/-! ### Spectral radius and spectrum -/

/-- **The spectral radius is `ρ`.** -/
theorem spectralRadius_complexRecoveryShift :
    spectralRadius ℂ complexRecoveryShift = ENNReal.ofReal recoveryRate := by
  have hgel := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius complexRecoveryShift
  have hlim : Tendsto (fun n : ℕ => ((‖complexRecoveryShift ^ n‖₊ : ℝ≥0∞) ^ (1 / (n : ℝ))))
      atTop (𝓝 (ENNReal.ofReal recoveryRate)) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp tendsto_cubicRecoveryUniformGrowth
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply]
    rw [← norm_complexRecoveryShift_pow hn, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      (by positivity), ofReal_norm]
    rfl
  exact tendsto_nhds_unique hgel hlim

theorem norm_le_of_mem_spectrum_complexRecoveryShift {z : ℂ}
    (hz : z ∈ spectrum ℂ complexRecoveryShift) : ‖z‖ ≤ recoveryRate := by
  have h : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ complexRecoveryShift := le_iSup₂ (α := ℝ≥0∞) z hz
  rw [spectralRadius_complexRecoveryShift] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.coe_toReal, coe_nnnorm, ENNReal.toReal_ofReal recoveryRate_bounds.1.le] at this

/-- `U - μ` is not surjective for `|μ| < ρ`: a preimage of `e_0` would be
`x_k = μ^{-k-1} δ_k/δ_0`, which is not square summable. -/
theorem not_surjective_complexRecoveryShift_sub {μ : ℂ} (hμ : ‖μ‖ < recoveryRate) :
    ¬ Function.Surjective (complexRecoveryShift - μ • ContinuousLinearMap.id ℂ RecoveryL2) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (lp.single 2 0 (1 : ℂ))
  have hcoord : ∀ n, (complexRecoveryShift x : ℕ → ℂ) n - μ * x n =
      (lp.single 2 0 (1 : ℂ) : RecoveryL2) n := fun n => by
    rw [← hx]; rfl
  -- `μ x_0 = -1` and `μ x_{k+1} = w_k x_k`
  have h0 : μ * x 0 = -1 := by
    have := hcoord 0
    rw [complexRecoveryShift_apply_zero, lp.single_apply, Pi.single_eq_same] at this
    linear_combination -this
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at h0
  have hrec : ∀ k, x (k + 1) = (cubicRecoveryShiftWeight k : ℂ) * x k / μ := fun k => by
    have := hcoord (k + 1)
    rw [complexRecoveryShift_apply_succ, lp.single_apply, Pi.single_eq_of_ne (by omega)] at this
    field_simp
    linear_combination -this
  have hC : ∀ j, ((cubicGradedRecoveryGap j : ℝ) : ℂ) ≠ 0 := fun j =>
    Complex.ofReal_ne_zero.mpr (cubicGradedRecoveryGap_positive j).ne'
  have hform : ∀ k, x k = -((cubicGradedRecoveryGap k : ℝ) : ℂ) /
      ((cubicGradedRecoveryGap 0 : ℝ) : ℂ) / μ ^ (k + 1) := fun k => by
    induction k with
    | zero =>
      rw [neg_div, div_self (hC 0), zero_add, pow_one]
      field_simp; linear_combination h0
    | succ k ih =>
      rw [hrec k, ih, cubicRecoveryShiftWeight, Complex.ofReal_div]
      have h1 := hC k
      have h2 := hC 0
      field_simp
      ring
  -- the norms `‖x_k‖` grow
  have hnorm : ∀ k, ‖x k‖ = cubicGradedRecoveryGap k / cubicGradedRecoveryGap 0 / ‖μ‖ ^ (k + 1) :=
    fun k => by
    rw [hform k, norm_div, norm_div, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, norm_pow,
      abs_of_pos (cubicGradedRecoveryGap_positive k), abs_of_pos (cubicGradedRecoveryGap_positive 0)]
  have hμpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ0
  have hlog : Tendsto (fun k : ℕ => Real.log ‖x k‖ / k) atTop
      (𝓝 (Real.log recoveryRate - Real.log ‖μ‖)) := by
    have h1 := tendsto_log_cubicGradedRecoveryGap
    have h2 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      (Real.log (cubicGradedRecoveryGap 0) + Real.log ‖μ‖)
    have h := (h1.sub h2).sub_const (Real.log ‖μ‖)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
    rw [hnorm, Real.log_div (div_pos (cubicGradedRecoveryGap_positive k)
      (cubicGradedRecoveryGap_positive 0)).ne' (pow_pos hμpos _).ne', Real.log_div
      (cubicGradedRecoveryGap_positive k).ne' (cubicGradedRecoveryGap_positive 0).ne',
      Real.log_pow]
    push_cast
    field_simp
    ring
  have hpos : 0 < Real.log recoveryRate - Real.log ‖μ‖ := by
    have := Real.log_lt_log hμpos hμ
    linarith
  -- but `‖x_k‖ → 0`
  have hzero : Tendsto (fun k => ‖x k‖ ^ 2) atTop (𝓝 0) :=
    (vecSeq_summable_sq x).tendsto_atTop_zero
  have hev := hlog.eventually (lt_mem_nhds hpos)
  have hev2 := hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨k, hk1, hk2, hk3⟩ := (hev.and (hev2.and (eventually_ge_atTop 1))).exists
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk3
  have hxk : 0 < ‖x k‖ := by
    rw [hnorm]; exact div_pos (div_pos (cubicGradedRecoveryGap_positive k)
      (cubicGradedRecoveryGap_positive 0)) (pow_pos hμpos _)
  have hlog1 : 0 < Real.log ‖x k‖ := by
    have := (lt_div_iff₀ hkR).mp hk1
    nlinarith
  have : 1 < ‖x k‖ := by
    by_contra h
    push Not at h
    linarith [Real.log_nonpos hxk.le h]
  nlinarith

/-- **The spectrum of the complexified recovery multiplier is the closed disc of radius `ρ`.** -/
theorem spectrum_complexRecoveryShift :
    spectrum ℂ complexRecoveryShift = closedBall 0 recoveryRate := by
  have hρ := recoveryRate_bounds.1
  apply le_antisymm
  · intro z hz
    rw [mem_closedBall, dist_zero_right]
    exact norm_le_of_mem_spectrum_complexRecoveryShift hz
  · have hball : ball (0 : ℂ) recoveryRate ⊆ spectrum ℂ complexRecoveryShift := by
      intro μ hμ
      rw [mem_ball, dist_zero_right] at hμ
      rw [spectrum.mem_iff]
      rintro ⟨u, hu⟩
      apply not_surjective_complexRecoveryShift_sub hμ
      intro y
      set z := ((u⁻¹ : (RecoveryL2 →L[ℂ] RecoveryL2)ˣ) : RecoveryL2 →L[ℂ] RecoveryL2) y with hz
      have hinv : (u : RecoveryL2 →L[ℂ] RecoveryL2) z = y := by
        rw [hz]
        change ((u : RecoveryL2 →L[ℂ] RecoveryL2) *
          ((u⁻¹ : (RecoveryL2 →L[ℂ] RecoveryL2)ˣ) : RecoveryL2 →L[ℂ] RecoveryL2)) y = y
        rw [Units.mul_inv]; rfl
      have hval : μ • z - complexRecoveryShift z = y := by
        rw [← hinv, hu, Algebra.algebraMap_eq_smul_one]; rfl
      refine ⟨-z, ?_⟩
      change complexRecoveryShift (-z) - μ • (-z) = y
      rw [map_neg, smul_neg, ← hval]
      abel
    have hcl := (spectrum.isClosed complexRecoveryShift).closure_subset_iff.mpr hball
    rwa [closure_ball _ hρ.ne'] at hcl

/-! ### Eigenvectors of the adjoint -/

theorem complexRecoveryShift_single (n : ℕ) :
    complexRecoveryShift (lp.single 2 n (1 : ℂ)) =
      (cubicRecoveryShiftWeight n : ℂ) • lp.single 2 (n + 1) (1 : ℂ) := by
  ext m
  rw [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, smul_eq_mul]
  cases m with
  | zero =>
    rw [complexRecoveryShift_apply_zero, Pi.single_eq_of_ne (by omega), mul_zero]
  | succ k =>
    rw [complexRecoveryShift_apply_succ, lp.single_apply]
    by_cases h : k = n
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (by omega), mul_zero, mul_zero]

theorem recoveryL2_apply_eq_inner (f : RecoveryL2) (n : ℕ) :
    (f : ℕ → ℂ) n = inner ℂ (lp.single 2 n (1 : ℂ) : RecoveryL2) f := by
  rw [lp.inner_single_left]; simp

/-- The eigenvector `v_μ = Σ μ^k (δ_0/δ_k) e_k` of `U^*`, for `|μ| < ρ`. -/
theorem memℓp_recoveryEigen {μ : ℂ} (hμ : ‖μ‖ < recoveryRate) :
    Memℓp (fun k : ℕ => μ ^ k * ((cubicGradedRecoveryGap 0 / cubicGradedRecoveryGap k : ℝ) : ℂ))
      2 := by
  refine memℓp_of_summable_sq ?_
  obtain ⟨q, hq1, hq2⟩ := exists_between hμ
  have hq0 : 0 < q := lt_of_le_of_lt (norm_nonneg μ) hq1
  -- eventually `δ_k ≥ q^k`
  have hev : ∀ᶠ k : ℕ in atTop, q ^ k ≤ cubicGradedRecoveryGap k := by
    have hlogq : Real.log q < Real.log recoveryRate := Real.log_lt_log hq0 hq2
    filter_upwards [tendsto_log_cubicGradedRecoveryGap.eventually (lt_mem_nhds hlogq),
      eventually_ge_atTop 1] with k hk hk1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [lt_div_iff₀ hkR] at hk
    rw [← Real.log_le_log_iff (by positivity) (cubicGradedRecoveryGap_positive k), Real.log_pow]
    linarith
  have hr : (‖μ‖ / q) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    exact pow_lt_pow_left₀ hq1 (norm_nonneg _) two_ne_zero
  have hgeo : Summable fun k : ℕ => cubicGradedRecoveryGap 0 ^ 2 * ((‖μ‖ / q) ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hgeo ?_
  filter_upwards [hev] with k hk
  have hδ := cubicGradedRecoveryGap_positive k
  have hδ0 := cubicGradedRecoveryGap_positive 0
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hδ0 hδ)]
  have hqk : 0 < q ^ k := pow_pos hq0 k
  have hle : cubicGradedRecoveryGap 0 / cubicGradedRecoveryGap k ≤
      cubicGradedRecoveryGap 0 / q ^ k := div_le_div_of_nonneg_left hδ0.le hqk hk
  calc (‖μ‖ ^ k * (cubicGradedRecoveryGap 0 / cubicGradedRecoveryGap k)) ^ 2
      ≤ (‖μ‖ ^ k * (cubicGradedRecoveryGap 0 / q ^ k)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (pow_nonneg (norm_nonneg _) _) (div_pos hδ0 hδ).le)
          (mul_le_mul_of_nonneg_left hle (pow_nonneg (norm_nonneg _) _)) 2
    _ = cubicGradedRecoveryGap 0 ^ 2 * ((‖μ‖ / q) ^ 2) ^ k := by
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
        field_simp
        ring

/-- **Eigenvectors of the adjoint**: for `|μ| < ρ`, `U^* v_μ = μ v_μ` with `v_μ ≠ 0`. -/
theorem adjoint_complexRecoveryShift_eigenvector {μ : ℂ} (hμ : ‖μ‖ < recoveryRate) :
    ∃ v : RecoveryL2, v ≠ 0 ∧
      ContinuousLinearMap.adjoint complexRecoveryShift v = μ • v := by
  set v : RecoveryL2 := ⟨_, memℓp_recoveryEigen hμ⟩ with hv
  refine ⟨v, fun h => ?_, ?_⟩
  · have h0 := congrArg (fun f : RecoveryL2 => (f : ℕ → ℂ) 0) h
    simp only [hv, pow_zero, one_mul, div_self (cubicGradedRecoveryGap_positive 0).ne',
      Complex.ofReal_one] at h0
    exact one_ne_zero h0
  · ext n
    rw [recoveryL2_apply_eq_inner, ContinuousLinearMap.adjoint_inner_right,
      complexRecoveryShift_single, inner_smul_left, ← recoveryL2_apply_eq_inner, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, Complex.conj_ofReal]
    simp only [hv]
    have h1 := Complex.ofReal_ne_zero.mpr (cubicGradedRecoveryGap_positive n).ne'
    have h2 := Complex.ofReal_ne_zero.mpr (cubicGradedRecoveryGap_positive (n + 1)).ne'
    rw [cubicRecoveryShiftWeight, Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_div]
    field_simp
    ring

/-! ### The complexification -/

/-- The coordinate map `x ↦ (⟨b_k, x⟩)_k` of the physical Hilbert basis, into `ℓ²(ℕ, ℂ)`. -/
def recoveryRealEmbedding (x : cubicDefectHilbert) : RecoveryL2 :=
  ⟨fun k => ((cubicHilbertBasis.repr x : ℕ → ℝ) k : ℂ), memℓp_of_summable_sq (by
    have h := (lp.memℓp (cubicHilbertBasis.repr x)).summable (by rw [recoveryL2_toReal]; norm_num)
    simp only [recoveryL2_toReal, Real.rpow_two] at h
    simpa only [Complex.norm_real] using h)⟩

theorem recoveryRealEmbedding_apply (x : cubicDefectHilbert) (k : ℕ) :
    (recoveryRealEmbedding x : ℕ → ℂ) k = ((cubicHilbertBasis.repr x : ℕ → ℝ) k : ℂ) := rfl

theorem recoveryRealEmbedding_add (x y : cubicDefectHilbert) :
    recoveryRealEmbedding (x + y) = recoveryRealEmbedding x + recoveryRealEmbedding y := by
  ext k; simp [recoveryRealEmbedding_apply]

theorem recoveryRealEmbedding_smul (r : ℝ) (x : cubicDefectHilbert) :
    recoveryRealEmbedding (r • x) = (r : ℂ) • recoveryRealEmbedding x := by
  ext k
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, recoveryRealEmbedding_apply,
    recoveryRealEmbedding_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]

theorem norm_recoveryRealEmbedding (x : cubicDefectHilbert) : ‖recoveryRealEmbedding x‖ = ‖x‖ := by
  have h1 := vecSeq_norm_sq (recoveryRealEmbedding x)
  have h2 := lp.norm_rpow_eq_tsum (by rw [recoveryL2_toReal]; norm_num) (cubicHilbertBasis.repr x)
  simp only [recoveryL2_toReal, Real.rpow_two] at h2
  rw [LinearIsometryEquiv.norm_map] at h2
  simp only [recoveryRealEmbedding_apply, Complex.norm_real] at h1
  rw [← h1] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2.symm

/-- **Intertwining**: `U_ℂ ∘ ι = ι ∘ U`. -/
theorem complexRecoveryShift_realEmbedding (x : cubicDefectHilbert) :
    complexRecoveryShift (recoveryRealEmbedding x) =
      recoveryRealEmbedding (cubicHilbertRecoveryShift x) := by
  ext n
  rw [recoveryRealEmbedding_apply, HilbertBasis.repr_apply_apply,
    ← ContinuousLinearMap.adjoint_inner_left]
  cases n with
  | zero =>
    rw [complexRecoveryShift_apply_zero, cubicHilbertRecoveryShift_adjoint_zero, inner_zero_left,
      Complex.ofReal_zero]
  | succ k =>
    rw [complexRecoveryShift_apply_succ, cubicHilbertRecoveryShift_adjoint_successor,
      real_inner_smul_left, recoveryRealEmbedding_apply, HilbertBasis.repr_apply_apply]
    push_cast; ring

/-- **The complexification**: `(x, y) ↦ ι x + i ι y` is a bijection
`H × H → ℓ²(ℕ, ℂ)` under which `U_ℂ` acts as `U` on both components. -/
theorem recoveryComplexification_bijective :
    Function.Bijective fun p : cubicDefectHilbert × cubicDefectHilbert =>
      recoveryRealEmbedding p.1 + Complex.I • recoveryRealEmbedding p.2 := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have hc : ∀ k, (cubicHilbertBasis.repr x : ℕ → ℝ) k = (cubicHilbertBasis.repr x' : ℕ → ℝ) k ∧
        (cubicHilbertBasis.repr y : ℕ → ℝ) k = (cubicHilbertBasis.repr y' : ℕ → ℝ) k := fun k => by
      have hk := congrArg (fun f : RecoveryL2 => (f : ℕ → ℂ) k) h
      simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        recoveryRealEmbedding_apply] at hk
      have hre := congrArg Complex.re hk
      have him := congrArg Complex.im hk
      simp at hre him
      exact ⟨hre, him⟩
    have hx : cubicHilbertBasis.repr x = cubicHilbertBasis.repr x' := lp.ext (funext fun k => (hc k).1)
    have hy : cubicHilbertBasis.repr y = cubicHilbertBasis.repr y' := lp.ext (funext fun k => (hc k).2)
    simp only [Prod.mk.injEq]
    exact ⟨cubicHilbertBasis.repr.injective hx, cubicHilbertBasis.repr.injective hy⟩
  · intro z
    have hre : Memℓp (fun k => ((z : ℕ → ℂ) k).re) 2 := memℓp_of_summable_sq (by
      refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
        (vecSeq_summable_sq z)
      exact pow_le_pow_left₀ (norm_nonneg _) (by
        rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _) 2)
    have him : Memℓp (fun k => ((z : ℕ → ℂ) k).im) 2 := memℓp_of_summable_sq (by
      refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
        (vecSeq_summable_sq z)
      exact pow_le_pow_left₀ (norm_nonneg _) (by
        rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _) 2)
    set x := cubicHilbertBasis.repr.symm (⟨_, hre⟩ : lp (fun _ : ℕ => ℝ) 2) with hxdef
    set y := cubicHilbertBasis.repr.symm (⟨_, him⟩ : lp (fun _ : ℕ => ℝ) 2) with hydef
    have hx : ∀ k, (cubicHilbertBasis.repr x : ℕ → ℝ) k = ((z : ℕ → ℂ) k).re := fun k => by
      rw [hxdef, LinearIsometryEquiv.apply_symm_apply]
    have hy : ∀ k, (cubicHilbertBasis.repr y : ℕ → ℝ) k = ((z : ℕ → ℂ) k).im := fun k => by
      rw [hydef, LinearIsometryEquiv.apply_symm_apply]
    refine ⟨(x, y), ?_⟩
    ext k
    change (recoveryRealEmbedding x : ℕ → ℂ) k + Complex.I * (recoveryRealEmbedding y : ℕ → ℂ) k =
      (z : ℕ → ℂ) k
    rw [recoveryRealEmbedding_apply, recoveryRealEmbedding_apply, hx, hy, mul_comm]
    exact Complex.re_add_im _

theorem complexRecoveryShift_complexification (x y : cubicDefectHilbert) :
    complexRecoveryShift (recoveryRealEmbedding x + Complex.I • recoveryRealEmbedding y) =
      recoveryRealEmbedding (cubicHilbertRecoveryShift x) +
        Complex.I • recoveryRealEmbedding (cubicHilbertRecoveryShift y) := by
  rw [map_add, map_smul, complexRecoveryShift_realEmbedding, complexRecoveryShift_realEmbedding]

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
