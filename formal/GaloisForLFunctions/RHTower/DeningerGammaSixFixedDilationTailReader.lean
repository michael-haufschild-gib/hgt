import GaloisForLFunctions.RHTower.DeningerGammaSixAbelSecondComparison
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Fixed-dilation readout of the complete Gamma-six integral tail

The original coordinate projection onto `a >= 6^M` is applied to the full
integral correction before its fixed-six Abel boundary is read. Exact shell
regrouping, including the offset 216 and every tensor cross term, identifies
its second coefficient with a complete complex shell sum.

The existing successor normalization gives this sum an explicit nonzero
limit whenever the retained internal Xi jet is nonzero. Geometric domination
controls cancellation across all shells. Every finite diagonal repair has
the same eventual cutoff readout, including at each admitted multiplicity-top
source. Finite diagonal support is distinct from finite operator rank.

The Abel limit is taken for each fixed cutoff first; the normalized depth
limit follows. No interchange or uniform joint limit is asserted. This does
not prove nonvanishing of the uncut fixed-six coefficient, construct the
required Sonin comparison, or prove RH. In particular, the original source
spectral parameter remains distinct from the Abel regulator.
-/

open Complex Real Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Geometric averaging of a moving, convergent complex source tail. -/
theorem tendsto_geometric_moving_source_sum
    {a : ℕ → ℂ} {A q : ℂ} (ha : Tendsto a atTop (𝓝 A)) (hq : ‖q‖ < 1) :
    Tendsto (fun M : ℕ => ∑' j : ℕ, q ^ j * a (M + j)) atTop
      (𝓝 ((1 - q)⁻¹ * A)) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_norm_le
  have hBa : ∀ m, ‖a m‖ ≤ B := fun m => hB (a m) ⟨m, rfl⟩
  have hs : Summable (fun j : ℕ => ‖q‖ ^ j * B) :=
    by simpa only [norm_pow] using (summable_geometric_of_norm_lt_one hq).norm.mul_right B
  have ht := tendsto_tsum_of_dominated_convergence hs
    (f := fun M j => q ^ j * a (M + j))
    (g := fun j => q ^ j * A)
    (fun j => (ha.comp (tendsto_add_atTop_nat j)).const_mul (q ^ j))
    (Filter.Eventually.of_forall (fun M j => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hBa (M + j)) (by positivity)))
  simpa only [tsum_mul_right, tsum_geometric_of_norm_lt_one hq] using ht

/-- The literal harmonic mass in the degree-six divisible part of a shell. -/
def deningerGammaSixDivisibleShellMass (m : ℕ) : ℝ :=
  (1 / 6 : ℝ) * ∑ j ∈ Finset.Ico (6 ^ m : ℕ) (6 ^ (m + 1)), (j : ℝ)⁻¹

theorem reciprocal_Ico_eq_harmonic (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, (j : ℝ)⁻¹) = (harmonic (b - 1) : ℝ) - (harmonic (a - 1) : ℝ) := by
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ)⁻¹) = (harmonic n : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hi := Finset.sum_Ico_add' (fun j : ℕ => (j : ℝ)⁻¹) (a - 1) (b - 1) (c := 1)
  have hb : 0 < b := lt_of_lt_of_le ha hab
  simp only [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] at hi
  rw [← hi, Finset.sum_Ico_eq_sub _ (by omega), hsum, hsum]


theorem tendsto_deningerGammaSixDivisibleShellMass :
    Tendsto deningerGammaSixDivisibleShellMass atTop (𝓝 (Real.log 6 / 6)) := by
  have hp : Tendsto (fun m : ℕ => 6 ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hh : Tendsto (fun m : ℕ => (harmonic (6 ^ m - 1) : ℝ) - Real.log ((6 : ℝ) ^ m))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    apply (Real.tendsto_harmonic_sub_log_add_one.comp ((tendsto_sub_atTop_nat 1).comp hp)).congr'
    apply Filter.Eventually.of_forall
    intro m
    have hpos : 0 < 6 ^ m := by positivity
    have he : ((6 ^ m - 1 : ℕ) : ℝ) + 1 = (6 : ℝ) ^ m := by
      have hn : 6 ^ m - 1 + 1 = 6 ^ m := Nat.sub_add_cancel (by omega)
      exact_mod_cast hn
    simp only [Function.comp_apply, he]
  have ht := ((hh.comp (tendsto_add_atTop_nat 1)).sub hh).add_const (Real.log 6)
  simp only [sub_self, zero_add] at ht
  have hg : Tendsto (fun m : ℕ => ∑ j ∈ Finset.Ico (6 ^ m : ℕ) (6 ^ (m + 1)), (j : ℝ)⁻¹)
      atTop (𝓝 (Real.log 6)) := by
    apply ht.congr'
    apply Filter.Eventually.of_forall
    intro m
    dsimp only [Function.comp_apply]
    rw [reciprocal_Ico_eq_harmonic (6 ^ m) (6 ^ (m + 1)) (by positivity)
      (Nat.pow_le_pow_right (by norm_num) (by omega))]
    simp only [Real.log_pow, Nat.cast_add, Nat.cast_one]
    ring
  have he : (1 / 6 : ℝ) * Real.log 6 = Real.log 6 / 6 := by ring
  rw [← he]
  exact hg.const_mul (1 / 6 : ℝ)

/-- The ratio is forced by the same successor normalization as the full tensor source. -/
def deningerGammaSixSuccessorRatio (w : ℂ) : ℂ :=
  (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ 1 (mobiusThetaCenteredParameter w))⁻¹

theorem deningerGammaSixSuccessorNormalizer_pow (m : ℕ) (w : ℂ) :
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ m (mobiusThetaCenteredParameter w) =
      (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ 1 (mobiusThetaCenteredParameter w)) ^ m := by
  simp only [mobiusThetaSuccessorSpectralNormalizer, Nat.cast_one, one_mul, Complex.cpow_nat_mul]

theorem one_lt_deningerGammaSixSuccessorBase :
    1 < (mobiusSuccessor 6 : ℝ) / 6 := by
  apply (one_lt_div (by norm_num : (0 : ℝ) < 6)).2
  exact_mod_cast lt_mobiusSuccessor 6

theorem deningerGammaSixSuccessorNormalizer_ne_zero (m : ℕ) (w : ℂ) :
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ m (mobiusThetaCenteredParameter w) ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one
    one_lt_deningerGammaSixSuccessorBase).ne'

theorem norm_deningerGammaSixSuccessorRatio_lt_one
    {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    ‖deningerGammaSixSuccessorRatio w‖ < 1 := by
  rw [deningerGammaSixSuccessorRatio, norm_inv, inv_lt_one₀]
  · rw [mobiusThetaSuccessorSpectralNormalizer, Nat.cast_one, one_mul]
    change 1 < ‖(((mobiusSuccessor 6 : ℝ) / 6 : ℝ) : ℂ) ^ mobiusThetaCenteredParameter w‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one
      one_lt_deningerGammaSixSuccessorBase)]
    exact Real.one_lt_rpow one_lt_deningerGammaSixSuccessorBase hw
  · exact norm_pos_iff.mpr (deningerGammaSixSuccessorNormalizer_ne_zero 1 w)

/-- The full shell sum, with no shell cancellation discarded. -/
def deningerGammaSixShellTailBoundary (k l M : ℕ) (w : ℂ) : ℂ :=
  (Real.log 6 : ℂ) * (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
    ∑' j : ℕ, deningerGammaSixTensorRemainderMultiplier (M + j) w w *
      (deningerGammaSixDivisibleShellMass (M + j - 1) : ℂ)

theorem deningerGammaSixSuccessorNormalizer_shift_cancel (M j : ℕ) (w : ℂ) :
    deningerGammaSixSuccessorRatio w ^ j *
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ (M + j) (mobiusThetaCenteredParameter w) =
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) := by
  rw [deningerGammaSixSuccessorNormalizer_pow (M + j) w, deningerGammaSixSuccessorNormalizer_pow M w,
    deningerGammaSixSuccessorRatio, pow_add, inv_pow]
  have hn := deningerGammaSixSuccessorNormalizer_ne_zero 1 w
  field_simp

/-- The exact full-tail normalization, prior to the operator-cutoff identification. -/
theorem tendsto_deningerGammaSixShellTailBoundary_normalized
    (k l : ℕ) {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun M : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
        deningerGammaSixShellTailBoundary k l M w) atTop
      (𝓝 ((Real.log 6 : ℂ) * (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        ((1 - deningerGammaSixSuccessorRatio w)⁻¹ *
          ((2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ))) *
            ((Real.log 6 / 6 : ℝ) : ℂ))))) := by
  have hh := (tendsto_deningerGammaSixDivisibleShellMass.comp (tendsto_sub_atTop_nat 1)).ofReal
  have ha := (tendsto_deningerGammaSixTensorRemainderMultiplier_normalized hw).mul hh
  have ht := (tendsto_geometric_moving_source_sum ha
    (norm_deningerGammaSixSuccessorRatio_lt_one hw)).const_mul
      ((Real.log 6 : ℂ) * (iteratedDeriv k XiC w * iteratedDeriv l XiC w))
  convert ht using 1
  funext M
  unfold deningerGammaSixShellTailBoundary
  rw [← mul_assoc, mul_comm _ ((Real.log 6 : ℂ) * _), mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [Function.comp_apply]
  linear_combination -(deningerGammaSixTensorRemainderMultiplier (M + j) w w *
    (deningerGammaSixDivisibleShellMass (M + j - 1) : ℂ)) *
      deningerGammaSixSuccessorNormalizer_shift_cancel M j w


theorem deningerGammaSixDivisibleShellMass_eq_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ a ∈ Finset.Ico (6 ^ m : ℕ) (6 ^ (m + 1)),
      if 6 ∣ a then (a : ℝ)⁻¹ else 0) = deningerGammaSixDivisibleShellMass (m - 1) := by
  have hp : 6 ^ m = 6 * 6 ^ (m - 1) := by
    calc 6 ^ m = 6 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm]
         _ = 6 * 6 ^ (m - 1) := by rw [pow_succ, mul_comm]
  have hp' : 6 ^ (m + 1) = 6 * 6 ^ m := by rw [pow_succ, mul_comm]
  have hset : (Finset.Ico (6 ^ m : ℕ) (6 ^ (m + 1))).filter (fun a => 6 ∣ a) =
      (Finset.Ico (6 ^ (m - 1)) (6 ^ m)).image (fun j => 6 * j) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, ⟨j, hj⟩⟩
      refine ⟨j, ⟨?_, ?_⟩, hj.symm⟩
      · rw [hp, hj] at ha
        omega
      · rw [hp', hj] at hb
        omega
    · rintro ⟨j, ⟨ha, hb⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right 6 j⟩
      · rw [hp]
        omega
      · rw [hp']
        omega
  rw [← Finset.sum_filter, hset, Finset.sum_image]
  · simp only [Nat.cast_mul, Nat.cast_ofNat, mul_inv_rev]
    rw [deningerGammaSixDivisibleShellMass, Nat.sub_add_cancel hm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro a ha b hb h
    change 6 * a = 6 * b at h
    omega

/-- The complete integral correction in every literal shell coordinate. -/
theorem deningerGammaSixIntegralRemainder_eq_shell_multiplier
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) (n : ℕ) :
    deningerGammaSixIntegralRemainder k l w w n =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        deningerGammaSixTensorRemainderMultiplier (deningerGammaSixShellDepth n) w w *
          (((n + 216 : ℕ) : ℂ))⁻¹ := by
  have ha := deningerGammaSixIntegral_every_depth_admitted (deningerGammaSixShellHonestDepth n) hrw
  rw [deningerGammaSixIntegralRemainder,
    (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l _ hw hw ha ha).2,
    deningerGammaSixShellHalfWeight_sq]
  dsimp only [deningerGammaSixShellHonestDepth]
  have hf := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
  push_cast at hf ⊢
  unfold deningerGammaSixTensorRemainderMultiplier
  linear_combination ((mobiusThetaPrimeNormalResidualMultiplier 6 (deningerGammaSixShellDepth n) w *
      mobiusThetaPrimeNormalResidualMultiplier 6 (deningerGammaSixShellDepth n) w - 1) *
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w)) * hf

def deningerGammaSixIntegralTailTerm (k l M : ℕ) (w : ℂ) (n : ℕ) : ℂ :=
  if 6 ^ M ≤ n + 216 ∧ 6 ∣ n + 216 then deningerGammaSixIntegralRemainder k l w w n else 0

theorem summable_deningerGammaSixIntegralTailTerm
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (deningerGammaSixIntegralTailTerm k l M w) := by
  apply (summable_deningerGammaSixIntegralRemainder k l hw hw hrw hrw).norm.of_norm_bounded
  intro n
  unfold deningerGammaSixIntegralTailTerm
  split_ifs <;> simp


theorem deningerGammaSixTailCut_iff_depth (M n : ℕ) :
    6 ^ M ≤ n + 216 ↔ M ≤ deningerGammaSixShellDepth n :=
  (Nat.le_log_iff_pow_le (by norm_num : 1 < 6) (by omega : n + 216 ≠ 0)).symm

theorem deningerGammaSixIntegralTailTerm_depth
    (k l M : ℕ) (w : ℂ) (m : ℕ) (n : deningerGammaSixDepthFiber m) :
    deningerGammaSixIntegralTailTerm k l M w n =
      if M ≤ m then
        (if 6 ∣ (n : ℕ) + 216 then deningerGammaSixIntegralRemainder k l w w n else 0)
      else 0 := by
  have hd : deningerGammaSixShellDepth n = m := n.property
  simp only [deningerGammaSixIntegralTailTerm, deningerGammaSixTailCut_iff_depth, hd]
  split_ifs <;> simp_all

theorem deningerGammaSixIntegralTailTerm_fiber
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) (m : ℕ) :
    (∑' n : deningerGammaSixDepthFiber m, deningerGammaSixIntegralTailTerm k l M w n) =
      if M ≤ m then (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        deningerGammaSixTensorRemainderMultiplier m w w *
          (deningerGammaSixDivisibleShellMass (m - 1) : ℂ) else 0 := by
  simp_rw [deningerGammaSixIntegralTailTerm_depth]
  by_cases hMm : M ≤ m
  · simp only [if_pos hMm]
    have hm : 3 ≤ m := hM.trans hMm
    have hfiber : (∑' n : deningerGammaSixDepthFiber m,
        if 6 ∣ (n : ℕ) + 216 then deningerGammaSixIntegralRemainder k l w w n else 0) =
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
          deningerGammaSixTensorRemainderMultiplier m w w *
            ∑' n : deningerGammaSixDepthFiber m,
              if 6 ∣ (n : ℕ) + 216 then (((n : ℕ) + 216 : ℕ) : ℂ)⁻¹ else 0 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [deningerGammaSixIntegralRemainder_eq_shell_multiplier k l hw hrw,
        show deningerGammaSixShellDepth n = m from n.property]
      split_ifs <;> simp
    rw [hfiber]
    congr 1
    rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
    rw [Finset.tsum_subtype' (deningerGammaSixShellCoordinates m)
      (fun n : ℕ => if 6 ∣ n + 216 then (((n + 216 : ℕ) : ℂ))⁻¹ else 0)]
    have hlo := deningerGammaSix_pow_three_le hm
    have hhi := deningerGammaSix_pow_three_le (show 3 ≤ m + 1 by omega)
    have hshift := Finset.sum_Ico_add'
      (fun a : ℕ => if 6 ∣ a then (a : ℂ)⁻¹ else 0)
      (6 ^ m - 216) (6 ^ (m + 1) - 216) (c := 216)
    rw [Nat.sub_add_cancel hlo, Nat.sub_add_cancel hhi] at hshift
    change (∑ n ∈ Finset.Ico (6 ^ m - 216) (6 ^ (m + 1) - 216),
      if 6 ∣ n + 216 then ((n + 216 : ℕ) : ℂ)⁻¹ else 0) = _
    rw [hshift]
    have hreal := congrArg Complex.ofReal (deningerGammaSixDivisibleShellMass_eq_sum m (by omega))
    push_cast at hreal
    simpa only [apply_ite, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using hreal
  · simp only [if_neg hMm, tsum_zero]

/-- Exact regrouping of the complete, admitted source tail by its literal shell depth. -/
theorem deningerGammaSixIntegralTailTerm_tsum
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    (∑' n : ℕ, deningerGammaSixIntegralTailTerm k l M w n) =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        ∑' j : ℕ, deningerGammaSixTensorRemainderMultiplier (M + j) w w *
          (deningerGammaSixDivisibleShellMass (M + j - 1) : ℂ) := by
  have hs := summable_deningerGammaSixIntegralTailTerm k l M hw hrw
  have hf := hs.hasSum.tsum_fiberwise deningerGammaSixShellDepth
  change HasSum (fun m : ℕ => ∑' n : deningerGammaSixDepthFiber m,
    deningerGammaSixIntegralTailTerm k l M w n)
      (∑' n : ℕ, deningerGammaSixIntegralTailTerm k l M w n) at hf
  rw [← hf.tsum_eq]
  simp_rw [deningerGammaSixIntegralTailTerm_fiber k l M hw hrw hM]
  have hinj : Function.Injective (fun j : ℕ => M + j) := fun _ _ h => Nat.add_left_cancel h
  have he := hinj.tsum_eq (f := fun m : ℕ =>
    if M ≤ m then (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
      deningerGammaSixTensorRemainderMultiplier m w w *
        (deningerGammaSixDivisibleShellMass (m - 1) : ℂ) else 0) (by
          intro m hm
          have hMm : M ≤ m := by
            by_contra h
            exact hm (if_neg h)
          exact ⟨m - M, by change M + (m - M) = m; omega⟩)
  rw [← he]
  simp only [Nat.le_add_right, if_true, mul_assoc, tsum_mul_left]


/-- The original coordinate tail projection, defined before evaluating a source. -/
def deningerOrdinaryIntegerTailProjection (N : ℕ) : DeningerOrdinaryIntegerEnd where
  toFun x k := if N ≤ (k : ℕ) then x k else 0
  map_add' x y := by
    funext k
    by_cases h : N ≤ (k : ℕ) <;> simp [h]
  map_smul' c x := by
    funext k
    split <;> simp_all

theorem deningerOrdinaryIntegerDiagonalCoefficient_tailProjection
    (N : ℕ) (T : DeningerOrdinaryIntegerEnd) (a : PNat) :
    deningerOrdinaryIntegerDiagonalCoefficient a (deningerOrdinaryIntegerTailProjection N * T) =
      if N ≤ (a : ℕ) then deningerOrdinaryIntegerDiagonalCoefficient a T else 0 := rfl

theorem deningerOrdinaryIntegerSummableDiagonal_tailProjection
    (N : ℕ) (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a T)) :
    Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerOrdinaryIntegerTailProjection N * T)) := by
  apply hs.norm.of_norm_bounded
  intro a
  rw [deningerOrdinaryIntegerDiagonalCoefficient_tailProjection]
  split_ifs <;> simp

/-- Tail of the actual full integral correction, through the original coordinate projection. -/
def deningerGammaSixIntegralTailOperator (k l M : ℕ) (w : ℂ) : DeningerOrdinaryIntegerEnd :=
  deningerOrdinaryIntegerTailProjection (6 ^ M) *
    (deningerGammaSixIntegralOperator k l w w -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen)

theorem deningerGammaSixIntegralTailOperator_summable
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerGammaSixIntegralTailOperator k l M w)) :=
  deningerOrdinaryIntegerSummableDiagonal_tailProjection _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hw hrw hrw)

/-- The fixed-six second boundary coefficient is the complete original cutoff readout. -/
theorem deningerGammaSixIntegralTailOperator_second_eq_tsum
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 =
        (Real.log 6 : ℂ) * ∑' n : ℕ, deningerGammaSixIntegralTailTerm k l M w n := by
  let R := deningerGammaSixIntegralOperator k l w w -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen
  let f : PNat → ℂ := fun a => if 6 ^ M ≤ (a : ℕ) ∧ (6 : PNat) ∣ a then
    deningerOrdinaryIntegerDiagonalCoefficient a R else 0
  have hf : deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 = (Real.log 6 : ℂ) * ∑' a : PNat, f a := by
    simp only [deningerOrdinaryIntegerAbelSecondCoefficient, zero_smul, sub_zero,
      deningerGammaSixIntegralTailOperator, deningerOrdinaryIntegerDiagonalCoefficient_tailProjection]
    congr 1
    apply tsum_congr
    intro a
    dsimp only [f, R]
    split_ifs <;> simp_all
  rw [hf]
  congr 1
  let g : ℕ → PNat := fun n => ⟨n + 216, by omega⟩
  have hg : Function.Injective g := by
    intro i j h
    have he := congrArg (fun a : PNat => (a : ℕ)) h
    change i + 216 = j + 216 at he
    omega
  have hsupp : Function.support f ⊆ Set.range g := by
    intro a ha
    have hpow : 6 ^ M ≤ (a : ℕ) := by
      by_contra h
      exact ha (by simp only [f, h, false_and, if_false])
    have hlow := deningerGammaSix_pow_three_le hM
    refine ⟨(a : ℕ) - 216, ?_⟩
    apply Subtype.ext
    change (a : ℕ) - 216 + 216 = (a : ℕ)
    exact Nat.sub_add_cancel (hlow.trans hpow)
  rw [← hg.tsum_eq hsupp]
  apply tsum_congr
  intro n
  dsimp only [f, g]
  rw [show deningerOrdinaryIntegerDiagonalCoefficient ⟨n + 216, by omega⟩ R =
    deningerGammaSixIntegralRemainder k l w w n from
      deningerGammaSixIntegralCorrection_tail k l hw hw hrw hrw n]
  unfold deningerGammaSixIntegralTailTerm
  split_ifs <;> simp_all [PNat.dvd_iff]

theorem deningerGammaSixIntegralTailOperator_second_eq_shell
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 =
        deningerGammaSixShellTailBoundary k l M w := by
  rw [deningerGammaSixIntegralTailOperator_second_eq_tsum k l M hw hrw hM,
    deningerGammaSixIntegralTailTerm_tsum k l M hw hrw hM,
    deningerGammaSixShellTailBoundary]
  ring

/-- The actual fixed-dilation cutoff boundary admits the proved second limit. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_second
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) / (ε : ℂ)^2)
      (𝓝[>] 0) (𝓝 (deningerGammaSixShellTailBoundary k l M w)) := by
  have h := tendsto_deningerOrdinaryIntegerAbelDefect_second
    (deningerGammaSixIntegralTailOperator k l M w) 0
    (by simpa only [zero_smul, sub_zero] using deningerGammaSixIntegralTailOperator_summable k l M hw hrw)
    (6 : PNat)
  simpa only [zero_mul, sub_zero,
    deningerGammaSixIntegralTailOperator_second_eq_shell k l M hw hrw hM] using h


/-- Closed form of the retained, full-tail fixed-six readout. -/
def deningerGammaSixTailBoundaryLimit (k l : ℕ) (w : ℂ) : ℂ :=
  (Real.log 6 : ℂ) * (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
    ((1 - deningerGammaSixSuccessorRatio w)⁻¹ *
      ((2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ))) *
        ((Real.log 6 / 6 : ℝ) : ℂ)))

theorem deningerGammaSixTailBoundaryLimit_ne_zero
    (k l : ℕ) {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0) :
    deningerGammaSixTailBoundaryLimit k l w ≠ 0 := by
  have hlog : Real.log 6 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 6)).ne'
  have hq : 1 - deningerGammaSixSuccessorRatio w ≠ 0 := by
    intro h
    have he : deningerGammaSixSuccessorRatio w = 1 := sub_eq_zero.mp h |>.symm
    have hnorm := norm_deningerGammaSixSuccessorRatio_lt_one hw
    rw [he, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  apply mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hlog) hc)
  apply mul_ne_zero (inv_ne_zero hq)
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast moebius_mobiusSuccessor_ne_zero 6)
  · exact Complex.ofReal_ne_zero.mpr (div_ne_zero hlog (by norm_num))

/-- Exact fixed-six readout of the complete original cutoff operator, retaining depth. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_normalized
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun M : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
          (deningerGammaSixIntegralTailOperator k l M w) 0) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) := by
  apply (tendsto_deningerGammaSixShellTailBoundary_normalized k l (by linarith)).congr'
  filter_upwards [eventually_ge_atTop 3] with M hM
  rw [deningerGammaSixIntegralTailOperator_second_eq_shell k l M hw hrw hM]

theorem eventually_deningerGammaSixIntegralTailOperator_second_ne_zero
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0) :
    ∀ᶠ M : ℕ in atTop, deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 ≠ 0 := by
  have ht := (tendsto_deningerGammaSixIntegralTailOperator_normalized k l hw hrw).eventually_ne
    (deningerGammaSixTailBoundaryLimit_ne_zero k l (by linarith) hc)
  filter_upwards [ht] with M hM
  intro hz
  exact hM (by rw [hz, mul_zero])

theorem eventually_deningerOrdinaryInteger_finite_tail_diagonal_zero
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, ∀ a : PNat, deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerOrdinaryIntegerTailProjection (6 ^ M) * F) = 0 := by
  obtain ⟨N, hN⟩ := hF.bddAbove
  filter_upwards [eventually_ge_atTop ((N : ℕ) + 1)] with M hM
  intro a
  rw [deningerOrdinaryIntegerDiagonalCoefficient_tailProjection]
  split_ifs with ha
  · by_contra hne
    have hle : a ≤ N := hN hne
    change (a : ℕ) ≤ (N : ℕ) at hle
    have hp : M < 6 ^ M := Nat.lt_pow_self (by norm_num)
    omega
  · rfl

/-- Finite diagonal repairs disappear from every sufficiently late actual cutoff measurement. -/
theorem eventually_deningerOrdinaryInteger_finite_tail_second_eq
    (T F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerOrdinaryIntegerTailProjection (6 ^ M) * (T + F)) 0 =
        deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
          (deningerOrdinaryIntegerTailProjection (6 ^ M) * T) 0 := by
  filter_upwards [eventually_deningerOrdinaryInteger_finite_tail_diagonal_zero F hF] with M hM
  simp only [deningerOrdinaryIntegerAbelSecondCoefficient, zero_smul, sub_zero, mul_add, map_add]
  congr 1
  apply tsum_congr
  intro a
  rw [hM a, add_zero]

/-- Every finite diagonal repair retains the same normalized fixed-six tail limit. -/
theorem tendsto_deningerGammaSixIntegral_finite_repair_tail_normalized
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    Tendsto (fun M : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
          (deningerOrdinaryIntegerTailProjection (6 ^ M) *
            ((deningerGammaSixIntegralOperator k l w w + F) -
              (iteratedDeriv k XiC w * iteratedDeriv l XiC w) •
                deningerOrdinaryIntegerReciprocalGreen)) 0) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) := by
  have he := eventually_deningerOrdinaryInteger_finite_tail_second_eq
    (deningerGammaSixIntegralOperator k l w w -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) F hF
  apply (tendsto_deningerGammaSixIntegralTailOperator_normalized k l hw hrw).congr'
  filter_upwards [he] with M hM
  rw [show (deningerGammaSixIntegralOperator k l w w + F) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen =
      (deningerGammaSixIntegralOperator k l w w -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) + F by abel,
    hM]
  rfl

/-- At every admitted Xi divisor, each sufficiently late original cutoff has
nonvanishing second boundary variation at the fixed arithmetic dilation six. -/
theorem eventually_deningerGammaSixIntegral_top_finite_repair_fixed_six
    (rho : XiDivisorSupport) (hrho : (1 / 3 : ℝ) < (rho : ℂ).re)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, ¬ Tendsto (fun ε : ℝ =>
      deningerOrdinaryIntegerAbelDefect ε (6 : PNat)
        (deningerOrdinaryIntegerTailProjection (6 ^ M) *
          ((deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
            (xiSpectralPointSupport rho) (xiSpectralPointSupport rho) + F) -
              (iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
                iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) •
                  deningerOrdinaryIntegerReciprocalGreen)) / (ε : ℂ)^2)
      (𝓝[>] 0) (𝓝 0) := by
  have hw := abs_im_xiSpectralPointSupport_lt_one rho
  have hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho
  have hc := mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
  have ht := (tendsto_deningerGammaSixIntegral_finite_repair_tail_normalized _ _ hw hrw F hF).eventually_ne
    (deningerGammaSixTailBoundaryLimit_ne_zero _ _ (by linarith) hc)
  filter_upwards [ht] with M hM
  have hsource := deningerGammaSixIntegral_finite_repair_principal_class
    (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) hw hw hrw hrw F hF
  have hs := deningerOrdinaryIntegerSummableDiagonal_tailProjection (6 ^ M) _ hsource
  have hlim := tendsto_deningerOrdinaryIntegerAbelDefect_second _ 0
    (by simpa only [zero_smul, sub_zero] using hs) (6 : PNat)
  simp only [zero_mul, sub_zero] at hlim
  intro hz
  have hcoef := tendsto_nhds_unique hlim hz
  exact hM (by rw [hcoef, mul_zero])

end
end RHTower
