import GaloisForLFunctions.ArithmeticDefectRigidity.RepairingKernelsVanishOnEscape
import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Full Wiener covariances along a common cofactor limit

The sharp cofactor radius supplies a summable majorant for every critical Wiener
kernel. Its covariances converge with the Gram table; paid kernels tend to zero.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Extend the cofactor covariance row by zero at the unused index zero. -/
def naturalCofactorGram (ε : SubcriticalDamping) (T n : ℕ) (j : ℕ+) : ℝ :=
  if hn : 0 < n then cofactorGram ε T ⟨n, hn⟩ j else 0

theorem naturalCofactorGram_zero (ε : SubcriticalDamping) (T : ℕ) (j : ℕ+) :
    naturalCofactorGram ε T 0 j = 0 := by
  exact dif_neg (Nat.not_lt_zero 0)

theorem naturalCofactorGram_pos (ε : SubcriticalDamping) (T n : ℕ) (j : ℕ+)
    (hn : 0 < n) : naturalCofactorGram ε T n j = cofactorGram ε T ⟨n, hn⟩ j :=
  dif_pos hn

theorem inv_sqrt_pnat_le_one (j : ℕ+) : 1 / Real.sqrt (j : ℝ) ≤ 1 := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.property
  exact (div_le_one (by positivity)).mpr (Real.one_le_sqrt.mpr hj)

/-- The critical Wiener weight dominates every covariance coordinate. -/
theorem norm_naturalCofactorGram_le (ε : SubcriticalDamping) (T : ℕ) (j : ℕ+)
    (n : ℕ) (hn : n ≠ 0) :
    ‖(naturalCofactorGram ε T n j : ℂ)‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [naturalCofactorGram_pos ε T n j (Nat.pos_of_ne_zero hn), Complex.norm_real,
    Real.norm_eq_abs]
  calc
    _ ≤ cofactorGramRadius ⟨n, Nat.pos_of_ne_zero hn⟩ j := abs_cofactorGram_le ε T _ _
    _ ≤ 1 / Real.sqrt (n : ℝ) :=
      mul_le_of_le_one_right (by positivity) (inv_sqrt_pnat_le_one j)
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- At a finite horizon no cofactor beyond that horizon contributes. -/
theorem naturalCofactorGram_eq_zero_of_lt (ε : SubcriticalDamping) (T n : ℕ) (j : ℕ+)
    (hn : T + 1 < n) : naturalCofactorGram ε T n j = 0 := by
  rw [naturalCofactorGram_pos ε T n j (by omega)]
  unfold cofactorGram pronicPairing rowDilate
  have hz : (∑ m ∈ Icc 1 (T + 1),
      pmPowerDampedCenteredDivisorPrefix ε (m / n) *
        pmPowerDampedCenteredDivisorPrefix ε (m / j) /
          ((m : ℝ) * ((m : ℝ) + 1))) = 0 := by
    apply sum_eq_zero
    intro m hm
    rw [Nat.div_eq_of_lt ((mem_Icc.mp hm).2.trans_lt hn),
      ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      zero_mul, zero_div]
  exact (congrArg (fun x : ℝ => x / dampedMobiusEnergy ε (T + 1)) hz).trans (zero_div _)

/-- Pair a complete Wiener kernel with one actual cofactor coordinate. -/
def wienerCofactorCovariance (ε : SubcriticalDamping) (T : ℕ) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) : ℂ :=
  ∑' n, a.toFn n * (naturalCofactorGram ε T n j : ℂ)

theorem wienerCofactorCovariance_eq_sum (ε : SubcriticalDamping) (T : ℕ) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    wienerCofactorCovariance ε T j a =
      ∑ n ∈ Icc 1 (T + 1), a.toFn n * (naturalCofactorGram ε T n j : ℂ) := by
  apply tsum_eq_sum
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [naturalCofactorGram_zero, Complex.ofReal_zero, mul_zero]
  · rw [naturalCofactorGram_eq_zero_of_lt ε T n j (by
      simp only [mem_Icc] at hn; omega), Complex.ofReal_zero, mul_zero]

/-- The signed source pairing represented by a covariance coordinate. -/
def dilationCofactorWork (ε : SubcriticalDamping) (g : ℕ → ℝ) (j : ℕ+) (T : ℕ) : ℝ :=
  pronicPairing (T + 1) (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε))
    (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) /
      dampedMobiusEnergy ε (T + 1)

theorem dilationCofactorWork_eq_sum (ε : SubcriticalDamping) (g : ℕ → ℝ)
    (j : ℕ+) (T : ℕ) : dilationCofactorWork ε g j T =
      ∑ n ∈ Icc 1 (T + 1), g n * naturalCofactorGram ε T n j := by
  have hrow (m : ℕ) (hm : m ∈ Icc 1 (T + 1)) :
      prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε) m =
      ∑ n ∈ Icc 1 (T + 1), g n * pmPowerDampedCenteredDivisorPrefix ε (m / n) := by
    apply sum_subset (Icc_subset_Icc le_rfl (mem_Icc.mp hm).2)
    intro n hn hnm
    have hmn : m < n := by simp only [mem_Icc] at hn hnm; omega
    rw [Nat.div_eq_of_lt hmn,
      ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      mul_zero]
  have hentry (n : ℕ) (hn : n ∈ Icc 1 (T + 1)) :
      naturalCofactorGram ε T n j =
      (∑ m ∈ Icc 1 (T + 1), pmPowerDampedCenteredDivisorPrefix ε (m / n) *
        pmPowerDampedCenteredDivisorPrefix ε (m / j) /
          ((m : ℝ) * ((m : ℝ) + 1))) / dampedMobiusEnergy ε (T + 1) := by
    rw [naturalCofactorGram_pos ε T n j (mem_Icc.mp hn).1]
    rfl
  calc
    _ = (∑ m ∈ Icc 1 (T + 1),
        (∑ n ∈ Icc 1 (T + 1), g n * pmPowerDampedCenteredDivisorPrefix ε (m / n)) *
          pmPowerDampedCenteredDivisorPrefix ε (m / j) /
            ((m : ℝ) * ((m : ℝ) + 1))) / dampedMobiusEnergy ε (T + 1) := by
      unfold dilationCofactorWork pronicPairing rowDilate
      congr 1
      exact sum_congr rfl fun m hm => by rw [hrow m hm]
    _ = _ := by
      simp only [sum_mul, sum_div]
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [hentry n hn]
      simp only [mul_div_assoc, mul_sum, sum_div]
      exact sum_congr rfl fun m _ => by ring

theorem wienerCofactorCovariance_re (ε : SubcriticalDamping) (T : ℕ) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    (wienerCofactorCovariance ε T j a).re = dilationCofactorWork ε (rePart a) j T := by
  rw [wienerCofactorCovariance_eq_sum, dilationCofactorWork_eq_sum]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, rePart]

theorem wienerCofactorCovariance_im (ε : SubcriticalDamping) (T : ℕ) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    (wienerCofactorCovariance ε T j a).im = dilationCofactorWork ε (imPart a) j T := by
  rw [wienerCofactorCovariance_eq_sum, dilationCofactorWork_eq_sum]
  simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add, imPart]

theorem abs_pronicPairing_le (T : ℕ) (v w : ℕ → ℝ) :
    |pronicPairing T v w| ≤ pronicNorm T v * pronicNorm T w := by
  have hp := sum_mul_div_le_pronicNorm T v w
  have hn := sum_mul_div_le_pronicNorm T v (fun n => -w n)
  rw [pronicNorm_neg] at hn
  have heq : (∑ n ∈ Icc 1 T, v n * -w n / ((n : ℝ) * ((n : ℝ) + 1))) =
      -pronicPairing T v w := by
    simp only [pronicPairing, mul_neg, neg_div, sum_neg_distrib]
  rw [heq] at hn
  exact abs_le.mpr ⟨by linarith only [hn], hp⟩

/-- A paid dilation is asymptotically orthogonal to every fixed cofactor row. -/
theorem admits_or_all_dilationCofactorWork_vanish (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (g : ℕ → ℝ), TransHorizonIncidenceMechanics.CriticalWiener g →
        TransHorizonIncidenceMechanics.ReceiverBounded
          (dirichletConv g (pmPowerDampedRealWeight ε)) →
        ∀ j : ℕ+, Tendsto (dilationCofactorWork ε g j) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun g hg hpaid j => ?_
    obtain ⟨B, hB⟩ := exists_pronicNorm_prefixDilation_le_of_repairs ε hg hpaid
    have hzero : Tendsto (fun T => (B * (1 / Real.sqrt (j : ℝ))) /
        Real.sqrt (dampedMobiusEnergy ε (T + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp (hE.comp (tendsto_add_atTop_nat 1)))
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    refine squeeze_zero (fun _ => abs_nonneg _) (fun T => ?_) hzero
    have hET := receiverEnergy_succ_pos ε T
    have hrow := pronicNorm_rowDilate_le_sharp j.property (T + 1)
      (pmPowerDampedCenteredDivisorPrefix ε)
      (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)
    rw [pronicNorm_centeredPrefix] at hrow
    dsimp only [Function.comp_apply]
    rw [dilationCofactorWork, abs_div, abs_of_pos hET]
    calc
      _ ≤ (pronicNorm (T + 1) (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)) *
          pronicNorm (T + 1) (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))) /
            dampedMobiusEnergy ε (T + 1) :=
        div_le_div_of_nonneg_right (abs_pronicPairing_le _ _ _) hET.le
      _ ≤ (B * ((1 / Real.sqrt (j : ℝ)) *
          Real.sqrt (dampedMobiusEnergy ε (T + 1)))) / dampedMobiusEnergy ε (T + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul (hB (T + 1)) hrow (pronicNorm_nonneg _ _)
            ((pronicNorm_nonneg _ _).trans (hB (T + 1)))) hET.le
      _ = _ := by
        have hsqrt := Real.sq_sqrt hET.le
        have hspos : 0 < Real.sqrt (dampedMobiusEnergy ε (T + 1)) :=
          Real.sqrt_pos.mpr hET
        apply (div_eq_div_iff hET.ne' hspos.ne').mpr
        calc
          _ = (B * (1 / Real.sqrt (j : ℝ))) *
              Real.sqrt (dampedMobiusEnergy ε (T + 1)) ^ 2 := by ring
          _ = _ := by rw [hsqrt]

/-- Infinite paid kernels, including both complex components, lose every covariance. -/
theorem admits_or_paid_wienerCofactorCovariance_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ a ∈ paidIdeal (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1),
        ∀ j : ℕ+, Tendsto (fun T => wienerCofactorCovariance ε T j a) atTop (𝓝 0) := by
  rcases admits_or_all_dilationCofactorWork_vanish ε with h | h
  · exact Or.inl h
  · refine Or.inr fun a ha j => ?_
    have hr := h _ (criticalWiener_rePart a) ha.1 j
    have hi := h _ (criticalWiener_imPart a) ha.2 j
    have heq (T : ℕ) : wienerCofactorCovariance ε T j a =
        (dilationCofactorWork ε (rePart a) j T : ℂ) +
          (dilationCofactorWork ε (imPart a) j T : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp only [wienerCofactorCovariance_re, wienerCofactorCovariance_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, zero_add, add_zero, sub_zero]
    have hr' := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    have hi' := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
    have hlim := hr'.add (hi'.mul_const Complex.I)
    simp only [Complex.ofReal_zero, zero_mul, zero_add] at hlim
    exact hlim.congr fun T => (heq T).symm

/-- A common Gram limit passes through every Wiener coefficient series. -/
theorem wienerCofactorCovariance_tendsto (ε : SubcriticalDamping)
    (ns : ℕ → ℕ) (K : ℕ+ → ℕ+ → ℝ)
    (hK : ∀ n j, Tendsto (fun m => cofactorGram ε (ns m) n j) atTop (𝓝 (K n j)))
    (a : WienerAlgebraAt (1 / 2)) (j : ℕ+) :
    Tendsto (fun m => wienerCofactorCovariance ε (ns m) j a) atTop
      (𝓝 (∑' n, a.toFn n * (if hn : 0 < n then (K ⟨n, hn⟩ j : ℂ) else 0))) := by
  apply tendsto_tsum_of_dominated_convergence a.summable_norm
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [naturalCofactorGram_zero, Complex.ofReal_zero, mul_zero,
        dif_neg (Nat.not_lt_zero 0)]
      exact tendsto_const_nhds
    · simp only [naturalCofactorGram_pos ε _ n j hn, dif_pos hn]
      exact tendsto_const_nhds.mul
        (Complex.continuous_ofReal.continuousAt.tendsto.comp (hK ⟨n, hn⟩ j))
  · exact Eventually.of_forall fun m n =>
      norm_coefficient_smul_le (fun n => (naturalCofactorGram ε (ns m) n j : ℂ))
        (by rw [naturalCofactorGram_zero, Complex.ofReal_zero])
        (norm_naturalCofactorGram_le ε (ns m) j) a n

end GaloisForLFunctions.ArithmeticDefectRigidity
