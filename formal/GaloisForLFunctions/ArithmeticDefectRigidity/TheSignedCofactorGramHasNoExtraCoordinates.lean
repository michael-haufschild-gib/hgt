import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit
import GaloisForLFunctions.ArithmeticDefectRigidity.FixedCofactorsHaveAHarmonicBoundaryTrace

/-!
# The signed cofactor Gram table

The globally bounded forcing remainder disappears at receiver scale. Every
actual common limit therefore determines all fixed receiver, residual, and
forcing covariances, together with vanishing normalized fixed pole traces.
-/
noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open scoped InnerProductSpace
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem tendsto_zero_of_square_tendsto_zero {f : ℕ → ℝ}
    (h : Tendsto (fun n => f n ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hs

private theorem pairing_comm (T : ℕ) (v w : ℕ → ℝ) :
    pronicPairing T v w = pronicPairing T w v := by
  unfold pronicPairing
  exact sum_congr rfl fun n _ => by ring

private theorem norm_dilated_forcing_le (ε : SubcriticalDamping) (j : ℕ+) (T : ℕ) :
    pronicNorm T (rowDilate j (forcingRemainder ε)) ≤ forcingRemainderBudget ε := by
  have h := pronicNorm_rowDilate_le_sharp j.property T (forcingRemainder ε)
    (forcingRemainder_zero ε)
  exact h.trans ((mul_le_mul_of_nonneg_left (pronicNorm_forcingRemainder_le ε T)
    (by positivity)).trans (mul_le_of_le_one_left (forcingRemainderBudget_nonneg ε)
      (inv_sqrt_pnat_le_one j)))

private theorem norm_dilated_receiver_le (ε : SubcriticalDamping) (j : ℕ+) (T : ℕ) :
    pronicNorm T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) ≤
      Real.sqrt (dampedMobiusEnergy ε T) := by
  have h := pronicNorm_rowDilate_le_sharp j.property T
    (pmPowerDampedCenteredDivisorPrefix ε)
    (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)
  rw [pronicNorm_centeredPrefix] at h
  exact h.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) (inv_sqrt_pnat_le_one j))

/-- A forcing-remainder cofactor paired with a receiver cofactor at receiver scale. -/
def forcingReceiverCovariance (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) : ℝ :=
  pronicPairing (T + 1) (rowDilate j (forcingRemainder ε))
    (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) /
      dampedMobiusEnergy ε (T + 1)

/-- The normalized Gram table of the paid forcing remainder. -/
def forcingRemainderGram (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) : ℝ :=
  pronicPairing (T + 1) (rowDilate j (forcingRemainder ε))
    (rowDilate k (forcingRemainder ε)) / dampedMobiusEnergy ε (T + 1)

/-- The mixed error has a uniform bound independent of both cofactor indices. -/
theorem forcingReceiverCovariance_sq_le (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) :
    forcingReceiverCovariance ε T j k ^ 2 ≤
      forcingRemainderBudget ε ^ 2 / dampedMobiusEnergy ε (T + 1) := by
  have hE := receiverEnergy_succ_pos ε T
  have hp := (abs_pronicPairing_le (T + 1) (rowDilate j (forcingRemainder ε))
    (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε))).trans
    (mul_le_mul (norm_dilated_forcing_le ε j (T + 1))
      (norm_dilated_receiver_le ε k (T + 1)) (pronicNorm_nonneg _ _)
      (forcingRemainderBudget_nonneg ε))
  have hs := pow_le_pow_left₀ (abs_nonneg _) hp 2
  simp only [sq_abs, mul_pow, Real.sq_sqrt hE.le] at hs
  unfold forcingReceiverCovariance
  rw [div_pow]
  calc
    _ ≤ (forcingRemainderBudget ε ^ 2 * dampedMobiusEnergy ε (T + 1)) /
        dampedMobiusEnergy ε (T + 1) ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp [hE.ne']

theorem abs_forcingRemainderGram_le (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) :
    |forcingRemainderGram ε T j k| ≤
      forcingRemainderBudget ε ^ 2 / dampedMobiusEnergy ε (T + 1) := by
  have hE := receiverEnergy_succ_pos ε T
  unfold forcingRemainderGram
  rw [abs_div, abs_of_pos hE]
  apply div_le_div_of_nonneg_right _ hE.le
  exact (abs_pronicPairing_le _ _ _).trans (by
    simpa only [pow_two] using mul_le_mul (norm_dilated_forcing_le ε j (T + 1))
      (norm_dilated_forcing_le ε k (T + 1)) (pronicNorm_nonneg _ _)
      (forcingRemainderBudget_nonneg ε))

/-- Every fixed forcing covariance vanishes along the full escaping horizon sequence. -/
theorem admits_or_forcing_covariances_vanish (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ j k : ℕ+,
      Tendsto (fun T => forcingReceiverCovariance ε T j k) atTop (𝓝 0) ∧
      Tendsto (fun T => forcingRemainderGram ε T j k) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · have hB : Tendsto (fun T => forcingRemainderBudget ε ^ 2 /
        dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hE.comp (tendsto_add_atTop_nat 1))
    refine Or.inr fun j k => ⟨?_, ?_⟩
    · exact tendsto_zero_of_square_tendsto_zero (squeeze_zero (fun T => sq_nonneg _)
        (fun T => forcingReceiverCovariance_sq_le ε T j k) hB)
    · rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero (fun T => abs_nonneg _) (fun T => abs_forcingRemainderGram_le ε T j k) hB

/-- The three source rows retained after the forcing power has been subtracted. -/
inductive CofactorComponent
  | receiver
  | residual
  | forcing

/-- The receiver coefficient that survives normalization. -/
def CofactorComponent.sign : CofactorComponent → ℝ
  | .receiver => 1
  | .residual => -1
  | .forcing => 0

/-- The coefficient of the paid forcing remainder in the exact source split. -/
def CofactorComponent.remainderCoefficient : CofactorComponent → ℝ
  | .receiver => 0
  | .residual => 1
  | .forcing => 1

def cofactorComponentRow (ε : SubcriticalDamping) : CofactorComponent → (ℕ → ℝ)
  | .receiver => pmPowerDampedCenteredDivisorPrefix ε
  | .residual => renormalizedCofactor ε
  | .forcing => forcingRemainder ε

private theorem component_row_decomposition (ε : SubcriticalDamping) (b : CofactorComponent) :
    cofactorComponentRow ε b = fun n => b.sign * pmPowerDampedCenteredDivisorPrefix ε n +
      b.remainderCoefficient * forcingRemainder ε n := by
  funext n
  cases b with
  | receiver => simp only [cofactorComponentRow, CofactorComponent.sign,
      CofactorComponent.remainderCoefficient, one_mul, zero_mul, add_zero]
  | forcing => simp only [cofactorComponentRow, CofactorComponent.sign,
      CofactorComponent.remainderCoefficient, one_mul, zero_mul, zero_add]
  | residual =>
    have hzero : renormalizedCofactor ε 0 = 0 := by
      have h := actual_renormalizedCofactor_mem_poleTraceDomain ε
      rw [renormalizedCofactorOperator_actualTraceVector] at h
      exact h.1
    cases n with
    | zero => simp only [cofactorComponentRow, CofactorComponent.sign,
        CofactorComponent.remainderCoefficient, hzero,
        ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
        forcingRemainder_zero, mul_zero, add_zero]
    | succ n =>
      have h := receiver_add_renormalizedCofactor_eq ε n
      change renormalizedCofactor ε (n + 1) =
        (-1) * pmPowerDampedCenteredDivisorPrefix ε (n + 1) +
          1 * forcingRemainder ε (n + 1)
      linarith only [h]

private theorem pairing_linear_combinations (T : ℕ) (a b c d : ℝ) (v w x y : ℕ → ℝ) :
    pronicPairing T (fun n => a * v n + b * w n) (fun n => c * x n + d * y n) =
      a * c * pronicPairing T v x + a * d * pronicPairing T v y +
        b * c * pronicPairing T w x + b * d * pronicPairing T w y := by
  simp only [pronicPairing, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- The actual joint signed Gram table of receiver, residual, and paid forcing rows. -/
def signedCofactorGram (ε : SubcriticalDamping) (T : ℕ)
    (b c : CofactorComponent) (j k : ℕ+) : ℝ :=
  pronicPairing (T + 1) (rowDilate j (cofactorComponentRow ε b))
    (rowDilate k (cofactorComponentRow ε c)) / dampedMobiusEnergy ε (T + 1)

theorem signedCofactorGram_decomposition (ε : SubcriticalDamping) (T : ℕ)
    (b c : CofactorComponent) (j k : ℕ+) :
    signedCofactorGram ε T b c j k = b.sign * c.sign * cofactorGram ε T j k +
      b.sign * c.remainderCoefficient * forcingReceiverCovariance ε T k j +
      b.remainderCoefficient * c.sign * forcingReceiverCovariance ε T j k +
      b.remainderCoefficient * c.remainderCoefficient * forcingRemainderGram ε T j k := by
  unfold signedCofactorGram
  rw [component_row_decomposition, component_row_decomposition]
  change pronicPairing (T + 1)
    (fun n => b.sign * rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n +
      b.remainderCoefficient * rowDilate j (forcingRemainder ε) n)
    (fun n => c.sign * rowDilate k (pmPowerDampedCenteredDivisorPrefix ε) n +
      c.remainderCoefficient * rowDilate k (forcingRemainder ε) n) / _ = _
  rw [pairing_linear_combinations]
  rw [pairing_comm (T + 1) (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
    (rowDilate k (forcingRemainder ε))]
  unfold cofactorGram forcingReceiverCovariance forcingRemainderGram
  ring

namespace ActualCofactorLimit

/-- The complete fixed signed Gram table converges along the original common subsequence. -/
theorem admits_or_signedCofactorGram_tendsto {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨ ∀ (b c : CofactorComponent) (j k : ℕ+),
      Tendsto (fun m => signedCofactorGram ε (L.subsequence m) b c j k) atTop
        (𝓝 (b.sign * c.sign * L.kernel j k)) := by
  rcases admits_or_forcing_covariances_vanish ε with h | h
  · exact Or.inl h
  · refine Or.inr fun b c j k => ?_
    simp_rw [signedCofactorGram_decomposition]
    have hm := L.strictMono.tendsto_atTop
    simpa only [Function.comp_apply, mul_zero, add_zero] using
      ((((L.converges j k).const_mul (b.sign * c.sign)).add
        (((h k j).1.comp hm).const_mul (b.sign * c.remainderCoefficient))).add
        (((h j k).1.comp hm).const_mul (b.remainderCoefficient * c.sign))).add
        (((h j k).2.comp hm).const_mul (b.remainderCoefficient * c.remainderCoefficient))

/-- All limiting signed coordinates already live in the original cofactor Hilbert module. -/
def componentVector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (b : CofactorComponent) (j : ℕ+) : Hilbert L := (b.sign : ℂ) • vector L j

theorem inner_componentVector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (b c : CofactorComponent) (j k : ℕ+) :
    ⟪componentVector L c k, componentVector L b j⟫_ℂ =
      ((b.sign * c.sign * L.kernel j k : ℝ) : ℂ) := by
  simp only [componentVector, inner_smul_left, inner_smul_right, inner_vector,
    Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end ActualCofactorLimit

/-- Fixed source pole traces disappear at the escaping receiver's Hilbert scale. -/
theorem admits_or_normalized_fixed_poleTrace_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ j : ℕ+,
      Tendsto (fun T => poleTrace ε (traceDilation ε j (actualTraceVector ε)) /
        Real.sqrt (dampedMobiusEnergy ε (T + 1))) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun j => tendsto_zero_of_square_tendsto_zero ?_
    simp only [div_pow, Real.sq_sqrt (dampedMobiusEnergy_nonneg ε _)]
    exact tendsto_const_nhds.div_atTop (hE.comp (tendsto_add_atTop_nat 1))

end GaloisForLFunctions.ArithmeticDefectRigidity
