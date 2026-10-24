import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure
import GaloisForLFunctions.HTGeometry.PointwiseLimitClass

/-!
# A common limit for every fixed cofactor covariance

The actual receiver's cofactor Gram matrices have one common convergent subsequence. Their
limit retains unit receiver mass, every signed mixed covariance, positivity of finite packets
and the sharp contraction of simultaneous integer dilation. The construction does not require
energy admission or concentration in finitely many cells. It does not pass an infinite cofactor
sum through the limit: the moving forcing boundary remains a separate obligation.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The complete signed covariance table of the actual cofactor rows, at receiver scale. -/
def cofactorGram (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) : ℝ :=
  pronicPairing (T + 1)
    (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
    (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) /
      dampedMobiusEnergy ε (T + 1)

/-- The sharp two-cofactor radius supplied by pronic self-similarity. -/
def cofactorGramRadius (j k : ℕ+) : ℝ :=
  (1 / Real.sqrt (j : ℝ)) * (1 / Real.sqrt (k : ℝ))

private theorem abs_pairing_le (T : ℕ) (v w : ℕ → ℝ) :
    |pronicPairing T v w| ≤ pronicNorm T v * pronicNorm T w := by
  have hp := sum_mul_div_le_pronicNorm T v w
  have hn := sum_mul_div_le_pronicNorm T v (fun n => -w n)
  rw [pronicNorm_neg] at hn
  have heq : (∑ n ∈ Icc 1 T, v n * -w n / ((n : ℝ) * ((n : ℝ) + 1))) =
      -pronicPairing T v w := by
    simp only [pronicPairing, mul_neg, neg_div, sum_neg_distrib]
  rw [heq] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

/-- Every normalized mixed cofactor entry has its sharp, horizon-independent radius. -/
theorem abs_cofactorGram_le (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) :
    |cofactorGram ε T j k| ≤ cofactorGramRadius j k := by
  have hE := receiverEnergy_succ_pos ε T
  have hj := pronicNorm_rowDilate_le_sharp j.property (T + 1)
    (pmPowerDampedCenteredDivisorPrefix ε)
    (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)
  have hk := pronicNorm_rowDilate_le_sharp k.property (T + 1)
    (pmPowerDampedCenteredDivisorPrefix ε)
    (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)
  rw [pronicNorm_centeredPrefix] at hj hk
  rw [cofactorGram, abs_div, abs_of_pos hE]
  calc
    _ ≤ (pronicNorm (T + 1) (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) *
        pronicNorm (T + 1) (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε))) /
        dampedMobiusEnergy ε (T + 1) :=
      div_le_div_of_nonneg_right (abs_pairing_le _ _ _) hE.le
    _ ≤ ((1 / Real.sqrt (j : ℝ)) * Real.sqrt (dampedMobiusEnergy ε (T + 1)) *
        ((1 / Real.sqrt (k : ℝ)) * Real.sqrt (dampedMobiusEnergy ε (T + 1)))) /
        dampedMobiusEnergy ε (T + 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul hj hk (pronicNorm_nonneg _ _) (by positivity)) hE.le
    _ = cofactorGramRadius j k := by
      have hnum : (1 / Real.sqrt (j : ℝ)) * Real.sqrt (dampedMobiusEnergy ε (T + 1)) *
          ((1 / Real.sqrt (k : ℝ)) * Real.sqrt (dampedMobiusEnergy ε (T + 1))) =
          cofactorGramRadius j k * dampedMobiusEnergy ε (T + 1) := by
        calc
          _ = cofactorGramRadius j k * Real.sqrt (dampedMobiusEnergy ε (T + 1)) ^ 2 := by
            unfold cofactorGramRadius
            ring
          _ = _ := by rw [Real.sq_sqrt hE.le]
      rw [hnum, mul_div_cancel_right₀ _ hE.ne']

private theorem cofactorGramRadius_le_one (j k : ℕ+) : cofactorGramRadius j k ≤ 1 := by
  have hbound (p : ℕ+) : 1 / Real.sqrt (p : ℝ) ≤ 1 := by
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.property
    have hp0 : (0 : ℝ) < p := by linarith only [hp]
    exact (div_le_one (Real.sqrt_pos.mpr hp0)).mpr (Real.one_le_sqrt.mpr hp)
  exact (mul_le_mul (hbound j) (hbound k) (by positivity) zero_le_one).trans_eq (one_mul 1)

private theorem pairing_symm (T : ℕ) (v w : ℕ → ℝ) :
    pronicPairing T v w = pronicPairing T w v := by
  unfold pronicPairing
  exact sum_congr rfl fun n _ => by ring

theorem cofactorGram_symm (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) :
    cofactorGram ε T j k = cofactorGram ε T k j := by
  unfold cofactorGram
  rw [pairing_symm]

/-- The receiver coordinate survives exactly, before any subsequence is selected. -/
theorem cofactorGram_one_one (ε : SubcriticalDamping) (T : ℕ) :
    cofactorGram ε T 1 1 = 1 := by
  have h : pronicPairing (T + 1) (pmPowerDampedCenteredDivisorPrefix ε)
      (pmPowerDampedCenteredDivisorPrefix ε) = dampedMobiusEnergy ε (T + 1) := by
    rw [← Real.sq_sqrt (dampedMobiusEnergy_nonneg ε (T + 1)),
      ← pronicNorm_centeredPrefix ε (T + 1), pronicNorm_sq]
    simp only [pronicPairing, pow_two]
  change pronicPairing (T + 1) (fun n => pmPowerDampedCenteredDivisorPrefix ε (n / 1))
    (fun n => pmPowerDampedCenteredDivisorPrefix ε (n / 1)) /
    dampedMobiusEnergy ε (T + 1) = 1
  simp only [Nat.div_one]
  rw [h, div_self (receiverEnergy_succ_pos ε T).ne']

private theorem pairing_sum_left (T : ℕ) (S : Finset ℕ+) (c : ℕ+ → ℝ)
    (v : ℕ+ → ℕ → ℝ) (w : ℕ → ℝ) :
    pronicPairing T (fun n => ∑ j ∈ S, c j * v j n) w =
      ∑ j ∈ S, c j * pronicPairing T (v j) w := by
  simp only [pronicPairing, sum_mul, sum_div, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun n _ => ?_
  ring

private theorem pairing_sum_right (T : ℕ) (S : Finset ℕ+) (c : ℕ+ → ℝ)
    (v : ℕ → ℝ) (w : ℕ+ → ℕ → ℝ) :
    pronicPairing T v (fun n => ∑ j ∈ S, c j * w j n) =
      ∑ j ∈ S, c j * pronicPairing T v (w j) := by
  rw [pairing_symm, pairing_sum_left]
  exact sum_congr rfl fun j _ => congrArg (fun x => c j * x) (pairing_symm T (w j) v)

/-- A finite cofactor packet retains its complete quadratic energy in the Gram table. -/
theorem cofactorGram_quadratic_eq (ε : SubcriticalDamping) (T : ℕ)
    (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * cofactorGram ε T j k) =
      pronicNorm (T + 1) (fun n => ∑ j ∈ S, c j *
        pmPowerDampedCenteredDivisorPrefix ε (n / j)) ^ 2 /
          dampedMobiusEnergy ε (T + 1) := by
  have hs : ∀ v : ℕ → ℝ, pronicNorm (T + 1) v ^ 2 = pronicPairing (T + 1) v v := by
    intro v
    simp only [pronicNorm_sq, pronicPairing, pow_two]
  rw [hs, pairing_sum_left]
  simp_rw [pairing_sum_right]
  simp only [cofactorGram, rowDilate, sum_div, mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- Every finite signed packet has nonnegative normalized energy. -/
theorem cofactorGram_quadratic_nonneg (ε : SubcriticalDamping) (T : ℕ)
    (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * cofactorGram ε T j k := by
  rw [cofactorGram_quadratic_eq]
  exact div_nonneg (sq_nonneg _) (receiverEnergy_succ_pos ε T).le

/-- Simultaneous dilation of a finite signed packet costs at most its exact pronic mass ratio. -/
theorem cofactorGram_packet_dilation_le (ε : SubcriticalDamping) (T : ℕ)
    (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * cofactorGram ε T (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * cofactorGram ε T j k) := by
  let v : ℕ → ℝ := fun n => ∑ j ∈ S, c j * pmPowerDampedCenteredDivisorPrefix ε (n / j)
  have hv0 : v 0 = 0 := by
    simp only [v, Nat.zero_div,
      ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      mul_zero, sum_const_zero]
  have heq : (∑ j ∈ S, ∑ k ∈ S, c j * c k * cofactorGram ε T (p * j) (p * k)) =
      pronicNorm (T + 1) (rowDilate p v) ^ 2 / dampedMobiusEnergy ε (T + 1) := by
    have hrow : rowDilate p v = fun n =>
        ∑ j ∈ S, c j * pmPowerDampedCenteredDivisorPrefix ε (n / (p * j : ℕ+)) := by
      funext n
      unfold rowDilate v
      refine sum_congr rfl fun j _ => ?_
      congr 2
      exact Nat.div_div_eq_div_mul n p j
    have hs : ∀ w : ℕ → ℝ, pronicNorm (T + 1) w ^ 2 = pronicPairing (T + 1) w w := by
      intro w
      simp only [pronicNorm_sq, pronicPairing, pow_two]
    rw [hrow, hs, pairing_sum_left]
    simp_rw [pairing_sum_right]
    simp only [cofactorGram, rowDilate, sum_div, mul_sum]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  have hnorm := pronicNorm_rowDilate_le_sharp p.property (T + 1) v hv0
  have hsq := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hnorm 2
  have hp : (0 : ℝ) ≤ p := by positivity
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hp] at hsq
  rw [heq, cofactorGram_quadratic_eq]
  calc
    _ ≤ ((1 / (p : ℝ)) * pronicNorm (T + 1) v ^ 2) /
        dampedMobiusEnergy ε (T + 1) :=
      div_le_div_of_nonneg_right hsq (receiverEnergy_succ_pos ε T).le
    _ = _ := by dsimp only [v]; ring

private theorem finite_sum_tendsto {ι : Type*} (S : Finset ι)
    {f : ℕ → ι → ℝ} {g : ι → ℝ} (h : ∀ j ∈ S, Tendsto (fun n => f n j) atTop (𝓝 (g j))) :
    Tendsto (fun n => ∑ j ∈ S, f n j) atTop (𝓝 (∑ j ∈ S, g j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [sum_empty] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | @insert j S hj ih =>
    simp only [sum_insert hj]
    exact (h j (mem_insert_self _ _)).add (ih fun k hk => h k (mem_insert_of_mem hk))

/-- One subsequence retains all fixed signed cofactor covariances and all finite packet energies. -/
theorem exists_cofactorGram_limit (ε : SubcriticalDamping) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ K : ℕ+ → ℕ+ → ℝ,
      (∀ j k, Tendsto (fun m => cofactorGram ε (ns m) j k) atTop (𝓝 (K j k))) ∧
      K 1 1 = 1 ∧
      (∀ j k, K j k = K k j) ∧
      (∀ j k, |K j k| ≤ cofactorGramRadius j k) ∧
      (∀ (S : Finset ℕ+) (c : ℕ+ → ℝ),
        0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k) ∧
      ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
        (∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k)) ≤
          (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k) := by
  have hmem : ∀ T (jk : ℕ+ × ℕ+), cofactorGram ε T jk.1 jk.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro T jk
    exact abs_le.mp ((abs_cofactorGram_le ε T jk.1 jk.2).trans
      (cofactorGramRadius_le_one jk.1 jk.2))
  obtain ⟨ns, hns, L, _, hL⟩ := HTGeometry.exists_subseq_tendsto_of_mem_Icc hmem
  let K : ℕ+ → ℕ+ → ℝ := fun j k => L (j, k)
  have hlim (j k : ℕ+) : Tendsto (fun m => cofactorGram ε (ns m) j k) atTop (𝓝 (K j k)) :=
    hL (j, k)
  have hq (S : Finset ℕ+) (c : ℕ+ → ℝ) (a : ℕ+ → ℕ+) :
      Tendsto (fun m => ∑ j ∈ S, ∑ k ∈ S,
        c j * c k * cofactorGram ε (ns m) (a j) (a k)) atTop
        (𝓝 (∑ j ∈ S, ∑ k ∈ S, c j * c k * K (a j) (a k))) := by
    apply finite_sum_tendsto S
    intro j _
    apply finite_sum_tendsto S
    intro k _
    exact tendsto_const_nhds.mul (hlim (a j) (a k))
  refine ⟨ns, hns, K, hlim, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hlim 1 1
    simp only [cofactorGram_one_one] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · intro j k
    exact tendsto_nhds_unique (hlim j k)
      ((hlim k j).congr fun m => cofactorGram_symm ε (ns m) k j)
  · intro j k
    exact le_of_tendsto (hlim j k).abs
      (Eventually.of_forall fun m => abs_cofactorGram_le ε (ns m) j k)
  · intro S c
    exact ge_of_tendsto (hq S c id) (Eventually.of_forall fun m =>
      cofactorGram_quadratic_nonneg ε (ns m) S c)
  · intro p S c
    exact le_of_tendsto_of_tendsto' (hq S c fun j => p * j)
      (tendsto_const_nhds.mul (hq S c id)) fun m =>
        cofactorGram_packet_dilation_le ε (ns m) p S c

end GaloisForLFunctions.ArithmeticDefectRigidity
