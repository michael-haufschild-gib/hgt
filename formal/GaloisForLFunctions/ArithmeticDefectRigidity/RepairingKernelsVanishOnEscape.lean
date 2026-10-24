import GaloisForLFunctions.ArithmeticDefectRigidity.CountableCofactorCovariancesHaveACommonLimit
import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorIsAntipodalOnEscape
import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationCalculusOnIntegerPrefixes

/-!
# Repairing kernels vanish in receiver escape limits

Convolution of a centered divisor prefix differs from its cofactor dilation by a
bounded pronic-norm correction. Consequently every critical Wiener kernel which
repairs a weight has bounded dilation energy. For the actual Möbius receiver,
that energy vanishes after normalization along escape. Finite repairing packets
therefore lie in the nullspace of every limiting cofactor Gram form.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics (weightCenteredPrefix)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The critical Wiener norm uniformly controls cofactor dilation. This estimate
allows infinite kernels to be approximated before taking a Gram limit. -/
theorem pronicNorm_prefixDilation_le {g : ℕ → ℝ}
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g)
    (v : ℕ → ℝ) (hv0 : v 0 = 0) (T : ℕ) :
    TransHorizonIncidenceMechanics.pronicNorm (prefixDilation g v) T ≤
      (∑' n : ℕ, |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
        TransHorizonIncidenceMechanics.pronicNorm v T := by
  have hrow : ∀ n ∈ Icc 1 T,
      prefixDilation g v n = ∑ q ∈ Icc 1 T, g q * v (n / q) := by
    intro n hn
    apply sum_subset (Icc_subset_Icc le_rfl (mem_Icc.mp hn).2)
    intro q hq hqn
    have hlt : n < q := by simp only [mem_Icc] at hq hqn; omega
    rw [Nat.div_eq_of_lt hlt, hv0, mul_zero]
  rw [TransHorizonIncidenceMechanics.pronicNorm_congr hrow]
  refine (TransHorizonIncidenceMechanics.pronicNorm_sum_le _ _ T).trans ?_
  have hfin : (∑ q ∈ Icc 1 T, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
    hg.sum_le_tsum _ fun q _ => by positivity
  calc
    _ ≤ (∑ q ∈ Icc 1 T, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) *
        TransHorizonIncidenceMechanics.pronicNorm v T := by
      rw [sum_mul]
      refine sum_le_sum fun q hq => ?_
      rw [TransHorizonIncidenceMechanics.pronicNorm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (TransHorizonIncidenceMechanics.pronicNorm_dilate_le v hv0 (mem_Icc.mp hq).1 T)
        (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin
      (TransHorizonIncidenceMechanics.pronicNorm_nonneg v T)

/-- Convolution payment is exactly boundedness of its cofactor dilation; the
mean correction is paid by the critical Wiener norm. -/
theorem receiverBounded_iff_prefixDilation_bounded {g c : ℕ → ℝ}
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g) (hc : Summable fun n : ℕ => |c n / n|) :
    TransHorizonIncidenceMechanics.ReceiverBounded (dirichletConv g c) ↔
      ∃ B : ℝ, ∀ T : ℕ,
        TransHorizonIncidenceMechanics.pronicNorm (prefixDilation g (weightCenteredPrefix c (∑' n : ℕ, c n / n))) T ≤ B := by
  let mg := ∑' n : ℕ, g n / n
  let mc := ∑' n : ℕ, c n / n
  let C := |mc| * ((Real.sqrt 2 + 1) *
    ∑' n : ℕ, |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)))
  have hmean : ∑' n : ℕ, dirichletConv g c n / n = mg * mc :=
    (TransHorizonIncidenceMechanics.hasSum_dirichletConv_div hg.summable_abs_div.of_abs.hasSum hc.of_abs.hasSum
      hg.summable_abs_div hc).tsum_eq
  have hcor (T : ℕ) :
      TransHorizonIncidenceMechanics.pronicNorm (fun n => mc * weightCenteredPrefix g mg n) T ≤ C := by
    rw [TransHorizonIncidenceMechanics.pronicNorm_smul]
    exact mul_le_mul_of_nonneg_left
      (TransHorizonIncidenceMechanics.pronicNorm_weightCenteredPrefix_le_critical hg T) (abs_nonneg mc)
  have hid : weightCenteredPrefix (dirichletConv g c) (mg * mc) =
      fun n => prefixDilation g (weightCenteredPrefix c mc) n +
        mc * weightCenteredPrefix g mg n :=
    funext fun n => TransHorizonIncidenceMechanics.weightCenteredPrefix_dirichletConv g c mg mc n
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨Real.sqrt E + C, fun T => ?_⟩
    have hpaid : TransHorizonIncidenceMechanics.pronicNorm (weightCenteredPrefix (dirichletConv g c) (mg * mc)) T ≤
        Real.sqrt E := by
      have h := hE T
      rw [hmean, TransHorizonIncidenceMechanics.weightPronicEnergy_eq_sq_pronicNorm] at h
      simpa only [Real.sqrt_sq (TransHorizonIncidenceMechanics.pronicNorm_nonneg _ T)] using
        Real.sqrt_le_sqrt h
    have hsub : prefixDilation g (weightCenteredPrefix c mc) =
        fun n => weightCenteredPrefix (dirichletConv g c) (mg * mc) n +
          (-mc) * weightCenteredPrefix g mg n := by
      funext n
      rw [hid]
      ring
    rw [hsub]
    refine (TransHorizonIncidenceMechanics.pronicNorm_add_le _ _ T).trans (add_le_add hpaid ?_)
    rw [TransHorizonIncidenceMechanics.pronicNorm_smul, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (TransHorizonIncidenceMechanics.pronicNorm_weightCenteredPrefix_le_critical hg T) (abs_nonneg mc)
  · rintro ⟨B, hB⟩
    refine ⟨(B + C) ^ 2, fun T => ?_⟩
    rw [hmean, TransHorizonIncidenceMechanics.weightPronicEnergy_eq_sq_pronicNorm]
    apply pow_le_pow_left₀ (TransHorizonIncidenceMechanics.pronicNorm_nonneg _ T)
    rw [hid]
    exact (TransHorizonIncidenceMechanics.pronicNorm_add_le _ _ T).trans (add_le_add (hB T) (hcor T))

/-- A repairing kernel has uniformly bounded dilation norm on the actual source. -/
theorem exists_pronicNorm_prefixDilation_le_of_repairs (ε : SubcriticalDamping)
    {g : ℕ → ℝ} (hg : TransHorizonIncidenceMechanics.CriticalWiener g)
    (hpaid : TransHorizonIncidenceMechanics.ReceiverBounded
      (dirichletConv g (pmPowerDampedRealWeight ε))) :
    ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm T (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)) ≤ B := by
  have hp : weightCenteredPrefix (pmPowerDampedRealWeight ε)
      (∑' n : ℕ, pmPowerDampedRealWeight ε n / n) =
      pmPowerDampedCenteredDivisorPrefix ε := by
    funext n
    rw [(TransHorizonIncidenceMechanics.hasSum_pmPowerDampedRealWeight_div ε.property.1).tsum_eq,
      weightCenteredPrefix, pmPowerDampedCenteredDivisorPrefix_eq]
    rfl
  obtain ⟨B, hB⟩ := (receiverBounded_iff_prefixDilation_bounded hg
    (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1)).mp hpaid
  refine ⟨B, fun T => ?_⟩
  rw [hp] at hB
  exact hB T

/-- Squared cofactor-dilation norm at the receiver's own scale. -/
def normalizedDilationEnergy (ε : SubcriticalDamping) (g : ℕ → ℝ) (T : ℕ) : ℝ :=
  pronicNorm (T + 1) (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 /
    dampedMobiusEnergy ε (T + 1)

theorem normalizedDilationEnergy_nonneg (ε : SubcriticalDamping) (g : ℕ → ℝ) (T : ℕ) :
    0 ≤ normalizedDilationEnergy ε g T :=
  div_nonneg (sq_nonneg _) (receiverEnergy_succ_pos ε T).le

/-- Either the actual receiver is admitted, or every critical Wiener repair
annihilates its normalized cofactor state. The alternative is simultaneous in
all kernels and needs no finite-support restriction. -/
theorem admits_or_all_repairs_vanish (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ g : ℕ → ℝ, TransHorizonIncidenceMechanics.CriticalWiener g →
        TransHorizonIncidenceMechanics.ReceiverBounded
          (dirichletConv g (pmPowerDampedRealWeight ε)) →
        Tendsto (normalizedDilationEnergy ε g) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun g hg hpaid => ?_
    obtain ⟨B, hB⟩ := exists_pronicNorm_prefixDilation_le_of_repairs ε hg hpaid
    have hzero : Tendsto (fun T => B ^ 2 / dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hE.comp (tendsto_add_atTop_nat 1))
    refine squeeze_zero (normalizedDilationEnergy_nonneg ε g) (fun T => ?_) hzero
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB (T + 1)) 2)
      (receiverEnergy_succ_pos ε T).le

/-- Both real components of every element of the repairing ideal vanish on
escape. This is the complex Wiener ideal's annihilation law in Gram coordinates. -/
theorem admits_or_paidIdeal_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ k ∈ ArithmeticOrientationTheory.paidIdeal (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1),
        Tendsto (fun T =>
          normalizedDilationEnergy ε (ArithmeticOrientationTheory.rePart k) T +
          normalizedDilationEnergy ε (ArithmeticOrientationTheory.imPart k) T) atTop (𝓝 0) := by
  rcases admits_or_all_repairs_vanish ε with h | h
  · exact Or.inl h
  · refine Or.inr fun k hk => ?_
    have hr := h _ (ArithmeticOrientationTheory.criticalWiener_rePart k) hk.1
    have hi := h _ (ArithmeticOrientationTheory.criticalWiener_imPart k) hk.2
    simpa only [add_zero] using hr.add hi

/-- A finite real packet as a kernel on the positive integers. -/
def finiteCofactorKernel (S : Finset ℕ+) (c : ℕ+ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ S, if (j : ℕ) = n then c j else 0

/-- Finite packets belong to the critical Wiener algebra. -/
theorem criticalWiener_finiteCofactorKernel (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    TransHorizonIncidenceMechanics.CriticalWiener (finiteCofactorKernel S c) := by
  apply summable_of_ne_finset_zero (s := S.image (fun j : ℕ+ => (j : ℕ)))
  intro n hn
  have hz : finiteCofactorKernel S c n = 0 := by
    apply sum_eq_zero
    intro j hj
    exact if_neg fun h => hn (mem_image.mpr ⟨j, hj, h⟩)
  simp only [hz, abs_zero, zero_mul]

/-- The finite kernel acts by exactly its listed cofactor packet. -/
theorem prefixDilation_finiteCofactorKernel (S : Finset ℕ+) (c : ℕ+ → ℝ)
    (v : ℕ → ℝ) (hv0 : v 0 = 0) (n : ℕ) :
    prefixDilation (finiteCofactorKernel S c) v n = ∑ j ∈ S, c j * v (n / j) := by
  simp only [prefixDilation, finiteCofactorKernel, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) ≤ n
  · simp [j.property, hj]
  · have hd : n / (j : ℕ) = 0 := Nat.div_eq_of_lt (lt_of_not_ge hj)
    simp [hj, hd, hv0]

/-- The finite part of the Wiener action is already recorded in the cofactor Gram table. -/
theorem normalizedDilationEnergy_finiteCofactorKernel (ε : SubcriticalDamping)
    (S : Finset ℕ+) (c : ℕ+ → ℝ) (T : ℕ) :
    normalizedDilationEnergy ε (finiteCofactorKernel S c) T =
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * cofactorGram ε T j k := by
  have hrow : prefixDilation (finiteCofactorKernel S c)
      (pmPowerDampedCenteredDivisorPrefix ε) =
      fun n => ∑ j ∈ S, c j * pmPowerDampedCenteredDivisorPrefix ε (n / j) :=
    funext fun n => prefixDilation_finiteCofactorKernel S c _
      (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε) n
  rw [normalizedDilationEnergy, hrow, cofactorGram_quadratic_eq]

end GaloisForLFunctions.ArithmeticDefectRigidity
