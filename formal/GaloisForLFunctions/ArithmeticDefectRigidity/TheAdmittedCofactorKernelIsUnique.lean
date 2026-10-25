import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The admitted cofactor kernel is unique

Bounded pronic norms give full-horizon energy and pairing limits. Admission
therefore leaves no subsequence choice in the actual cofactor Gram kernel.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Adding nonnegative pronic cells makes every squared row norm monotone in its horizon. -/
theorem pronicNorm_sq_monotone (f : ℕ → ℝ) : Monotone (fun T => pronicNorm T f ^ 2) := by
  intro T U hTU
  change pronicNorm T f ^ 2 ≤ pronicNorm U f ^ 2
  rw [pronicNorm_sq, pronicNorm_sq]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hTU)
    (fun n _ _ => by positivity)

/-- Bounded pronic energy has a finite limit without selecting a subsequence. -/
theorem exists_pronicNorm_sq_limit {f : ℕ → ℝ} {B : ℝ}
    (hB : ∀ T, pronicNorm T f ≤ B) :
    ∃ e : ℝ, Tendsto (fun T => pronicNorm T f ^ 2) atTop (𝓝 e) := by
  refine ⟨⨆ T, pronicNorm T f ^ 2, tendsto_atTop_ciSup (pronicNorm_sq_monotone f) ?_⟩
  refine ⟨B ^ 2, ?_⟩
  rintro _ ⟨T, rfl⟩
  exact pow_le_pow_left₀ (pronicNorm_nonneg T f) (hB T) 2

/-- Polarization gives convergence of every pairing between two paid rows. -/
theorem exists_pronicPairing_limit_of_bounded_norms {f g : ℕ → ℝ} {B C : ℝ}
    (hf : ∀ T, pronicNorm T f ≤ B) (hg : ∀ T, pronicNorm T g ≤ C) :
    ∃ q : ℝ, Tendsto (fun T => pronicPairing T f g) atTop (𝓝 q) := by
  obtain ⟨ef, hef⟩ := exists_pronicNorm_sq_limit hf
  obtain ⟨eg, heg⟩ := exists_pronicNorm_sq_limit hg
  obtain ⟨es, hes⟩ := exists_pronicNorm_sq_limit
    (fun T => (pronicNorm_add_le T f g).trans (add_le_add (hf T) (hg T)))
  have hpol (T : ℕ) : pronicPairing T f g =
      (pronicNorm T (fun n => f n + g n) ^ 2 -
        pronicNorm T f ^ 2 - pronicNorm T g ^ 2) / 2 := by
    simp only [pronicNorm_sq, pronicPairing, ← sum_sub_distrib, sum_div]
    exact sum_congr rfl fun n _ => by ring
  refine ⟨(es - ef - eg) / 2, ?_⟩
  simpa only [hpol] using ((hes.sub hef).sub heg).div_const 2

/-- Admission gives a positive finite receiver energy limit. -/
theorem exists_positive_receiverEnergy_limit_of_admits (ε : SubcriticalDamping)
    (hpaid : Admits dampedMobiusEnergy ε) :
    ∃ e : ℝ, 0 < e ∧ Tendsto (dampedMobiusEnergy ε) atTop (𝓝 e) := by
  have hlim := tendsto_atTop_ciSup (dampedMobiusEnergy_mono ε)
    (admits_iff_bddAbove.mp hpaid)
  refine ⟨_, ?_, hlim⟩
  have hle : dampedMobiusEnergy ε 1 ≤ ⨆ T, dampedMobiusEnergy ε T := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
    exact dampedMobiusEnergy_mono ε hT
  exact (receiverEnergy_succ_pos ε 0).trans_le hle

/-- Every admitted cofactor table converges on the full horizon sequence. -/
theorem exists_cofactorGram_full_limit_of_admits (ε : SubcriticalDamping)
    (hpaid : Admits dampedMobiusEnergy ε) :
    ∃ K : ℕ+ → ℕ+ → ℝ, ∀ j k,
      Tendsto (fun T => cofactorGram ε T j k) atTop (𝓝 (K j k)) := by
  obtain ⟨C, hC⟩ := hpaid
  have hrow (j : ℕ+) (T : ℕ) :
      pronicNorm T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) ≤ Real.sqrt C := by
    have h := pronicNorm_rowDilate_le_sharp j.property T
      (pmPowerDampedCenteredDivisorPrefix ε)
      (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)
    rw [pronicNorm_centeredPrefix] at h
    exact h.trans ((mul_le_of_le_one_left (Real.sqrt_nonneg _)
      (inv_sqrt_pnat_le_one j)).trans (Real.sqrt_le_sqrt (hC T)))
  choose q hq using fun j k =>
    exists_pronicPairing_limit_of_bounded_norms (hrow j) (hrow k)
  obtain ⟨e, he, hE⟩ := exists_positive_receiverEnergy_limit_of_admits ε ⟨C, hC⟩
  refine ⟨fun j k => q j k / e, fun j k => ?_⟩
  exact ((hq j k).div hE he.ne').comp (tendsto_add_atTop_nat 1)

namespace ActualCofactorLimit

/-- Admission leaves no subsequence choice in the actual Gram kernel. -/
theorem kernel_eq_of_admits {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε) :
    kernel L = kernel M := by
  obtain ⟨K, hK⟩ := exists_cofactorGram_full_limit_of_admits ε hpaid
  funext j k
  exact (tendsto_nhds_unique (L.converges j k)
    ((hK j k).comp L.strictMono.tendsto_atTop)).trans
    (tendsto_nhds_unique (M.converges j k)
      ((hK j k).comp M.strictMono.tendsto_atTop)).symm

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.kernel_eq_of_admits
