import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompletedDiagonal
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePhysicalChannels

/-!
# Finite physical bounds for a coherent receiving charge

Harmonic centering is exactly orthogonality to conductor one. Below a small
cutoff, coefficient Cauchy–Schwarz bounds both complete residual moments;
nonnegative completed energies control the remaining Gram discrepancy.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CompletedArithmeticForms
  CriticalArithmeticCorrelationTheory

/-- The conductor-one subspace consists exactly of the harmonic pole mode. -/
theorem conductorSubspace_one_eq_span (N : ℕ) : conductorSubspace 1 N =
    Submodule.span ℝ {normalizedRamanujanHorizonVector 1 N} := by
  unfold conductorSubspace
  congr 1
  ext u
  constructor
  · rintro ⟨m, rfl⟩
    have hm : (m : ℕ) = 1 := by have h := mem_Icc.mp m.property; omega
    simp only [Set.mem_singleton_iff, conductorBasisFamily, hm]
  · intro hu
    obtain rfl := Set.mem_singleton_iff.mp hu
    exact ⟨⟨1, mem_Icc.mpr ⟨le_rfl, le_rfl⟩⟩, rfl⟩

/-- Harmonic neutrality places a literal packet in the polar orthogonal complement. -/
theorem packetVector_mem_pole_orthogonal (N : ℕ) (F : ℕ → ℝ)
    (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) :
    packetVector F N ∈ (conductorSubspace 1 N)ᗮ := by
  rw [conductorSubspace_one_eq_span, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have he : ramanujanHorizonVector 1 N = packetVector (fun _ => (1 : ℝ)) N := by
    ext n
    change normalizedRamanujanMode 1 n / Real.sqrt (n : ℕ) = 1 / Real.sqrt (n : ℕ)
    rw [normalizedRamanujanMode_one]
  rw [normalizedRamanujanHorizonVector, real_inner_smul_left, he, packetVector_inner]
  simp only [one_mul, hF, mul_zero]

/-- The coherent physical charge is exactly orthogonal to the harmonic pole. -/
theorem harmonicPrimeChargeVector_mem_pole_orthogonal {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 1 ≤ N) (t : ℝ) :
    harmonicPrimeChargeVector Q N t ∈ (conductorSubspace 1 N)ᗮ := by
  have hzero := (harmonicPrimeCharge_charge_and_adjunction hQ hN t).1
  simp only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile,
    div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)] at hzero
  exact Submodule.smul_mem _ _ (packetVector_mem_pole_orthogonal N _ hzero)

/-- Weighted absolute coefficient moments cost only a power of the finite cutoff. -/
theorem conductor_abs_moment_sq_le (Q k : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, |a m| * (m : ℝ) ^ k) ^ 2 ≤
      (Q : ℝ) ^ (2 * k + 1) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hc := sum_mul_sq_le_sq_mul_sq (Icc 1 Q) (fun m => |a m|) (fun m => (m : ℝ) ^ k)
  simp only [sq_abs] at hc
  have hs : (∑ m ∈ Icc 1 Q, ((m : ℝ) ^ k) ^ 2) ≤ (Q : ℝ) * (Q : ℝ) ^ (2 * k) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, (Q : ℝ) ^ (2 * k) := by
        apply sum_le_sum
        intro m hm
        rw [← pow_mul, Nat.mul_comm k 2]
        exact pow_le_pow_left₀ (Nat.cast_nonneg m) (by exact_mod_cast (mem_Icc.mp hm).2) _
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  refine hc.trans ((mul_le_mul_of_nonneg_left hs (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq ?_)
  rw [pow_succ]
  ring

private theorem sqrt_square_multiplier_le (S : Finset ℕ) (E a : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hE : ∀ m ∈ S, 0 ≤ E m ∧ E m ≤ M) :
    Real.sqrt (∑ m ∈ S, (E m * a m) ^ 2) * Real.sqrt (∑ m ∈ S, a m ^ 2) ≤
      M * ∑ m ∈ S, a m ^ 2 := by
  have hs : (∑ m ∈ S, (E m * a m) ^ 2) ≤ M ^ 2 * ∑ m ∈ S, a m ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun m hm => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hE m hm).1 (hE m hm).2 2) (sq_nonneg _)
  have hroot := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] at hroot
  refine (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)).trans_eq ?_
  rw [mul_assoc, Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]

/-- Completed energies bound the polarized Gram error by the ordinary coefficient square. -/
theorem completedConductor_gram_cost_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 1 ≤ c) (Q : ℕ) (a : ℕ → ℝ) :
    Real.sqrt (∑ m ∈ Icc 1 Q, (completedConductorEnergy φ c m * a m) ^ 2) *
      Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
        (|completeWeilSelfFinitePart φ 1| + 3) * (1 + Real.log Q) *
          ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hD : 0 ≤ |completeWeilSelfFinitePart φ 1| + 3 := by positivity
  have hlogQ := Real.log_natCast_nonneg Q
  apply sqrt_square_multiplier_le (Icc 1 Q) _ a (mul_nonneg hD (by linarith only [hlogQ]))
  intro m hm
  have hm0 := (mem_Icc.mp hm).1
  refine ⟨completedConductorEnergy_nonneg hφ hsupp hM (zero_lt_one.trans_le hc) hm0, ?_⟩
  have hlog := Real.log_le_log (show (0 : ℝ) < m by exact_mod_cast hm0)
    (show (m : ℝ) ≤ Q by exact_mod_cast (mem_Icc.mp hm).2)
  have hE := completedConductorEnergy_le_logarithmic_uniform hφ hsupp hM hc hm0
  have hprod := mul_nonneg (add_nonneg (abs_nonneg (completeWeilSelfFinitePart φ 1)) zero_le_one) hlogQ
  nlinarith only [hE, hlog, hprod]

/-- A finite cutoff gives an absolute complete-energy bound, retaining the full completed diagonal. -/
theorem exists_harmonicPrimeCharge_small_cutoff_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → Q * Q ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N → ∀ t : ℝ,
      let D := |completeWeilSelfFinitePart φ 1| + 3
      let P := (|t| + 8 * |t| / primePoleScale Q) / Real.log N
      let s := t / primePoleScale Q
      let S := ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)
      |completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t)| ≤
        D * (P ^ 2 + s ^ 2 * (S + primePoleScale Q)) +
          (K * ((Q : ℝ) ^ 5 * c / Real.log N + (Q : ℝ) ^ 11 * c ^ 5 * Real.log N / N) +
            9 * D * (1 + Real.log Q) ^ 2 / Real.log N) * (P ^ 2 + s ^ 2 * S) := by
  obtain ⟨K, hK, hbound⟩ := exists_complete_packet_diagonal_error_bound hφ hsupp hM
  refine ⟨K, hK, ?_⟩
  intro Q N c hQ hQ2 hframe hc hrad hc4 t
  dsimp only
  let a := harmonicPrimeChargeCoefficients Q N t
  let A := ∑ m ∈ Icc 1 Q, a m ^ 2
  let D := |completeWeilSelfFinitePart φ 1| + 3
  let Z := ((|t| + 8 * |t| / primePoleScale Q) / Real.log N) ^ 2 +
    (t / primePoleScale Q) ^ 2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)
  have hQN : Q ≤ N := by
    have h := Nat.mul_le_mul_left Q (show 1 ≤ Q by omega)
    simp only [mul_one] at h
    exact h.trans hQ2
  have hL : 0 < Real.log N := by linarith only [hframe, Real.log_natCast_nonneg Q]
  have hA : A ≤ Z := harmonicPrimeCharge_coefficient_square_le hQ hQN t
  have h2 := conductor_abs_moment_sq_le Q 2 a
  have h5 := conductor_abs_moment_sq_le Q 5 a
  norm_num only [show 2 * 2 + 1 = 5 by norm_num] at h2
  norm_num only [show 2 * 5 + 1 = 11 by norm_num] at h5
  have hGram := completedConductor_gram_cost_le hφ hsupp hM hc Q a
  have herr := hbound hQ hQ2 hframe hc hrad hc4 a
  dsimp only at herr
  rw [← harmonicPrimeChargeVector_eq_sum Q N t] at herr
  have hErr : |completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t) -
      ∑ m ∈ Icc 1 Q, completedConductorEnergy φ c m * a m ^ 2| ≤
      (K * ((Q : ℝ) ^ 5 * c / Real.log N + (Q : ℝ) ^ 11 * c ^ 5 * Real.log N / N) +
        9 * D * (1 + Real.log Q) ^ 2 / Real.log N) * A := by
    refine herr.trans ?_
    have hMom := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left h2
        (show 0 ≤ c / Real.log N by positivity))
        (mul_le_mul_of_nonneg_left h5
          (show 0 ≤ c ^ 5 * Real.log N / N by positivity))) hK.le
    have hG : 9 * (1 + Real.log Q) / Real.log N *
        Real.sqrt (∑ m ∈ Icc 1 Q, (completedConductorEnergy φ c m * a m) ^ 2) *
          Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
        (9 * (1 + Real.log Q) / Real.log N) * (D * (1 + Real.log Q) * A) := by
      simpa only [mul_assoc, D, A] using mul_le_mul_of_nonneg_left hGram
        (show 0 ≤ 9 * (1 + Real.log Q) / Real.log N by positivity)
    exact (add_le_add hMom hG).trans_eq (by dsimp only [D, A]; ring)
  have hErr' := hErr.trans (mul_le_mul_of_nonneg_left hA (by
    dsimp only [D]
    have hlog := Real.log_natCast_nonneg Q
    positivity))
  have hDiag := harmonicPrimeCharge_completed_diagonal_le hφ hsupp hM hc hQ hQN t
  have hDiag0 := harmonicPrimeCharge_completed_diagonal_nonneg hφ hsupp hM
    (zero_lt_one.trans_le hc) Q N t
  calc
    _ = |(completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t) -
        ∑ m ∈ Icc 1 Q, completedConductorEnergy φ c m * a m ^ 2) +
        ∑ m ∈ Icc 1 Q, completedConductorEnergy φ c m * a m ^ 2| := by
      congr 1
      ring
    _ ≤ |completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t) -
        ∑ m ∈ Icc 1 Q, completedConductorEnergy φ c m * a m ^ 2| +
        |∑ m ∈ Icc 1 Q, completedConductorEnergy φ c m * a m ^ 2| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hDiag0]
      exact (add_le_add hErr' hDiag).trans_eq (by dsimp only [D, Z]; ring)

#print axioms packetVector_mem_pole_orthogonal
#print axioms harmonicPrimeChargeVector_mem_pole_orthogonal
#print axioms completedConductor_gram_cost_le
#print axioms exists_harmonicPrimeCharge_small_cutoff_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
