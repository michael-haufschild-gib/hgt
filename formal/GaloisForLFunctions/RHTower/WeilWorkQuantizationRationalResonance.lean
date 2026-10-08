import GaloisForLFunctions.RHTower.WeilWorkQuantizationPhaseCoupling
import Mathlib.Data.Nat.MaxPowDiv

/-!
# Exact one-sided rational resonance rows

The actual canonical phase supplies finite triangular equations for a rational
base u/v. Coprimality retains every resonance and fixes the nonzero constant
coefficient. No phase representation is asserted to follow from positivity.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz HamburgerStability HamburgerTwisted PhaseLockRigidity IntegerMassRigidity
  GaloisForLFunctions.HTGeometry

theorem quantization_rational_resonance_iff {u v m n k : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) :
    quantizationFrequencyResonates (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) m n ↔
      1 ≤ n ∧ n * u ^ k = m * v ^ k := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlr : Real.log ((u : ℝ) / v) = Real.log u - Real.log v :=
    Real.log_div huR.ne' hvR.ne'
  constructor
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hl : Real.log ((n : ℝ) * (u : ℝ) ^ k) =
        Real.log ((m : ℝ) * (v : ℝ) ^ k) := by
      rw [Real.log_mul hnR.ne' (pow_pos huR k).ne',
        Real.log_mul hmR.ne' (pow_pos hvR k).ne', Real.log_pow, Real.log_pow]
      rw [hlr] at he
      linarith
    have he' := congrArg Real.exp hl
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at he'
    exact_mod_cast he'
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heR : (n : ℝ) * (u : ℝ) ^ k = (m : ℝ) * (v : ℝ) ^ k := by
      exact_mod_cast he
    have hl := congrArg Real.log heR
    rw [Real.log_mul hnR.ne' (pow_pos huR k).ne',
      Real.log_mul hmR.ne' (pow_pos hvR k).ne', Real.log_pow, Real.log_pow] at hl
    rw [hlr]
    linarith

theorem quantization_rational_residue {lam : ℕ → ℝ} {u v m : ℕ}
    (hu : 2 ≤ u) (hv : 1 ≤ v) (huv : u.Coprime v) (hm : 1 ≤ m) (k : ℕ) :
    quantizationFrequencyResidue lam (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) m =
      if k ≤ padicValNat u m then
        (Real.exp ((2 * (k : ℝ) * Real.log ((u : ℝ) / v)) / 4) : ℂ) *
          dirichletExp (lamLog lam) (m / u ^ k * v ^ k)
      else 0 := by
  classical
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have hm0 : 0 < m := by omega
  have hcop := (huv.pow_left k).pow_right k
  by_cases hk : k ≤ padicValNat u m
  · rw [if_pos hk]
    have hd : u ^ k ∣ m := (Nat.pow_dvd_iff_le_padicValNat (by omega) hm0.ne').mpr hk
    apply quantizationFrequencyResidue_eq
    apply (quantization_rational_resonance_iff hu0 hv0 hm0).mpr
    refine ⟨Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hm0 hd) (pow_pos hu0 k))
      (pow_pos hv0 k), ?_⟩
    rw [Nat.mul_right_comm, Nat.div_mul_cancel hd]
  · rw [if_neg hk]
    have hnone : ¬∃ n : ℕ,
        quantizationFrequencyResonates (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) m n := by
      rintro ⟨n, hn⟩
      have he := ((quantization_rational_resonance_iff hu0 hv0 hm0).mp hn).2
      have hd : u ^ k ∣ m * v ^ k := he ▸ dvd_mul_left (u ^ k) n
      have hd' := hcop.dvd_of_dvd_mul_right hd
      exact hk ((Nat.pow_dvd_iff_le_padicValNat (by omega) hm0.ne').mp hd')
    simp only [quantizationFrequencyResidue, dif_neg hnone]

theorem quantization_rational_residue_sum {lam : ℕ → ℝ} {u v m : ℕ}
    (hu : 2 ≤ u) (hv : 1 ≤ v) (huv : u.Coprime v) (hm : 1 ≤ m) (p : ℕ → ℂ) :
    (∑' k : ℕ, p k * quantizationFrequencyResidue lam
      (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) m) =
      ∑ k ∈ Finset.range (padicValNat u m + 1),
        (p k * (Real.exp ((2 * (k : ℝ) * Real.log ((u : ℝ) / v)) / 4) : ℂ)) *
          dirichletExp (lamLog lam) (m / u ^ k * v ^ k) := by
  classical
  rw [tsum_eq_sum (s := Finset.range (padicValNat u m + 1))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [quantization_rational_residue hu hv huv hm, if_pos (by simpa using hk)]
    exact (mul_assoc _ _ _).symm
  · intro k hk
    rw [quantization_rational_residue hu hv huv hm, if_neg (by simpa using hk), mul_zero]

theorem quantization_phase_rational_rows {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {u v : ℕ} (hv : 1 ≤ v) (hvu : v < u) (huv : u.Coprime v) {p : ℕ → ℂ}
    (hp : Summable fun k => ‖p k‖ * ((u : ℝ) / v) ^ k)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℕ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) :
    p 0 ≠ 0 ∧ ∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ Finset.range (padicValNat u m + 1),
        (p k * (Real.exp ((2 * (k : ℝ) * Real.log ((u : ℝ) / v)) / 4) : ℂ)) *
          dirichletExp (lamLog lam) (m / u ^ k * v ^ k)) = p 0 := by
  have hu : 2 ≤ u := by omega
  have hr : 1 < (u : ℝ) / v := by
    apply (lt_div_iff₀ (by exact_mod_cast (show 0 < v by omega))).mpr
    norm_num
    exact_mod_cast hvu
  have hmoment : Summable fun k : ℕ =>
      ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2) := by
    apply hp.congr
    intro k
    have hl : 0 ≤ Real.log ((u : ℝ) / v) := Real.log_nonneg hr.le
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (k : ℝ) * Real.log ((u : ℝ) / v)),
      show 2 * (k : ℝ) * Real.log ((u : ℝ) / v) / 2 =
        (k : ℝ) * Real.log ((u : ℝ) / v) by ring,
      Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hr)]
  obtain ⟨hne, heq⟩ := quantization_phase_resonance_constant hW hmoment hphase
  have hzero : (∑' k : ℕ, p k * quantizationFrequencyResidue lam
      (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) 1) = p 0 := by
    rw [quantization_rational_residue_sum hu hv huv (by norm_num)]
    simp [dirichletExp_one (lamLog_zero lam) (lamLog_one lam)]
  refine ⟨by rwa [hzero] at hne, fun m hm => ?_⟩
  rw [← quantization_rational_residue_sum hu hv huv hm, heq m hm, hzero]

end RHTower.WeilSpectral
