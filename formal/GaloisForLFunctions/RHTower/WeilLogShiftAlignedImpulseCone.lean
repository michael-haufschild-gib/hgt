import GaloisForLFunctions.RHTower.WeilLogShiftAlternatingColumns
import GaloisForLFunctions.RHTower.WeilLogShiftFactorialFiniteErrors

/-!
# A cone of finite history errors without cancellation

Late columns have exact alternating signs. Amplitudes with nonnegative
parity-adjusted signs therefore attain equality in the triangle inequality
on their common tail, at every real shift. Any nonzero such error defeats
all finite factorial majorants and factorial/exponential regularizations.
-/

noncomputable section

open Filter Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

private theorem abs_sum_eq_sum_abs_of_common_sign {d : ℕ} (f : Fin d → ℝ)
    (s : ℝ) (hs : |s| = 1) (hf : ∀ i, 0 ≤ s * f i) :
    |∑ i, f i| = ∑ i, |f i| := by
  calc
    _ = |∑ i, s * f i| := by rw [← Finset.mul_sum, abs_mul, hs, one_mul]
    _ = ∑ i, s * f i := Finset.abs_sum_of_nonneg' hf
    _ = ∑ i, |f i| := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = |s * f i| := (abs_of_nonneg (hf i)).symm
        _ = |f i| := by rw [abs_mul, hs, one_mul]

/-- Parity-aligned finite late responses attain the triangle equality at
every shift after the largest seed. Repeated indices and zero amplitudes
are allowed; the threshold is uniform in the finite list and amplitudes. -/
theorem exists_weilLogShiftAlignedResponse_abs_sum :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ) (a : Fin d → ℝ),
      (∀ i, K ≤ indices i) → (∀ i, 0 ≤ a i * (-1 : ℝ) ^ indices i) →
      ∀ (y : ℝ) (n : ℕ), Finset.univ.sup indices + 2 ≤ n →
        |∑ i, a i * weilLogShiftRecoveryMomentResponse y n (indices i)| =
          ∑ i, |a i| * |weilLogShiftRecoveryMomentResponse y n (indices i)| := by
  obtain ⟨K, hK, hsign⟩ := exists_weilLogShiftRecoveryCoefficientColumn_alternating_sign
  refine ⟨K, hK, ?_⟩
  intro d indices a hk ha y n hn
  have hphase (i : Fin d) :
      0 ≤ (-1 : ℝ) ^ n * (a i * weilLogShiftRecoveryCoefficientColumn (indices i) n) := by
    have hi : indices i ≤ Finset.univ.sup indices := Finset.le_sup (Finset.mem_univ i)
    have hmul := mul_nonneg (ha i) (hsign (indices i) (hk i) n (by omega)).le
    have hkk : (-1 : ℝ) ^ indices i * (-1 : ℝ) ^ indices i = 1 := by
      rw [← mul_pow]
      norm_num
    have heq : (a i * (-1 : ℝ) ^ indices i) *
        ((-1 : ℝ) ^ (n + indices i) * weilLogShiftRecoveryCoefficientColumn (indices i) n) =
        (-1 : ℝ) ^ n * (a i * weilLogShiftRecoveryCoefficientColumn (indices i) n) := by
      rw [pow_add]
      calc
        _ = ((-1 : ℝ) ^ indices i * (-1 : ℝ) ^ indices i) *
            ((-1 : ℝ) ^ n * (a i * weilLogShiftRecoveryCoefficientColumn (indices i) n)) := by ring
        _ = _ := by rw [hkk, one_mul]
    rw [heq] at hmul
    exact hmul
  have hcoef : |∑ i, a i * weilLogShiftRecoveryCoefficientColumn (indices i) n| =
      ∑ i, |a i * weilLogShiftRecoveryCoefficientColumn (indices i) n| := by
    apply abs_sum_eq_sum_abs_of_common_sign _ ((-1 : ℝ) ^ n) _ hphase
    rw [abs_pow]
    norm_num
  let q := pairedLogKernel y n / sqrt n
  have hresp (i : Fin d) : a i * weilLogShiftRecoveryMomentResponse y n (indices i) =
      (a i * weilLogShiftRecoveryCoefficientColumn (indices i) n) * q := by
    rw [weilLogShiftRecoveryMomentResponse_eq_coefficientColumn y (indices i) n (by omega)]
    dsimp only [q]
    ring
  calc
    _ = |(∑ i, a i * weilLogShiftRecoveryCoefficientColumn (indices i) n) * q| := by
      simp_rw [hresp]
      rw [Finset.sum_mul]
    _ = (∑ i, |a i * weilLogShiftRecoveryCoefficientColumn (indices i) n|) * |q| := by
      rw [abs_mul, hcoef]
    _ = ∑ i, |(a i * weilLogShiftRecoveryCoefficientColumn (indices i) n) * q| := by
      rw [Finset.sum_mul]
      simp_rw [abs_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hresp, abs_mul]

/-- Every nonzero parity-aligned finite combination of sufficiently late
responses has no finite factorial majorant at any real shift. -/
theorem exists_weilLogShiftAlignedResponse_no_factorial_majorant :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ) (a : Fin d → ℝ),
      (∀ i, K ≤ indices i) → (∀ i, 0 ≤ a i * (-1 : ℝ) ^ indices i) →
      (∃ i, a i ≠ 0) → ∀ y : ℝ, ¬ WeilLogShiftHasFactorialMajorant
        (fun n => ∑ i, a i * weilLogShiftRecoveryMomentResponse y n (indices i)) := by
  obtain ⟨K₁, hK₁, habs⟩ := exists_weilLogShiftAlignedResponse_abs_sum
  obtain ⟨K₂, _, hno⟩ := exists_weilLogShiftRecoveryMomentResponse_no_factorial_majorant
  refine ⟨max K₁ K₂, by omega, ?_⟩
  intro d indices a hk ha hnonzero y hreg
  obtain ⟨i, hi⟩ := hnonzero
  have hscaled : WeilLogShiftHasFactorialMajorant
      (fun n => a i * weilLogShiftRecoveryMomentResponse y n (indices i)) := by
    apply weilLogShiftHasFactorialMajorant_of_eventually_abs_le _ hreg
    refine eventually_atTop.mpr ⟨Finset.univ.sup indices + 2, ?_⟩
    intro n hn
    rw [abs_mul, habs d indices a (fun j => by have := hk j; omega) ha y n hn]
    exact Finset.single_le_sum
      (f := fun j : Fin d => |a j| * |weilLogShiftRecoveryMomentResponse y n (indices j)|)
      (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hcolumn := (weilLogShiftHasFactorialMajorant_mul_iff (a i) hi
    (fun n => weilLogShiftRecoveryMomentResponse y n (indices i))).mp hscaled
  obtain ⟨m, A, D, N, hN⟩ := hcolumn
  exact hno (indices i) (by have := hk i; omega) y m A D ⟨N, hN⟩

/-- The same common cone threshold excludes every factorial/exponential
summability normalization, simultaneously with every finite factorial majorant. -/
theorem exists_weilLogShiftAlignedResponse_factorial_obstruction :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ) (a : Fin d → ℝ),
      (∀ i, K ≤ indices i) → (∀ i, 0 ≤ a i * (-1 : ℝ) ^ indices i) →
      (∃ i, a i ≠ 0) → ∀ y : ℝ,
        (¬ WeilLogShiftHasFactorialMajorant
          (fun n => ∑ i, a i * weilLogShiftRecoveryMomentResponse y n (indices i))) ∧
        ∀ (m : ℕ) (A : ℝ), ¬ Summable (fun n : ℕ => exp (-(A * n)) *
          (∑ i, a i * weilLogShiftRecoveryMomentResponse y n (indices i)) /
            (n.factorial : ℝ) ^ m) := by
  obtain ⟨K, hK, hno⟩ := exists_weilLogShiftAlignedResponse_no_factorial_majorant
  refine ⟨K, hK, ?_⟩
  intro d indices a hk ha hnonzero y
  have h := hno d indices a hk ha hnonzero y
  refine ⟨h, ?_⟩
  intro m A hs
  exact h (weilLogShiftHasFactorialMajorant_of_summable_normalization _ m A hs)

/-- Around the arithmetic history the full finite-error moment is exactly
the finite sum of native column responses, with no residual affine baseline. -/
theorem weilLogShiftFiniteImpulse_moment_arithmetic {d : ℕ}
    (indices : Fin d → ℕ) (a : Fin d → ℝ) (y : ℝ) (n : ℕ) :
    weilLogShiftRecoveryMoment y
      (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a) n =
      ∑ i, a i * weilLogShiftRecoveryMomentResponse y n (indices i) := by
  calc
    _ = weilLogShiftRecoveryMomentCLM y n (weilLogShiftFiniteImpulseMap indices a) := by
      have h := weilLogShiftRecoveryMomentCLM_sub_arithmetic y n
        (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a)
      rw [add_sub_cancel_left] at h
      exact h.symm
    _ = _ := by
      change weilLogShiftRecoveryMomentCLM y n
        (∑ i, a i • weilLogShiftRecoveryUnitHistory (indices i)) = _
      simp only [map_sum, map_smul, smul_eq_mul, weilLogShiftRecoveryMomentResponse]

/-- Every nonzero aligned late finite history error at the arithmetic anchor
defeats all factorial majorants and all factorial/exponential normalizations,
at every real shift, with one threshold before every finite-list parameter. -/
theorem exists_weilLogShiftAlignedFiniteImpulse_arithmetic_obstruction :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ) (a : Fin d → ℝ),
      (∀ i, K ≤ indices i) → (∀ i, 0 ≤ a i * (-1 : ℝ) ^ indices i) →
      (∃ i, a i ≠ 0) → ∀ y : ℝ,
        (¬ WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y
          (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a))) ∧
        ∀ (m : ℕ) (A : ℝ), ¬ Summable (fun n : ℕ => exp (-(A * n)) *
          weilLogShiftRecoveryMoment y
            (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a) n /
              (n.factorial : ℝ) ^ m) := by
  obtain ⟨K, hK, hno⟩ := exists_weilLogShiftAlignedResponse_factorial_obstruction
  refine ⟨K, hK, ?_⟩
  intro d indices a hk ha hnonzero y
  have heq : weilLogShiftRecoveryMoment y
      (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a) =
      (fun n => ∑ i, a i * weilLogShiftRecoveryMomentResponse y n (indices i)) := by
    funext n
    exact weilLogShiftFiniteImpulse_moment_arithmetic indices a y n
  rw [heq]
  exact hno d indices a hk ha hnonzero y

end RHTower
