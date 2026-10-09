import GaloisForLFunctions.RHTower.WeilLogShiftVanishingNormalization
import GaloisForLFunctions.RHTower.WeilLogShiftUniformFactorialLinear

/-!
# A common bounded C₀ operator on the actual regular subspace

One factorial normalization makes the whole regular subspace of a
finite-dimensional coefficient family summable. Its actual paired-kernel
potentials form a continuous linear map into `C₀`, with an operator norm
bound. The domain is the regular subspace itself.
-/

open Real Zeta23
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- The supremum norm of the actual potential is controlled by coefficient mass. -/
theorem norm_pairedLogPotentialC0_le (v : ℕ → ℝ) (hv : Summable v) :
    ‖pairedLogPotentialC0 v hv‖ ≤ (2 * riemannAutocorr 0) * ∑' n : ℕ, |v n| := by
  have hU : 0 ≤ 2 * riemannAutocorr 0 :=
    mul_nonneg (by norm_num) (riemannAutocorr_pos 0).le
  have hvabs : Summable (fun n : ℕ => |v n|) := by simpa only [Real.norm_eq_abs] using hv.norm
  change ‖(pairedLogPotentialC0 v hv).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg hU (tsum_nonneg (fun n => abs_nonneg (v n))))).mpr
  intro y
  change ‖∑' n : ℕ, v n * pairedLogKernel y n‖ ≤ _
  have hs := summable_pairedLogPotential_of_summable v hv y
  calc
    _ ≤ ∑' n : ℕ, ‖v n * pairedLogKernel y n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (2 * riemannAutocorr 0) * |v n| := by
      apply Summable.tsum_le_tsum _ hs.norm (hvabs.mul_left (2 * riemannAutocorr 0))
      intro n
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (pairedLogKernel_pos y n), mul_comm] using
        mul_le_mul_of_nonneg_left (pairedLogKernel_le_two_mul_riemannAutocorr_zero y n)
          (abs_nonneg (v n))
    _ = _ := by rw [tsum_mul_left]

/-- Every finite-dimensional coefficient family admits one normalization
whose potentials define a bounded linear `C₀` operator on its actual regular subspace. -/
theorem exists_weilLogShift_uniform_c0_operator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E →ₗ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      ∃ S : (weilLogShiftFactorialSequenceSubmodule.comap R) →L[ℝ] C₀(ℝ, ℝ),
        ‖S‖ ≤ C ∧ ∀ (a : weilLogShiftFactorialSequenceSubmodule.comap R) (y : ℝ),
          HasSum (fun n : ℕ =>
            exp (-(B * n)) * (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m)
            (S a y) := by
  obtain ⟨m, B, D, hB, hD, hiff, hsum⟩ := exists_weilLogShift_uniform_linear_factorial_normalization R
  let L : Submodule ℝ E := weilLogShiftFactorialSequenceSubmodule.comap R
  let w : L → ℕ → ℝ := fun a n => exp (-(B * n)) * R (a : E) n / (n.factorial : ℝ) ^ m
  have hw (a : L) : Summable (w a) := (hiff (a : E)).mp a.property
  have hadd (a b : L) (n : ℕ) : w (a + b) n = w a n + w b n := by
    change exp (-(B * n)) * R ((a : E) + (b : E)) n / (n.factorial : ℝ) ^ m = _
    rw [map_add, Pi.add_apply]
    dsimp only [w]
    ring
  have hsmul (c : ℝ) (a : L) (n : ℕ) : w (c • a) n = c * w a n := by
    change exp (-(B * n)) * R (c • (a : E)) n / (n.factorial : ℝ) ^ m = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    dsimp only [w]
    ring
  let S : L →ₗ[ℝ] C₀(ℝ, ℝ) := {
    toFun := fun a => pairedLogPotentialC0 (w a) (hw a)
    map_add' := by
      intro a b
      apply ZeroAtInftyContinuousMap.ext
      intro y
      change (∑' n : ℕ, w (a + b) n * pairedLogKernel y n) =
        (∑' n : ℕ, w a n * pairedLogKernel y n) + ∑' n : ℕ, w b n * pairedLogKernel y n
      simp_rw [hadd, add_mul]
      exact (summable_pairedLogPotential_of_summable (w a) (hw a) y).tsum_add
        (summable_pairedLogPotential_of_summable (w b) (hw b) y)
    map_smul' := by
      intro c a
      apply ZeroAtInftyContinuousMap.ext
      intro y
      change (∑' n : ℕ, w (c • a) n * pairedLogKernel y n) =
        c * ∑' n : ℕ, w a n * pairedLogKernel y n
      simp_rw [hsmul, mul_assoc]
      rw [tsum_mul_left] }
  let C := (2 * riemannAutocorr 0) * D
  have hU : 0 ≤ 2 * riemannAutocorr 0 :=
    mul_nonneg (by norm_num) (riemannAutocorr_pos 0).le
  have hC : 0 ≤ C := mul_nonneg hU hD
  have hbound (a : L) : ‖S a‖ ≤ C * ‖a‖ := by
    calc
      _ ≤ (2 * riemannAutocorr 0) * ∑' n : ℕ, |w a n| :=
        norm_pairedLogPotentialC0_le (w a) (hw a)
      _ ≤ (2 * riemannAutocorr 0) * (D * ‖(a : E)‖) :=
        mul_le_mul_of_nonneg_left (hsum (a : E) a.property) hU
      _ = _ := by change _ = ((2 * riemannAutocorr 0) * D) * ‖(a : E)‖; ring
  refine ⟨m, B, C, hB, hC, S.mkContinuous C hbound, S.mkContinuous_norm_le hC hbound, ?_⟩
  intro a y
  exact (summable_pairedLogPotential_of_summable (w a) (hw a) y).hasSum.congr_fun
    (fun n => by dsimp only [w]; ring)

end RHTower
