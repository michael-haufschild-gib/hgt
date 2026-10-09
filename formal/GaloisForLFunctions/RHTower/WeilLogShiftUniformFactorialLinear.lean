import GaloisForLFunctions.RHTower.WeilLogShiftFactorialNormalization
import GaloisForLFunctions.RHTower.WeilLogShiftFactorialAmplitudeSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# One factorial envelope on a finite regular submodule

Sum the absolute responses of a finite basis of the regular submodule.
That single sequence has a factorial majorant. Bounded basis coordinates
then give a global envelope uniform over every regular vector, and one
normalization detects the whole regular submodule exactly.
-/

noncomputable section

open Real

namespace RHTower

/-- Every finite-dimensional linear sequence family admits a common global
factorial envelope on its actual regular submodule, with norm-controlled
prefactor. No regularity of the whole amplitude space is assumed. -/
theorem exists_weilLogShiftFactorialMajorant_uniform_linear_envelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E →ₗ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (A D : ℝ), 0 < A ∧ 0 ≤ D ∧ ∀ a : E,
      WeilLogShiftHasFactorialMajorant (R a) → ∀ n : ℕ,
      |R a n| ≤ D * ‖a‖ * exp (A * n) * (n.factorial : ℝ) ^ m := by
  let L : Submodule ℝ E := weilLogShiftFactorialSequenceSubmodule.comap R
  let R' : L →ₗ[ℝ] (ℕ → ℝ) := R.comp L.subtype
  let b := Module.finBasis ℝ L
  let g : ℕ → ℝ := fun n => ∑ i, |R' (b i) n|
  have hb (i : Fin (Module.finrank ℝ L)) :
      WeilLogShiftHasFactorialMajorant (fun n => |R' (b i) n|) := by
    have hi := (b i).property
    change WeilLogShiftHasFactorialMajorant (R' (b i)) at hi
    obtain ⟨m, A, D, N, hi⟩ := hi
    exact ⟨m, A, D, N, fun n hn => by simpa only [abs_abs] using hi n hn⟩
  have hg : WeilLogShiftHasFactorialMajorant g := by
    have hmem := weilLogShiftFactorialSequenceSubmodule.sum_mem
      (t := Finset.univ) (f := fun i => (fun n => |R' (b i) n|)) (fun i _ => hb i)
    change WeilLogShiftHasFactorialMajorant (∑ i, (fun n => |R' (b i) n|)) at hmem
    have heq : (∑ i, (fun n => |R' (b i) n|)) = g := by
      funext n
      simp only [Finset.sum_apply, g]
    rwa [heq] at hmem
  obtain ⟨m, A, D, hA, hD, hbound⟩ := weilLogShiftHasFactorialMajorant_global_bound g hg
  let C := ‖b.equivFunL.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg b.equivFunL.toContinuousLinearMap
  have hcoord (a : L) (i : Fin (Module.finrank ℝ L)) : |b.equivFun a i| ≤ C * ‖a‖ := by
    calc
      _ = ‖b.equivFunL a i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖b.equivFunL a‖ := norm_le_pi_norm _ i
      _ ≤ _ := b.equivFunL.toContinuousLinearMap.le_opNorm a
  refine ⟨m, A, C * D, hA, mul_nonneg hC hD, ?_⟩
  intro a ha n
  let aL : L := ⟨a, ha⟩
  have hsum : R a n = ∑ i, b.equivFun aL i * R' (b i) n := by
    change R' aL n = _
    calc
      _ = R' (∑ i, b.equivFun aL i • b i) n := by rw [b.sum_equivFun]
      _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = |∑ i, b.equivFun aL i * R' (b i) n| := by rw [hsum]
    _ ≤ ∑ i, |b.equivFun aL i * R' (b i) n| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |b.equivFun aL i| * |R' (b i) n| := by simp_rw [abs_mul]
    _ ≤ ∑ i, (C * ‖a‖) * |R' (b i) n| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hcoord aL i) (abs_nonneg _)
    _ = (C * ‖a‖) * g n := by dsimp only [g]; rw [Finset.mul_sum]
    _ ≤ (C * ‖a‖) * (D * exp (A * n) * (n.factorial : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left ((le_abs_self (g n)).trans (hbound n))
        (mul_nonneg hC (norm_nonneg a))
    _ = _ := by ring

/-- One fixed normalization detects the entire factorial-regular submodule
of a finite-dimensional family, with an absolute-sum bound linear in norm. -/
theorem exists_weilLogShift_uniform_linear_factorial_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E →ₗ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      (∀ a : E, WeilLogShiftHasFactorialMajorant (R a) ↔
        Summable (fun n : ℕ => exp (-(B * n)) * R a n / (n.factorial : ℝ) ^ m)) ∧
      ∀ a : E, WeilLogShiftHasFactorialMajorant (R a) →
        (∑' n : ℕ, |exp (-(B * n)) * R a n / (n.factorial : ℝ) ^ m|) ≤ C * ‖a‖ := by
  obtain ⟨m, A, D, hA, hD, hbound⟩ :=
    exists_weilLogShiftFactorialMajorant_uniform_linear_envelope R
  let S := ∑' n : ℕ, exp (-n)
  have hS : 0 ≤ S := tsum_nonneg (fun _ => (exp_pos _).le)
  refine ⟨m, A + 1, D * S, by linarith, mul_nonneg hD hS, ?_, ?_⟩
  · intro a
    constructor
    · intro ha
      exact (weilLogShift_factorial_normalization_summable_bound (R a) m A (D * ‖a‖)
        (hbound a ha)).1
    · intro hs
      exact weilLogShiftHasFactorialMajorant_of_summable_normalization (R a) m (A + 1) hs
  · intro a ha
    have h := (weilLogShift_factorial_normalization_summable_bound (R a) m A (D * ‖a‖)
      (hbound a ha)).2
    simpa only [S, mul_assoc, mul_comm, mul_left_comm] using h

end RHTower
