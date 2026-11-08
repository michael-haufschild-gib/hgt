import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.SampledJumpsAdmitLipschitzApproximation
import Mathlib.NumberTheory.Chebyshev

/-!
# Reciprocal Chebyshev profiles admit sampled ramp approximation

On every positive terminal fraction, the Chebyshev profile is a finite sum of
jumps at reciprocal integers. Smoothing those jumps gives continuous profiles
with an explicit square-mean error, including the lattice endpoints.
-/

set_option autoImplicit false
noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- On a fixed positive terminal fraction, the reciprocal Chebyshev profile has finitely many
jumps, located at reciprocal integers. -/
theorem chebyshevPsi_reciprocal_eq_finite_jumps {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    Chebyshev.psi (1 / x) = ∑ k ∈ Icc 1 ⌊1 / δ⌋₊,
      (ArithmeticFunction.vonMangoldt k : ℝ) * (if x ≤ 1 / (k : ℝ) then 1 else 0) := by
  have hx0 : 0 < x := hδ.trans_le hx
  have hbound : ⌊1 / x⌋₊ ≤ ⌊1 / δ⌋₊ := Nat.floor_mono
    (one_div_le_one_div_of_le hδ hx)
  have hset : (Icc 1 ⌊1 / δ⌋₊).filter (fun k : ℕ => x ≤ 1 / (k : ℝ)) = Ioc 0 ⌊1 / x⌋₊ := by
    ext k
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨hk1, _⟩, hstep⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      refine ⟨by omega, Nat.le_floor ?_⟩
      exact (le_div_iff₀ hx0).mpr (by
        have hh := (le_div_iff₀ hk0).mp hstep
        simpa only [mul_comm] using hh)
    · rintro ⟨hk0, hkcut⟩
      have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
      refine ⟨⟨by omega, hkcut.trans hbound⟩, ?_⟩
      apply (le_div_iff₀ hkr).mpr
      have hh := (le_div_iff₀ hx0).mp
        ((Nat.le_floor_iff (by positivity : 0 ≤ 1 / x)).mp hkcut)
      simpa only [mul_comm] using hh
  unfold Chebyshev.psi
  rw [← hset, sum_filter]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- The finite reciprocal Chebyshev jumps have a continuous ramp approximation. -/
def chebyshevReciprocalRamp (δ η x : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊1 / δ⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) *
    descendingRamp (1 / (k : ℝ)) η x

lemma continuous_chebyshevReciprocalRamp (δ : ℝ) {η : ℝ} (hη : 0 < η) :
    Continuous (chebyshevReciprocalRamp δ η) := by
  unfold chebyshevReciprocalRamp
  exact continuous_finset_sum _ fun k _ =>
    (lipschitzWith_descendingRamp hη (1 / (k : ℝ))).continuous.const_mul _


/-- Finite jump ramps approximate the reciprocal Chebyshev profile in sampled square mean
on every fixed terminal fraction. -/
theorem normalized_sum_chebyshevPsi_sub_ramp_sq_le {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hηδ : η ≤ δ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (Chebyshev.psi (1 / ((n : ℝ) / N)) - chebyshevReciprocalRamp δ η ((n : ℝ) / N)) ^ 2) / N ≤
      (∑ k ∈ Icc 1 ⌊1 / δ⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) ^ 2) *
        ((Icc 1 ⌊1 / δ⌋₊).card * (2 * η + 4 / N)) := by
  let S := Icc 1 ⌊1 / δ⌋₊
  let d : ℕ → ℝ := fun n => ∑ k ∈ S, (ArithmeticFunction.vonMangoldt k : ℝ) *
    ((if (n : ℝ) / N ≤ 1 / (k : ℝ) then 1 else 0) -
      descendingRamp (1 / (k : ℝ)) η ((n : ℝ) / N))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      Chebyshev.psi (1 / ((n : ℝ) / N)) - chebyshevReciprocalRamp δ η ((n : ℝ) / N) = d n := by
    intro n hn
    have hx : δ ≤ (n : ℝ) / N := (le_div_iff₀ hN0).mpr
      (le_of_lt ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1))
    rw [chebyshevPsi_reciprocal_eq_finite_jumps hδ hx]
    unfold chebyshevReciprocalRamp
    dsimp only [d, S]
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hsub : Ioc ⌊δ * (N : ℝ)⌋₊ N ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, hnhi⟩
  have hu : ∀ k ∈ S, η ≤ 1 / (k : ℝ) := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkδ : (k : ℝ) ≤ 1 / δ :=
      (by exact_mod_cast (mem_Icc.mp hk).2 : (k : ℝ) ≤ ⌊1 / δ⌋₊).trans
        (Nat.floor_le (by positivity))
    exact hηδ.trans ((le_div_iff₀ hk0).mpr (by
      have hh := (le_div_iff₀ hδ).mp hkδ
      simpa only [mul_comm] using hh))
  calc
    _ = (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, d n ^ 2) / N := by
      congr 1
      exact sum_congr rfl fun n hn => congrArg (fun x : ℝ => x ^ 2) (heq n hn)
    _ ≤ (∑ n ∈ Icc 1 N, d n ^ 2) / N :=
      div_le_div_of_nonneg_right
        (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)) hN0.le
    _ ≤ _ := normalized_sum_finite_jumps_sub_ramps_sq_le hN S
      (fun k => ArithmeticFunction.vonMangoldt k) (fun k => 1 / (k : ℝ)) hη hu

#print axioms normalized_sum_chebyshevPsi_sub_ramp_sq_le

#print axioms chebyshevPsi_reciprocal_eq_finite_jumps
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
