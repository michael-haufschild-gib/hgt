import GaloisForLFunctions.HTGeometry.WeightedRpowTailCesaro
import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointWienerCharge

/-!
# Exact ultraviolet tail of physical prime endpoint characters

Abel summation converts a Cesàro limit for cumulative square energy into exact scaled
inverse-square tail. Applied to signed physical FCRJ endpoint moments, endpoint differentiation
then yields exact positive one-over-N tail coefficient for raw character energy. Result is
unconditional and source-pure: no Xi-zero or RH hypothesis enters.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

private theorem shift_rpow_neg_two (n k : ℕ) :
    ((n : ℝ) + 1 + (k : ℝ)) ^ (-2 : ℝ) =
      (((n : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (by positivity)]
  congr 1
  exact Real.rpow_natCast _ 2

/-- A convergent weight passes through shifted inverse-square tail. -/
theorem tendsto_weightedTail_invSq {c : ℝ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        ∑' k : ℕ, g (n + 1 + k) / (((n : ℝ) + 1 + (k : ℝ)) ^ 2))
      atTop (𝓝 c) := by
  have h := tendsto_weightedTail_rpow (p := 0) (c := c) (by norm_num) hg
  simpa only [sub_zero, Real.rpow_one, zero_sub, shift_rpow_neg_two,
    div_eq_mul_inv, inv_one, mul_one] using h

private theorem summable_shift_invSq (N : ℕ) :
    Summable fun k : ℕ => (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹ := by
  have h := summable_shift_rpow (q := -1) (by norm_num) N
  have h' : Summable fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ (-2 : ℝ) := by
    convert h using 1
    norm_num
  exact h'.congr fun k => shift_rpow_neg_two N k

private theorem summable_weighted_shift_invSq {c : ℝ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 c)) (N : ℕ) :
    Summable fun k : ℕ =>
      g (N + 1 + k) / (((N : ℝ) + 1 + (k : ℝ)) ^ 2) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n : ℕ, ‖g n‖ ≤ B := by
    obtain ⟨B, hB⟩ := hg.norm.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  refine Summable.of_norm_bounded ((summable_shift_invSq N).mul_left B) fun k => ?_
  have hw : 0 ≤ (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹ := by positivity
  rw [div_eq_mul_inv, norm_mul, Real.norm_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right (hB (N + 1 + k)) hw

private theorem tendsto_ratio_succ_one :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hzero)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem invSqKernel_decomp (S g : ℕ → ℝ)
    (hS : ∀ n : ℕ, n ≠ 0 → S n = (n : ℝ) * g n)
    {j : ℕ} (hj : j ≠ 0) :
    S (j + 1) * (1 / (j : ℝ) ^ 2 - 1 / ((j + 1 : ℕ) : ℝ) ^ 2) =
      g (j + 1) / (j : ℝ) ^ 2 +
        (g (j + 1) * (j : ℝ) / ((j : ℝ) + 1)) / (j : ℝ) ^ 2 := by
  rw [hS (j + 1) (by omega)]
  norm_num [Nat.cast_add, Nat.cast_one]
  have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  field_simp
  ring

private theorem tendsto_cumulative_boundary_invSq_zero {c : ℝ} {S g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 c))
    (hS : ∀ n : ℕ, n ≠ 0 → S n = (n : ℝ) * g n)
    {M : ℕ} (hM : M ≠ 0) :
    Tendsto (fun R : ℕ => S (M + R + 1) / ((M + R : ℕ) : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hgshift : Tendsto (fun R : ℕ => g (M + R + 1)) atTop (𝓝 c) := by
    have h := hg.comp (tendsto_add_atTop_nat (M + 1))
    apply h.congr'
    filter_upwards with R
    simp only [Function.comp_apply]
    congr 1
    omega
  have hinv : Tendsto (fun R : ℕ => 1 / ((M + R : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat M)
    simpa [Function.comp_def, Nat.add_comm] using h
  have hfactor : Tendsto (fun R : ℕ =>
      1 / ((M + R : ℕ) : ℝ) +
        (1 / ((M + R : ℕ) : ℝ)) * (1 / ((M + R : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using hinv.add (hinv.mul hinv)
  have hprod := hgshift.mul hfactor
  have hprod0 : Tendsto (fun R : ℕ =>
      g (M + R + 1) * (1 / ((M + R : ℕ) : ℝ) +
        (1 / ((M + R : ℕ) : ℝ)) * (1 / ((M + R : ℕ) : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hprod
  apply hprod0.congr'
  filter_upwards with R
  have hMR : ((M + R : ℕ) : ℝ) ≠ 0 := by
    positivity
  rw [hS (M + R + 1) (by omega)]
  push_cast
  field_simp

private theorem finite_abel_invSq (S : ℕ → ℝ) (M R : ℕ) :
    (∑ k ∈ Finset.range (R + 1),
        (S (M + k + 1) - S (M + k)) / ((M + k : ℕ) : ℝ) ^ 2) =
      S (M + R + 1) / ((M + R : ℕ) : ℝ) ^ 2 - S M / (M : ℝ) ^ 2 +
        ∑ k ∈ Finset.range R, S (M + k + 1) *
          (1 / ((M + k : ℕ) : ℝ) ^ 2 - 1 / ((M + k + 1 : ℕ) : ℝ) ^ 2) := by
  induction R with
  | zero => simp; ring
  | succ R ih =>
      calc
        (∑ k ∈ Finset.range (R + 1 + 1),
            (S (M + k + 1) - S (M + k)) / ((M + k : ℕ) : ℝ) ^ 2) =
            (∑ k ∈ Finset.range (R + 1),
              (S (M + k + 1) - S (M + k)) / ((M + k : ℕ) : ℝ) ^ 2) +
              (S (M + (R + 1) + 1) - S (M + (R + 1))) /
                ((M + (R + 1) : ℕ) : ℝ) ^ 2 := by
                  rw [Finset.sum_range_succ]
        _ = (S (M + R + 1) / ((M + R : ℕ) : ℝ) ^ 2 - S M / (M : ℝ) ^ 2 +
              ∑ k ∈ Finset.range R, S (M + k + 1) *
                (1 / ((M + k : ℕ) : ℝ) ^ 2 - 1 / ((M + k + 1 : ℕ) : ℝ) ^ 2)) +
              (S (M + (R + 1) + 1) - S (M + (R + 1))) /
                ((M + (R + 1) : ℕ) : ℝ) ^ 2 := by rw [ih]
        _ = S (M + (R + 1) + 1) / ((M + (R + 1) : ℕ) : ℝ) ^ 2 -
              S M / (M : ℝ) ^ 2 +
              ((∑ k ∈ Finset.range R, S (M + k + 1) *
                (1 / ((M + k : ℕ) : ℝ) ^ 2 - 1 / ((M + k + 1 : ℕ) : ℝ) ^ 2) +
                S (M + R + 1) *
                  (1 / ((M + R : ℕ) : ℝ) ^ 2 -
                    1 / ((M + R + 1 : ℕ) : ℝ) ^ 2))) := by ring_nf
        _ = S (M + (R + 1) + 1) / ((M + (R + 1) : ℕ) : ℝ) ^ 2 -
              S M / (M : ℝ) ^ 2 +
              ∑ k ∈ Finset.range (R + 1), S (M + k + 1) *
                (1 / ((M + k : ℕ) : ℝ) ^ 2 - 1 / ((M + k + 1 : ℕ) : ℝ) ^ 2) := by
                  rw [Finset.sum_range_succ]

/-- Abel transfer from a Cesàro limit to a scaled inverse-square tail. -/
theorem tendsto_cesaro_invSqTail_of_summable {a : ℕ → ℝ} {c : ℝ}
    (hmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, a n)
      atTop (𝓝 c))
    (hsumm : Summable fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) :
    Tendsto (fun N : ℕ => (N : ℝ) *
        ∑' k : ℕ, a (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2)
      atTop (𝓝 c) := by
  let S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, a j
  let g : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * S n
  have hg : Tendsto g atTop (𝓝 c) := by
    simpa only [g, S] using hmean
  have hS (n : ℕ) (hn : n ≠ 0) : S n = (n : ℝ) * g n := by
    simp only [g]
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hdiff (n : ℕ) : S (n + 1) - S n = a n := by
    simp only [S, Finset.sum_range_succ]
    ring
  let g₁ : ℕ → ℝ := fun n => g (n + 1)
  let g₂ : ℕ → ℝ := fun n => g (n + 1) * (n : ℝ) / ((n : ℝ) + 1)
  have hg₁ : Tendsto g₁ atTop (𝓝 c) := by
    have h := hg.comp (tendsto_add_atTop_nat 1)
    simpa [g₁, Function.comp_def] using h
  have hg₂ : Tendsto g₂ atTop (𝓝 c) := by
    have h := hg₁.mul tendsto_ratio_succ_one
    convert h using 1
    · funext n
      simp only [g₂, g₁]
      ring
    · simp
  have htail (N : ℕ) :
      (∑' k : ℕ, a (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2) =
        -S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2 +
          (∑' k : ℕ, g₁ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2) +
          ∑' k : ℕ, g₂ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2 := by
    have hsummN : Summable fun k : ℕ =>
        a (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2 := by
      have h := (summable_nat_add_iff N).2 hsumm
      simpa only [Function.comp_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hsumm₁ : Summable fun k : ℕ =>
        g₁ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2 := by
      have h := summable_weighted_shift_invSq hg₁ N
      simpa only [Nat.cast_add, Nat.cast_one] using h
    have hsumm₂ : Summable fun k : ℕ =>
        g₂ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2 := by
      have h := summable_weighted_shift_invSq hg₂ N
      simpa only [Nat.cast_add, Nat.cast_one] using h
    have hkernel : Summable fun k : ℕ =>
        S (N + 1 + k + 1) *
          (1 / ((N + 1 + k : ℕ) : ℝ) ^ 2 -
            1 / ((N + 1 + k + 1 : ℕ) : ℝ) ^ 2) := by
      refine (hsumm₁.add hsumm₂).congr fun k => ?_
      have hdec := invSqKernel_decomp S g hS
        (j := N + 1 + k) (by omega)
      simpa only [g₁, g₂, Nat.cast_add, Nat.cast_one] using hdec.symm
    have hleft := hsummN.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hright := ((tendsto_cumulative_boundary_invSq_zero hg hS (M := N + 1) (by omega)).sub_const
      (S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2)).add hkernel.hasSum.tendsto_sum_nat
    have hright' : Tendsto (fun R : ℕ =>
        (∑ k ∈ Finset.range (R + 1),
          a (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2)) atTop
        (𝓝 (0 - S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2 +
          ∑' k : ℕ, S (N + 1 + k + 1) *
            (1 / ((N + 1 + k : ℕ) : ℝ) ^ 2 -
              1 / ((N + 1 + k + 1 : ℕ) : ℝ) ^ 2))) := by
      apply hright.congr'
      filter_upwards with R
      rw [← finite_abel_invSq S (N + 1) R]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hdiff]
    have hleft' : Tendsto (fun R : ℕ =>
        (∑ k ∈ Finset.range (R + 1),
          a (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2)) atTop
        (𝓝 (∑' k : ℕ, a (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2)) := by
      simpa [Function.comp_def] using hleft
    have heq := tendsto_nhds_unique hleft' hright'
    rw [heq]
    simp only [zero_sub]
    calc
      -(S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2) +
          ∑' k : ℕ, S (N + 1 + k + 1) *
            (1 / ((N + 1 + k : ℕ) : ℝ) ^ 2 -
              1 / ((N + 1 + k + 1 : ℕ) : ℝ) ^ 2) =
          -(S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2) +
            ∑' k : ℕ, (g₁ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2 +
              g₂ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2) := by
                congr 1
                apply tsum_congr
                intro k
                have hdec := invSqKernel_decomp S g hS
                  (j := N + 1 + k) (by omega)
                simpa only [g₁, g₂, Nat.cast_add, Nat.cast_one] using hdec
      _ = _ := by
        rw [hsumm₁.tsum_add hsumm₂]
        ring
  have hboundary : Tendsto (fun N : ℕ =>
      (N : ℝ) * (-S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 (-c)) := by
    have hprod := tendsto_ratio_succ_one.mul hg₁
    have hneg := hprod.neg
    have hneg' : Tendsto (fun N : ℕ => -((N : ℝ) / ((N : ℝ) + 1) * g₁ N))
        atTop (𝓝 (-c)) := by simpa only [one_mul] using hneg
    apply hneg'.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hS (N + 1) (by omega)]
    push_cast
    have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have htail₁ : Tendsto (fun N : ℕ => (N : ℝ) *
      ∑' k : ℕ, g₁ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2)
      atTop (𝓝 c) := by
    have h := tendsto_weightedTail_invSq hg₁
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have htail₂ : Tendsto (fun N : ℕ => (N : ℝ) *
      ∑' k : ℕ, g₂ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2)
      atTop (𝓝 c) := by
    have h := tendsto_weightedTail_invSq hg₂
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hfinal := (hboundary.add htail₁).add htail₂
  have hfinal' : Tendsto (fun N : ℕ =>
      (N : ℝ) * (-S (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2) +
        (N : ℝ) * (∑' k : ℕ,
          g₁ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2) +
        (N : ℝ) * ∑' k : ℕ,
          g₂ (N + 1 + k) / ((N + 1 + k : ℕ) : ℝ) ^ 2) atTop (𝓝 c) := by
    simpa only [neg_add_cancel, zero_add] using hfinal
  apply hfinal'.congr'
  filter_upwards with N
  rw [htail N]
  ring

end GaloisForLFunctions.HTGeometry

namespace RHTower

open Complex Filter Topology
open scoped BigOperators

noncomputable section

private theorem normSq_xiPhysicalApertureCharacterRate_nat
    {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Complex.normSq (xiPhysicalApertureCharacterRate A (n : ℤ)) =
      4 * Real.pi ^ 2 * (n : ℝ) ^ 2 / A ^ 2 := by
  rw [xiPhysicalApertureCharacterRate, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_I]
  field_simp [hA.ne']
  norm_cast
  ring

private theorem summable_positive_xiPhysicalPrimeLogCharacterAmplitude_normSq
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    Summable fun n : ℕ => Complex.normSq
      (xiPhysicalPrimeLogCharacterAmplitude P A ((n : ℤ) + 1) m k) := by
  have hcenter : Summable fun n : ℕ => Complex.normSq
      (xiPhysicalPrimeLogCenteredCharacterAmplitude P A ((n : ℤ) + 1) m k) := by
    have h := (hasSum_normSq_xiPhysicalPrimeLogCenteredCharacterAmplitude_neg
      P hA m k).summable.comp_injective
        (i := fun n : ℕ => -((n : ℤ) + 1)) (by
          intro x y hxy
          have h1 : (x : ℤ) + 1 = (y : ℤ) + 1 := neg_injective hxy
          have h2 : (x : ℤ) = (y : ℤ) := add_right_cancel h1
          exact_mod_cast h2)
    simpa [Function.comp_def] using h
  refine hcenter.congr fun n => ?_
  rw [xiPhysicalPrimeLogCenteredCharacterAmplitude_eq P hA (by omega) m k]

private theorem xiPhysicalPrimeLogEndpointCircleMoment_normSq_div_sq
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    {n : ℕ} (hn : n ≠ 0) :
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 / (n : ℝ) ^ 2 =
      (4 * Real.pi ^ 2 / A ^ 2) *
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A (n : ℤ) m k) := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment_eq_rate_mul_amplitude hA hn hactive,
    Complex.sq_norm, Complex.normSq_mul, normSq_xiPhysicalApertureCharacterRate_nat hA]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hA.ne', hnR]

private theorem summable_xiPhysicalPrimeLogEndpointCircleMoment_norm_sq_div_sq
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    Summable fun n : ℕ =>
      ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (n + 1)‖ ^ 2 /
        ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have h := (summable_positive_xiPhysicalPrimeLogCharacterAmplitude_normSq P hA m k).mul_left
    (4 * Real.pi ^ 2 / A ^ 2)
  refine h.congr fun n => ?_
  simpa only [Nat.cast_add, Nat.cast_one] using
    (xiPhysicalPrimeLogEndpointCircleMoment_normSq_div_sq hA hactive (n := n + 1) (by omega)).symm

/-- Exact scaled inverse-square tail of differentiated physical endpoint moments. -/
theorem tendsto_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' r : ℕ,
        ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
          ((N + 1 + r : ℕ) : ℝ) ^ 2) atTop
      (𝓝 (∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2)) := by
  apply GaloisForLFunctions.HTGeometry.tendsto_cesaro_invSqTail_of_summable
    (a := fun n => ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2)
    (c := ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
      ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2)
  · exact tendsto_xiPhysicalPrimeLogEndpointCircleMoment_cesaro_norm_sq P hA m k
  · exact summable_xiPhysicalPrimeLogEndpointCircleMoment_norm_sq_div_sq hA hactive

private theorem normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_endpointMoment
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    {n : ℕ} (hn : n ≠ 0) :
    Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A (n : ℤ) m k) =
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        (‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 / (n : ℝ) ^ 2) := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment_normSq_div_sq hA hactive hn]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hA.ne', hpi]

/-- Exact one-over-N ultraviolet tail law for positive physical FCRJ characters. -/
theorem tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k)) atTop
      (𝓝 ((A ^ 2 / (4 * Real.pi ^ 2)) *
        ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
          ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2)) := by
  have h := (tendsto_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail P hA hactive).const_mul
    (A ^ 2 / (4 * Real.pi ^ 2))
  apply h.congr'
  filter_upwards with N
  have htsum : (∑' r : ℕ, Complex.normSq
      (xiPhysicalPrimeLogCharacterAmplitude P A ((N + 1 + r : ℕ) : ℤ) m k)) =
      (A ^ 2 / (4 * Real.pi ^ 2)) * ∑' r : ℕ,
        (‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
          ((N + 1 + r : ℕ) : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    exact normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_endpointMoment hA hactive (by omega)
  rw [htsum]
  ring

/-- A nonempty active physical packet cannot have an o(1/N) character-energy tail. -/
theorem not_tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail_zero
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    ¬ Tendsto (fun N : ℕ => (N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k)) atTop (𝓝 0) := by
  intro hzero
  have hA : 0 < A := hwidth0.trans hwidthA
  have htail := tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail P hA hactive
  have heq := tendsto_nhds_unique htail hzero
  have hmass := sum_normSq_xiPhysicalPrimeLogEndpointCircleJump_pos
    hP hactive hwidth0 hwidthA
  have hcoef : 0 < A ^ 2 / (4 * Real.pi ^ 2) := by positivity
  nlinarith

end

end RHTower
