import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ResidueModesAndBackwardContinuation
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The complete spectrum of the centered arithmetic damping operator

At damping `η > 0` the centered chain `C_η = P_η − e_η` is a compact operator on `c₀`
(`isCompactOperator_arithmeticDampingCenteredOperator`) with the residue modes
`v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d` as eigenvectors, `C_η v_d = d^{−η} v_d`
(`SignedArithmeticEnergyIncidence.centeredOperator_normalizedResidueMode`). This module shows that
these are *all* the eigenvectors and computes the spectrum exactly:

* `arithmeticDampingCenteredOperator_hasEigenvalue_iff`: the eigenvalues are exactly `d^{−η}`, `d ≥ 2`;
* `arithmeticDampingCenteredOperator_eigen_iff`: the `d^{−η}`-eigenspace is the line `ℝ v_d`;
* `arithmeticDampingCenteredOperator_injective`: `C_η` is injective;
* `mem_spectrum_arithmeticDampingCenteredOperator_iff`: `σ(C_η) = {0} ∪ {d^{−η} : d ≥ 2}`.

Mechanism: an eigen-equation `C_η b = λ b` read at the first state fixes the entrance value,
`e_η(b) = (1 − λ) b(0)`, so `g = b − b(0)` solves the *raw* lower-triangular equation
`P_η g = λ g` with diagonal `(n+1)^{−η}`. The first state where `g` is nonzero therefore
forces `λ = d^{−η}`; distinct diagonal entries propagate one free coordinate. Compactness and the
Fredholm alternative turn eigenvalues into the nonzero spectrum, and `d^{−η} → 0` adds zero.

The statements concern `c₀`. They give the damping chain a diagonal spectral calculus on the
residue modes, not bounded spectral projections and not an estimate in the pronic receiver norm.
-/

open Finset Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.SignedArithmeticEnergyIncidence

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

private theorem ads_tendsto_zero (b : C₀(ℕ, ℝ)) :
    Tendsto (fun n => b n) atTop (𝓝 0) := by
  have h := b.zero_at_infty'
  rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at h

/-- A constant sequence vanishing at infinity is zero. -/
private theorem ads_constant_eq_zero (b : C₀(ℕ, ℝ)) (h : ∀ n, b n = b 0) : b = 0 := by
  have hz : b 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds ((ads_tendsto_zero b).congr' (Eventually.of_forall h))
  exact ZeroAtInftyContinuousMap.ext fun n => (h n).trans hz

private theorem ads_finite_zero (η : ℝ) (b : ℕ → ℝ) :
    arithmeticDampingFiniteAction η b 0 = b 0 := by
  have h := arithmeticDampingTransition_diagonal η (n := 1) one_pos
  simp only [arithmeticDampingFiniteAction, zero_add, range_one, sum_singleton]
  rw [h, Nat.cast_one, Real.one_rpow, one_mul]

/-- Centered eigen-equations are raw eigen-equations after removing the first coordinate. -/
private theorem ads_eigen_raw {η r : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ))
    (hb : arithmeticDampingCenteredOperator hη b = r • b) (n : ℕ) :
    arithmeticDampingFiniteAction η (fun k => b k - b 0) n = r * (b n - b 0) := by
  have hn := congrArg (fun c : C₀(ℕ, ℝ) => c n) hb
  have h0 := congrArg (fun c : C₀(ℕ, ℝ) => c 0) hb
  simp only [arithmeticDampingCenteredOperator_eq_finiteAction,
    ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul] at hn h0
  rw [ads_finite_zero] at h0
  rw [arithmeticDampingFiniteAction_sub_const]
  linear_combination hn - h0

/-- Triangularity: once the eigenvector is constant before `n`, the diagonal decides state `n`. -/
private theorem ads_eigen_step {η r : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ))
    (hb : arithmeticDampingCenteredOperator hη b = r • b) (n : ℕ)
    (hprev : ∀ k < n, b k = b 0) :
    (r - ((n + 1 : ℕ) : ℝ) ^ (-η)) * (b n - b 0) = 0 := by
  have h := ads_eigen_raw hη b hb n
  simp only [arithmeticDampingFiniteAction] at h
  rw [Finset.sum_range_succ] at h
  have hz : (∑ k ∈ range n, arithmeticDampingTransition η (n + 1) (k + 1) *
      (b k - b 0)) = 0 :=
    sum_eq_zero fun k hk => by rw [hprev k (mem_range.mp hk), sub_self, mul_zero]
  rw [hz, zero_add, arithmeticDampingTransition_diagonal η (Nat.succ_pos n)] at h
  linear_combination -h

private theorem ads_eq_zero_of_no_diagonal {η r : ℝ} (hη : 0 < η)
    (b : C₀(ℕ, ℝ)) (hb : arithmeticDampingCenteredOperator hη b = r • b)
    (hr : ∀ d : ℕ, 2 ≤ d → r ≠ (d : ℝ) ^ (-η)) : b = 0 := by
  apply ads_constant_eq_zero b
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    exact sub_eq_zero.mp ((mul_eq_zero.mp (ads_eigen_step hη b hb n ih)).resolve_left
      (sub_ne_zero.mpr (hr (n + 1) (by omega))))

/-- **Eigenvalues.** The centered chain has exactly the eigenvalues `d^{−η}`, `d ≥ 2`. -/
theorem arithmeticDampingCenteredOperator_hasEigenvalue_iff {η : ℝ} (hη : 0 < η) (r : ℝ) :
    Module.End.HasEigenvalue (arithmeticDampingCenteredOperator hη : Module.End ℝ C₀(ℕ, ℝ)) r ↔
      ∃ d : ℕ, 2 ≤ d ∧ r = (d : ℝ) ^ (-η) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_hasEigenvector
    by_contra! hn
    exact hb.2 (ads_eq_zero_of_no_diagonal hη b hb.apply_eq_smul hn)
  · rintro ⟨d, hd, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (centeredOperator_normalizedResidueMode hη (by omega)),
        normalizedResidueMode_ne_zero hd⟩

/-- An eigenvector of `d^{−η}` that agrees with its first coordinate at state `d − 1` is zero. -/
private theorem ads_eq_zero_of_anchor {η : ℝ} (hη : 0 < η) {d : ℕ} (hd : 2 ≤ d)
    (b : C₀(ℕ, ℝ)) (hb : arithmeticDampingCenteredOperator hη b = (d : ℝ) ^ (-η) • b)
    (ha : b (d - 1) = b 0) : b = 0 := by
  apply ads_constant_eq_zero b
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnd : n + 1 = d
    · rw [show n = d - 1 by omega]; exact ha
    have hne : (d : ℝ) ^ (-η) ≠ ((n + 1 : ℕ) : ℝ) ^ (-η) := by
      intro he
      have he' := (Real.rpow_left_inj (Nat.cast_nonneg d) (Nat.cast_nonneg (n + 1))
        (neg_ne_zero.mpr hη.ne')).mp he
      exact hnd (Nat.cast_injective he').symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp (ads_eigen_step hη b hb n ih)).resolve_left
      (sub_ne_zero.mpr hne))

/-- **Eigenspaces are lines.** The `d^{−η}`-eigenspace of `C_η` is spanned by the residue mode `v_d`. -/
theorem arithmeticDampingCenteredOperator_eigen_iff {η : ℝ} (hη : 0 < η) {d : ℕ}
    (hd : 2 ≤ d) (b : C₀(ℕ, ℝ)) :
    arithmeticDampingCenteredOperator hη b = (d : ℝ) ^ (-η) • b ↔
      ∃ a : ℝ, b = a • normalizedResidueMode d := by
  have hd0 : 0 < d := by omega
  have hv : ∀ a : ℝ, arithmeticDampingCenteredOperator hη (a • normalizedResidueMode d) =
      (d : ℝ) ^ (-η) • (a • normalizedResidueMode d) := fun a => by
    rw [map_smul, centeredOperator_normalizedResidueMode hη hd0, smul_comm]
  constructor
  · intro hb
    set a : ℝ := (d : ℝ) * (b (d - 1) - b 0) with ha
    have hvd : normalizedResidueMode d (d - 1) = 0 := by
      rw [normalizedResidueMode_apply, normalizedResidueProfile, Nat.sub_add_cancel (by omega),
        Nat.div_self hd0, Nat.cast_one, sub_self]
    have hv0 : normalizedResidueMode d 0 = -1 / (d : ℝ) := by
      rw [normalizedResidueMode_apply, normalizedResidueProfile_of_lt (by omega)]
    have he : arithmeticDampingCenteredOperator hη (b - a • normalizedResidueMode d) =
        (d : ℝ) ^ (-η) • (b - a • normalizedResidueMode d) := by
      rw [map_sub, hb, hv, smul_sub]
    have hanchor : (b - a • normalizedResidueMode d) (d - 1) =
        (b - a • normalizedResidueMode d) 0 := by
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
        smul_eq_mul, hvd, hv0, ha]
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      field_simp
      ring
    exact ⟨a, sub_eq_zero.mp (ads_eq_zero_of_anchor hη hd _ he hanchor)⟩
  · rintro ⟨a, rfl⟩
    exact hv a

/-- **Injectivity.** No nonzero `c₀` sequence is annihilated by a positive-time centered transition. -/
theorem arithmeticDampingCenteredOperator_injective {η : ℝ} (hη : 0 < η) :
    Function.Injective (arithmeticDampingCenteredOperator hη) := by
  intro b c hbc
  refine sub_eq_zero.mp (ads_eq_zero_of_no_diagonal hη (b - c) (r := 0) ?_ fun d hd => ?_)
  · rw [map_sub, hbc, sub_self, zero_smul]
  · exact (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < d by omega)) _).ne

private theorem ads_power_mem_spectrum {η : ℝ} (hη : 0 < η) {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) ^ (-η) ∈ spectrum ℝ (arithmeticDampingCenteredOperator hη) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact ((arithmeticDampingCenteredOperator_hasEigenvalue_iff hη _).2 ⟨d, hd, rfl⟩).mem_spectrum

/-- Zero is spectral, as the accumulation point of the eigenvalues, though not an eigenvalue. -/
theorem zero_mem_spectrum_arithmeticDampingCenteredOperator {η : ℝ} (hη : 0 < η) :
    (0 : ℝ) ∈ spectrum ℝ (arithmeticDampingCenteredOperator hη) := by
  have ht : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-η)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hη).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  exact (spectrum.isClosed (arithmeticDampingCenteredOperator hη)).mem_of_tendsto ht
    (Eventually.of_forall fun n => ads_power_mem_spectrum hη (by omega))

/-- **The complete real spectrum** `σ(C_η) = {0} ∪ {d^{−η} : d ≥ 2}` at every positive damping. -/
theorem mem_spectrum_arithmeticDampingCenteredOperator_iff {η : ℝ} (hη : 0 < η) (r : ℝ) :
    r ∈ spectrum ℝ (arithmeticDampingCenteredOperator hη) ↔
      r = 0 ∨ ∃ d : ℕ, 2 ≤ d ∧ r = (d : ℝ) ^ (-η) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [zero_mem_spectrum_arithmeticDampingCenteredOperator hη, true_or]
  · rw [← (isCompactOperator_arithmeticDampingCenteredOperator hη).hasEigenvalue_iff_mem_spectrum hr,
      arithmeticDampingCenteredOperator_hasEigenvalue_iff hη]
    simp only [hr, false_or]

end

end GaloisForLFunctions.BezoutValuationIncidence
