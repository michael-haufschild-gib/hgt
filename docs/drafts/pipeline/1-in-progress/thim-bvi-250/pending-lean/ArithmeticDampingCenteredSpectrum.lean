import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingCenteredSemigroup
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The real spectrum of the centered arithmetic damping semigroup

Normalized residue profiles are the common eigenvectors of all positive-time
operators. Their eigenvalues are the powers `d ^ (-η)`, for `d ≥ 2`; zero is
spectral but is not an eigenvalue. Triangular incidence determines every
eigenvector, and compact Fredholm theory completes the real spectrum.
These statements concern `c₀`, not the critical pronic receiver norm.
-/

open Finset Filter Topology
open scoped ZeroAtInfty

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private theorem ads_tendsto_zero (b : C₀(ℕ, ℝ)) :
    Tendsto (fun n => b n) atTop (𝓝 0) := by
  have h := b.zero_at_infty'
  rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at h

private theorem ads_constant_eq_zero (b : C₀(ℕ, ℝ))
    (h : ∀ n, b n = b 0) : b = 0 := by
  have hz : b 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds ((ads_tendsto_zero b).congr h)
  exact ZeroAtInftyContinuousMap.ext fun n => (h n).trans hz

private theorem ads_floor_sub {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    arithmeticDampingFloorProfile d n - 1 / (d : ℝ) =
      -((n % d : ℕ) : ℝ) / ((d : ℝ) * n) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : ((n % d : ℕ) : ℝ) + (d : ℝ) * (n / d : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n d
  unfold arithmeticDampingFloorProfile
  field_simp
  nlinarith

private theorem ads_floor_sub_bound {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    |arithmeticDampingFloorProfile d n - 1 / (d : ℝ)| ≤ 1 / (n : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ads_floor_sub hd hn, abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (mul_pos hd' hn')]
  calc
    _ ≤ (d : ℝ) / ((d : ℝ) * n) :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Nat.mod_lt n hd).le)
        (mul_pos hd' hn').le
    _ = 1 / (n : ℝ) := by field_simp

private theorem ads_floor_sub_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n => arithmeticDampingFloorProfile d (n + 1) - 1 / (d : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    ads_floor_sub_bound hd (Nat.succ_pos n)

/-- The floor eigenprofile with its limiting constant removed. -/
def arithmeticDampingResidueMode (d : ℕ) (hd : 0 < d) : C₀(ℕ, ℝ) :=
  ⟨⟨fun n => arithmeticDampingFloorProfile d (n + 1) - 1 / (d : ℝ),
    continuous_of_discreteTopology⟩, by
      rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
      exact ads_floor_sub_tendsto hd⟩

@[simp] theorem arithmeticDampingResidueMode_apply (d : ℕ) (hd : 0 < d) (n : ℕ) :
    arithmeticDampingResidueMode d hd n =
      arithmeticDampingFloorProfile d (n + 1) - 1 / (d : ℝ) := rfl

theorem arithmeticDampingResidueMode_zero {d : ℕ} (hd : 2 ≤ d) :
    arithmeticDampingResidueMode d (by omega) 0 = -1 / (d : ℝ) := by
  rw [arithmeticDampingResidueMode_apply,
    arithmeticDampingFloorProfile_eq_zero_of_lt (by omega)]
  ring

theorem arithmeticDampingResidueMode_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    arithmeticDampingResidueMode d (by omega) ≠ 0 := by
  intro h
  have he := congrArg (fun b : C₀(ℕ, ℝ) => b 0) h
  rw [arithmeticDampingResidueMode_zero hd] at he
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have : (-1 : ℝ) / d < 0 := div_neg_of_neg_of_pos (by linarith) hd'
  exact this.ne he

private theorem ads_finite_floor (η : ℝ) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    arithmeticDampingFiniteAction η
      (fun k => arithmeticDampingFloorProfile d (k + 1)) n =
      (d : ℝ) ^ (-η) * arithmeticDampingFloorProfile d (n + 1) := by
  simpa only [arithmeticDampingFiniteAction, sum_Icc_eq_sum_range_shift] using
    arithmeticDampingTransition_floorProfile η (Nat.succ_pos n) hd

private theorem ads_centered_mode_difference {η : ℝ} (hη : 0 < η)
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    arithmeticDampingCenteredOperator hη (arithmeticDampingResidueMode d hd) n -
        (d : ℝ) ^ (-η) * arithmeticDampingResidueMode d hd n =
      ((d : ℝ) ^ (-η) - 1) / d -
        arithmeticDampingEntrancePair η (arithmeticDampingResidueMode d hd) := by
  rw [arithmeticDampingCenteredOperator_eq_finiteAction]
  change arithmeticDampingFiniteAction η
      (fun k => arithmeticDampingFloorProfile d (k + 1) - 1 / (d : ℝ)) n - _ -
      (d : ℝ) ^ (-η) * (arithmeticDampingFloorProfile d (n + 1) - 1 / (d : ℝ)) = _
  rw [arithmeticDampingFiniteAction_sub_const, ads_finite_floor η hd]
  ring

/-- Centering fixes the entrance value of every floor eigenprofile. -/
theorem arithmeticDampingEntrancePair_residueMode {η : ℝ} (hη : 0 < η)
    (d : ℕ) (hd : 0 < d) :
    arithmeticDampingEntrancePair η (arithmeticDampingResidueMode d hd) =
      ((d : ℝ) ^ (-η) - 1) / d := by
  have ht := (ads_tendsto_zero
    (arithmeticDampingCenteredOperator hη (arithmeticDampingResidueMode d hd))).sub
      ((ads_tendsto_zero (arithmeticDampingResidueMode d hd)).const_mul ((d : ℝ) ^ (-η)))
  simp only [mul_zero, sub_zero] at ht
  have hc := ht.congr (ads_centered_mode_difference hη d hd)
  have he := tendsto_nhds_unique hc tendsto_const_nhds
  linarith

/-- Residue profiles are simultaneous eigenvectors at every positive damping. -/
theorem arithmeticDampingCenteredOperator_residueMode {η : ℝ} (hη : 0 < η)
    (d : ℕ) (hd : 0 < d) :
    arithmeticDampingCenteredOperator hη (arithmeticDampingResidueMode d hd) =
      (d : ℝ) ^ (-η) • arithmeticDampingResidueMode d hd := by
  apply ZeroAtInftyContinuousMap.ext
  intro n
  have h := ads_centered_mode_difference hη d hd n
  rw [arithmeticDampingEntrancePair_residueMode hη, sub_self] at h
  exact sub_eq_zero.mp h

private theorem ads_finite_zero (η : ℝ) (b : ℕ → ℝ) :
    arithmeticDampingFiniteAction η b 0 = b 0 := by
  simp [arithmeticDampingFiniteAction, arithmeticDampingTransition_diagonal]

private theorem ads_eigen_raw {η λ : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ))
    (hb : arithmeticDampingCenteredOperator hη b = λ • b) (n : ℕ) :
    arithmeticDampingFiniteAction η (fun k => b k - b 0) n = λ * (b n - b 0) := by
  have hn := congrArg (fun c : C₀(ℕ, ℝ) => c n) hb
  have h0 := congrArg (fun c : C₀(ℕ, ℝ) => c 0) hb
  rw [arithmeticDampingCenteredOperator_eq_finiteAction] at hn h0
  rw [ads_finite_zero] at h0
  change arithmeticDampingFiniteAction η b n - arithmeticDampingEntrancePair η b =
    λ * b n at hn
  change b 0 - arithmeticDampingEntrancePair η b = λ * b 0 at h0
  rw [arithmeticDampingFiniteAction_sub_const]
  nlinarith

private theorem ads_eigen_step {η λ : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ))
    (hb : arithmeticDampingCenteredOperator hη b = λ • b) (n : ℕ)
    (hprev : ∀ k < n, b k = b 0) :
    (λ - ((n + 1 : ℕ) : ℝ) ^ (-η)) * (b n - b 0) = 0 := by
  have h := ads_eigen_raw hη b hb n
  unfold arithmeticDampingFiniteAction at h
  rw [sum_range_succ] at h
  have hz : (∑ k ∈ range n, arithmeticDampingTransition η (n + 1) (k + 1) *
      (b k - b 0)) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [hprev k (mem_range.mp hk), sub_self, mul_zero]
  rw [hz, zero_add, arithmeticDampingTransition_diagonal η (Nat.succ_pos n)] at h
  nlinarith

private theorem ads_eigen_eq_zero_of_no_diagonal {η λ : ℝ} (hη : 0 < η)
    (b : C₀(ℕ, ℝ)) (hb : arithmeticDampingCenteredOperator hη b = λ • b)
    (hλ : ∀ d : ℕ, 2 ≤ d → λ ≠ (d : ℝ) ^ (-η)) : b = 0 := by
  apply ads_constant_eq_zero b
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn]
    have hstep := ads_eigen_step hη b hb n ih
    exact sub_eq_zero.mp ((mul_eq_zero.mp hstep).resolve_left
      (sub_ne_zero.mpr (hλ (n + 1) (by omega))))

/-- A centered eigenvalue is forced by the first nonconstant incidence state. -/
theorem arithmeticDampingCenteredOperator_eigenvalue_iff {η : ℝ} (hη : 0 < η)
    (λ : ℝ) :
    (arithmeticDampingCenteredOperator hη : Module.End ℝ C₀(ℕ, ℝ)).HasEigenvalue λ ↔
      ∃ d : ℕ, 2 ≤ d ∧ λ = (d : ℝ) ^ (-η) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_hasEigenvector
    by_contra! hn
    exact hb.ne_zero (ads_eigen_eq_zero_of_no_diagonal hη b hb.apply_eq_smul hn)
  · rintro ⟨d, hd, rfl⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := arithmeticDampingResidueMode d (by omega))
    exact ⟨Module.End.mem_eigenspace_iff.mpr
      (arithmeticDampingCenteredOperator_residueMode hη d (by omega)),
      arithmeticDampingResidueMode_ne_zero hd⟩

private theorem ads_eigen_eq_zero_of_anchor {η : ℝ} (hη : 0 < η) {d : ℕ}
    (hd : 2 ≤ d) (b : C₀(ℕ, ℝ))
    (hb : arithmeticDampingCenteredOperator hη b = (d : ℝ) ^ (-η) • b)
    (ha : b (d - 1) = b 0) : b = 0 := by
  apply ads_constant_eq_zero b
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn]
    by_cases hnd : n + 1 = d
    · have : n = d - 1 := by omega
      simpa only [this] using ha
    have hne : (d : ℝ) ^ (-η) ≠ ((n + 1 : ℕ) : ℝ) ^ (-η) := by
      intro he
      have he' := (Real.rpow_left_inj (Nat.cast_nonneg d)
        (Nat.cast_nonneg (n + 1)) (neg_ne_zero.mpr hη.ne')).mp he
      exact hnd (Nat.cast_injective he').symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp (ads_eigen_step hη b hb n ih)).resolve_left
      (sub_ne_zero.mpr hne))

/-- Each eigenspace is the line of one normalized residue profile. -/
theorem arithmeticDampingCenteredOperator_eigenspace_iff {η : ℝ} (hη : 0 < η)
    {d : ℕ} (hd : 2 ≤ d) (b : C₀(ℕ, ℝ)) :
    arithmeticDampingCenteredOperator hη b = (d : ℝ) ^ (-η) • b ↔
      ∃ a : ℝ, b = a • arithmeticDampingResidueMode d (by omega) := by
  constructor
  · intro hb
    let a : ℝ := (d : ℝ) * (b (d - 1) - b 0)
    let v := arithmeticDampingResidueMode d (show 0 < d by omega)
    have hv : v (d - 1) = 0 := by
      simp only [v, arithmeticDampingResidueMode_apply,
        Nat.sub_add_cancel (show 1 ≤ d by omega),
        arithmeticDampingFloorProfile_self (show 0 < d by omega), sub_self]
    have hv0 : v 0 = -1 / (d : ℝ) := arithmeticDampingResidueMode_zero hd
    have he : arithmeticDampingCenteredOperator hη (b - a • v) =
        (d : ℝ) ^ (-η) • (b - a • v) := by
      rw [map_sub, map_smul, hb, arithmeticDampingCenteredOperator_residueMode]
      module
    have ha : (b - a • v) (d - 1) = (b - a • v) 0 := by
      change b (d - 1) - a * v (d - 1) = b 0 - a * v 0
      rw [hv, hv0]
      dsimp [a]
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      field_simp
      ring
    exact ⟨a, sub_eq_zero.mp (ads_eigen_eq_zero_of_anchor hη hd _ he ha)⟩
  · rintro ⟨a, rfl⟩
    rw [map_smul, arithmeticDampingCenteredOperator_residueMode]
    module

/-- No information is killed by a positive-time centered transition on `c₀`. -/
theorem arithmeticDampingCenteredOperator_injective {η : ℝ} (hη : 0 < η) :
    Function.Injective (arithmeticDampingCenteredOperator hη) := by
  intro b c hbc
  apply sub_eq_zero.mp
  apply ads_eigen_eq_zero_of_no_diagonal hη (b - c) (λ := 0)
  · simp only [map_sub, hbc, sub_self, zero_smul]
  · intro d hd
    exact (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < d by omega)) _).ne

private theorem ads_power_mem_spectrum {η : ℝ} (hη : 0 < η) {d : ℕ}
    (hd : 2 ≤ d) :
    (d : ℝ) ^ (-η) ∈ spectrum ℝ (arithmeticDampingCenteredOperator hη) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact ((arithmeticDampingCenteredOperator_eigenvalue_iff hη _).2 ⟨d, hd, rfl⟩).mem_spectrum

/-- Zero is a spectral accumulation point, although the operator is injective. -/
theorem zero_mem_spectrum_arithmeticDampingCenteredOperator {η : ℝ} (hη : 0 < η) :
    0 ∈ spectrum ℝ (arithmeticDampingCenteredOperator hη) := by
  apply (spectrum.isClosed (arithmeticDampingCenteredOperator hη)).mem_of_tendsto
    ((Real.tendsto_rpow_neg_atTop hη).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))
  exact Eventually.of_forall fun n => ads_power_mem_spectrum hη (by omega : 2 ≤ n + 2)

/-- The complete real spectrum: positive integer damping powers and their limit zero. -/
theorem mem_spectrum_arithmeticDampingCenteredOperator_iff {η : ℝ} (hη : 0 < η)
    (λ : ℝ) :
    λ ∈ spectrum ℝ (arithmeticDampingCenteredOperator hη) ↔
      λ = 0 ∨ ∃ d : ℕ, 2 ≤ d ∧ λ = (d : ℝ) ^ (-η) := by
  by_cases hλ : λ = 0
  · simp only [hλ, zero_mem_spectrum_arithmeticDampingCenteredOperator hη, true_or]
  · rw [← (isCompactOperator_arithmeticDampingCenteredOperator hη).
      hasEigenvalue_iff_mem_spectrum hλ,
      arithmeticDampingCenteredOperator_eigenvalue_iff hη]
    simp only [hλ, false_or]

end
end GaloisForLFunctions.BezoutValuationIncidence
