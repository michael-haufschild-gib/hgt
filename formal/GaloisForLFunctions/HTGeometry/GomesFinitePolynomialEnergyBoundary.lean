import GaloisForLFunctions.HTGeometry.GomesFiniteQuadraticCurvature

/-!
# Exact energy offsets of finite polynomial profiles against arbitrary competitors

The scalar Gomes reconstruction experiment has a one-sided energy boundary. Finite
profiles admit only zero offsets, except negative-curvature quadratics, which admit
one additional negative offset and one opposite-profile connection class.
-/

noncomputable section
open Polynomial MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- An arbitrary competitor either has the same connection or is the opposite negative quadratic. -/
theorem gomesFinitePolynomialEnergyShift_arbitrary_iff
    (P : GomesFinitePolynomialProfile) (K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift P.val K k ↔
      (dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM K ∧ k = 0) ∨
        (k < 0 ∧ P.val.derivative.derivative = C k ∧ ∃ c : ℝ, K = -P.val + C c) := by
  rw [gomesDilatonEnergyShift_potential_iff, gomesDilatonPotential_shifted_derivatives_iff]
  constructor
  · rintro (⟨hd, hk⟩ | ⟨a, b, hp, _, _⟩ | ⟨hu, hd⟩)
    · exact Or.inl ⟨(gomesDilatonConnection_eq_iff P.val K).mpr hd, hk⟩
    · exfalso
      apply gomesFinitePolynomialProfile_curvature_ne_zero P
      rw [hp, derivative_C]
    · refine Or.inr ⟨((gomesFinitePolynomialProfile_constant_curvature_iff P k).mp hd).1, hd, ?_⟩
      apply (gomesDilatonDerivative_eq_iff K (-P.val)).mp
      rw [derivative_neg]
      exact ((neg_eq_iff_eq_neg).mpr hu).symm
  · rintro (⟨hc, hk⟩ | ⟨_, hd, c, hc⟩)
    · exact Or.inl ⟨(gomesDilatonConnection_eq_iff P.val K).mp hc, hk⟩
    · refine Or.inr (Or.inr ⟨?_, hd⟩)
      rw [hc]
      simp

/-- Every possible scalar energy offset, allowing all real polynomial competitors. -/
def gomesFinitePolynomialEnergyOffsets (P : GomesFinitePolynomialProfile) : Set ℝ :=
  {k | ∃ K : ℝ[X], gomesDilatonEnergyShift P.val K k}

/-- The admissible offsets are zero and, only for a quadratic, its unique negative curvature. -/
theorem gomesFinitePolynomialEnergyOffsets_mem_iff (P : GomesFinitePolynomialProfile) (k : ℝ) :
    k ∈ gomesFinitePolynomialEnergyOffsets P ↔
      k = 0 ∨ (k < 0 ∧ P.val.derivative.derivative = C k) := by
  constructor
  · rintro ⟨K, h⟩
    rcases (gomesFinitePolynomialEnergyShift_arbitrary_iff P K k).mp h with ⟨_, hk⟩ | ⟨hk, hd, _⟩
    · exact Or.inl hk
    · exact Or.inr ⟨hk, hd⟩
  · rintro (rfl | ⟨hk, hd⟩)
    · exact ⟨P.val, (gomesDilatonEnergyShift_zero_iff P.val P.val).mpr rfl⟩
    · exact ⟨-P.val, (gomesFinitePolynomialEnergyShift_arbitrary_iff P (-P.val) k).mpr
        (Or.inr ⟨hk, hd, 0, by simp⟩)⟩

/-- Every admissible energy offset from a finite profile is nonpositive. -/
theorem gomesFinitePolynomialEnergyOffsets_nonpositive (P : GomesFinitePolynomialProfile) :
    gomesFinitePolynomialEnergyOffsets P ⊆ Set.Iic 0 := by
  intro k h
  change k ≤ (0 : ℝ)
  rcases (gomesFinitePolynomialEnergyOffsets_mem_iff P k).mp h with rfl | ⟨hk, _⟩
  · exact le_rfl
  · exact hk.le

/-- A nonzero offset exists exactly for profiles with vanishing third derivative. -/
theorem gomesFinitePolynomialEnergyOffsets_nonzero_iff (P : GomesFinitePolynomialProfile) :
    (∃ k ∈ gomesFinitePolynomialEnergyOffsets P, k ≠ 0) ↔
      P.val.derivative.derivative.derivative = 0 := by
  constructor
  · rintro ⟨k, h, hn⟩
    have hd := ((gomesFinitePolynomialEnergyOffsets_mem_iff P k).mp h).resolve_left hn
    rw [hd.2, derivative_C]
  · intro h
    obtain ⟨k, hk, hd⟩ := (gomesFinitePolynomialProfile_third_derivative_zero_iff P).mp h
    exact ⟨k, (gomesFinitePolynomialEnergyOffsets_mem_iff P k).mpr (Or.inr ⟨hk, hd⟩), hk.ne⟩

/-- The full offset set has exactly one value, or zero and the negative origin curvature. -/
theorem gomesFinitePolynomialEnergyOffsets_exact (P : GomesFinitePolynomialProfile) :
    gomesFinitePolynomialEnergyOffsets P =
      if P.val.derivative.derivative.derivative = 0
      then {0, P.val.derivative.derivative.eval 0} else {0} := by
  classical
  by_cases hp : P.val.derivative.derivative.derivative = 0
  · rw [if_pos hp]
    obtain ⟨hk, hd⟩ := gomesFinitePolynomialProfile_quadratic_origin_curvature ⟨P, hp⟩
    ext k
    rw [gomesFinitePolynomialEnergyOffsets_mem_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hz | ⟨_, hc⟩)
      · exact Or.inl hz
      · right
        have he := congrArg (Polynomial.eval 0) hc
        simpa only [eval_C] using he.symm
    · rintro (hz | rfl)
      · exact Or.inl hz
      · exact Or.inr ⟨hk, hd⟩
  · rw [if_neg hp]
    ext k
    rw [gomesFinitePolynomialEnergyOffsets_mem_iff]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro (hz | ⟨_, hd⟩)
      · exact hz
      · exact False.elim (hp (by rw [hd, derivative_C]))
    · exact Or.inl

/-- The zero-offset boundary is precisely equality of first-order connections. -/
theorem gomesFinitePolynomialEnergyShift_zero_connection_iff (P : GomesFinitePolynomialProfile) (K : ℝ[X]) :
    gomesDilatonEnergyShift P.val K 0 ↔ dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM K := by
  rw [gomesFinitePolynomialEnergyShift_arbitrary_iff]
  simp only [lt_self_iff_false, false_and, or_false, and_true]

end GaloisForLFunctions.HTGeometry
