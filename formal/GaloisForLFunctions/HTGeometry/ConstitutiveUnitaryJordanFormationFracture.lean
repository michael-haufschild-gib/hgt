import GaloisForLFunctions.HTGeometry.ConstitutiveCanonicalCoinducedReporter
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Unitary Jordan collapse and coinduced formation fracture

A positive unitary action has no nontrivial finite Jordan chains at eigenvalue one.  The canonical
coinduced history quotient, however, contains the exact chain `[x²] -> 2[x] -> 0` under translation
by one.  Hence no injective additive reporter can intertwine that exact recovery action with a
Hilbert-space linear isometry.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A fixed displacement of an isometric action vanishes. -/
theorem linearIsometryEquiv_fixed_of_fixed_displacement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H ≃ₗᵢ[ℝ] H) (v : H)
    (hfix : U (U v - v) = U v - v) :
    U v = v := by
  let w : H := U v - v
  have hUv : U v = v + w := by
    simp [w]
  have hUw : U w = w := hfix
  have hin := U.inner_map_map v w
  rw [hUv, hUw, inner_add_left] at hin
  have hww : inner ℝ w w = 0 := by
    linarith
  have hw : w = 0 := (inner_self_eq_zero.mp hww)
  exact sub_eq_zero.mp (by simpa [w] using hw)

/-- Iterated displacement under an isometric action. -/
def iteratedIsometricDisplacement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H ≃ₗᵢ[ℝ] H) : ℕ → H → H
  | 0, v => v
  | n + 1, v => iteratedIsometricDisplacement U n (U v - v)

/-- A unitary/isometric action has no nontrivial finite Jordan chains at eigenvalue one. -/
theorem linearIsometryEquiv_fixed_of_iterated_displacement_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H ≃ₗᵢ[ℝ] H) (v : H) (n : ℕ)
    (hzero : iteratedIsometricDisplacement U (n + 1) v = 0) :
    U v = v := by
  induction n generalizing v with
  | zero =>
      exact sub_eq_zero.mp hzero
  | succ n ih =>
      have hfix : U (U v - v) = U v - v := by
        apply ih (v := U v - v)
        exact hzero
      exact linearIsometryEquiv_fixed_of_fixed_displacement U v hfix

/-- Coinduced real histories modulo constant functions. -/
abbrev RealCoinducedHistoryQuotient :=
  CohomologicalCoinducedQuotient (G := ℝ) (A := ℝ)

/-- Linear history on the additive real source. -/
def coinducedLinearHistory (x : ℝ) : ℝ := x

/-- Quadratic history on the additive real source. -/
def coinducedQuadraticHistory (x : ℝ) : ℝ := x ^ 2

/-- Linear coinduced history modulo constants. -/
def coinducedLinearHistoryClass : RealCoinducedHistoryQuotient :=
  QuotientAddGroup.mk coinducedLinearHistory

/-- Quadratic coinduced history modulo constants. -/
def coinducedQuadraticHistoryClass : RealCoinducedHistoryQuotient :=
  QuotientAddGroup.mk coinducedQuadraticHistory

/-- Translation by one fixes the linear history modulo constants. -/
theorem coinducedLinearHistoryClass_fixed :
    coinducedQuotientRightTranslateEquiv (A := ℝ) (1 : ℝ)
        coinducedLinearHistoryClass =
      coinducedLinearHistoryClass := by
  rw [coinducedLinearHistoryClass, coinducedQuotientRightTranslateEquiv_mk]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨(1 : ℝ), ?_⟩
  funext x
  simp [coinducedFormationRightTranslate, coinducedFormationConstant,
    coinducedLinearHistory]

/-- Translation by one sends the quadratic history to itself plus twice the linear history. -/
theorem coinducedQuadraticHistoryClass_translate :
    coinducedQuotientRightTranslateEquiv (A := ℝ) (1 : ℝ)
        coinducedQuadraticHistoryClass =
      coinducedQuadraticHistoryClass +
        coinducedLinearHistoryClass + coinducedLinearHistoryClass := by
  rw [coinducedQuadraticHistoryClass, coinducedLinearHistoryClass,
    coinducedQuotientRightTranslateEquiv_mk]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨(1 : ℝ), ?_⟩
  funext x
  simp [coinducedFormationRightTranslate, coinducedFormationConstant,
    coinducedLinearHistory, coinducedQuadraticHistory]
  ring

/-- Twice the linear history is not constant, hence survives the quotient. -/
theorem coinducedLinearHistoryClass_add_self_ne_zero :
    coinducedLinearHistoryClass + coinducedLinearHistoryClass ≠ 0 := by
  intro hzero
  have hmk : (QuotientAddGroup.mk
      (fun x : ℝ => coinducedLinearHistory x + coinducedLinearHistory x) :
        RealCoinducedHistoryQuotient) = 0 := by
    change (QuotientAddGroup.mk'
      (coinducedFormationConstantSubgroup (G := ℝ) (A := ℝ)))
        (coinducedLinearHistory + coinducedLinearHistory) = 0
    rw [map_add]
    exact hzero
  rw [QuotientAddGroup.eq_zero_iff] at hmk
  obtain ⟨a, ha⟩ := hmk
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [coinducedLinearHistory, coinducedFormationConstant] at h0 h1
  linarith

/-- **Canonical Hilbertization fracture.**  No injective additive reporter intertwines translation
on real coinduced histories modulo constants with a Hilbert-space linear isometry. -/
theorem no_faithful_unitary_realization_of_coinduced_translation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r : RealCoinducedHistoryQuotient →+ H)
    (U : H ≃ₗᵢ[ℝ] H)
    (hr : Function.Injective r)
    (hintertwine : ∀ q,
      r (coinducedQuotientRightTranslateEquiv (A := ℝ) (1 : ℝ) q) = U (r q)) :
    False := by
  let l := coinducedLinearHistoryClass
  let q := coinducedQuadraticHistoryClass
  have hlfix : U (r l) = r l := by
    rw [← hintertwine]
    exact congrArg r (by simpa [l] using coinducedLinearHistoryClass_fixed)
  have hqtranslate : U (r q) = r q + r l + r l := by
    rw [← hintertwine, coinducedQuadraticHistoryClass_translate]
    simp [q, l]
  have hdisp : U (U (r q) - r q) = U (r q) - r q := by
    rw [map_sub, hqtranslate, map_add, map_add, hqtranslate, hlfix]
    abel
  have hfixed := linearIsometryEquiv_fixed_of_fixed_displacement U (r q) hdisp
  have hrl : r (l + l) = 0 := by
    rw [map_add]
    rw [hqtranslate] at hfixed
    have : r l + r l = 0 := by
      apply add_left_cancel (a := r q)
      simpa [add_assoc] using hfixed
    simpa using this
  have hll : l + l = 0 := hr (by simpa using hrl)
  exact coinducedLinearHistoryClass_add_self_ne_zero (by simpa [l] using hll)

end GaloisForLFunctions.HTGeometry
