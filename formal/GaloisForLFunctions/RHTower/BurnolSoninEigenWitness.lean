import GaloisForLFunctions.RHTower.BurnolSoninReflectedEvaluation
import GaloisForLFunctions.RHTower.BurnolSoninApertureMonotone

/-!
# Eigen-reduction of the Sonine witness problem

The cosine transform is an involution of the extended Sonine space, so every Sonine vector splits
into a self-dual and an anti-self-dual part, both still Sonine vectors at the same aperture.  The
completed Mellin evaluation is additive there, so a vector with nonvanishing evaluation forces one
of its two eigen-parts to have nonvanishing evaluation.

Consequently the outstanding nonvanishing input needs only an eigenvector witness: a single vector
`g` with `F g = g` or `F g = -g`, constant on the aperture head, and `M g(w) /= 0`.  For such a
vector the constant-head condition on the cosine transform is automatic, so only one of the two
defining Sonine conditions has to be verified.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The self-dual part of a Sonine vector. -/
def soninSelfDualPart {a : ℝ} (f : soninExtendedSpace a) : soninExtendedSpace a :=
  f + burnolExtendedSoninCosine a f

/-- The anti-self-dual part of a Sonine vector. -/
def soninAntiSelfDualPart {a : ℝ} (f : soninExtendedSpace a) : soninExtendedSpace a :=
  f - burnolExtendedSoninCosine a f

theorem soninSelfDualPart_isSelfDual {a : ℝ} (f : soninExtendedSpace a) :
    burnolExtendedSoninCosine a (soninSelfDualPart f) = soninSelfDualPart f := by
  rw [soninSelfDualPart, map_add, burnolExtendedSoninCosine_involutive]
  abel

theorem soninAntiSelfDualPart_isAntiSelfDual {a : ℝ} (f : soninExtendedSpace a) :
    burnolExtendedSoninCosine a (soninAntiSelfDualPart f) = -soninAntiSelfDualPart f := by
  rw [soninAntiSelfDualPart, (burnolExtendedSoninCosine a).map_sub,
    burnolExtendedSoninCosine_involutive]
  abel

theorem soninSelfDualPart_add_antiSelfDualPart {a : ℝ} (f : soninExtendedSpace a) :
    soninSelfDualPart f + soninAntiSelfDualPart f = (2 : ℂ) • f := by
  rw [soninSelfDualPart, soninAntiSelfDualPart]
  module

/-- **Eigen-reduction of the witness problem.**  A Sonine vector with nonvanishing completed Mellin
evaluation forces an eigenvector of the cosine involution with nonvanishing evaluation. -/
theorem exists_cosine_eigen_witness
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a)
    (f : soninExtendedSpace a)
    (hf : soninMellinEvaluation w
      (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) ≠ 0) :
    ∃ g : soninExtendedSpace a,
      (burnolExtendedSoninCosine a g = g ∨ burnolExtendedSoninCosine a g = -g) ∧
        soninMellinEvaluation w
          (((g : soninExtendedSpace a) : evenSubspace) : SoninL2) ≠ 0 := by
  have hsum := soninMellinEvaluation_add_extendedSonin hlo hhi ha
    (soninSelfDualPart f) (soninAntiSelfDualPart f)
  rw [soninSelfDualPart_add_antiSelfDualPart,
    soninMellinEvaluation_smul_extendedSonin] at hsum
  by_cases hplus : soninMellinEvaluation w
      (((soninSelfDualPart f : soninExtendedSpace a) : evenSubspace) : SoninL2) = 0
  · refine ⟨soninAntiSelfDualPart f, Or.inr (soninAntiSelfDualPart_isAntiSelfDual f), ?_⟩
    rw [hplus, zero_add] at hsum
    rw [← hsum]
    exact fun h => hf (by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      exact (mul_eq_zero.mp h).resolve_left h2)
  · exact ⟨soninSelfDualPart f, Or.inl (soninSelfDualPart_isSelfDual f), hplus⟩

/-- **A single eigenvector witness settles the nonvanishing input.**  If some eigenvector of the
cosine involution at aperture `b` has nonvanishing completed Mellin evaluation, then the evaluation
vector is nonzero at every aperture `a ≤ b`. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_eigen_witness
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (g : soninExtendedSpace b)
    (_hdual : burnolExtendedSoninCosine b g = g ∨ burnolExtendedSoninCosine b g = -g)
    (hg : soninMellinEvaluation w
      (((g : soninExtendedSpace b) : evenSubspace) : SoninL2) ≠ 0) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
  burnolExtendedSoninEvaluationVector_ne_zero_of_witness hlo hhi ha hb hab g hg

/-- For an eigenvector of the cosine involution the second Sonine condition is automatic: the
constant head of the cosine transform is `±` the constant head of the vector. -/
theorem soninHeadConstant_of_cosine_eigen {a : ℝ} {f : evenSubspace}
    (hdual : soninCosineUnitary f = f ∨ soninCosineUnitary f = -f)
    (hhead : SoninHeadConstant a ((f : SoninL2) : ℝ → ℂ)) :
    SoninHeadConstant a (((soninCosineUnitary f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  rcases hdual with h | h
  · rw [h]
    exact hhead
  · rw [h]
    obtain ⟨c, hc⟩ := hhead
    refine ⟨-c, ?_⟩
    have hneg : ((((-f : evenSubspace) : SoninL2)) : ℝ → ℂ) =ᵐ[volume]
        -(((f : SoninL2) : ℝ → ℂ)) := by
      simpa using Lp.coeFn_neg ((f : SoninL2))
    filter_upwards [hc, ae_restrict_of_ae hneg] with t h1 h2
    rw [h2, Pi.neg_apply, h1]

/-- **The eigen-condition halves the Sonine conditions.**  An even eigenvector of the cosine
involution with constant aperture head lies in the extended Sonine space. -/
theorem mem_soninExtendedSpace_of_cosine_eigen {a : ℝ} {f : evenSubspace}
    (hdual : soninCosineUnitary f = f ∨ soninCosineUnitary f = -f)
    (hhead : SoninHeadConstant a ((f : SoninL2) : ℝ → ℂ)) :
    f ∈ soninExtendedSpace a :=
  (mem_soninExtendedSpace).mpr ⟨hhead, soninHeadConstant_of_cosine_eigen hdual hhead⟩


/-! ## The eigen-condition is free -/

theorem soninCosineUnitary_add_self (f : evenSubspace) :
    soninCosineUnitary (f + soninCosineUnitary f) = f + soninCosineUnitary f := by
  rw [map_add, soninCosineUnitary_involutive]
  abel

theorem soninCosineUnitary_sub_self (f : evenSubspace) :
    soninCosineUnitary (f - soninCosineUnitary f) = -(f - soninCosineUnitary f) := by
  rw [soninCosineUnitary.map_sub, soninCosineUnitary_involutive]
  abel

/-- **Symmetrization lands in the Sonine space.**  Every symmetrized even vector is a cosine
eigenvector, so only the constant-head condition has to be checked. -/
theorem mem_soninExtendedSpace_symmetrized {a : ℝ} (f : evenSubspace)
    (hhead : SoninHeadConstant a
      (((f + soninCosineUnitary f : evenSubspace) : SoninL2) : ℝ → ℂ)) :
    f + soninCosineUnitary f ∈ soninExtendedSpace a :=
  mem_soninExtendedSpace_of_cosine_eigen (Or.inl (soninCosineUnitary_add_self f)) hhead

theorem mem_soninExtendedSpace_antisymmetrized {a : ℝ} (f : evenSubspace)
    (hhead : SoninHeadConstant a
      (((f - soninCosineUnitary f : evenSubspace) : SoninL2) : ℝ → ℂ)) :
    f - soninCosineUnitary f ∈ soninExtendedSpace a :=
  mem_soninExtendedSpace_of_cosine_eigen (Or.inr (soninCosineUnitary_sub_self f)) hhead

/-- **The witness problem in reduced form.**  A single even vector whose symmetrization is constant
on one aperture head and has nonvanishing completed Mellin evaluation settles the nonvanishing input
at every smaller aperture.  Neither the cosine-head condition nor the eigen-condition has to be
verified separately. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_symmetrized_witness
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (u : evenSubspace)
    (hhead : SoninHeadConstant b
      (((u + soninCosineUnitary u : evenSubspace) : SoninL2) : ℝ → ℂ))
    (hval : soninMellinEvaluation w
      (((u + soninCosineUnitary u : evenSubspace) : SoninL2)) ≠ 0) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
  burnolExtendedSoninEvaluationVector_ne_zero_of_witness hlo hhi ha hb hab
    ⟨u + soninCosineUnitary u, mem_soninExtendedSpace_symmetrized u hhead⟩ hval

end RHTower
