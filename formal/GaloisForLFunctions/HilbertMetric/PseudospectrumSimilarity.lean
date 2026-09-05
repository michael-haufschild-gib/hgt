import GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Pseudospectra under adjoints and bounded similarities

This module formalizes the reusable bounded-operator mechanisms surrounding equations (6)--(8)
and Proposition 2 of Krejčiřík--Siegl--Tater--Viola, *Pseudospectra in non-Hermitian quantum
mechanics*, arXiv:1402.1082.

The norm-resolvent pseudospectrum includes the spectrum explicitly because mathlib's total
`resolvent` is zero on spectral points.  Positive tolerances are bundled, so the strict reciprocal
threshold and every condition-number rescaling remain premise-free at call sites.
-/

open Set
open scoped MatrixOrder

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Strictly positive pseudospectral tolerance. -/
abbrev PseudospectralScale := { ε : ℝ // 0 < ε }

namespace PseudospectralScale

instance : Coe PseudospectralScale ℝ := ⟨Subtype.val⟩

@[simp] theorem coe_pos (ε : PseudospectralScale) : 0 < (ε : ℝ) := ε.property

end PseudospectralScale

/-- Norm-resolvent definition of the open epsilon-pseudospectrum. -/
def normResolventPseudospectrum
    (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] (ε : PseudospectralScale) (a : A) : Set 𝕜 :=
  spectrum 𝕜 a ∪ {z | (ε : ℝ)⁻¹ < ‖resolvent a z‖}

/-- Condition number of an invertible similarity element. -/
def similarityConditionNumber
    {A : Type*} [NormedRing A] (u : Aˣ) : ℝ :=
  ‖(u : A)‖ * ‖(↑(u⁻¹) : A)‖

theorem similarityConditionNumber_pos
    {A : Type*} [NormedRing A] [Nontrivial A] (u : Aˣ) :
    0 < similarityConditionNumber u := by
  exact mul_pos (norm_pos_iff.mpr u.ne_zero)
    (norm_pos_iff.mpr (show (↑(u⁻¹) : A) ≠ 0 from u⁻¹.ne_zero))

/-- Enlarge a positive pseudospectral scale by the similarity condition number. -/
def PseudospectralScale.mulConditionNumber
    {A : Type*} [NormedRing A] [Nontrivial A]
    (ε : PseudospectralScale) (u : Aˣ) : PseudospectralScale :=
  ⟨(ε : ℝ) * similarityConditionNumber u,
    mul_pos ε.property (similarityConditionNumber_pos u)⟩

/-- Shrink a positive pseudospectral scale by the similarity condition number. -/
def PseudospectralScale.divConditionNumber
    {A : Type*} [NormedRing A] [Nontrivial A]
    (ε : PseudospectralScale) (u : Aˣ) : PseudospectralScale :=
  ⟨(ε : ℝ) / similarityConditionNumber u,
    div_pos ε.property (similarityConditionNumber_pos u)⟩

/-- Exact transport of the total resolvent through conjugation by a unit. -/
theorem resolvent_units_conjugate
    {𝕜 A : Type*} [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A]
    (u : Aˣ) (a : A) (z : 𝕜) :
    resolvent ((u : A) * a * (↑(u⁻¹) : A)) z =
      (u : A) * resolvent a z * (↑(u⁻¹) : A) := by
  have hscalar : algebraMap 𝕜 A z - (u : A) * a * (↑(u⁻¹) : A) =
      (u : A) * (algebraMap 𝕜 A z - a) * (↑(u⁻¹) : A) := by
    simp [mul_sub, sub_mul, Algebra.commutes, mul_assoc]
  rw [resolvent, resolvent, hscalar]
  rw [show (u : A) * (algebraMap 𝕜 A z - a) * (↑(u⁻¹) : A) =
      (u : A) * ((algebraMap 𝕜 A z - a) * (↑(u⁻¹) : A)) by
    simp [mul_assoc]]
  rw [Ring.inverse_mul (Or.inl u.isUnit)]
  rw [Ring.inverse_mul (Or.inr u⁻¹.isUnit)]
  simp [mul_assoc]

/-- Forward condition-number bound for the conjugated resolvent. -/
theorem norm_resolvent_units_conjugate_le
    {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (u : Aˣ) (a : A) (z : 𝕜) :
    ‖resolvent ((u : A) * a * (↑(u⁻¹) : A)) z‖ ≤
      similarityConditionNumber u * ‖resolvent a z‖ := by
  rw [resolvent_units_conjugate]
  calc
    ‖(u : A) * resolvent a z * (↑(u⁻¹) : A)‖ ≤
        ‖(u : A)‖ * ‖resolvent a z‖ * ‖(↑(u⁻¹) : A)‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = similarityConditionNumber u * ‖resolvent a z‖ := by
      rw [similarityConditionNumber]
      ring

/-- Reverse condition-number bound, obtained by conjugating with the inverse unit. -/
theorem norm_resolvent_le_conditionNumber_mul_conjugate
    {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (u : Aˣ) (a : A) (z : 𝕜) :
    ‖resolvent a z‖ ≤
      similarityConditionNumber u *
        ‖resolvent ((u : A) * a * (↑(u⁻¹) : A)) z‖ := by
  have h := norm_resolvent_units_conjugate_le (u := u⁻¹)
    (a := (u : A) * a * (↑(u⁻¹) : A)) z
  simpa [similarityConditionNumber, mul_assoc, mul_comm] using h

/-- Equation (7): the adjoint pseudospectrum is the scalar-star mirror image. -/
theorem star_mem_normResolventPseudospectrum_iff
    {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [InvolutiveStar 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]
    (ε : PseudospectralScale) (a : A) (z : 𝕜) :
    star z ∈ normResolventPseudospectrum 𝕜 ε (star a) ↔
      z ∈ normResolventPseudospectrum 𝕜 ε a := by
  have hspectrum : star z ∈ spectrum 𝕜 (star a) ↔ z ∈ spectrum 𝕜 a := by
    simpa only [spectrum, Set.mem_compl_iff, not_iff_not, star_star] using
      (spectrum.star_mem_resolventSet_iff (r := z) (a := star a))
  have hresolvent : resolvent (star a) (star z) = star (resolvent a z) := by
    unfold resolvent
    rw [← Ring.inverse_star]
    congr 1
    simp only [Algebra.algebraMap_eq_smul_one, star_sub, star_smul, star_one]
  simp only [normResolventPseudospectrum, Set.mem_union, Set.mem_setOf_eq,
    hspectrum, hresolvent, norm_star]

/-- Equation (6), useful direction: normalized pseudomode implies pseudospectral membership. -/
theorem mem_normResolventPseudospectrum_of_pseudomode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (ε : PseudospectralScale) (T : E →L[ℂ] E) (z : ℂ)
    {v : E} (hv : ‖v‖ = 1) (hres : ‖T v - z • v‖ < (ε : ℝ)) :
    z ∈ normResolventPseudospectrum ℂ ε T := by
  by_cases hz : z ∈ spectrum ℂ T
  · exact Or.inl hz
  · right
    have hunit : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - T) :=
      spectrum.notMem_iff.mp hz
    have hinv := Ring.inverse_mul_cancel
      (algebraMap ℂ (E →L[ℂ] E) z - T) hunit
    have happ := congrArg (fun S : E →L[ℂ] E => S v) hinv
    have hvfactor : v = resolvent T z (z • v - T v) := by
      simpa [resolvent, sub_apply, smul_apply] using happ.symm
    have hbound : 1 ≤ ‖resolvent T z‖ * ‖T v - z • v‖ := by
      calc
        1 = ‖v‖ := hv.symm
        _ = ‖resolvent T z (z • v - T v)‖ := congrArg norm hvfactor
        _ ≤ ‖resolvent T z‖ * ‖z • v - T v‖ := (resolvent T z).le_opNorm _
        _ = ‖resolvent T z‖ * ‖T v - z • v‖ := by rw [norm_sub_rev]
    have hRpos : 0 < ‖resolvent T z‖ := by
      rw [norm_pos_iff]
      intro hzero
      simp [hzero] at hbound
      exact (not_lt_of_ge hbound) zero_lt_one
    have hstrict : 1 < ‖resolvent T z‖ * (ε : ℝ) :=
      hbound.trans_lt (mul_lt_mul_of_pos_left hres hRpos)
    exact (inv_lt_iff_one_lt_mul₀ ε.property).2 (by simpa [mul_comm] using hstrict)

/-- Equation (8): exact spectrum preservation and the two condition-number inclusions. -/
theorem normResolventPseudospectrum_similarity_sandwich
    {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [Nontrivial A] (ε : PseudospectralScale) (u : Aˣ) (a : A) :
    normResolventPseudospectrum 𝕜 (ε.divConditionNumber u) a ⊆
        normResolventPseudospectrum 𝕜 ε
          ((u : A) * a * (↑(u⁻¹) : A)) ∧
      normResolventPseudospectrum 𝕜 ε
          ((u : A) * a * (↑(u⁻¹) : A)) ⊆
        normResolventPseudospectrum 𝕜 (ε.mulConditionNumber u) a := by
  constructor
  · intro z hz
    rcases hz with hz | hz
    · left
      simpa using (show
        spectrum 𝕜 ((u : A) * a * (↑(u⁻¹) : A)) = spectrum 𝕜 a from
          spectrum.units_conjugate).symm ▸ hz
    · right
      have hnorm := norm_resolvent_le_conditionNumber_mul_conjugate u a z
      have hk := similarityConditionNumber_pos u
      dsimp [PseudospectralScale.divConditionNumber] at hz
      rw [inv_div] at hz
      have hmain : similarityConditionNumber u * (ε : ℝ)⁻¹ <
          similarityConditionNumber u *
            ‖resolvent ((u : A) * a * (↑(u⁻¹) : A)) z‖ :=
        lt_of_lt_of_le hz hnorm
      apply lt_of_mul_lt_mul_left _ hk.le
      simpa [mul_comm] using hmain
  · intro z hz
    rcases hz with hz | hz
    · left
      simpa using (show
        spectrum 𝕜 ((u : A) * a * (↑(u⁻¹) : A)) = spectrum 𝕜 a from
          spectrum.units_conjugate) ▸ hz
    · right
      have hnorm := norm_resolvent_units_conjugate_le u a z
      have hk := similarityConditionNumber_pos u
      dsimp [PseudospectralScale.mulConditionNumber]
      have hmain : (ε : ℝ)⁻¹ < similarityConditionNumber u * ‖resolvent a z‖ :=
        lt_of_lt_of_le hz hnorm
      apply lt_of_mul_lt_mul_left _ hk.le
      rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
      exact hmain

/-- Proposition 2 metric identity for every positive-square-root similarity. -/
theorem matrixSqrtSimilarity_metric_relation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef)
    (D : Matrix ι ι ℝ) (hD : D.transpose = D) :
    M⁻¹ * matrixSqrtSimilarity M D =
      (matrixSqrtSimilarity M D).transpose * M⁻¹ := by
  let R := CFC.sqrt M
  let Ri := (CFC.sqrt M)⁻¹
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hleft : Ri * R = 1 := Matrix.inv_mul_of_invertible R
  have hright : R * Ri = 1 := Matrix.mul_inv_of_invertible R
  rw [matrixSqrtSimilarity_transpose M D hD,
    matrix_inv_eq_sqrt_inv_mul M hM]
  change (Ri * Ri) * (R * D * Ri) = (Ri * D * R) * (Ri * Ri)
  calc
    (Ri * Ri) * (R * D * Ri) = Ri * (Ri * R) * D * Ri := by noncomm_ring
    _ = Ri * D * Ri := by rw [hleft]; simp
    _ = Ri * D * (R * Ri) * Ri := by rw [hright]; simp
    _ = (Ri * D * R) * (Ri * Ri) := by noncomm_ring

/-- Proposition 2 in a star algebra: a self-adjoint unit conjugate supplies its metric. -/
theorem units_conjugate_metric_relation
    {A : Type*} [Ring A] [StarRing A]
    (u : Aˣ) (a : A)
    (hself : IsSelfAdjoint ((u : A) * a * (↑(u⁻¹) : A))) :
    star a * (star (u : A) * (u : A)) =
      (star (u : A) * (u : A)) * a := by
  have hstarCancel : star (u : A) * star (↑(u⁻¹) : A) = 1 := by
    rw [← star_mul]
    simp
  have hcancel : (↑(u⁻¹) : A) * (u : A) = 1 := by simp
  calc
    star a * (star (u : A) * (u : A)) =
        (star (u : A) * star (↑(u⁻¹) : A)) *
          star a * (star (u : A) * (u : A)) := by rw [hstarCancel]; simp
    _ = star (u : A) *
        star ((u : A) * a * (↑(u⁻¹) : A)) * (u : A) := by
      simp only [star_mul]
      noncomm_ring
    _ = star (u : A) *
        ((u : A) * a * (↑(u⁻¹) : A)) * (u : A) := by rw [hself.star_eq]
    _ = (star (u : A) * (u : A)) * a := by
      rw [show star (u : A) * ((u : A) * a * (↑(u⁻¹) : A)) * (u : A) =
        (star (u : A) * (u : A)) * a * ((↑(u⁻¹) : A) * (u : A)) by
          noncomm_ring, hcancel]
      simp

end

end GaloisForLFunctions.HilbertMetric
