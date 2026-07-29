import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalDimensionCascadeLaw
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Exact bridge from spectral-character relations to observer-time dimension

For a finite spectrum, an integer projective character has the same
finite-order relation depth whether it is viewed in the integral character
lattice or in the rational vector space used to measure temporal dimension.
Thus the character wall crossings and the dimension cascade concern one
filtration, not two analogous constructions.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Scalar extension of an integer projective character to a rational one. -/
def projectiveCharacterToRational
    {I : Type*} [Fintype I]
    (k : ProjectiveCharacter I) :
    ProjectiveRationalCharacter I :=
  ⟨fun i => (k.1 i : ℚ), by
    change ∑ i, (k.1 i : ℚ) = 0
    have hk : k.1.sum (fun _ m => m) = 0 := k.2
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hk
    exact_mod_cast hk⟩

/-- Jet evaluation commutes with scalar extension from integral to rational
projective characters. -/
theorem projectiveJetMap_toRational_apply
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ)
    (k : ProjectiveCharacter I) (n : Fin r) :
    projectiveJetMap jet r (projectiveCharacterToRational k) n =
      projectiveSpectralRelationJet jet n k := by
  classical
  change
    (∑ i, ((k.1 i : ℚ) : ℂ) * jet n i) =
      k.1.sum fun i m => (m : ℂ) * jet n i
  rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  norm_num

/-- **Integral/rational filtration identity.** An integer phase relation
persists to order `r` exactly when its rational scalar extension belongs to
the kernel whose codimension is observer-time dimension. -/
theorem mem_rationalConstraint_toRational_iff
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ)
    (k : ProjectiveCharacter I) :
    projectiveCharacterToRational k ∈
        rationalSpectralConstraintSpace jet r ↔
      k ∈ spectralConstraintFiltration jet r := by
  constructor
  · intro hk n hn
    let m : Fin r := ⟨n, hn⟩
    have hm := congrFun hk m
    rwa [projectiveJetMap_toRational_apply] at hm
  · intro hk
    change projectiveJetMap jet r (projectiveCharacterToRational k) = 0
    ext n
    rw [projectiveJetMap_toRational_apply]
    exact hk n n.isLt

/-- Every rational projective character becomes an integral projective
character after multiplication by one nonzero integer. -/
theorem exists_integer_projective_multiple
    {I : Type*} [Fintype I]
    (q : ProjectiveRationalCharacter I) :
    ∃ b : ℤ, b ≠ 0 ∧
      ∃ k : ProjectiveCharacter I,
        projectiveCharacterToRational k = b • q := by
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors ℤ) q.1
  choose z hz using fun i => hb i
  have hb0 : b.val ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hz' : ∀ i, (z i : ℚ) = (b.val : ℚ) * q.1 i := by
    intro i
    simpa [IsLocalization.IsInteger, Algebra.smul_def] using hz i
  have hqsum : ∑ i, q.1 i = 0 := q.2
  have hzsum : ∑ i, z i = 0 := by
    apply_mod_cast
      (show (∑ i, (z i : ℚ)) = 0 by
        calc
          (∑ i, (z i : ℚ)) =
              ∑ i, (b.val : ℚ) * q.1 i := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hz' i
          _ = (b.val : ℚ) * ∑ i, q.1 i := by
                rw [Finset.mul_sum]
          _ = 0 := by rw [hqsum, mul_zero])
  let k₀ : I →₀ ℤ := Finsupp.equivFunOnFinite.symm z
  have hk₀ : integerCharacterCharge I k₀ = 0 := by
    change k₀.sum (fun _ m => m) = 0
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa [k₀] using hzsum
  let k : ProjectiveCharacter I := ⟨k₀, hk₀⟩
  refine ⟨b.val, hb0, k, ?_⟩
  ext i
  change ((k₀ i : ℤ) : ℚ) = (b.val : ℚ) * q.1 i
  simpa [k₀] using hz' i

/-- **Integral span theorem.** The rational relation kernel is exactly the
rational span of persistent integral phase characters. This identifies the
rank-nullity dimension cascade with the character filtration used by
recurrence theory. -/
theorem rationalConstraint_eq_span_integerConstraints
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ) :
    rationalSpectralConstraintSpace jet r =
      Submodule.span ℚ
        (projectiveCharacterToRational ''
          (spectralConstraintFiltration jet r : Set
            (ProjectiveCharacter I))) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨b, hb, k, hk⟩ := exists_integer_projective_multiple q
    have hkconstraint :
        k ∈ spectralConstraintFiltration jet r := by
      rw [← mem_rationalConstraint_toRational_iff]
      rw [hk]
      exact (rationalSpectralConstraintSpace jet r).smul_mem b hq
    have hgenerator :
        projectiveCharacterToRational k ∈
          projectiveCharacterToRational ''
            (spectralConstraintFiltration jet r : Set
              (ProjectiveCharacter I)) :=
      ⟨k, hkconstraint, rfl⟩
    have hspan :
        projectiveCharacterToRational k ∈
          Submodule.span ℚ
            (projectiveCharacterToRational ''
              (spectralConstraintFiltration jet r : Set
                (ProjectiveCharacter I))) :=
      Submodule.subset_span hgenerator
    rw [hk] at hspan
    have hbinv : (b : ℚ)⁻¹ • ((b : ℚ) • q) = q := by
      rw [← mul_smul]
      simp [hb]
    rw [← hbinv]
    exact Submodule.smul_mem _ _ hspan
  · apply Submodule.span_le.mpr
    rintro q ⟨k, hk, rfl⟩
    exact (mem_rationalConstraint_toRational_iff jet r k).2 hk

end

end GaloisForLFunctions.HTGeometry
