import GaloisForLFunctions.HTGeometry.PowerNormalizationProfieldKreinBlindness
import GaloisForLFunctions.HTGeometry.EvenCanonicalProductLaguerrePolya
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients

/-!
# Laguerre–Pólya and Jensen blindness of a maximal-HT power pro-field

One functional-equation-even maximal-HT power pro-field has a Laguerre–Pólya representative, whose
Jensen polynomials are all hyperbolic, and, for every `k ≥ 1`, a representative carrying exactly `k`
off-real zero quartets, which is therefore not Laguerre–Pólya and has a nonhyperbolic Jensen
polynomial.  Every algebraic power-translation level, the complete divisibility tower, its
intersection, and maximal translation differential independence are identical along the family.
-/

open Complex Filter Polynomial
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance] testUpperDomain testUpperAlgebra testRatDiff testUpperDiff
  testUpperDiffAlg testUpperCharZero

/-- The even surgery representative carrying `k` off-real quartets. -/
def kreinEvenSurgeryFunction (θ : BoundedRealSequence) (k : ℕ) : ℂ → ℂ :=
  movingEvenCanonicalSurgeryProduct θ (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
    (evenKreinCenters k)

theorem kreinEvenSurgeryFunction_zero_eq (θ : BoundedRealSequence) :
    kreinEvenSurgeryFunction θ 0 = movingEvenCanonicalProduct θ := by
  funext z
  have h1 : (@evenSurgeryAIdx 0) = fun i : Fin 0 => Fin.elim0 i := funext fun i => Fin.elim0 i
  have h2 : (@evenSurgeryBIdx 0) = fun i : Fin 0 => Fin.elim0 i := funext fun i => Fin.elim0 i
  have h3 : evenKreinCenters 0 = fun i : Fin 0 => Fin.elim0 i := funext fun i => Fin.elim0 i
  rw [kreinEvenSurgeryFunction, h1, h2, h3, movingEvenCanonicalSurgeryProduct_empty]

theorem laguerrePolya_kreinEvenSurgeryFunction_zero (θ : BoundedRealSequence) :
    LaguerrePolya (kreinEvenSurgeryFunction θ 0) := by
  rw [kreinEvenSurgeryFunction_zero_eq]
  exact laguerrePolya_movingEvenCanonicalProduct θ

/-- The origin is never a zero of a surgery representative. -/
theorem kreinEvenSurgeryFunction_zero_ne_zero (θ : BoundedRealSequence) (k : ℕ)
    (hzero : ∀ z, kreinEvenSurgeryFunction θ k z = 0 ↔
      (∃ n : ℕ, n ∉ movingCanonicalSurgerySelectedIndices
            (@evenSurgeryAIdx k) (@evenSurgeryBIdx k) ∧
          (z = (movingCanonicalZero θ n : ℂ) ∨ z = -(movingCanonicalZero θ n : ℂ))) ∨
        ∃ i : Fin k, z = evenKreinCenters k i ∨ z = star (evenKreinCenters k i) ∨
          z = -evenKreinCenters k i ∨ z = -star (evenKreinCenters k i)) :
    kreinEvenSurgeryFunction θ k 0 ≠ 0 := by
  intro h0
  rcases (hzero 0).1 h0 with ⟨n, _, hn⟩ | ⟨i, hi⟩
  · have hpos := movingCanonicalZero_pos θ n
    rcases hn with hn | hn
    · have : (movingCanonicalZero θ n : ℝ) = 0 := by
        have := congrArg Complex.re hn
        simpa using this.symm
      linarith
    · have : (movingCanonicalZero θ n : ℝ) = 0 := by
        have := congrArg Complex.re hn
        simp at this
        linarith
      linarith
  · have him := evenKreinCenters_im_pos k i
    rcases hi with hi | hi | hi | hi
    · have := congrArg Complex.im hi
      simp at this
      linarith
    · have := congrArg Complex.im hi
      simp at this
      linarith
    · have := congrArg Complex.im hi
      simp at this
      linarith
    · have := congrArg Complex.im hi
      simp at this
      linarith

/-- **Laguerre–Pólya and Jensen blindness of one maximal-HT power pro-field.** -/
theorem exists_powerNormalizationProfield_laguerrePolyaJensenBlindness
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    ∃ θ : BoundedRealSequence,
      LaguerrePolya (kreinEvenSurgeryFunction θ 0) ∧
      (∀ d, (jensenPoly (realTaylorCoeff (kreinEvenSurgeryFunction θ 0)) d).Splits) ∧
      ∀ k : ℕ,
        AnalyticOnNhd ℂ (kreinEvenSurgeryFunction θ k) Set.univ ∧
        (∀ z, kreinEvenSurgeryFunction θ k (-z) = kreinEvenSurgeryFunction θ k z) ∧
        (∀ z, kreinEvenSurgeryFunction θ k (conj z) = conj (kreinEvenSurgeryFunction θ k z)) ∧
        OrderOneEnvelope (kreinEvenSurgeryFunction θ k) ∧
        (∀ z, kreinEvenSurgeryFunction θ k z = 0 ↔
          (∃ n : ℕ, n ∉ movingCanonicalSurgerySelectedIndices
                (@evenSurgeryAIdx k) (@evenSurgeryBIdx k) ∧
              (z = (movingCanonicalZero θ n : ℂ) ∨ z = -(movingCanonicalZero θ n : ℂ))) ∨
            ∃ i : Fin k, z = evenKreinCenters k i ∨ z = star (evenKreinCenters k i) ∨
              z = -evenKreinCenters k i ∨ z = -star (evenKreinCenters k i)) ∧
        EvenSurgeryPoleSeparated (evenKreinCenters k) ∧
        (∀ i : Fin k, 0 < (evenKreinCenters k i).im) ∧
        (∀ N, evenFiniteKreinPowerTranslationField θ k N =
          evenBasePowerTranslationField θ N) ∧
        ({z : upperEndMeroField | ∀ n,
            z ∈ evenFiniteKreinPowerTranslationField θ k (D n)} =
          (evenFiniteKreinLogResidue θ k : Set upperEndMeroField)) ∧
        ({z : upperEndMeroField | ∀ n,
            z ∈ evenFiniteKreinPowerTranslationField θ k (D n)} =
          {z : upperEndMeroField | ∀ n, z ∈ evenBasePowerTranslationField θ (D n)}) ∧
        DifferentialIndependent (RatFunc ℂ)
          (fun h : ℂ => Differential.logDeriv
            (evenSurgeryProductTranslateFamily θ
              (@evenSurgeryAIdx k) (@evenSurgeryBIdx k) (evenKreinCenters k) h)) ∧
        (1 ≤ k →
          ¬ LaguerrePolya (kreinEvenSurgeryFunction θ k) ∧
          ∃ d, ¬ (jensenPoly (realTaylorCoeff (kreinEvenSurgeryFunction θ k)) d).Splits) := by
  obtain ⟨θ, hθ⟩ := exists_powerNormalizationProfield_allEvenKreinIndex D hD0 hdiv hlt
  refine ⟨θ, laguerrePolya_kreinEvenSurgeryFunction_zero θ, ?_, fun k => ?_⟩
  · intro d
    refine splits_jensenPoly_realTaylorCoeff (laguerrePolya_kreinEvenSurgeryFunction_zero θ) ?_ d
    exact (movingEvenCanonicalSurgeryProduct_exactOrderOneDivisor θ
      (@evenSurgeryAIdx 0) (@evenSurgeryBIdx 0) (evenKreinCenters 0)
      (evenKreinCenters_im_pos 0) (evenKreinCenters_separated 0)).2.2.1
  · have hk := hθ k
    have hpackage := movingEvenCanonicalSurgeryProduct_exactOrderOneDivisor θ
      (@evenSurgeryAIdx k) (@evenSurgeryBIdx k) (evenKreinCenters k)
      (evenKreinCenters_im_pos k) (evenKreinCenters_separated k)
    have hzero := hpackage.2.2.2.2.2.1
    refine ⟨hpackage.1, hpackage.2.1, hpackage.2.2.1, hpackage.2.2.2.1, hzero,
      evenKreinCenters_separated k, evenKreinCenters_im_pos k,
      hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2, ?_⟩
    intro hk1
    have hne : kreinEvenSurgeryFunction θ k 0 ≠ 0 :=
      kreinEvenSurgeryFunction_zero_ne_zero θ k hzero
    have hi : (⟨0, by omega⟩ : Fin k) = ⟨0, by omega⟩ := rfl
    set i : Fin k := ⟨0, by omega⟩ with hidef
    have hzi : kreinEvenSurgeryFunction θ k (evenKreinCenters k i) = 0 :=
      (hzero _).2 (Or.inr ⟨i, Or.inl rfl⟩)
    have him : (evenKreinCenters k i).im ≠ 0 := ne_of_gt (evenKreinCenters_im_pos k i)
    have hdiff : Differentiable ℂ (kreinEvenSurgeryFunction θ k) :=
      fun z => (hpackage.1 z (Set.mem_univ z)).differentiableAt
    refine ⟨fun hLP => him (im_eq_zero_of_laguerrePolya hLP hne hzi), ?_⟩
    exact exists_jensenPoly_not_splits_of_nonreal_zero hdiff hpackage.2.2.1 hne hzi him

end

end GaloisForLFunctions.HTGeometry
