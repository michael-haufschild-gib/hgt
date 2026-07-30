import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolAncestralShiftRealization
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.DirectionalDerivationLawSpace
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Universal realization of arbitrary hyperplane phase boundaries

The conditional ancestral-shift theorem is made unconditional here.  Start with the polynomial
ring on a free countable jet grid `X_(i,n)`, prescribe the character-weighted shift on generators,
and extend that derivation to the fraction field by the quotient rule.  The coordinate grid remains
algebraically independent after embedding in the fraction field.

Consequently every central hyperplane arrangement, finite or infinite, is the exact
varying-derivation differential-dependence spectrum of a concrete observable family in a field.
No external source, existence axiom, or packet oracle remains.  The matrix-principal specialization
is finite-rank; the free-field realization itself has no finiteness assumption.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set MvPolynomial

variable {K h ι : Type*} [Field K]
  [AddCommGroup h] [Module K h]

/-- The freely generated polynomial jet algebra. -/
abbrev UniversalShiftPolynomial (K ι : Type*) [Field K] :=
  MvPolynomial (ℕ × ι) K

/-- The rational differential field of the free jet algebra. -/
abbrev UniversalShiftField (K ι : Type*) [Field K] :=
  FractionRing (UniversalShiftPolynomial K ι)

/-- The canonical injective algebra embedding of the free jet algebra into its fraction field. -/
def universalShiftEmbedding :
    UniversalShiftPolynomial K ι →ₐ[K] UniversalShiftField K ι :=
  IsScalarTower.toAlgHom K (UniversalShiftPolynomial K ι) (UniversalShiftField K ι)

theorem universalShiftEmbedding_injective :
    Function.Injective (universalShiftEmbedding (K := K) (ι := ι)) :=
  IsFractionRing.injective (UniversalShiftPolynomial K ι) (UniversalShiftField K ι)

@[simp] theorem universalShiftEmbedding_apply
    (p : UniversalShiftPolynomial K ι) :
    universalShiftEmbedding (K := K) (ι := ι) p =
      algebraMap (UniversalShiftPolynomial K ι) (UniversalShiftField K ι) p := rfl

/-- The universal ancestral coordinate `X_(i,n)` in the fraction field. -/
def universalShiftAncestor (n : ℕ) (i : ι) : UniversalShiftField K ι :=
  universalShiftEmbedding (K := K) (ι := ι) (MvPolynomial.X (n, i))

/-- The polynomial-level character-weighted shift, with values embedded in the fraction field. -/
def universalWeightedShiftPolynomialDerivation
    (characters : ι → h →ₗ[K] K) (A : h) :
    Derivation K (UniversalShiftPolynomial K ι) (UniversalShiftField K ι) :=
  MvPolynomial.mkDerivation K fun p : ℕ × ι ↦
    algebraMap (UniversalShiftPolynomial K ι) (UniversalShiftField K ι)
      (MvPolynomial.C (characters p.2 A) * MvPolynomial.X (p.1 + 1, p.2))

/-- The quotient-rule extension of the weighted shift to the universal rational field. -/
def universalWeightedShiftDerivation
    (characters : ι → h →ₗ[K] K) (A : h) :
    Derivation K (UniversalShiftField K ι) (UniversalShiftField K ι) :=
  fractionRingDerivation (universalWeightedShiftPolynomialDerivation characters A)

/-- The universal field derivation acts on ancestral coordinates by the prescribed weighted
unilateral shift. -/
theorem universalWeightedShiftDerivation_ancestor
    (characters : ι → h →ₗ[K] K) (A : h) (n : ℕ) (i : ι) :
    universalWeightedShiftDerivation characters A (universalShiftAncestor n i) =
      characters i A • universalShiftAncestor (n + 1) i := by
  rw [universalWeightedShiftDerivation, universalShiftAncestor,
    universalShiftEmbedding_apply, fractionRingDerivation_algebraMap]
  rw [universalWeightedShiftPolynomialDerivation, MvPolynomial.mkDerivation_X]
  simp [universalShiftAncestor, Algebra.smul_def,
    IsScalarTower.algebraMap_apply K (UniversalShiftPolynomial K ι)
      (UniversalShiftField K ι)]

/- The complete universal ancestral grid is algebraically independent in the fraction field. -/
theorem universalShiftAncestor_algebraicIndependent :
    AlgebraicIndependent K
      (fun p : ℕ × ι ↦ universalShiftAncestor (K := K) p.1 p.2) := by
  simpa only [universalShiftAncestor, Function.comp_apply] using!
    (MvPolynomial.algebraicIndependent_X (ℕ × ι) K).map'
      (universalShiftEmbedding_injective (K := K) (ι := ι))

/-- Iterating the universal weighted shift multiplies the `n`-th ancestral coordinate by the
`n`-th power of its law character.  No finiteness assumption is placed on the observable type. -/
theorem selectedDerivationJet_universalWeightedShift
    (characters : ι → h →ₗ[K] K) (A : h) (i : ι) :
    ∀ n, selectedDerivationJet (universalWeightedShiftDerivation characters A) n
        (universalShiftAncestor (K := K) 0 i) =
      (characters i A) ^ n • universalShiftAncestor (K := K) n i := by
  intro n
  induction n with
  | zero => simp [selectedDerivationJet]
  | succ n ih =>
      simp only [selectedDerivationJet, Function.iterate_succ_apply']
      change universalWeightedShiftDerivation characters A
          (selectedDerivationJet (universalWeightedShiftDerivation characters A) n
            (universalShiftAncestor (K := K) 0 i)) = _
      rw [ih, (universalWeightedShiftDerivation characters A).map_smul,
        universalWeightedShiftDerivation_ancestor characters A n i]
      simp [pow_succ, smul_smul, mul_comm]

/-- **Arbitrary-rank universal realization.**  For any index type, the complete selected-law jet
packet is algebraically independent exactly when no prescribed character vanishes. -/
theorem universalShift_completeJet_algebraicIndependent_iff
    (characters : ι → h →ₗ[K] K) (A : h) :
    AlgebraicIndependent K
        (fun p : ι × ℕ ↦
          selectedDerivationJet (universalWeightedShiftDerivation characters A) p.2
            (universalShiftAncestor (K := K) 0 p.1)) ↔
      ∀ i, characters i A ≠ 0 := by
  constructor
  · intro hindependent i hi
    have hne := hindependent.ne_zero (i, 1)
    apply hne
    rw [selectedDerivationJet_universalWeightedShift characters A i 1]
    simp [hi]
  · intro hall
    let swap : ι × ℕ → ℕ × ι := fun p ↦ (p.2, p.1)
    have hswap : Function.Injective swap := by
      rintro ⟨i, n⟩ ⟨j, m⟩ hij
      exact Prod.ext (congrArg Prod.snd hij) (congrArg Prod.fst hij)
    have hbase : AlgebraicIndependent K
        (fun p : ι × ℕ ↦ universalShiftAncestor (K := K) p.2 p.1) := by
      simpa [swap, Function.comp_def] using
        (universalShiftAncestor_algebraicIndependent (K := K) (ι := ι)).comp
          swap hswap
    have hscaled := AlgebraicIndependent.const_mul_coordinates hbase
      (fun p : ι × ℕ ↦ (characters p.1 A) ^ p.2)
      (fun p ↦ pow_ne_zero p.2 (hall p.1))
    simpa only [selectedDerivationJet_universalWeightedShift, Algebra.smul_def] using hscaled

/-- **Universal projective-horizon theorem.**  Every possibly infinite central hyperplane
arrangement is the exact complete-jet dependence spectrum of one concrete rational differential
field.  Finiteness is unnecessary for the realization direction. -/
theorem universalShift_completeDependenceSpectrum_eq_hyperplaneArrangement
    (characters : ι → h →ₗ[K] K) :
    {A | ¬ AlgebraicIndependent K
        (fun p : ι × ℕ ↦
          selectedDerivationJet (universalWeightedShiftDerivation characters A) p.2
            (universalShiftAncestor (K := K) 0 p.1))} =
      {A | ∃ i, characters i A = 0} := by
  classical
  ext A
  change (¬ AlgebraicIndependent K _) ↔ _
  rw [universalShift_completeJet_algebraicIndependent_iff characters A]
  push Not
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- **Universal hyperplane-spectrum theorem.**  Every finite family of linear characters is
realized, without hypotheses, as the exact differential-algebraic dependence spectrum of the
universal ancestral observables in a concrete rational differential field. -/
theorem universalShift_derivationLawDependentSet_eq_hyperplaneArrangement
    (characters : ι → h →ₗ[K] K) :
    derivationLawDependentSet (K := K)
        (universalWeightedShiftDerivation characters)
        (universalShiftAncestor (K := K) 0) =
      {A | ∃ i, characters i A = 0} := by
  apply derivationLawDependentSet_ancestralShift_eq_hyperplaneArrangement
    (universalShiftAncestor (K := K))
    (universalWeightedShiftDerivation characters)
    characters
  · exact universalWeightedShiftDerivation_ancestor characters
  · exact universalShiftAncestor_algebraicIndependent

/-- Pointwise form of the universal realization: the free observable family is
hypertranscendental for the selected law exactly off all prescribed hyperplanes. -/
theorem universalShift_derivationIndependentOver_iff
    (characters : ι → h →ₗ[K] K) (A : h) :
    DerivationIndependentOver K
        (universalWeightedShiftDerivation characters A)
        (universalShiftAncestor (K := K) 0) ↔
      ∀ i, characters i A ≠ 0 := by
  exact derivationIndependentOver_ancestralShift_iff
    (universalShiftAncestor (K := K))
    (universalWeightedShiftDerivation characters)
    characters
    (universalWeightedShiftDerivation_ancestor characters)
    universalShiftAncestor_algebraicIndependent A

end

end GaloisForLFunctions.HTGeometry
