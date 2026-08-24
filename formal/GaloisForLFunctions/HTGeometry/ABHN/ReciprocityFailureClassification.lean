import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousReciprocityHasseClassification
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSumHasseClassification

/-!
# Reciprocity-failure classification

Two finite-support local profiles fail to be congruent modulo the reciprocity kernel exactly when
their total invariants differ. This is the failure dual of the quotient classifications and turns
a global mismatch into an explicit nonzero invariant-sum obstruction.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v w

/-- Number-field finite-support profiles fail zero-sum congruence exactly when their sums differ. -/
theorem numberFieldFinsuppRatModIntSum_not_congr_hasse_iff
    (K : Type u) [Field K] [NumberField K]
    (x y : NumberFieldPlace K →₀ RatModInt) :
    x - y ∉ (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker ↔
      finsuppRatModIntSumAddHom (NumberFieldPlace K) x ≠
        finsuppRatModIntSumAddHom (NumberFieldPlace K) y :=
  not_congr (numberFieldFinsuppRatModIntSum_congr_hasse_iff K x y)

/-- `F(t)` finite-support profiles fail zero-sum congruence exactly when their sums differ. -/
theorem rationalFunctionFinsuppRatModIntSum_not_congr_hasse_iff
    (F : Type u) [Field F] [Finite F]
    (x y : RationalFunctionPlace F →₀ RatModInt) :
    x - y ∉ (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker ↔
      finsuppRatModIntSumAddHom (RationalFunctionPlace F) x ≠
        finsuppRatModIntSumAddHom (RationalFunctionPlace F) y :=
  not_congr (rationalFunctionFinsuppRatModIntSum_congr_hasse_iff F x y)

/-- Heterogeneous profiles fail reciprocity congruence exactly when their invariant sums differ. -/
theorem heterogeneousRatModIntProfile_not_congr_hasse_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (f g : Π₀ i, A i) :
    f - g ∉ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker ↔
      heterogeneousRatModIntProfileInvariantSumAddHom A inv f ≠
        heterogeneousRatModIntProfileInvariantSumAddHom A inv g :=
  not_congr (heterogeneousRatModIntProfile_congr_hasse_iff A inv f g)

/-- Place-dependent torsion profiles fail reciprocity congruence exactly when their sums differ. -/
theorem heterogeneousTorsionProfile_not_congr_hasse_iff
    {ι : Type u} [DecidableEq ι] (A : ι → Type v)
    [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i))
    (f g : Π₀ i, A i) :
    f - g ∉ (heterogeneousTorsionProfileInvariantSumAddHom A n e).ker ↔
      heterogeneousTorsionProfileInvariantSumAddHom A n e f ≠
        heterogeneousTorsionProfileInvariantSumAddHom A n e g :=
  not_congr (heterogeneousTorsionProfile_congr_hasse_iff A n e f g)

variable {ι : Type w} [DecidableEq ι]
  (K L : ι → Type)
  [(i : ι) → Field (K i)] [(i : ι) → Field (L i)]
  [(i : ι) → Algebra (K i) (L i)]
  [(i : ι) → FiniteDimensional (K i) (L i)]
  [(i : ι) → IsGalois (K i) (L i)]
  [(i : ι) → IsCyclic Gal(L i / K i)]
  (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
  (qEquiv : ∀ i,
    Additive (K i)ˣ ⧸ cyclicGaloisH2BaseNormImage (K i) (L i) ≃+ ZMod (n i))

local instance reciprocityFailureClassificationDecidableEq (i : ι) :
    DecidableEq (cyclicGaloisH2 (K i) (L i)) := Classical.decEq _

/-- Heterogeneous cyclic carry profiles fail reciprocity congruence exactly when their invariant
sums differ. -/
theorem cyclicGaloisCarryH2Heterogeneous_not_congr_hasse_iff
    (f g : Π₀ i, cyclicGaloisH2 (K i) (L i)) :
    f - g ∉
        (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).ker ↔
      cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv f ≠
        cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv g :=
  not_congr
    (cyclicGaloisCarryH2Heterogeneous_congr_hasse_iff K L n hn qEquiv f g)

end

end GaloisForLFunctions.HTGeometry.ABHN
