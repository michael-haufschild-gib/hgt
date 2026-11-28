import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicFrobeniusStage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinExistence

/-! A tame stage consists of a placed number field with prescribed
residue cardinality and rational uniformizer, its inverse Artin map,
and a presentation of its residue field. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

/-- A number-field stage whose completion is unramified over the rational p-adic field. -/
structure LocalTameStage (_h : IsPlaceOver A v) (p : ℕ) [Fact p.Prime] (n : ℕ) : Type 1 where
  L : Type
  [field : Field L]
  [numberField : NumberField L]
  [baseAlgebra : Algebra K L]
  [absoluteAlgebra : Algebra L Ω]
  [tower : IsScalarTower K L Ω]
  [closure : IsAlgClosure L Ω]
  w : HeightOneSpectrum (𝓞 L)
  hw : IsPlaceOver A w
  uniformizer : (p : 𝓞 L) ∉ w.asIdeal ^ 2
  cardinality : normV w = p ^ n
  artin : Weil hw →* (w.adicCompletion L)ˣ
  artin_law : IsLocalArtin L Ω (h := hw) artin
  residue : Type
  [residueField : Field residue]
  [primeAlgebra : Algebra (ZMod p) residue]
  reduction : 𝓞 L →+* residue
  reduction_surjective : Function.Surjective reduction
  reduction_ker : RingHom.ker reduction = w.asIdeal

attribute [instance] LocalTameStage.field LocalTameStage.numberField LocalTameStage.baseAlgebra
  LocalTameStage.absoluteAlgebra LocalTameStage.tower LocalTameStage.closure
  LocalTameStage.residueField LocalTameStage.primeAlgebra

def LocalTameStage.IsInertiaResidue {h : IsPlaceOver A v} {p n : ℕ} [Fact p.Prime]
    (D : LocalTameStage h p n) (r : Ine (F := K) A →* D.residueˣ) : Prop :=
  ∀ (t : Ine (F := K) A) (s : Ine (F := D.L) A) (x : 𝓞 D.L) (z : D.residueˣ),
    t.val = s.val.restrictScalars K → D.reduction x = (z : D.residue) →
    Valued.v ((D.artin (ineIncl D.hw s) : D.w.adicCompletion D.L) -
      algebraMap D.L (D.w.adicCompletion D.L) (x : D.L)) < 1 → r t = z

/-- Use the canonical residue field at the selected place. -/
def LocalTameStage.ofQuotient {h : IsPlaceOver A v} {p n : ℕ} [Fact p.Prime]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω]
    [IsScalarTower K L Ω] [IsAlgClosure L Ω]
    {w : HeightOneSpectrum (𝓞 L)} (hw : IsPlaceOver A w)
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (hp' : (p : 𝓞 L) ∉ w.asIdeal ^ 2)
    (hc : normV w = p ^ n)
    (α : Weil hw →* (w.adicCompletion L)ˣ) (hα : IsLocalArtin L Ω α) :
    LocalTameStage h p n := by
  let κ := 𝓞 L ⧸ w.asIdeal
  letI := w.isMaximal
  letI : Field κ := Ideal.Quotient.field w.asIdeal
  let r : 𝓞 L →+* κ := Ideal.Quotient.mk w.asIdeal
  have hp0 : (p : κ) = 0 :=
    (map_natCast r p).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  letI : CharP κ p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  letI : Algebra (ZMod p) κ := (ZMod.castHom (dvd_refl p) κ).toAlgebra
  exact {
    L := L
    w := w
    hw := hw
    uniformizer := hp'
    cardinality := hc
    artin := α
    artin_law := hα
    residue := κ
    reduction := r
    reduction_surjective := Ideal.Quotient.mk_surjective
    reduction_ker := Ideal.mk_ker }

theorem exists_localTameStage (h : IsPlaceOver A v) {p n : ℕ} [Fact p.Prime]
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i) (hn : 0 < n) :
    Nonempty (LocalTameStage h p n) := by
  obtain ⟨S, -, hc, hp, hp'⟩ := exists_unramified_padicStage K Ω h i hi hn
  let L := (S : IntermediateField K Ω)
  letI : FiniteDimensional K L := S.2.1
  letI : IsAbelianGalois K L := S.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩
  let hw := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
  obtain ⟨α, hα, -⟩ := existsUnique_localArtin L Ω hw
  exact ⟨LocalTameStage.ofQuotient hw hp hp' hc α hα⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_localTameStage
