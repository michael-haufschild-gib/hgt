import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplementaryExteriorCoordinate
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularFormLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormDenominatorLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedTraceDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct

/-! The top wedge tests regularity of a rational exterior form in the
complementary degree. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology KaehlerDifferential
open scoped nonZeroDivisors GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k E : Type} [Field k] [Field E] [Algebra k E]

/-- Regular chart forms viewed inside the rational exterior degree. -/
def regularExteriorLattice (B : Subalgebra k E) (p : ℕ) :
    Submodule k (ExteriorDifferentials k E p) :=
  (omB k E B p).comap ((⋀[E]^p Ω[E⁄k]).subtype.restrictScalars k)

private theorem mem_formRange_of_local_wedge_test
    {C : Type} [CommRing C] [IsDomain C] [Algebra k C] [Algebra C E] [IsScalarTower k C E]
    [IsFractionRing C E] {p q : ℕ} (b : Module.Basis (Fin (p + q)) C Ω[C⁄k])
    (y : ExteriorDifferentials k E q)
    (htest : ∀ a : ExteriorDifferentials k C p, ∃ z : ExteriorDifferentials k C (p + q),
      (algebraFormPullback k C E (p + q) z : DR k E) =
        (algebraFormPullback k C E p a : DR k E) * y) :
    y ∈ LinearMap.range (algebraFormPullback k C E q) := by
  letI : Algebra.FormallyEtale C E := .of_isLocalization C⁰
  let g := tensorKaehlerEquivOfFormallyEtale k C E
  let bE := (b.baseChange E).map g
  have hb (i : Fin (p + q)) : bE i = KaehlerDifferential.map k k C E (b i) := by
    change ((b.baseChange E).map g) i = _
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul]
  let f (n : ℕ) := algebraFormPullback k C E n
  have hf (n : ℕ) (v : Fin n → Fin (p + q)) :
      f n (exteriorPower.ιMulti C n (b ∘ v)) = exteriorPower.ιMulti E n (bE ∘ v) := by
    simp only [f, algebraFormPullback, GlobalTheory.SchemeCohomology.exteriorMapOver_ιMulti,
      Function.comp_apply]
    exact congrArg (exteriorPower.ιMulti E n) (funext fun i => (hb (v i)).symm)
  let η := f (p + q) (exteriorPower.ιMulti C (p + q) b)
  have hη : (η : DR k E) = ExteriorAlgebra.ιMulti E (p + q) bE := by
    simpa only [Function.comp_id, exteriorPower.ιMulti_apply_coe] using
      congrArg Subtype.val (hf (p + q) id)
  have hc (J : Set.powersetCard (Fin (p + q)) q) :
      (bE.exteriorPower q).repr y J ∈ (algebraMap C E).range := by
    obtain ⟨I, ε, hI⟩ := exists_complementary_exterior_coordinate bE y J
    obtain ⟨z, hz⟩ := htest (exteriorPower.ιMulti_family C p b I)
    have he : (f (p + q) z : DR k E) = (ε : ℤ) •
        ((bE.exteriorPower q).repr y J • (η : DR k E)) := by
      rw [hz, hη, exteriorPower.ιMulti_family, hf, exteriorPower.ιMulti_apply_coe]
      exact hI
    refine (topForm_smul_mem_range_iff b _).mp ?_
    have hε : (ε : ℤ) • ((bE.exteriorPower q).repr y J • η) ∈
        LinearMap.range (f (p + q)) := ⟨z, Subtype.ext (by
          simpa only [Submodule.coe_smul, Submodule.coe_smul_of_tower] using he)⟩
    simpa only [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul] using
      zsmul_mem hε (ε : ℤ)
  rw [← (bE.exteriorPower q).sum_repr y]
  refine Submodule.sum_mem _ fun J _ => ?_
  obtain ⟨c, hc⟩ := hc J
  refine ⟨c • (b.exteriorPower q) J, ?_⟩
  rw [map_smul, ← IsScalarTower.algebraMap_smul E, hc]
  congr 1
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact hf q (Set.powersetCard.ofFinEmbEquiv.symm J)

/-- On a smooth normal chart, a homogeneous rational form is regular
if all products by complementary regular forms are regular. -/
theorem mem_omB_of_complementary_wedge_regular (B : Subalgebra k E) [IsFractionRing B E]
    [Algebra.Smooth k B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {p q : ℕ} (bE : Module.Basis (Fin (p + q)) E Ω[E⁄k]) (y : ExteriorDifferentials k E q)
    (htest : ∀ a ∈ omB k E B p, a * (y : DR k E) ∈ omB k E B (p + q)) :
    (y : DR k E) ∈ omB k E B q := by
  refine mem_omB_of_forall_height_one B q y fun Q hQ _ => ?_
  letI : Q.IsPrime := hQ
  let C := (primeLocalizationInField E Q).restrictScalars k
  letI : Algebra B C := (primeLocalizationInField E Q).algebra
  letI : IsScalarTower B C E := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k B C := .of_algebraMap_eq fun _ => rfl
  letI : IsLocalization Q.primeCompl C := inferInstanceAs
    (IsLocalization Q.primeCompl (primeLocalizationInField E Q))
  letI : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C Q
  letI : IsFractionRing C E := inferInstanceAs (IsFractionRing (primeLocalizationInField E Q) E)
  letI : Algebra.FormallyEtale B C := .of_isLocalization Q.primeCompl
  obtain ⟨b⟩ := nonempty_kaehler_basis_of_fraction_basis (B := B) (C := C) bE
  have hlocal (a : ExteriorDifferentials k C p) : ∃ z : ExteriorDifferentials k C (p + q),
      (algebraFormPullback k C E (p + q) z : DR k E) =
        (algebraFormPullback k C E p a : DR k E) * y := by
    let w := algebraFormPullback k C E p a
    have hw : w ∈ LinearMap.range (algebraFormPullback k C E p) := ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := (mem_formRange_localization_iff Q.primeCompl (C := C) w).mp hw
    have ha := (mem_omB_iff_pullback_range B ((s : B) • w)).mpr hs
    have hdeg : (w : DR k E) * (y : DR k E) ∈ ⋀[E]^(p + q) Ω[E⁄k] :=
      SetLike.mul_mem_graded w.property y.property
    let z : ExteriorDifferentials k E (p + q) := ⟨_, hdeg⟩
    have hz : (s : B) • z ∈ LinearMap.range (algebraFormPullback k B E (p + q)) :=
      (mem_omB_iff_pullback_range B ((s : B) • z)).mp (by
        simpa only [z, Submodule.coe_smul_of_tower, smul_mul_assoc] using htest _ ha)
    obtain ⟨z₀, hz₀⟩ :=
      (mem_formRange_localization_iff Q.primeCompl (C := C) z).mpr ⟨s, hz⟩
    exact ⟨z₀, congrArg Subtype.val hz₀⟩
  have hy := mem_formRange_of_local_wedge_test b y hlocal
  obtain ⟨s, hs⟩ := (mem_formRange_localization_iff Q.primeCompl (C := C) y).mp hy
  exact ⟨s, s.property, (mem_omB_iff_pullback_range B ((s : B) • y)).mpr hs⟩

end GlobalTheory.PD
