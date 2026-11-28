import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinInertiaImage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinFinitePlaceInjectivity
import GaloisForLFunctions.HTGeometry.MilnorKTameValuation

/-! With arithmetic Artin normalization, the inverse on the Weil group
sends an arithmetic Frobenius to a uniformizer. Finite-stage Frobenius
comparison leaves an inertia error that can be removed by a local unit. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField WithZero Topology
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GaloisForLFunctions.HTGeometry
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

local notation "C" => CompactIdeleClassQuotient K
local notation "M" => maximalAbelianExtension K Ω
local notation "Fv" => v.adicCompletion K
local notation "ν" => tameValHom (Valued.v : Valuation Fv ℤᵐ⁰)

local instance : CommGroup Gal(M/K) :=
  { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }

variable {K} in
private theorem tameValHom_toAdd_eq_neg_log (x : Fvˣ) :
    Multiplicative.toAdd (ν x) = -log (Valued.v (x : Fv)) := by
  rw [tameValHom_toAdd, ← coe_tameUnzero Valued.v x] <;> rfl

variable {K} in
theorem unitsLevel_zero_iff_tameValHom_eq_one (x : Fvˣ) :
    x ∈ unitsLevel (K := K) v 0 ↔ ν x = 1 := by
  rw [← MonoidHom.mem_ker, tameValHom_mem_ker_iff]
  constructor
  · exact fun hx => (mem_unitsLevel.mp hx).1
  · intro hx
    refine mem_unitsLevel.mpr ⟨hx, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valued.v.map_sub_le hx.le (map_one Valued.v).le

theorem exists_uniformizer_matching_absoluteFrobenius
    (a : C →* Gal(M/K)) (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a)
    (h : IsPlaceOver A v) :
    ∃ π : Fvˣ, ν π = Multiplicative.ofAdd 1 ∧
      a (toCompactIdeleClassQuotient K (finiteEmbedding v π)) =
        toMaxAb K Ω (frob h : Gal(Ω/K)) := by
  let f := a.comp ((toCompactIdeleClassQuotient K).comp (finiteEmbedding v))
  obtain ⟨z, hz⟩ := exists_ord_eq_ite v
  let π := finiteProj v z
  have hπ : ν π = Multiplicative.ofAdd 1 := by
    apply Multiplicative.toAdd.injective
    rw [tameValHom_toAdd_eq_neg_log (v := v)]
    change -log (Valued.v ((finiteProj v z : Fvˣ) : Fv)) = 1
    rw [coe_finiteProj]
    change ord v z = 1
    exact (hz v).trans (if_pos rfl)
  let σ := (frob h : Gal(Ω/K))
  let g := f π / toMaxAb K Ω σ
  obtain ⟨u, hu, hfu⟩ := exists_localUnit_of_all_restrictions_mem_inertia K Ω a hc ha h g (fun V => by
    let L := (V : IntermediateField K Ω)
    letI := V.2.1
    letI := V.2.2
    letI : NumberField L := NumberField.of_module_finite K L
    let w := finitePlaceAtAbsoluteValuation (L := L) A h
    letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
    let b := finiteStageArtin K Ω a V
    let r := restrictAb L (le_maximalAbelianExtension L)
    have hf := finiteIdelicArtin_finiteEmbedding_div_frob_mem_inertia b
      (finiteStageArtin_isFiniteIdelicArtin K Ω a ha V) (finiteStageArtin_diagonal K Ω a V)
      v w (AlgEquiv.restrictNormalHom L σ) (restrictNormalHom_isArithFrobAt A h (isFrob_frob (h := h))) π
    have hπ' : (-log (Valued.v (π : Fv)) : ℤ) = 1 := by
      have he := congrArg (fun x : Multiplicative ℤ => Multiplicative.toAdd x) hπ
      rwa [tameValHom_toAdd_eq_neg_log (v := v)] at he
    rw [hπ', zpow_one] at hf
    change r (f π / toMaxAb K Ω σ) ∈ w.asIdeal.inertia Gal(L/K)
    rw [map_div]
    have he : r (toMaxAb K Ω σ) = AlgEquiv.restrictNormalHom L σ := restrictAbPi_toMaxAb K Ω V σ
    rw [he]
    exact hf)
  refine ⟨π / u, ?_, ?_⟩
  · rw [map_div, hπ, (unitsLevel_zero_iff_tameValHom_eq_one u).mp hu, div_one]
  · change f (π / u) = toMaxAb K Ω σ
    change f u = f π / toMaxAb K Ω σ at hfu
    rw [map_div, hfu, div_div_cancel]

#print axioms exists_uniformizer_matching_absoluteFrobenius

theorem exists_inverse_arithmeticArtin_on_Weil
    (a : C →* Gal(M/K)) (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a)
    (h : IsPlaceOver A v) :
    ∃ b : Weil h →* Fvˣ, Function.Surjective b ∧
      (∀ s, ν (b s) = Multiplicative.ofAdd (deg s)) ∧
      ∀ s : Weil h, a (toCompactIdeleClassQuotient K (finiteEmbedding v (b s))) =
        toMaxAb K Ω (s : Gal(Ω/K)) := by
  let f := a.comp ((toCompactIdeleClassQuotient K).comp (finiteEmbedding v))
  let ρ := (toMaxAb K Ω).comp (Weil h).subtype
  have hf : Function.Injective f := globalArtin_injective_finiteEmbedding a hc ha v
  obtain ⟨π, hπ, hfπ⟩ := exists_uniformizer_matching_absoluteFrobenius K Ω a hc ha h
  have hπF : f π = ρ (frob h) := hfπ
  have hπVal (d : ℤ) : ν (π ^ d) = Multiplicative.ofAdd d := by
    rw [map_zpow, hπ]
    apply Multiplicative.toAdd.injective
    change d • (1 : ℤ) = d
    simp
  have hpre (s : Weil h) : ∃ x : Fvˣ, ν x = Multiplicative.ofAdd (deg s) ∧ f x = ρ s := by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
    obtain ⟨u, hu, hU⟩ := exists_localUnit_of_Ine_artin K Ω a hc ha h τ
    have hU' : f u = ρ (ineIncl h τ) := hU
    have huVal : ν u = 1 := (unitsLevel_zero_iff_tameValHom_eq_one u).mp hu
    refine ⟨π ^ deg s * u, ?_, ?_⟩
    · rw [map_mul (ν), hπVal, huVal, mul_one]
    · calc
        f (π ^ deg s * u) = f π ^ deg s * f u := by rw [map_mul f, map_zpow f]
        _ = ρ (frob h ^ deg s * ineIncl h τ) := by
          rw [map_mul ρ, map_zpow ρ, hπF, hU']
        _ = ρ s := congrArg ρ hτ.symm
  choose b hb hbF using hpre
  let β : Weil h →* Fvˣ :=
    { toFun := b
      map_one' := hf ((hbF 1).trans ((map_one ρ).trans (map_one f).symm))
      map_mul' := fun s t => hf (calc
        f (b (s * t)) = ρ (s * t) := hbF (s * t)
        _ = ρ s * ρ t := map_mul ρ s t
        _ = f (b s * b t) := by rw [map_mul f, hbF s, hbF t]) }
  refine ⟨β, fun x => ?_, hb, hbF⟩
  let d := Multiplicative.toAdd (ν x)
  let u := x / π ^ d
  have hu : u ∈ unitsLevel (K := K) v 0 := by
    apply (unitsLevel_zero_iff_tameValHom_eq_one u).mpr
    change ν (x / π ^ d) = 1
    rw [map_div (ν), hπVal]
    exact div_self' (ν x)
  obtain ⟨τ, hτ⟩ := exists_Ine_of_localUnit_artin K Ω a ha h u hu
  have hτ' : ρ (ineIncl h τ) = f u := hτ
  refine ⟨frob h ^ d * ineIncl h τ, hf ?_⟩
  calc
    f (b (frob h ^ d * ineIncl h τ)) = ρ (frob h ^ d * ineIncl h τ) := hbF _
    _ = f (π ^ d * u) := by rw [map_mul ρ, map_zpow ρ, ← hπF, hτ', map_mul f, map_zpow f]
    _ = f x := congrArg f (mul_div_cancel (π ^ d) x)

theorem continuous_inverseArtin_on_inertia
    (a : C →* Gal(M/K)) (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a)
    {h : IsPlaceOver A v} (b : Weil h →* Fvˣ)
    (hb : ∀ s, ν (b s) = Multiplicative.ofAdd (deg s))
    (hfix : ∀ s : Weil h, a (toCompactIdeleClassQuotient K (finiteEmbedding v (b s))) =
      toMaxAb K Ω (s : Gal(Ω/K))) :
    Continuous (fun (s : Ine (F := K) A) => b (ineIncl h s)) := by
  let U := unitsLevel (K := K) v 0
  letI : CompactSpace U := isCompact_iff_compactSpace.mp (isCompact_unitsLevel_zero K v)
  letI : T2Space Gal(M/K) := krullTopology_t2
  let f := a.comp ((toCompactIdeleClassQuotient K).comp (finiteEmbedding v))
  let fU := f.comp U.subtype
  have hf : Function.Injective f := globalArtin_injective_finiteEmbedding a hc ha v
  have hcU : Continuous fU := hc.comp
    (QuotientGroup.continuous_mk.comp ((continuous_finiteEmbedding v).comp continuous_subtype_val))
  let e : U ≃ fU.range := Equiv.ofBijective fU.rangeRestrict
    ⟨fun x y hxy => Subtype.ext (hf (congrArg Subtype.val hxy)), fU.rangeRestrict_surjective⟩
  have he : Continuous e := hcU.subtype_mk _
  let H := he.homeoOfEquivCompactToT2 (f := e)
  have hu (s : Ine (F := K) A) : b (ineIncl h s) ∈ U :=
    (unitsLevel_zero_iff_tameValHom_eq_one _).mpr (by
      rw [hb, deg_ineIncl]
      rfl)
  let g (s : Ine (F := K) A) : fU.range :=
    ⟨toMaxAb K Ω s.val, ⟨⟨b (ineIncl h s), hu s⟩, hfix (ineIncl h s)⟩⟩
  have hg : Continuous g := ((continuous_toMaxAb K Ω).comp continuous_subtype_val).subtype_mk _
  have heq : (fun (s : Ine (F := K) A) => b (ineIncl h s)) = Subtype.val ∘ H.symm ∘ g := by
    funext s
    let u : U := ⟨b (ineIncl h s), hu s⟩
    have hG : H u = g s := Subtype.ext (hfix (ineIncl h s))
    change u.val = (H.symm (g s)).val
    rw [← hG, H.symm_apply_apply]
  rw [heq]
  exact continuous_subtype_val.comp (H.symm.continuous.comp hg)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_inverse_arithmeticArtin_on_Weil
#print axioms GlobalTheory.Reciprocity.continuous_inverseArtin_on_inertia
