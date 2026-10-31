import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCylinderIntegrals
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticIdeleCharacters
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalHaarMagnitude
/-!
# Actual idele scaling of elliptic adelic Haar

An idele scales the full integral box into one finite cylinder. Exact
cylinder Haar coordinates and local moduli give its mass as the global
idele magnitude, which determines the ambient Haar modulus.
-/

open MeasureTheory Set
open scoped Pointwise NNReal ENNReal WithZero WithZeroMulInt


namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Filter HTGeometry.DiscreteValuationHaar
noncomputable section


local instance ideleHaarFiniteMeasurable (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance ideleHaarFiniteBorel (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance ideleHaarFiniteCompact (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v
local instance ideleHaarFiniteSigmaCompact (v : FinitePlace) : SigmaCompactSpace (v.adicCompletion K) := by
  letI := finiteCompletion_secondCountable v
  letI := finiteCompletion_locallyCompact v
  exact sigmaCompactSpace_of_locallyCompact_secondCountable
local instance ideleHaarFiniteHaar (v : FinitePlace) : (normalizedHaar (v.adicCompletion K)).IsAddHaarMeasure :=
  normalizedHaar_isAddHaar (v.adicCompletion K)
local instance ideleHaarFiniteSigmaFinite (v : FinitePlace) : SigmaFinite (normalizedHaar (v.adicCompletion K)) := inferInstance
local instance ideleHaarInfinityMeasurable : MeasurableSpace InfinityCompletion := borel _
local instance ideleHaarInfinityBorel : BorelSpace InfinityCompletion := ⟨rfl⟩

private def finiteIdeleUnit (u : Ideles) (v : FinitePlace) : (v.adicCompletion K)ˣ where
  val := (u : Adeles).1 v
  inv := ((u⁻¹ : Ideles) : Adeles).1 v
  val_inv := congrArg (fun a : Adeles => a.1 v) u.val_inv
  inv_val := congrArg (fun a : Adeles => a.1 v) u.inv_val

private def infinityIdeleUnit (u : Ideles) : InfinityCompletionˣ where
  val := (u : Adeles).2
  inv := ((u⁻¹ : Ideles) : Adeles).2
  val_inv := congrArg Prod.snd u.val_inv
  inv_val := congrArg Prod.snd u.inv_val

private theorem exists_ideleUnit_places (u : Ideles) :
    ∃ S : Finset FinitePlace, ∀ v ∉ S, Valued.v ((u : Adeles).1 v) = 1 := by
  classical
  have hu : IsUnit (u : Adeles).1 := u.isUnit.map (RingHom.fst FiniteAdeles InfinityCompletion)
  have hv := (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp hu).2
  have hfinite := Filter.eventually_cofinite.mp hv
  refine ⟨hfinite.toFinset, ?_⟩
  intro v hv
  have hn : ¬ Valued.v ((u : Adeles).1 v) ≠ 1 := by
    intro h
    exact hv (hfinite.mem_toFinset.mpr h)
  exact not_not.mp hn

private theorem finiteIdeleUnit_inv_value_one (u : Ideles) (v : FinitePlace)
    (hu : Valued.v ((u : Adeles).1 v) = 1) :
    Valued.v (((u⁻¹ : Ideles) : Adeles).1 v) = 1 := by
  have he := congrArg (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    (congrArg (fun a : Adeles => a.1 v) u.inv_val)
  change Valued.v ((((u⁻¹ : Ideles) : Adeles).1 v) * ((u : Adeles).1 v)) =
    Valued.v (1 : v.adicCompletion K) at he
  simpa only [map_mul,hu,mul_one,map_one] using he

private def scaledIntegralBox (S : Finset FinitePlace) (u : Ideles) :
    Set (EllipticCylinderCoordinates S) :=
  ((Set.univ.pi fun v : S => finiteIdeleUnit u v.1 •
      (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K))) ×ˢ Set.univ) ×ˢ
    (infinityIdeleUnit u • ((Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer : Set InfinityCompletion))

private theorem assembly_preimage_scaledIntegral (S : Finset FinitePlace) (u : Ideles)
    (hu : ∀ v ∉ S, Valued.v ((u : Adeles).1 v) = 1) :
    ellipticCylinderAssembly S ⁻¹' (u • integralAdeles) = scaledIntegralBox S u := by
  classical
  ext x
  rw [mem_preimage,Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hx
    refine ⟨⟨fun v _ => ?_,mem_univ _⟩,?_⟩
    · apply Set.mem_smul_set_iff_inv_smul_mem.mpr
      change Valued.v ((((u⁻¹ : Ideles) : Adeles).1 v.1) * x.1.1 v) ≤ 1
      have he := hx.1 v.1
      change Valued.v ((((u⁻¹ : Ideles) : Adeles).1 v.1) *
        (finiteCylinderAssembly S x.1 : FiniteAdeles) v.1) ≤ 1 at he
      rwa [finiteCylinderAssembly_apply_mem] at he
    · apply Set.mem_smul_set_iff_inv_smul_mem.mpr
      exact hx.2
  · intro hx
    refine ⟨fun v => ?_,Set.mem_smul_set_iff_inv_smul_mem.mp hx.2⟩
    by_cases hv : v ∈ S
    · have he := Set.mem_smul_set_iff_inv_smul_mem.mp (hx.1.1 ⟨v,hv⟩ (mem_univ _))
      change Valued.v ((((u⁻¹ : Ideles) : Adeles).1 v) * x.1.1 ⟨v,hv⟩) ≤ 1 at he
      change Valued.v ((((u⁻¹ : Ideles) : Adeles).1 v) *
        (finiteCylinderAssembly S x.1 : FiniteAdeles) v) ≤ 1
      rw [finiteCylinderAssembly_apply_mem S x.1 ⟨v,hv⟩]
      exact he
    · change Valued.v ((((u⁻¹ : Ideles) : Adeles).1 v) *
        (finiteCylinderAssembly S x.1 : FiniteAdeles) v) ≤ 1
      rw [map_mul,finiteIdeleUnit_inv_value_one u v (hu v hv),one_mul,
        finiteCylinderAssembly_apply_notMem S x.1 ⟨v,hv⟩]
      exact (x.1.2 ⟨v,hv⟩).property

private theorem scaledIntegral_subset_cylinder (S : Finset FinitePlace) (u : Ideles)
    (hu : ∀ v ∉ S, Valued.v ((u : Adeles).1 v) = 1) :
    u • integralAdeles ⊆ ellipticAdeleCylinder S := by
  rintro a ⟨b,hb,rfl⟩ v hv
  change Valued.v ((u : Adeles).1 v * b.1 v) ≤ 1
  rw [map_mul,hu v hv,one_mul]
  exact hb.1 v

private theorem assembly_image_scaledIntegral (S : Finset FinitePlace) (u : Ideles)
    (hu : ∀ v ∉ S, Valued.v ((u : Adeles).1 v) = 1) :
    ellipticCylinderAssembly S '' scaledIntegralBox S u = u • integralAdeles := by
  rw [← assembly_preimage_scaledIntegral S u hu]
  apply Set.image_preimage_eq_of_subset
  rw [ellipticCylinderAssembly_range]
  exact scaledIntegral_subset_cylinder S u hu


private theorem finite_scaled_integer_mass (u : Ideles) (v : FinitePlace) :
    normalizedHaar (v.adicCompletion K)
      (finiteIdeleUnit u v • (v.adicCompletionIntegers K : Set (v.adicCompletion K))) =
        (finiteCompletionMagnitude v ((u : Adeles).1 v) : ℝ≥0∞) := by
  rw [← distribHaarChar_mul (normalizedHaar (v.adicCompletion K)),
    normalizedHaar_integer, mul_one, finiteCompletion_distribHaarChar]
  rfl

private theorem infinity_scaled_integer_mass (u : Ideles) :
    normalizedHaar InfinityCompletion
      (infinityIdeleUnit u • ((Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer : Set InfinityCompletion)) =
        (infinityCompletionMagnitude (u : Adeles).2 : ℝ≥0∞) := by
  rw [← distribHaarChar_mul (normalizedHaar InfinityCompletion),
    normalizedHaar_integer, mul_one, infinityCompletion_distribHaarChar]
  rfl

private theorem magnitude_eq_finite_product (S : Finset FinitePlace) (u : Ideles)
    (hu : ∀ v ∉ S, Valued.v ((u : Adeles).1 v) = 1) :
    ideleMagnitude u = infinityCompletionMagnitude (u : Adeles).2 *
      ∏ v ∈ S, finiteCompletionMagnitude v ((u : Adeles).1 v) := by
  classical
  let f : FinitePlace → ℝ≥0 := fun v => finiteCompletionMagnitude v ((u : Adeles).1 v)
  have hs : Function.mulSupport f ⊆ S := by
    intro v hv
    by_contra hn
    apply hv
    have he := hu v hn
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom
      ((u : Adeles).1 v) = 1 at he
    simp only [f,finiteCompletionMagnitude,MonoidWithZeroHom.comp_apply,he,map_one]
  change infinityCompletionMagnitude (u : Adeles).2 * (∏ᶠ v, f v) = _
  rw [finprod_eq_prod_of_mulSupport_subset f hs]

private theorem scaledIntegralBox_mass (S : Finset FinitePlace) (u : Ideles)
    (hu : ∀ v ∉ S, Valued.v ((u : Adeles).1 v) = 1) :
    ellipticCylinderProductHaar S (scaledIntegralBox S u) = (ideleMagnitude u : ℝ≥0∞) := by
  classical
  letI (v : S) : SigmaFinite (normalizedHaar (v.1.adicCompletion K)) := inferInstance
  rw [ellipticCylinderProductHaar,scaledIntegralBox,Measure.prod_prod,Measure.prod_prod,Measure.pi_pi]
  simp only [finite_scaled_integer_mass,infinity_scaled_integer_mass,measure_univ,mul_one]
  rw [magnitude_eq_finite_product S u hu,
    Finset.prod_coe_sort S (fun v => (finiteCompletionMagnitude v ((u : Adeles).1 v) : ℝ≥0∞))]
  norm_cast
  exact mul_comm _ _

/-- Scaling the full integral box has exactly the actual idele magnitude. -/
theorem adeleHaar_idele_smul_integralAdeles (u : Ideles) :
    adeleHaar (u • integralAdeles) = (ideleMagnitude u : ℝ≥0∞) := by
  obtain ⟨S,hS⟩ := exists_ideleUnit_places u
  calc
    adeleHaar (u • integralAdeles) =
        adeleHaar (ellipticCylinderAssembly S '' scaledIntegralBox S u) :=
      congrArg adeleHaar (assembly_image_scaledIntegral S u hS).symm
    _ = ellipticCylinderAmbientHaar S (scaledIntegralBox S u) := by
      rw [ellipticCylinderAmbientHaar,
        (ellipticCylinderAssembly_isOpenEmbedding S).measurableEmbedding.comap_apply]
    _ = ellipticCylinderProductHaar S (scaledIntegralBox S u) :=
      congrArg (fun μ => μ (scaledIntegralBox S u)) (ellipticCylinderAmbientHaar_eq_product S)
    _ = _ := scaledIntegralBox_mass S u hS

/-- The actual idele norm is the change-of-variables factor for ambient adelic Haar. -/
theorem adele_distribHaarChar (u : Ideles) : distribHaarChar Adeles u = ideleMagnitude u := by
  letI : adeleHaar.Regular := by unfold adeleHaar; infer_instance
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := adeleHaar) (s := integralAdeles)
    (by rw [adeleHaar_integralAdeles]; exact one_ne_zero)
    (by rw [adeleHaar_integralAdeles]; exact ENNReal.one_ne_top)
  rw [adeleHaar_idele_smul_integralAdeles,adeleHaar_integralAdeles,mul_one]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleHaar_idele_smul_integralAdeles

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adele_distribHaarChar
