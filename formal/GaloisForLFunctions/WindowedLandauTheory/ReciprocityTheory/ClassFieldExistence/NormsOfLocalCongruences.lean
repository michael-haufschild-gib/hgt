import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicProductNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InfiniteCompletionNormSigns
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleRayCongruence
import GaloisForLFunctions.RHTower.Artin.RelativeNormsOfRayElementsAreRayElements

/-! Idelic norm preserves the congruences at a rational ray modulus.
The valuation of the rational modulus in the upper field includes the
ramification index needed to descend the congruence. -/

noncomputable section

open NumberField IsDedekindDomain WithZero GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped GlobalTheory.Reciprocity.AdicLiesOver NumberField.LiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem valued_natCast_ray_exponent {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (c : ℕ) [NeZero c] :
    Valued.v (c : u.adicCompletion F) = exp (-(exponent (normModulus F c) u : ℤ)) := by
  rw [← map_natCast (algebraMap (𝓞 F) (u.adicCompletion F)), valued_algebraMap_int,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ (Nat.cast_ne_zero.mpr (NeZero.ne c))]
  rfl

private theorem algebraMap_normUnits_eq_prod (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (y : (w.adicCompletion L)ˣ) :
    Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L)).toMonoidHom
        (Units.map (Algebra.norm (v.adicCompletion K)) y) =
      ∏ σ : Gal(w.adicCompletion L/v.adicCompletion K), Units.map σ.toMonoidHom y := by
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, Units.coe_prod]
  change algebraMap (v.adicCompletion K) (w.adicCompletion L)
      (Algebra.norm (v.adicCompletion K) (y : w.adicCompletion L)) =
    ∏ σ : Gal(w.adicCompletion L/v.adicCompletion K), σ (y : w.adicCompletion L)
  exact Algebra.norm_eq_prod_automorphisms (K := v.adicCompletion K)
    (L := w.adicCompletion L) (y : w.adicCompletion L)

private theorem localNorm_mem_unitsLevel_of_rational (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (c : ℕ) [NeZero c]
    (y : (w.adicCompletion L)ˣ) (hy : y ∈ unitsLevel w (exponent (normModulus L c) w)) :
    Units.map (Algebra.norm (v.adicCompletion K)) y ∈ unitsLevel v (exponent (normModulus K c) v) := by
  let z : (v.adicCompletion K)ˣ := Units.map (Algebra.norm (v.adicCompletion K)) y
  have hgal (σ : Gal(w.adicCompletion L/v.adicCompletion K)) :
      Units.map σ.toMonoidHom y ∈ unitsLevel w (exponent (normModulus L c) w) := by
    obtain ⟨τ, rfl⟩ := (decompositionMulEquiv v w).surjective σ
    rw [mem_unitsLevel, Units.coe_map]
    change Valued.v (decompositionMulEquiv v w τ y.val) = 1 ∧
      Valued.v (decompositionMulEquiv v w τ y.val - 1) ≤ _
    rw [← map_one (decompositionMulEquiv v w τ), ← map_sub, valued_decompositionMulEquiv,
      valued_decompositionMulEquiv]
    exact hy
  have h : (∏ σ : Gal(w.adicCompletion L/v.adicCompletion K), Units.map σ.toMonoidHom y) ∈
      unitsLevel w (exponent (normModulus L c) w) :=
    (unitsLevel w _).prod_mem (fun σ _ => hgal σ)
  rw [← algebraMap_normUnits_eq_prod v w y] at h
  have hz : Valued.v z.val = 1 := by
    change Valued.v (Algebra.norm (v.adicCompletion K) y.val) = _
    rw [valued_finiteCompletion_norm v w, (mem_unitsLevel.mp hy).1, one_pow]
  refine mem_unitsLevel.mpr ⟨hz, ?_⟩
  rw [← valued_natCast_ray_exponent v c]
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  apply (pow_le_pow_iff_left₀ zero_le zero_le he).mp
  rw [← AdicLiesOver.valued_completionMap v w, ← AdicLiesOver.valued_completionMap v w,
    map_sub, map_one, map_natCast, valued_natCast_ray_exponent w c]
  exact (mem_unitsLevel.mp h).2

theorem ideleNorm_mem_idelesOneMod_rational (c : ℕ) [NeZero c]
    (y : IdeleGroup L) (hy : y ∈ idelesOneMod (normModulus L c)) :
    ideleNorm (K := K) y ∈ idelesOneMod (normModulus K c) := by
  obtain ⟨hyf, hyi⟩ := (mem_idelesOneMod _).mp hy
  refine (mem_idelesOneMod _).mpr ⟨fun v hv => ?_, fun v _ => ?_⟩
  · have hw (w : finitePlacesAbove L v) : w.val.asIdeal ∣ (normModulus L c).fin := by
      rw [dvd_normModulus_fin_iff] at hv ⊢
      have h := Ideal.LiesOver.over (p := v.asIdeal) (P := w.val.asIdeal)
      change (c : 𝓞 L) ∈ w.val.asIdeal
      rw [← map_natCast (algebraMap (𝓞 K) (𝓞 L))]
      change (c : 𝓞 K) ∈ w.val.asIdeal.under (𝓞 K)
      rwa [← h]
    rw [finiteProj_ideleNorm]
    change (∏ w : finitePlacesAbove L v, _) ∈ _
    exact (unitsLevel v _).prod_mem fun w _ =>
      localNorm_mem_unitsLevel_of_rational v w.val c _ (hyf w.val (hw w))
  · rw [infiniteProj_ideleNorm, coe_infiniteLocalNorm, map_prod]
    apply Finset.prod_pos
    intro w _
    rcases w.val.isReal_or_isComplex with hw | hw
    · rw [realNormOfRealCompletion v.val w v.2 hw]
      exact hyi ⟨w.val, hw⟩ (Set.mem_univ _)
    · exact realNormOfComplexCompletion_pos v.val w v.2 hw (infiniteProj w.val y).ne_zero

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.ideleNorm_mem_idelesOneMod_rational
