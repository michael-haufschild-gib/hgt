import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleDivisor
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayNormalization

/-! The idelic ray map extends the ideal ray map by diagonal
normalization. Its kernel contains every diagonal idele. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity.IdeleRay

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

local notation "U" => (idelesOneMod 𝔪)

theorem ord_eq_zero_of_mem_idelesOneMod {x : IdeleGroup K} (hx : x ∈ U)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.fin) : ord v x = 0 := by
  have h := ((mem_idelesOneMod 𝔪).1 hx).1 v hv
  have h₁ := (mem_unitsLevel.mp h).1
  rw [coe_finiteProj] at h₁
  rw [ord, h₁, log_one, neg_zero]

def toCoprimeIdeals : U →* idealGroup 𝔪 :=
  (toFractionalIdeal.comp (U).subtype).codRestrict _ fun x v hv => by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, count_toFractionalIdeal, ord_eq_zero_of_mem_idelesOneMod 𝔪 x.2 hv]

private theorem exists_idelesOneMod_of_prime {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.fin) :
    ∃ x ∈ U, toFractionalIdeal x = idealUnit v.ne_bot := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  let x := finiteEmbedding v (Units.mk0 _ hne)
  refine ⟨x, (mem_idelesOneMod 𝔪).2 ⟨fun w hw => ?_, fun w _ => ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w => ?_⟩
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    rw [show finiteProj w x = 1 from finiteProj_finiteEmbedding_of_ne hwv _]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
        neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

theorem toCoprimeIdeals_surjective : Function.Surjective (toCoprimeIdeals 𝔪) := by
  rintro ⟨I, hI⟩
  have h : I ∈ (U).map (toFractionalIdeal (K := K)) := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    refine finprod_induction (· ∈ (U).map (toFractionalIdeal (K := K))) (one_mem _)
      (fun _ _ => mul_mem) fun v => ?_
    by_cases hv : v.asIdeal ∣ 𝔪.fin
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨x, hx, hEq⟩ := exists_idelesOneMod_of_prime 𝔪 hv
      exact zpow_mem (Subgroup.mem_map.2 ⟨x, hx, hEq⟩) _
  obtain ⟨x, hx, hEq⟩ := h
  exact ⟨⟨x, hx⟩, Subtype.ext hEq⟩

private def normalizeProduct : Kˣ × U →* IdeleGroup K :=
  (diagonal K).coprod (U).subtype

private theorem normalizeProduct_surjective : Function.Surjective (normalizeProduct 𝔪) := by
  intro x
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod 𝔪 x
  refine ⟨(a⁻¹, ⟨diagonal K a * x, ha⟩), ?_⟩
  change diagonal K a⁻¹ * (diagonal K a * x) = x
  rw [map_inv, inv_mul_cancel_left]

private def onNormalizedProduct : Kˣ × U →* RayClassGroup 𝔪 :=
  (rayClass 𝔪).comp ((toCoprimeIdeals 𝔪).comp (MonoidHom.snd _ _))

private theorem ker_normalizeProduct_le : (normalizeProduct 𝔪).ker ≤ (onNormalizedProduct 𝔪).ker := by
  rintro ⟨a, x⟩ hx
  have he : diagonal K a * x.val = 1 := hx
  have hx' : x.val = diagonal K a⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right he
  have ha : a⁻¹ ∈ rayGroup 𝔪 := by
    rw [← rayUnits_eq]
    change diagonal K a⁻¹ ∈ U
    exact hx' ▸ x.2
  change rayClass 𝔪 (toCoprimeIdeals 𝔪 x) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change toFractionalIdeal x.val ∈ rayPrincipal 𝔪
  exact ⟨a⁻¹, ha, (toFractionalIdeal_diagonal _).symm.trans (congrArg toFractionalIdeal hx').symm⟩

/-- The ideal ray class of any diagonal normalization of an idele. -/
def toRayClass : IdeleGroup K →* RayClassGroup 𝔪 :=
  (normalizeProduct 𝔪).liftOfSurjective (normalizeProduct_surjective 𝔪)
    ⟨onNormalizedProduct 𝔪, ker_normalizeProduct_le 𝔪⟩

theorem toRayClass_normalized (a : Kˣ) (x : U) :
    toRayClass 𝔪 (diagonal K a * x.val) = rayClass 𝔪 (toCoprimeIdeals 𝔪 x) :=
  (normalizeProduct 𝔪).liftOfRightInverse_comp_apply _
    (Function.rightInverse_surjInv (normalizeProduct_surjective 𝔪))
    ⟨onNormalizedProduct 𝔪, ker_normalizeProduct_le 𝔪⟩ (a, x)

theorem toRayClass_diagonal (a : Kˣ) : toRayClass 𝔪 (diagonal K a) = 1 := by
  simpa using toRayClass_normalized 𝔪 a 1

theorem toRayClass_surjective : Function.Surjective (toRayClass 𝔪) := by
  intro q
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨x, rfl⟩ := toCoprimeIdeals_surjective 𝔪 I
  exact ⟨diagonal K 1 * x.val, toRayClass_normalized 𝔪 1 x⟩

end GlobalTheory.Reciprocity.IdeleRay
