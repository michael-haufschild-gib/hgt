import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleDivisor

/-! An idele with local powers at the specified places can be divided
by a single idelic power to give coordinates equal to one there. -/

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Reciprocity.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-- Local powers in the finite set and at infinity, integral units elsewhere. -/
def powerCongruence (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | (∀ v ∈ S, finiteProj v x ∈ (powMonoidHom n).range) ∧
    (∀ w : InfinitePlace K, infiniteProj w x ∈ (powMonoidHom n).range) ∧
    ∀ v ∉ S, ord v x = 0}
  one_mem' := ⟨fun v _ => by rw [map_one]; exact one_mem _,
    fun w => by rw [map_one]; exact one_mem _, fun v _ => ord_one v⟩
  mul_mem' {x y} hx hy := ⟨fun v hv => by
      rw [map_mul]; exact mul_mem (hx.1 v hv) (hy.1 v hv),
    fun w => by rw [map_mul]; exact mul_mem (hx.2.1 w) (hy.2.1 w),
    fun v hv => by rw [ord_mul, hx.2.2 v hv, hy.2.2 v hv, add_zero]⟩
  inv_mem' {x} hx := ⟨fun v hv => by rw [map_inv]; exact inv_mem (hx.1 v hv),
    fun w => by rw [map_inv]; exact inv_mem (hx.2.1 w),
    fun v hv => by rw [ord_inv, hx.2.2 v hv, neg_zero]⟩

/-- Any prescribed coordinates on finitely many finite places and at
infinity are realized by an idele with unit coordinates elsewhere. -/
theorem exists_with_local_coordinates (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : S, (v.val.adicCompletion K)ˣ)
    (b : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ∃ y : IdeleGroup K, (∀ v : S, finiteProj v.val y = a v) ∧
      (∀ w, infiniteProj w y = b w) ∧ ∀ v ∉ S, finiteProj v y = 1 := by
  classical
  let y := (∏ v : S, finiteEmbedding v.val (a v)) *
    ∏ w : InfinitePlace K, infiniteEmbedding w (b w)
  have hfin (v : S) : finiteProj v.val y = a v := by
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ huv => finiteProj_finiteEmbedding_of_ne
      (fun h => huv (Subtype.ext h.symm)) _) (by simp), finiteProj_finiteEmbedding]
  have hout (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : finiteProj v y = 1 := by
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    exact Finset.prod_eq_one fun u _ => finiteProj_finiteEmbedding_of_ne
      (fun h => hv (by rw [h]; exact u.2)) _
  have hinf (w : InfinitePlace K) : infiniteProj w y = b w := by
    simp only [y, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ huw => infiniteProj_infiniteEmbedding_of_ne huw.symm _)
      (by simp), infiniteProj_infiniteEmbedding]
  exact ⟨y, hfin, hinf, hout⟩

/-- Normalize all of the specified coordinates simultaneously by multiplying
by the inverse power of an idele supported at those places. -/
theorem exists_normalized_of_mem_powerCongruence {n : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {x : IdeleGroup K} (hx : x ∈ powerCongruence n S) :
    ∃ y z : IdeleGroup K, x = y ^ n * z ∧ (∀ v ∈ S, finiteProj v z = 1) ∧
      (∀ w : InfinitePlace K, infiniteProj w z = 1) ∧ ∀ v, ord v z = 0 := by
  classical
  have hx' : (∀ v ∈ S, finiteProj v x ∈ (powMonoidHom n).range) ∧
      (∀ w : InfinitePlace K, infiniteProj w x ∈ (powMonoidHom n).range) ∧
      ∀ v ∉ S, ord v x = 0 := hx
  choose a ha using fun v : S => hx'.1 (v : HeightOneSpectrum (𝓞 K)) v.2
  choose b hb using hx'.2.1
  obtain ⟨y, hfin, hinf, hout⟩ := exists_with_local_coordinates S a b
  set z := (y ^ n)⁻¹ * x with hzdef
  have hfin₁ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) : finiteProj v z = 1 := by
    rw [hzdef, map_mul, map_inv, map_pow, hfin ⟨v, hv⟩]
    exact inv_mul_eq_one.mpr (ha ⟨v, hv⟩)
  refine ⟨y, z, by rw [hzdef, mul_inv_cancel_left], hfin₁, ?_, ?_⟩
  · intro w
    rw [hzdef, map_mul, map_inv, map_pow, hinf]
    exact inv_mul_eq_one.mpr (hb w)
  · intro v
    have hord (t : IdeleGroup K) :
        ord v t = -WithZero.log (Valued.v (finiteProj v t : v.adicCompletion K)) := rfl
    by_cases hv : v ∈ S
    · rw [hord, hfin₁ v hv, Units.val_one, map_one, WithZero.log_one, neg_zero]
    · have hp : finiteProj v z = finiteProj v x := by
        rw [hzdef, map_mul, map_inv, map_pow, hout v hv, one_pow, inv_one, one_mul]
      rw [hord, hp, ← hord, hx'.2.2 v hv]

end GlobalTheory.Reciprocity.IdeleGroup
