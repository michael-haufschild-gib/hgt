import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.CompactFiniteIdeleUnits
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleRayCongruence
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! Modulo principal ideles and positive archimedean ideles, the ideles
are covered by finitely many translates of the finite integral units. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal Topology
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- Archimedean ideles with positive components at the real places. -/
def archPositive : Subgroup (IdeleGroup K) :=
  (toFinite K).ker ⊓ positiveAt Set.univ

abbrev CompactIdeleClassQuotient :=
  IdeleGroup K ⧸ ((diagonal K).range ⊔ archPositive K)

def toCompactIdeleClassQuotient : IdeleGroup K →* CompactIdeleClassQuotient K :=
  QuotientGroup.mk' _

theorem toCompactIdeleClassQuotient_diagonal (a : Kˣ) :
    toCompactIdeleClassQuotient K (diagonal K a) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr
    ((show (diagonal K).range ≤ (diagonal K).range ⊔ archPositive K from le_sup_left) ⟨a, rfl⟩)

theorem toCompactIdeleClassQuotient_of_archPositive {x : IdeleGroup K} (hx : x ∈ archPositive K) :
    toCompactIdeleClassQuotient K x = 1 :=
  (QuotientGroup.eq_one_iff _).mpr
    ((show archPositive K ≤ (diagonal K).range ⊔ archPositive K from le_sup_right) hx)

def toOrdinaryClassGroup : IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp toFractionalIdeal

theorem toOrdinaryClassGroup_surjective : Function.Surjective (toOrdinaryClassGroup K) := by
  refine ClassGroup.induction K (P := fun c => ∃ x, toOrdinaryClassGroup K x = c) ?_
  intro I
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K) I
  exact ⟨x, congrArg (ClassGroup.mk K) hx⟩

theorem toOrdinaryClassGroup_eq_one_iff {x : IdeleGroup K} :
    toOrdinaryClassGroup K x = 1 ↔
      toFractionalIdeal x ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  rw [toOrdinaryClassGroup, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (S := (toFractionalIdeal x : Submodule (𝓞 K) K))
    refine ⟨a, ?_⟩
    symm
    apply Subtype.coe_injective
    simp only [FractionalIdeal.val_eq_coe, ha, coe_spanSingleton]
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, by rw [← ha, coe_spanSingleton]⟩⟩

private def archSignIdele (b : InfinitePlace K → Bool) : IdeleGroup K :=
  ∏ w : InfinitePlace K, infiniteEmbedding w (if b w then -1 else 1)

private theorem infiniteProj_archSignIdele (b : InfinitePlace K → Bool) (w : InfinitePlace K) :
    infiniteProj w (archSignIdele K b) = if b w then -1 else 1 := by
  classical
  rw [archSignIdele, map_prod, Finset.prod_eq_single w]
  · exact infiniteProj_infiniteEmbedding _ _
  · intro u _ hu
    exact infiniteProj_infiniteEmbedding_of_ne hu.symm _
  · simp

private theorem finiteProj_archSignIdele (b : InfinitePlace K → Bool)
    (v : HeightOneSpectrum (𝓞 K)) : finiteProj v (archSignIdele K b) = 1 := by
  simp [archSignIdele]

private theorem exists_archPositive_mul_signs_finiteUnits {x : IdeleGroup K}
    (hx : ∀ v, ord v x = 0) :
    ∃ (b : InfinitePlace K → Bool) (a : FiniteIntegralUnits K),
      x * (archSignIdele K b * finiteIntegralIdele a)⁻¹ ∈ archPositive K := by
  classical
  obtain ⟨a, ha⟩ := exists_finiteIntegralUnits_of_ord_zero hx
  let b (w : InfinitePlace K) : Bool :=
    if hw : w.IsReal then decide (
      InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (infiniteProj w x : w.Completion) < 0) else false
  let y := x * (archSignIdele K b * finiteIntegralIdele a)⁻¹
  refine ⟨b, a, ⟨?_, ?_⟩⟩
  · apply MonoidHom.mem_ker.mpr
    apply toFinite_eq_one_of_finiteProj
    intro v
    simp only [map_mul, map_inv, finiteProj_archSignIdele, one_mul, ← ha v, mul_inv_cancel]
  · refine mem_positiveAt.mpr fun w _ => ?_
    let e := InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    let z := e (infiniteProj w.1 x : w.1.Completion)
    have hz : z ≠ 0 := (_root_.map_ne_zero e).mpr (Units.ne_zero _)
    change 0 < e (infiniteProj w.1 y : w.1.Completion)
    simp only [y, map_mul, map_inv, infiniteProj_archSignIdele, infiniteProj_finiteIntegralIdele,
      mul_one, Units.val_mul, Units.val_inv_eq_inv_val, map_inv₀]
    change 0 < z * (e (((if b w.1 then -1 else 1) : (w.1.Completion)ˣ) : w.1.Completion))⁻¹
    by_cases hn : z < 0
    · have hb : b w.1 = true := by
        change (if hw : w.val.IsReal then decide (_ < (0 : ℝ)) else false) = _
        rw [dif_pos w.2]
        change decide (z < 0) = _
        simp [hn]
      simpa [hb] using neg_pos.mpr hn
    · have hb : b w.1 = false := by
        change (if hw : w.val.IsReal then decide (_ < (0 : ℝ)) else false) = _
        rw [dif_pos w.2]
        change decide (z < 0) = _
        simp [hn]
      simpa [hb] using lt_of_le_of_ne (le_of_not_gt hn) hz.symm

instance compactSpace_compactIdeleClassQuotient : CompactSpace (CompactIdeleClassQuotient K) := by
  classical
  let q := toCompactIdeleClassQuotient K
  let r := Function.surjInv (toOrdinaryClassGroup_surjective K)
  have hr (c : ClassGroup (𝓞 K)) : toOrdinaryClassGroup K (r c) = c :=
    Function.rightInverse_surjInv (toOrdinaryClassGroup_surjective K) c
  let f (c : ClassGroup (𝓞 K)) (b : InfinitePlace K → Bool) (a : FiniteIntegralUnits K) :=
    q (r c * (archSignIdele K b * finiteIntegralIdele a))
  have hf (c) (b) : Continuous (f c b) := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (continuous_const.mul continuous_finiteIntegralIdele))
  have hU : (⋃ (c : ClassGroup (𝓞 K)) (b : InfinitePlace K → Bool), Set.range (f c b)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective j
    let c := toOrdinaryClassGroup K x
    have h1 : toOrdinaryClassGroup K (x * (r c)⁻¹) = 1 := by rw [map_mul, map_inv, hr, mul_inv_cancel]
    obtain ⟨d, hd⟩ := (toOrdinaryClassGroup_eq_one_iff K).mp h1
    set y := (diagonal K d)⁻¹ * (x * (r c)⁻¹) with hydef
    have hI : toFractionalIdeal y = 1 := by
      rw [hydef, map_mul, map_inv, toFractionalIdeal_diagonal, hd, inv_mul_cancel]
    have hy (v : HeightOneSpectrum (𝓞 K)) : ord v y = 0 := by
      simpa only [Units.val_one, count_one] using (toFractionalIdeal_eq_iff.mp hI v)
    obtain ⟨b, a, ha⟩ := exists_archPositive_mul_signs_finiteUnits K hy
    have hq := toCompactIdeleClassQuotient_of_archPositive K ha
    have hq' : q y = q (archSignIdele K b * finiteIntegralIdele a) :=
      mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using hq)
    have hxy : q x = q y * q (r c) := by
      have hd₁ : q (diagonal K d) = 1 := toCompactIdeleClassQuotient_diagonal K d
      have he : y * r c = (diagonal K d)⁻¹ * x := by
        rw [hydef, mul_assoc, inv_mul_cancel_right]
      rw [← map_mul, he, map_mul, map_inv, hd₁, inv_one]
      exact (one_mul (q x)).symm
    refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨b, a, ?_⟩⟩
    change q (r c * (archSignIdele K b * finiteIntegralIdele a)) = q x
    rw [hxy, hq', ← map_mul]
    exact congrArg q (mul_comm _ _)
  exact ⟨hU ▸ isCompact_iUnion (fun c => isCompact_iUnion fun b => isCompact_range (hf c b))⟩

end GlobalTheory.Reciprocity
