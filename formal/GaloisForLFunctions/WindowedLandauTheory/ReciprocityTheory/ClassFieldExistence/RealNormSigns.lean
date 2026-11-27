import GaloisForLFunctions.RHTower.Artin.IdealsArePrincipalUpToADescentSetOfPrimes
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-! If every real place admits a real lift, a norm realizes every
sign pattern on the base field. -/

noncomputable section

open NumberField InfinitePlace GaloisForLFunctions

namespace GlobalTheory.Reciprocity

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] infinitePlaceMulAction

private abbrev RealPlaces (F : Type u) [Field F] := {w : InfinitePlace F // w.IsReal}

omit [NumberField K] [NumberField L] [Algebra K L] in
private theorem realEmbedding_comap_apply (w : RealPlaces L) (f : K →+* L) (x : K) :
    embedding_of_isReal (w.2.comap f) x = embedding_of_isReal w.2 (f x) := by
  apply Complex.ofReal_injective
  calc
    (embedding_of_isReal (w.2.comap f) x : ℂ) = (w.val.comap f).embedding x :=
      embedding_of_isReal_apply (w.2.comap f) x
    _ = w.val.embedding (f x) :=
      RingHom.congr_fun (comap_embedding_of_isReal f (w.2.comap f)) x
    _ = (embedding_of_isReal w.2 (f x) : ℂ) := (embedding_of_isReal_apply w.2 (f x)).symm

omit [NumberField K] [NumberField L] in
theorem exists_real_place_of_completion_embedding {v : InfinitePlace K} (hv : v.IsReal)
    (j : L →ₐ[K] v.Completion) :
    ∃ w : RealPlaces L, w.val.comap (algebraMap K L) = v := by
  let f := (Completion.extensionEmbeddingOfIsReal hv).comp j.toRingHom
  let c := Complex.ofRealHom.comp f
  have hre : ComplexEmbedding.IsReal c := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    change (starRingEnd ℂ) ((f x : ℝ) : ℂ) = ((f x : ℝ) : ℂ)
    simp
  refine ⟨⟨InfinitePlace.mk c, InfinitePlace.isReal_mk_iff.mpr hre⟩, ?_⟩
  rw [InfinitePlace.comap_mk, ← InfinitePlace.mk_embedding v]
  congr 1
  ext x
  change (Completion.extensionEmbeddingOfIsReal hv (j (algebraMap K L x)) : ℂ) = v.embedding x
  rw [j.commutes, Completion.algebraMap_apply, Completion.extensionEmbeddingOfIsReal_coe]
  exact embedding_of_isReal_apply hv x

theorem exists_norm_with_real_signs (G : Type u) [CommGroup G] [Fintype G]
    [MulSemiringAction G L] [IsGaloisGroup G K L]
    (hs : ∀ v : RealPlaces K, ∃ w : RealPlaces L, w.val.comap (algebraMap K L) = v.val)
    (a : Kˣ) :
    ∃ b : Lˣ, ∀ v : RealPlaces K,
      0 < embedding_of_isReal v.2 ((a / Units.map (Algebra.norm K : L →* K) b : Kˣ) : K) := by
  classical
  choose pick hpick using hs
  let s : Set (RealPlaces L) := pick '' {v | embedding_of_isReal v.2 (a : K) < 0}
  obtain ⟨b, hb, hsign⟩ := exists_one_lt_and_sign L s
  have hb0 : b ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
    intro h
    have hh := hb w
    rw [h, map_zero] at hh
    exact (not_lt_of_ge zero_le_one) hh
  refine ⟨Units.mk0 b hb0, fun v => ?_⟩
  let w := pick v
  let f (σ : G) := MulSemiringAction.toRingHom G L σ
  let q (σ : G) : RealPlaces L := ⟨w.val.comap (f σ), w.2.comap (f σ)⟩
  have hqeq (σ : G) : (q σ).val = σ⁻¹ • w.val := by
    change w.val.comap (f σ) = w.val.comap (f (σ⁻¹)⁻¹)
    rw [inv_inv]
  have hq (σ : G) : (q σ).val.comap (algebraMap K L) = v.val := by
    rw [hqeq, comap_infinitePlace_smul]
    exact hpick v
  have hcard : Nat.card (MulAction.stabilizer G w.val) = 1 := by
    rw [card_stabilizer_infinitePlace K G,
      if_pos (InfinitePlace.isUnramified_iff.mpr (Or.inl w.2))]
  have hstab : MulAction.stabilizer G w.val = ⊥ := Subgroup.card_eq_one.mp hcard
  have hq₁ : q 1 = w := Subtype.ext ((hqeq 1).trans (by rw [inv_one, one_smul]))
  have hnot (σ : G) (hσ : σ ≠ 1) : q σ ∉ s := by
    rintro ⟨v', _, he⟩
    have h : v' = v := Subtype.ext ((hpick v').symm.trans
      ((congrArg (fun z : RealPlaces L => z.val.comap (algebraMap K L)) he).trans (hq σ)))
    subst v'
    have ht : σ⁻¹ ∈ MulAction.stabilizer G w.val := by
      rw [MulAction.mem_stabilizer_iff]
      exact (hqeq σ).symm.trans (congrArg Subtype.val he).symm
    rw [hstab, Subgroup.mem_bot, inv_eq_one] at ht
    exact hσ ht
  have hsignw : w ∈ s ↔ embedding_of_isReal v.2 (a : K) < 0 := by
    constructor
    · rintro ⟨v', hv', he⟩
      have h : v' = v := Subtype.ext ((hpick v').symm.trans
        ((congrArg (fun z : RealPlaces L => z.val.comap (algebraMap K L)) he).trans (hpick v)))
      exact h ▸ hv'
    · exact fun hv => ⟨v, hv, rfl⟩
  have heval (σ : G) : embedding_of_isReal (q σ).2 b =
      embedding_of_isReal w.2 (σ • b) :=
    realEmbedding_comap_apply w (f σ) b
  have he : embedding_of_isReal v.2 (Algebra.norm K b) =
      (∏ σ ∈ Finset.univ.erase (1 : G), embedding_of_isReal (q σ).2 b) *
        embedding_of_isReal w.2 b := by
    have hbase (x : K) : embedding_of_isReal v.2 x =
        embedding_of_isReal w.2 (algebraMap K L x) := by
      let v' : RealPlaces K := ⟨w.val.comap (algebraMap K L), w.2.comap _⟩
      have hv' : v' = v := Subtype.ext (hpick v)
      exact (congrArg (fun u : RealPlaces K => embedding_of_isReal u.2 x) hv').symm.trans
        (realEmbedding_comap_apply w (algebraMap K L) x)
    rw [hbase, algebraMap_norm_eq_prod_smul K L G, map_prod]
    simp_rw [← heval]
    rw [← hq₁, Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : G))]
  have hp : 0 < ∏ σ ∈ Finset.univ.erase (1 : G), embedding_of_isReal (q σ).2 b :=
    Finset.prod_pos fun σ hσ => zero_lt_one.trans ((hsign (q σ)).2 (hnot σ (Finset.mem_erase.mp hσ).1))
  have hd : ((a / Units.map (Algebra.norm K : L →* K) (Units.mk0 b hb0) : Kˣ) : K) =
      (a : K) / Algebra.norm K b := by
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0]
  rw [hd, map_div₀, he]
  by_cases h : embedding_of_isReal v.2 (a : K) < 0
  · exact div_pos_of_neg_of_neg h (mul_neg_of_pos_of_neg hp
      (((hsign w).1 (hsignw.mpr h)).trans (by norm_num)))
  · have ha : embedding_of_isReal v.2 (a : K) ≠ 0 := by simp
    exact div_pos ((not_lt.mp h).lt_of_ne ha.symm)
      (mul_pos hp (zero_lt_one.trans ((hsign w).2 (fun hs => h (hsignw.mp hs)))))

end GlobalTheory.Reciprocity
