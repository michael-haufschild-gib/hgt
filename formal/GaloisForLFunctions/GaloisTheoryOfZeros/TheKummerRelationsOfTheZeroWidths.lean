import GaloisForLFunctions.GaloisTheoryOfZeros.TheQuadraticCharactersOfConjugation

/-!
# Kummer relations of the full zero-width sign kernel

Adjoin all squared zero widths to the complete-fibre source field `K`, obtaining
`D` inside the full centered zero field `L`. The extension `D/K` is normal, and
restriction gives the exact sequence with kernel `Gal(L/D)`.

This kernel is the closed group of sign families annihilating every finite
square-class relation among the radicands `−δ_q²`. Finite sign-character
separation and Krull compactness prove simultaneous realization on the whole
field. The resulting group isomorphism is a homeomorphism. Centered conjugation
is uniform sign reversal; every square-class relation has even parity.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private def signProduct {ι : Type*} (S : Finset ι) : (ι → ℤˣ) →* ℤˣ where
  toFun ε := ∏ i ∈ S, ε i
  map_one' := by simp
  map_mul' ε η := by simp only [Pi.mul_apply, Finset.prod_mul_distrib]

/-- Translation by a negative character value cancels the complete finite sum. -/
private theorem sign_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℤˣ) (hχ : ∃ g, χ g ≠ 1) :
    ∑ g : G, (χ g : ℤ) = 0 := by
  obtain ⟨g,hg⟩ := hχ
  have hminus : χ g = -1 := (Int.units_eq_one_or (χ g)).resolve_left hg
  have he : (∑ h : G, (χ h : ℤ)) = ∑ h : G, (χ (g*h) : ℤ) :=
    (Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => (χ h : ℤ))).symm
  simp only [map_mul,hminus,Units.val_neg,neg_one_mul,
    Finset.sum_neg_distrib] at he
  linarith only [he]

private def signInt : ℤˣ →* ℤ where
  toFun u := u
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem signProduct_coe {ι : Type*} (S : Finset ι) (ε : ι → ℤˣ) :
    (signProduct S ε : ℤ) = ∏ i ∈ S, (ε i : ℤ) :=
  map_prod signInt ε S

/-- Unnormalized diagonal indicator on a finite sign cube. -/
private def signCorrelation {ι : Type*} [Fintype ι] (ε η : ι → ℤˣ) : ℤ :=
  ∏ i, (1+(ε i : ℤ)*(η i : ℤ))

private theorem signCorrelation_eq {ι : Type*} [Fintype ι] (ε η : ι → ℤˣ) :
    signCorrelation ε η = if ε = η then (2 : ℤ)^Fintype.card ι else 0 := by
  classical
  by_cases he : ε = η
  · subst η
    rw [if_pos rfl]
    have hterm (i : ι) : 1+(ε i : ℤ)*(ε i : ℤ) = 2 := by
      rcases Int.units_eq_one_or (ε i) with h | h <;> rw [h] <;> norm_num
    simp only [signCorrelation,hterm,Finset.prod_const,Finset.card_univ]
  · rw [if_neg he]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases Int.units_eq_one_or (ε i) with hε | hε <;>
      rcases Int.units_eq_one_or (η i) with hη | hη
    · exact False.elim (hi (hε.trans hη.symm))
    · rw [hε,hη]; norm_num
    · rw [hε,hη]; norm_num
    · exact False.elim (hi (hε.trans hη.symm))

private theorem signCorrelation_expansion {ι : Type*} [Fintype ι] (ε η : ι → ℤˣ) :
    signCorrelation ε η = ∑ S ∈ (Finset.univ : Finset ι).powerset,
      (signProduct S ε : ℤ)*(signProduct S η : ℤ) := by
  classical
  change (∏ i, (1+(ε i : ℤ)*(η i : ℤ))) = _
  simp only [add_comm (1 : ℤ)]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one,mul_one,Finset.prod_mul_distrib,signProduct_coe]

private theorem signCorrelation_sum {ι : Type*} [Fintype ι]
    (H : Subgroup (ι → ℤˣ)) [Fintype H] (ε : ι → ℤˣ) :
    (∑ h : H, signCorrelation ε (h : ι → ℤˣ)) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        (signProduct S ε : ℤ)*(∑ h : H, (signProduct S h : ℤ)) := by
  classical
  simp_rw [signCorrelation_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  exact (Finset.mul_sum _ _ _).symm

private theorem signCorrelation_nonneg {ι : Type*} [Fintype ι] (ε η : ι → ℤˣ) :
    (0 : ℤ) ≤ signCorrelation ε η := by
  classical
  rw [signCorrelation_eq]
  split
  · exact le_of_lt (pow_pos (by norm_num) _)
  · exact le_rfl

private theorem signCorrelation_one_sum_pos {ι : Type*} [Fintype ι]
    (H : Subgroup (ι → ℤˣ)) [Fintype H] :
    (0 : ℤ) < ∑ h : H, signCorrelation (1 : ι → ℤˣ) (h : ι → ℤˣ) := by
  classical
  have hterm : signCorrelation (1 : ι → ℤˣ) ((1 : H) : ι → ℤˣ) =
      (2 : ℤ)^Fintype.card ι := by
    rw [show ((1 : H) : ι → ℤˣ) = 1 from H.subtype.map_one,signCorrelation_eq,if_pos rfl]
  have hle : signCorrelation (1 : ι → ℤˣ) ((1 : H) : ι → ℤˣ) ≤
      ∑ h : H, signCorrelation (1 : ι → ℤˣ) (h : ι → ℤˣ) :=
    Finset.single_le_sum
      (f := fun h : H => signCorrelation (1 : ι → ℤˣ) (h : ι → ℤˣ))
      (s := Finset.univ) (fun h _ => signCorrelation_nonneg 1 (h : ι → ℤˣ))
      (Finset.mem_univ (1 : H))
  rw [hterm] at hle
  exact (pow_pos (by norm_num : (0 : ℤ) < 2) _).trans_le hle

private theorem signCorrelation_sum_eq {ι : Type*} [Fintype ι]
    (H : Subgroup (ι → ℤˣ)) [Fintype H] (ε : ι → ℤˣ)
    (hε : ∀ S : Finset ι, (∀ h ∈ H, signProduct S h = 1) → signProduct S ε = 1) :
    (∑ h : H, signCorrelation ε (h : ι → ℤˣ)) =
      ∑ h : H, signCorrelation (1 : ι → ℤˣ) (h : ι → ℤˣ) := by
  classical
  rw [signCorrelation_sum,signCorrelation_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases htriv : ∀ h : H, signProduct S h = 1
  · rw [hε S (fun h hh => htriv ⟨h,hh⟩),map_one]
  · have hsum : ∑ h : H, (signProduct S h : ℤ) = 0 := by
      apply sign_sum_eq_zero ((signProduct S).comp H.subtype)
      push Not at htriv
      exact htriv
    rw [hsum,mul_zero,mul_zero]

/-- Matching all annihilators forces the diagonal indicator to have positive total mass. -/
private theorem finite_sign_subgroup_mem {ι : Type*} [Fintype ι]
    (H : Subgroup (ι → ℤˣ)) (ε : ι → ℤˣ)
    (hε : ∀ S : Finset ι, (∀ h ∈ H, signProduct S h = 1) → signProduct S ε = 1) :
    ε ∈ H := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have heq := signCorrelation_sum_eq H ε hε
  by_contra hnot
  have hz : (∑ h : H, signCorrelation ε (h : ι → ℤˣ)) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    rw [signCorrelation_eq,if_neg]
    intro he
    exact hnot (he.symm ▸ h.property)
  have hp := signCorrelation_one_sum_pos H
  rw [← heq,hz] at hp
  exact (lt_irrefl (0 : ℤ)) hp

private theorem signProduct_map {ι κ : Type*} (e : ι ↪ κ) (S : Finset ι) (ε : κ → ℤˣ) :
    signProduct (S.map e) ε = signProduct S (fun i => ε (e i)) := by
  exact Finset.prod_map S e ε

/-- Finite-product characters determine the complete image of a compact sign action. -/
theorem compact_sign_image_iff {G ι : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (φ : G →* (ι → ℤˣ)) (hφ : Continuous φ) (ε : ι → ℤˣ) :
    ε ∈ Set.range φ ↔
      ∀ S : Finset ι, (∀ g : G, ∏ i ∈ S, φ g i = 1) → ∏ i ∈ S, ε i = 1 := by
  classical
  constructor
  · rintro ⟨g,rfl⟩ S hS
    exact hS g
  · intro hε
    -- Finite character separation realizes each finite set of coordinates.
    have hfinite : ∀ S : Finset ι, ∃ g : G, ∀ i ∈ S, φ g i = ε i := by
      intro S
      let ψ : G →* (S → ℤˣ) :=
        { toFun g i := φ g i.val
          map_one' := by funext i; exact congrFun φ.map_one i.val
          map_mul' g h := by funext i; exact congrFun (φ.map_mul g h) i.val }
      have hmem : (fun i : S => ε i.val) ∈ ψ.range := by
        apply finite_sign_subgroup_mem ψ.range
        intro T hT
        let e : S ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
        let U := T.map e
        have hU : ∀ g : G, ∏ i ∈ U, φ g i = 1 := by
          intro g
          change signProduct (T.map e) (φ g) = 1
          rw [signProduct_map]
          exact hT (ψ g) ⟨g,rfl⟩
        have he := hε U hU
        change signProduct (T.map e) ε = 1 at he
        rw [signProduct_map] at he
        exact he
      obtain ⟨g,hg⟩ := hmem
      exact ⟨g,fun i hi => congrFun hg ⟨i,hi⟩⟩
    -- Closed coordinate fibres have the finite-intersection property.
    let C : ι → Set G := fun i => {g | φ g i = ε i}
    have hC : ∀ i, IsClosed (C i) := fun i =>
      isClosed_eq ((continuous_apply i).comp hφ) continuous_const
    have hF : ∀ S : Finset ι, (⋂ i ∈ S, C i).Nonempty := by
      intro S
      obtain ⟨g,hg⟩ := hfinite S
      exact ⟨g,Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi => hg i hi⟩
    obtain ⟨g,hg⟩ := CompactSpace.iInter_nonempty hC hF
    exact ⟨g,funext fun i => Set.mem_iInter.mp hg i⟩

/-- Simultaneous sign action on any family of nonzero source square roots. -/
def radicalSignAction {K L ι : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i))
    (hb : ∀ i, b i ≠ 0) : (L ≃ₐ[K] L) →* (ι → ℤˣ) where
  toFun σ i := sourceRootSign (b i) (a i) (hs i) (hb i) σ
  map_one' := by funext i; exact map_one _
  map_mul' σ τ := by funext i; exact map_mul _ σ τ

/-- Each radical sign, hence the entire product action, is Krull-continuous. -/
theorem radicalSignAction_continuous {K L ι : Type*} [Field K] [Field L] [CharZero L]
    [Algebra K L] [Algebra.IsAlgebraic K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i))
    (hb : ∀ i, b i ≠ 0) : Continuous (radicalSignAction b a hs hb) :=
  continuous_pi fun i => sourceRootSign_continuous (b i) (a i) (hs i) (hb i)

private def signCast (L : Type*) [Field L] : ℤˣ →* L where
  toFun u := ((u : ℤ) : L)
  map_one' := by simp only [Units.val_one,Int.cast_one]
  map_mul' u v := by simp only [Units.val_mul,Int.cast_mul]

private theorem signCast_injective (L : Type*) [Field L] [CharZero L] :
    Function.Injective (signCast L) := by
  intro u v h
  apply Units.ext
  exact Int.cast_injective h

private theorem radical_product_action {K L ι : Type*} [Field K] [Field L] [CharZero L]
    [Algebra K L] (b : ι → L) (a : ι → K)
    (hs : ∀ i, b i^2 = algebraMap K L (a i)) (hb : ∀ i, b i ≠ 0)
    (S : Finset ι) (σ : L ≃ₐ[K] L) :
    σ (∏ i ∈ S, b i) = signCast L (∏ i ∈ S, radicalSignAction b a hs hb σ i)*(∏ i ∈ S, b i) := by
  calc
    σ (∏ i ∈ S, b i) = ∏ i ∈ S, σ (b i) := map_prod σ b S
    _ = ∏ i ∈ S, signCast L (radicalSignAction b a hs hb σ i)*b i := by
      apply Finset.prod_congr rfl
      intro i _
      exact sourceRootSign_action (b i) (a i) (hs i) (hb i) σ
    _ = (∏ i ∈ S, signCast L (radicalSignAction b a hs hb σ i))*(∏ i ∈ S, b i) :=
      Finset.prod_mul_distrib
    _ = _ := by rw [← map_prod]

private theorem radical_product_square {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i)) (S : Finset ι) :
    (∏ i ∈ S, b i)^2 = algebraMap K L (∏ i ∈ S, a i) := by
  rw [← Finset.prod_pow,map_prod]
  exact Finset.prod_congr rfl (fun i _ => hs i)

/-- A product sign is trivial exactly when the corresponding radicand product is a source square. -/
theorem radical_product_trivial_iff_square {K L ι : Type*}
    [Field K] [Field L] [CharZero L] [Algebra K L] [IsGalois K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i))
    (hb : ∀ i, b i ≠ 0) (S : Finset ι) :
    (∀ σ : L ≃ₐ[K] L, ∏ i ∈ S, radicalSignAction b a hs hb σ i = 1) ↔
      IsSquare (∏ i ∈ S, a i) := by
  have hsq := radical_product_square b a hs S
  have hprod : (∏ i ∈ S, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  constructor
  · intro h
    have hfix : ∀ σ : L ≃ₐ[K] L, σ (∏ i ∈ S, b i) = ∏ i ∈ S, b i := by
      intro σ
      rw [radical_product_action b a hs hb S σ,h σ,map_one,one_mul]
    obtain ⟨k,hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (∏ i ∈ S, b i)).mpr hfix
    refine ⟨k,?_⟩
    apply (algebraMap K L).injective
    rw [map_mul,hk,← pow_two,hsq]
  · rintro ⟨k,hk⟩ σ
    have hs' : (∏ i ∈ S, b i)^2 = (algebraMap K L k)^2 := by
      rw [hsq,hk,map_mul,pow_two]
    have hfix : σ (∏ i ∈ S, b i) = ∏ i ∈ S, b i := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs' with he | he
      · rw [he,σ.commutes]
      · rw [he,map_neg,σ.commutes]
    apply signCast_injective L
    rw [map_one]
    apply mul_right_cancel₀ hprod
    rw [one_mul,← radical_product_action b a hs hb S σ,hfix]

/-- Square-class relations characterize every simultaneous sign action on the whole Galois extension. -/
theorem radicalSignAction_mem_range_iff {K L ι : Type*}
    [Field K] [Field L] [CharZero L] [Algebra K L] [IsGalois K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i))
    (hb : ∀ i, b i ≠ 0) (ε : ι → ℤˣ) :
    ε ∈ Set.range (radicalSignAction b a hs hb) ↔
      ∀ S : Finset ι, IsSquare (∏ i ∈ S, a i) → ∏ i ∈ S, ε i = 1 := by
  rw [compact_sign_image_iff _ (radicalSignAction_continuous b a hs hb)]
  constructor
  · intro h S hS
    exact h S ((radical_product_trivial_iff_square b a hs hb S).mpr hS)
  · intro h S hS
    exact h S ((radical_product_trivial_iff_square b a hs hb S).mp hS)

/-- Signs determine the automorphism when the radicals generate the entire field. -/
theorem radicalSignAction_injective {K L ι : Type*}
    [Field K] [Field L] [CharZero L] [Algebra K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i))
    (hb : ∀ i, b i ≠ 0) (hgen : IntermediateField.adjoin K (Set.range b) = ⊤) :
    Function.Injective (radicalSignAction b a hs hb) := by
  intro σ τ hστ
  have hroot (i : ι) : σ (b i) = τ (b i) := by
    rw [sourceRootSign_action (b i) (a i) (hs i) (hb i) σ,
      sourceRootSign_action (b i) (a i) (hs i) (hb i) τ]
    have he := congrFun hστ i
    change sourceRootSign (b i) (a i) (hs i) (hb i) σ =
      sourceRootSign (b i) (a i) (hs i) (hb i) τ at he
    rw [he]
  have hext := IntermediateField.algHom_ext_of_eq_adjoin K (S := ⊤) hgen.symm
    (φ₁ := σ.toAlgHom.comp IntermediateField.topEquiv.toAlgHom)
    (φ₂ := τ.toAlgHom.comp IntermediateField.topEquiv.toAlgHom)
    (by rintro _ ⟨i,rfl⟩; exact hroot i)
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun hext ⟨z,trivial⟩

/-- Every compatible sign family extends uniquely through an infinite radical-generated Galois field. -/
theorem radicalSignAction_unique_extension {K L ι : Type*}
    [Field K] [Field L] [CharZero L] [Algebra K L] [IsGalois K L]
    (b : ι → L) (a : ι → K) (hs : ∀ i, b i^2 = algebraMap K L (a i))
    (hb : ∀ i, b i ≠ 0) (hgen : IntermediateField.adjoin K (Set.range b) = ⊤)
    (ε : ι → ℤˣ) :
    (∃! σ : L ≃ₐ[K] L, radicalSignAction b a hs hb σ = ε) ↔
      ∀ S : Finset ι, IsSquare (∏ i ∈ S, a i) → ∏ i ∈ S, ε i = 1 := by
  rw [← radicalSignAction_mem_range_iff b a hs hb ε]
  constructor
  · rintro ⟨σ,hσ,_⟩
    exact ⟨σ,hσ⟩
  · rintro ⟨σ,hσ⟩
    exact ⟨σ,hσ,fun τ hτ => radicalSignAction_injective b a hs hb hgen (hτ.trans hσ.symm)⟩

/-- Imaginary zero offset, as an element of the complete centered extension. -/
def zeroOffsetInExtension (q : XiZeroCopy) : fullFibreZeroExtension :=
  ⟨zeroImaginaryOffset q,zeroImaginaryOffset_mem q⟩

private theorem zeroOffsetInExtension_sq (q : XiZeroCopy) :
    ((zeroOffsetInExtension q : fullFibreZeroExtension) : ℂ)^2 = -(zeroWidth q^2) := by
  change zeroImaginaryOffset q^2 = -(zeroWidth q^2)
  rw [zeroImaginaryOffset_eq,mul_pow]
  have hi : I^2 = -1 := by simpa only [pow_two] using I_mul_I
  rw [hi,neg_one_mul]

private theorem zeroOffsetInExtension_ne_zero (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    zeroOffsetInExtension q ≠ 0 := by
  intro h
  have he := congrArg (fun z : fullFibreZeroExtension => (z : ℂ)) h
  change zeroImaginaryOffset q = 0 at he
  rw [zeroImaginaryOffset_eq] at he
  exact (mul_ne_zero I_ne_zero hq) he

private theorem zeroOffsetInExtension_conjugation (q : XiZeroCopy) :
    fullFibreZeroConjugation (zeroOffsetInExtension q) = -zeroOffsetInExtension q := by
  apply Subtype.ext
  change (starRingEnd ℂ) (zeroImaginaryOffset q) = -zeroImaginaryOffset q
  rw [zeroImaginaryOffset_eq]
  simp only [zeroWidth,map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul]

/-- The source enlarged by every squared width, internal to the full centered field. -/
def widthSquareField : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
  IntermediateField.adjoin fullFibreSourceField (Set.range fun q : XiZeroCopy =>
    zeroOffsetInExtension q^2)

/-- The squared-width field is contained in the full real part. -/
theorem widthSquareField_le_even : widthSquareField ≤ evenWidthInCentered := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨q,rfl⟩
  change ((zeroOffsetInExtension q : fullFibreZeroExtension) : ℂ)^2 ∈ evenWidthField
  rw [zeroOffsetInExtension_sq,pow_two]
  exact evenWidthField.neg_mem (zeroWidth_mul_mem_evenWidthField q q)

/-- Only nonzero widths carry a sign coordinate; repeated divisor copies remain subject to relations. -/
def NonzeroWidthZero := {q : XiZeroCopy // zeroWidth q ≠ 0}

/-- The nonzero imaginary radicals whose signs form the arithmetic kernel. -/
def widthSignRadical (q : NonzeroWidthZero) : fullFibreZeroExtension :=
  zeroOffsetInExtension q.val

/-- Its radicand is the negative squared width in the enlarged source. -/
def widthSignRadicand (q : NonzeroWidthZero) : widthSquareField :=
  ⟨widthSignRadical q^2,IntermediateField.subset_adjoin _ _ ⟨q.val,rfl⟩⟩

private theorem widthSignRadical_ne_zero (q : NonzeroWidthZero) : widthSignRadical q ≠ 0 :=
  zeroOffsetInExtension_ne_zero q.val q.property

private theorem widthSignRadical_sq (q : NonzeroWidthZero) :
    widthSignRadical q^2 = algebraMap widthSquareField fullFibreZeroExtension (widthSignRadicand q) :=
  rfl

/-- These radicals generate the entire centered field over its squared-width source. -/
theorem widthSignRadicals_adjoin_top :
    IntermediateField.adjoin widthSquareField (Set.range widthSignRadical) = ⊤ := by
  let H := IntermediateField.adjoin widthSquareField (Set.range widthSignRadical)
  have hroot (q : XiZeroCopy) : centeredZeroInFibreExtension q ∈ H := by
    have hoff : zeroOffsetInExtension q ∈ H := by
      by_cases hq : zeroWidth q = 0
      · have he : zeroOffsetInExtension q = 0 := by
          apply Subtype.ext
          change zeroImaginaryOffset q = 0
          rw [zeroImaginaryOffset_eq,hq,mul_zero]
        rw [he]
        exact H.zero_mem
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨q,hq⟩,rfl⟩
    let t : fullFibreSourceField :=
      ⟨((xiSpectralPoint q).re : ℂ),ordinate_mem_fullFibreSourceField q⟩
    have ht : algebraMap fullFibreSourceField fullFibreZeroExtension t ∈ H := by
      rw [IsScalarTower.algebraMap_apply fullFibreSourceField widthSquareField fullFibreZeroExtension]
      exact H.algebraMap_mem _
    have he : centeredZeroInFibreExtension q =
        algebraMap fullFibreSourceField fullFibreZeroExtension t+zeroOffsetInExtension q := by
      apply Subtype.ext
      change xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ)+zeroImaginaryOffset q
      rw [zeroImaginaryOffset]
      ring
    rw [he]
    exact H.add_mem ht hoff
  have hle : fullFibreZeroExtension ≤
      (H.restrictScalars fullFibreSourceField).map (IntermediateField.val fullFibreZeroExtension) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨q,rfl⟩
    exact ⟨centeredZeroInFibreExtension q,hroot q,rfl⟩
  apply top_unique
  intro z _
  obtain ⟨a,ha,he⟩ := hle z.property
  have haz : a = z := Subtype.ext he
  exact haz ▸ ha

instance widthSquareField_isGalois : IsGalois widthSquareField fullFibreZeroExtension := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  infer_instance

/-- The full arithmetic sign action over the squared-width source. -/
def widthKernelSignAction :
    (fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension) →* (NonzeroWidthZero → ℤˣ) :=
  radicalSignAction widthSignRadical widthSignRadicand widthSignRadical_sq widthSignRadical_ne_zero

/-- Every arithmetic sign family is determined exactly by all squared-width relations. -/
theorem widthKernelSignAction_unique_extension (ε : NonzeroWidthZero → ℤˣ) :
    (∃! σ : fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension,
      widthKernelSignAction σ = ε) ↔
      ∀ S : Finset NonzeroWidthZero, IsSquare (∏ q ∈ S, widthSignRadicand q) →
        ∏ q ∈ S, ε q = 1 :=
  radicalSignAction_unique_extension widthSignRadical widthSignRadicand widthSignRadical_sq
    widthSignRadical_ne_zero widthSignRadicals_adjoin_top ε

/-- The kernel action retains the full Krull topology as a closed sign subgroup. -/
theorem widthKernelSignAction_continuous : Continuous widthKernelSignAction :=
  radicalSignAction_continuous widthSignRadical widthSignRadicand widthSignRadical_sq
    widthSignRadical_ne_zero

/-- The full squared-width sign image is closed. -/
theorem widthKernelSignAction_range_isClosed : IsClosed (Set.range widthKernelSignAction) :=
  (isCompact_range widthKernelSignAction_continuous).isClosed

/-- Centered conjugation fixes the entire squared-width source. -/
def widthSquareConjugation : fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension where
  __ := fullFibreZeroConjugation.toRingEquiv
  commutes' a := by
    apply Subtype.ext
    obtain ⟨r,hr⟩ := evenWidthField_le_real (widthSquareField_le_even a.property)
    change (r : ℂ) = ((a : fullFibreZeroExtension) : ℂ) at hr
    change (starRingEnd ℂ) ((a : fullFibreZeroExtension) : ℂ) = ((a : fullFibreZeroExtension) : ℂ)
    rw [← hr]
    exact Complex.conj_ofReal r

/-- Uniform sign reversal is the actual conjugation action in the full arithmetic kernel. -/
theorem widthKernelSignAction_conjugation :
    widthKernelSignAction widthSquareConjugation = fun _ => -1 := by
  funext q
  change sourceRootSign (widthSignRadical q) (widthSignRadicand q)
    (widthSignRadical_sq q) (widthSignRadical_ne_zero q) widthSquareConjugation = -1
  have hn : sourceRootSign (widthSignRadical q) (widthSignRadicand q)
      (widthSignRadical_sq q) (widthSignRadical_ne_zero q) widthSquareConjugation ≠ 1 := by
    intro h
    have he := (sourceRootSign_eq_one_iff (widthSignRadical q) (widthSignRadicand q)
      (widthSignRadical_sq q) (widthSignRadical_ne_zero q) widthSquareConjugation).mp h
    have hc : widthSquareConjugation (widthSignRadical q) = -widthSignRadical q :=
      zeroOffsetInExtension_conjugation q.val
    rw [hc] at he
    apply widthSignRadical_ne_zero q
    linear_combination (-1/2 : fullFibreZeroExtension)*he
  exact (Int.units_eq_one_or _).resolve_left hn

/-- A source-square relation among imaginary radicands contains an even number of factors. -/
theorem widthKernelRelation_even (S : Finset NonzeroWidthZero)
    (hS : IsSquare (∏ q ∈ S, widthSignRadicand q)) : Even S.card := by
  have he := (radical_product_trivial_iff_square widthSignRadical widthSignRadicand
    widthSignRadical_sq widthSignRadical_ne_zero S).mpr hS widthSquareConjugation
  change (∏ q ∈ S, widthKernelSignAction widthSquareConjugation q) = 1 at he
  rw [widthKernelSignAction_conjugation,Finset.prod_const] at he
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp he

/-- The intrinsic source subgroup consists exactly of automorphisms fixing every squared width. -/
theorem widthSquareField_fixingSubgroup_iff
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    σ ∈ widthSquareField.fixingSubgroup ↔
      ∀ q : XiZeroCopy, σ (zeroOffsetInExtension q^2) = zeroOffsetInExtension q^2 := by
  constructor
  · intro h q
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h _
      (IntermediateField.subset_adjoin _ _ ⟨q,rfl⟩)
  · intro h
    have hext := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
      (S := widthSquareField) rfl
      (φ₁ := σ.toAlgHom.comp (IntermediateField.val widthSquareField))
      (φ₂ := IntermediateField.val widthSquareField)
      (by rintro _ ⟨q,rfl⟩; exact h q)
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro z hz
    exact DFunLike.congr_fun hext ⟨z,hz⟩

/-- Compatible signs are exactly the annihilator of all actual squared-width relations. -/
def widthRelationSigns : Subgroup (NonzeroWidthZero → ℤˣ) where
  carrier := {ε | ∀ S : Finset NonzeroWidthZero,
    IsSquare (∏ q ∈ S, widthSignRadicand q) → ∏ q ∈ S, ε q = 1}
  one_mem' := by intro S _; simp only [Pi.one_apply,Finset.prod_const_one]
  mul_mem' := by
    intro ε η hε hη S hS
    change signProduct S (ε*η) = 1
    rw [map_mul,show signProduct S ε = 1 from hε S hS,
      show signProduct S η = 1 from hη S hS,mul_one]
  inv_mem' := by
    intro ε hε S hS
    change signProduct S ε⁻¹ = 1
    rw [map_inv,show signProduct S ε = 1 from hε S hS,inv_one]

/-- The sign action with its exact arithmetic codomain. -/
def widthKernelSignCoordinates :
    (fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension) →* widthRelationSigns where
  toFun σ := ⟨widthKernelSignAction σ,fun S hS =>
    (radical_product_trivial_iff_square widthSignRadical widthSignRadicand
      widthSignRadical_sq widthSignRadical_ne_zero S).mpr hS σ⟩
  map_one' := Subtype.ext (map_one widthKernelSignAction)
  map_mul' σ τ := Subtype.ext (map_mul widthKernelSignAction σ τ)

theorem widthKernelSignCoordinates_bijective : Function.Bijective widthKernelSignCoordinates := by
  constructor
  · intro σ τ h
    apply radicalSignAction_injective widthSignRadical widthSignRadicand widthSignRadical_sq
      widthSignRadical_ne_zero widthSignRadicals_adjoin_top
    exact congrArg Subtype.val h
  · intro ε
    obtain ⟨σ,hσ,_⟩ := (widthKernelSignAction_unique_extension ε.val).mpr ε.property
    exact ⟨σ,Subtype.ext hσ⟩

/-- The full sign kernel is exactly the annihilator of the squared-width relations. -/
def widthKernelSignEquiv :
    (fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension) ≃* widthRelationSigns :=
  MulEquiv.ofBijective widthKernelSignCoordinates widthKernelSignCoordinates_bijective

/-- The classification preserves the complete Krull topology. -/
def widthKernelSignHomeomorph :
    (fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension) ≃ₜ widthRelationSigns := by
  let hc : Continuous widthKernelSignCoordinates :=
    widthKernelSignAction_continuous.subtype_mk _
  exact Continuous.homeoOfEquivCompactToT2 (f := widthKernelSignEquiv.toEquiv) hc

private theorem source_aut_offset_image
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) (q : XiZeroCopy) :
    ∃ q' : XiZeroCopy, σ (zeroOffsetInExtension q) = zeroOffsetInExtension q' := by
  obtain ⟨q',hq',he⟩ := fullFibre_aut_preserves_ordinate σ q
  have hre := (mem_ordinateFibreCopies _ _).mp hq'
  let t : fullFibreSourceField :=
    ⟨((xiSpectralPoint q).re : ℂ),ordinate_mem_fullFibreSourceField q⟩
  have hoff : zeroOffsetInExtension q = centeredZeroInFibreExtension q-
      algebraMap fullFibreSourceField fullFibreZeroExtension t := rfl
  refine ⟨q',?_⟩
  rw [hoff,map_sub,σ.commutes]
  apply Subtype.ext
  change (σ (centeredZeroInFibreExtension q) : ℂ)-((xiSpectralPoint q).re : ℂ) =
    xiSpectralPoint q'-((xiSpectralPoint q').re : ℂ)
  rw [he,hre]

/-- Conjugation by a source automorphism permutes the squared-offset stabilizers. -/
instance widthSquareField_fixingSubgroup_normal : widthSquareField.fixingSubgroup.Normal := by
  constructor
  intro τ hτ σ
  apply (widthSquareField_fixingSubgroup_iff _).mpr
  intro q
  obtain ⟨q',hq'⟩ := source_aut_offset_image σ⁻¹ q
  have hp : σ.symm (zeroOffsetInExtension q^2) = zeroOffsetInExtension q'^2 := by
    rw [map_pow]
    exact congrArg (fun z : fullFibreZeroExtension => z^2) hq'
  have ht := (widthSquareField_fixingSubgroup_iff τ).mp hτ q'
  change σ (τ (σ.symm (zeroOffsetInExtension q^2))) = zeroOffsetInExtension q^2
  rw [hp,ht,← hp,σ.apply_symm_apply]

/-- The entire squared-width field is normal over the original complete-fibre source. -/
instance widthSquareField_normal : Normal fullFibreSourceField widthSquareField := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  have hn : Normal fullFibreSourceField
      (IntermediateField.fixedField widthSquareField.fixingSubgroup) := inferInstance
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hn
  exact hn

/-- Restriction to squared widths is the quotient action after forgetting all radical signs. -/
def widthSquareRestriction :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      (widthSquareField ≃ₐ[fullFibreSourceField] widthSquareField) :=
  AlgEquiv.restrictNormalHom widthSquareField

theorem widthSquareRestriction_surjective : Function.Surjective widthSquareRestriction :=
  AlgEquiv.restrictNormalHom_surjective fullFibreZeroExtension

theorem widthSquareRestriction_continuous : Continuous widthSquareRestriction :=
  InfiniteGalois.restrictNormalHom_continuous widthSquareField

/-- The restriction kernel is exactly the intrinsic subgroup fixing all squared widths. -/
theorem widthSquareRestriction_ker :
    widthSquareRestriction.ker = widthSquareField.fixingSubgroup := by
  ext σ
  change widthSquareRestriction σ = 1 ↔ σ ∈ widthSquareField.fixingSubgroup
  constructor
  · intro h
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro z hz
    have he := congrArg (fun τ : widthSquareField ≃ₐ[fullFibreSourceField] widthSquareField =>
      (τ ⟨z,hz⟩ : fullFibreZeroExtension)) h
    have hc := AlgEquiv.restrictNormal_commutes σ widthSquareField ⟨z,hz⟩
    exact hc.symm.trans he
  · intro h
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    have hc := AlgEquiv.restrictNormal_commutes σ widthSquareField z
    exact hc.trans ((IntermediateField.mem_fixingSubgroup_iff _ _).mp h z z.property)

/-- The radical Galois group embeds in the original source group without changing its field action. -/
def widthKernelSourceEmbedding :
    (fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension) →*
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) where
  toFun σ := σ.restrictScalars fullFibreSourceField
  map_one' := rfl
  map_mul' _ _ := rfl

theorem widthKernelSourceEmbedding_injective : Function.Injective widthKernelSourceEmbedding := by
  intro σ τ h
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun g : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension => g z) h

/-- The explicit sign group is exactly the kernel of the full squared-width quotient. -/
theorem widthKernelSourceEmbedding_range :
    widthKernelSourceEmbedding.range = widthSquareRestriction.ker := by
  rw [widthSquareRestriction_ker]
  ext σ
  constructor
  · rintro ⟨τ,rfl⟩
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro z hz
    exact τ.commutes (⟨z,hz⟩ : widthSquareField)
  · intro h
    let τ : fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension :=
      { __ := σ.toRingEquiv
        commutes' a := (IntermediateField.mem_fixingSubgroup_iff _ _).mp h a a.property }
    exact ⟨τ,by apply AlgEquiv.ext; intro z; rfl⟩

/-- Each sign coordinate is the actual scalar action on the corresponding imaginary zero offset. -/
theorem widthKernelSignAction_on_offset
    (σ : fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension)
    (q : NonzeroWidthZero) :
    σ (widthSignRadical q) = ((widthKernelSignAction σ q : ℤ) : fullFibreZeroExtension)*
      widthSignRadical q :=
  sourceRootSign_action (widthSignRadical q) (widthSignRadicand q)
    (widthSignRadical_sq q) (widthSignRadical_ne_zero q) σ

/-- The kernel embedding preserves Krull topology: a primitive element controls each finite source field. -/
theorem widthKernelSourceEmbedding_continuous : Continuous widthKernelSourceEmbedding := by
  apply continuous_of_continuousAt_one widthKernelSourceEmbedding
  change Filter.Tendsto widthKernelSourceEmbedding (nhds 1)
    (nhds (widthKernelSourceEmbedding 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨E,hE,hEU⟩ :=
    (krullTopology_mem_nhds_one_iff fullFibreSourceField fullFibreZeroExtension U).mp hU
  letI : FiniteDimensional fullFibreSourceField E := hE
  let pb := Field.powerBasisOfFiniteOfSeparable fullFibreSourceField E
  let x : fullFibreZeroExtension := (pb.gen : E)
  have hfix : ∀ᶠ σ in nhds (1 : fullFibreZeroExtension ≃ₐ[widthSquareField] fullFibreZeroExtension),
      σ x = x :=
    (stabilizer_isOpen_of_isIntegral (K := widthSquareField) (L := fullFibreZeroExtension) x).mem_nhds
      (Subgroup.one_mem _)
  apply hfix.mono
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
  intro z hz
  obtain ⟨p,_,hp⟩ := pb.exists_eq_aeval (⟨z,hz⟩ : E)
  have hzp : z = Polynomial.aeval x p := by
    have hv := congrArg (fun r : E => (r : fullFibreZeroExtension)) hp
    exact hv.trans (Polynomial.aeval_algHom_apply (IntermediateField.val E) pb.gen p).symm
  change widthKernelSourceEmbedding σ z = z
  calc
    widthKernelSourceEmbedding σ z =
        (widthKernelSourceEmbedding σ).toAlgHom (Polynomial.aeval x p) :=
      congrArg (widthKernelSourceEmbedding σ) hzp
    _ = Polynomial.aeval ((widthKernelSourceEmbedding σ).toAlgHom x) p :=
      (Polynomial.aeval_algHom_apply (widthKernelSourceEmbedding σ).toAlgHom x p).symm
    _ = Polynomial.aeval x p := congrArg (fun y : fullFibreZeroExtension => Polynomial.aeval y p) hσ
    _ = z := hzp.symm

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.compact_sign_image_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.radical_product_trivial_iff_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.radicalSignAction_mem_range_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareField_le_even
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSignRadicals_adjoin_top
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSignAction_unique_extension
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSignAction_range_isClosed
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSignAction_conjugation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelRelation_even
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareField_fixingSubgroup_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSignCoordinates_bijective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSignHomeomorph
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareField_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareRestriction_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareRestriction_ker
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSourceEmbedding_range
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthKernelSourceEmbedding_continuous
