import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateResidueLift

/-!
# A label determines an embedding up to inertia

Let `L/F` be Galois over a Dedekind base `A` of `F`, let `W` be a valuation subring of `L` above a
maximal ideal of `A`, and let `σ, τ : E →ₐ[F] L` be two embeddings of a finite extension.  If they

* cut out the same place of `E` (`W.comap σ = W.comap τ`), and
* have the same residue map (`residue W (σ x) = residue W (τ x)` wherever both are integral),

then `τ = i ∘ σ` for an element `i` of the inertia group of `W` over `F`.

```text
exists_mem_inertia_comp_eq
    ** same place + same residues ⟹ the two embeddings differ by inertia **
```

So the fibre of the reduced label through an embedding lies in one inertia orbit, and therefore has
at most `|I|` elements.  For a cover this is the collision count, obtained without computing the
residue degree: the residue degree cancels between the two levels of the tower.

The proof composes three steps.  Normality of `L/F` gives some `g₀` with `τ = g₀ ∘ σ`
(`exists_algEquiv_comp_eq`, through `AlgEquiv.liftNormal`).  Equality of places makes `W` and
`W.comap g₀` two valuation subrings of `L` with the same centre on the integral closure of `A` in
`σ(E)`, so `exists_smul_valuationSubring_eq` corrects `g₀` by an element of `Gal(L/σ(E))` — which
does not change `g₀ ∘ σ` — into one that stabilises `W`.  Equality of residues then feeds
`exists_mem_inertia_eq_on_intermediateField`.

## Main results

* `isUnit_valuationSubring_iff`, `isUnit_comap_iff`, `comap_eq_inv_smul`, `comap_ne_top` — the
  elementary dictionary for a translated valuation subring.
* `exists_algEquiv_comp_eq` — two embeddings into a Galois extension differ by a Galois element.
* `exists_mem_inertia_comp_eq` — **the label determines the embedding up to inertia.**
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

open IsLocalRing IsDedekindDomain
open scoped Pointwise
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem isUnit_valuationSubring_iff (W : ValuationSubring L) {y : L} (hy : y ∈ W) :
    IsUnit (⟨y, hy⟩ : W) ↔ y ≠ 0 ∧ y⁻¹ ∈ W := by
  constructor
  · intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have hzc : y * (z : L) = 1 := congrArg Subtype.val hz
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hzc
      exact zero_ne_one hzc
    refine ⟨hy0, ?_⟩
    have : (z : L) = y⁻¹ := by
      field_simp at hzc ⊢
      linear_combination hzc
    rw [← this]
    exact z.2
  · rintro ⟨hy0, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, hinv⟩, Subtype.ext ?_⟩
    show y * y⁻¹ = 1
    field_simp

theorem comap_eq_inv_smul (g : L ≃ₐ[F] L) (W : ValuationSubring L) :
    W.comap (g : L →+* L) = g⁻¹ • W := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · intro hx
    exact ⟨g x, hx, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    have hgg : g (g⁻¹ • a) = a := by simp
    rw [show ((g : L →+* L) (g⁻¹ • a)) = g (g⁻¹ • a) from rfl, hgg]
    exact ha

def comapRingEquiv (g : L ≃ₐ[F] L) (W : ValuationSubring L) :
    (W.comap (g : L →+* L)) ≃+* W where
  toFun x := ⟨g (x : L), x.2⟩
  invFun y := ⟨g.symm (y : L), by
    show (g : L →+* L) (g.symm (y : L)) ∈ W
    rw [show ((g : L →+* L) (g.symm (y : L))) = g (g.symm (y : L)) from rfl,
      AlgEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem isUnit_comap_iff (g : L ≃ₐ[F] L) (W : ValuationSubring L)
    {y : L} (hy : y ∈ W.comap (g : L →+* L)) :
    IsUnit (⟨y, hy⟩ : (W.comap (g : L →+* L))) ↔ IsUnit (⟨g y, hy⟩ : W) := by
  constructor
  · intro h
    exact h.map (comapRingEquiv g W)
  · intro h
    have h2 := h.map (comapRingEquiv g W).symm
    have hcoe : ((comapRingEquiv g W).symm ⟨g y, hy⟩ : W.comap (g : L →+* L)) = ⟨y, hy⟩ := by
      apply Subtype.ext
      show g.symm (g y) = y
      simp
    rwa [hcoe] at h2

theorem isUnit_congr (W : ValuationSubring L) {y z : L} (hy : y ∈ W) (hz : z ∈ W) (hyz : y = z) :
    IsUnit (⟨y, hy⟩ : W) ↔ IsUnit (⟨z, hz⟩ : W) := by
  subst hyz
  exact Iff.rfl

theorem comap_ne_top (g : L ≃ₐ[F] L) {W : ValuationSubring L} (hW : W ≠ ⊤) :
    W.comap (g : L →+* L) ≠ ⊤ := by
  intro htop
  refine hW (SetLike.ext fun x => ?_)
  constructor
  · intro _; trivial
  · intro _
    have h1 : g.symm x ∈ W.comap (g : L →+* L) := by rw [htop]; trivial
    have h2 : (g : L →+* L) (g.symm x) ∈ W := h1
    rwa [show ((g : L →+* L) (g.symm x)) = g (g.symm x) from rfl, AlgEquiv.apply_symm_apply] at h2

theorem exists_algEquiv_comp_eq {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]
    [FiniteDimensional F L] [IsGalois F L] (σ τ : E →ₐ[F] L) :
    ∃ g : L ≃ₐ[F] L, ∀ x : E, τ x = g (σ x) := by
  haveI : Normal F L := inferInstance
  let χ : σ.fieldRange ≃ₐ[F] τ.fieldRange :=
    (AlgEquiv.ofInjectiveField σ).symm.trans (AlgEquiv.ofInjectiveField τ)
  refine ⟨χ.liftNormal L, fun x => ?_⟩
  have hσ : σ x = algebraMap (σ.fieldRange) L (AlgEquiv.ofInjectiveField σ x) := rfl
  have h := χ.liftNormal_commutes L (AlgEquiv.ofInjectiveField σ x)
  rw [hσ, h]
  have hχ : χ (AlgEquiv.ofInjectiveField σ x) = AlgEquiv.ofInjectiveField τ x := by
    show AlgEquiv.ofInjectiveField τ ((AlgEquiv.ofInjectiveField σ).symm
        (AlgEquiv.ofInjectiveField σ x)) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [hχ]
  rfl

theorem restrictScalars_smul_valuationSubring (M : IntermediateField F L)
    (h : L ≃ₐ[M] L) (X : ValuationSubring L) :
    (AlgEquiv.restrictScalars F h) • X = h • X := rfl


section Main

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A F] [IsFractionRing A F]
variable [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L]
variable {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]

/-- **Two embeddings with the same place and the same residue map differ by inertia.** -/
theorem exists_mem_inertia_comp_eq
    (σ τ : E →ₐ[F] L) (W : ValuationSubring L) (hAW : ∀ a : A, algebraMap A L a ∈ W)
    (hW : W ≠ ⊤) (p : Ideal A) [p.IsMaximal] (hp0 : p ≠ ⊥)
    (hcentA : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ p)
    (hplace : W.comap (σ : E →+* L) = W.comap (τ : E →+* L))
    (hres : ∀ (x : E) (hσx : σ x ∈ W) (hτx : τ x ∈ W),
      residue W ⟨σ x, hσx⟩ = residue W ⟨τ x, hτx⟩) :
    ∃ i : L ≃ₐ[F] L,
      i ∈ (centerPrime W (integralClosureTop_mem W hAW)).inertia (L ≃ₐ[F] L) ∧
      ∀ x : E, τ x = i (σ x) := by
  classical
  haveI : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A F L (integralClosure A L)
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F L (integralClosure A L)
  have hSW := integralClosureTop_mem (A := A) W hAW
  obtain ⟨g0, hg0⟩ := exists_algEquiv_comp_eq σ τ
  set M : IntermediateField F L := σ.fieldRange with hMdef
  haveI : IsDedekindDomain (integralClosure A M) :=
    IsIntegralClosure.isDedekindDomain A F M (integralClosure A M)
  haveI : IsFractionRing (integralClosure A M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F M (integralClosure A M)
  -- membership and unit transfer between the two embeddings
  have hmem : ∀ y : E, σ y ∈ W ↔ τ y ∈ W := by
    intro y
    constructor
    · intro hy
      have h1 : y ∈ W.comap (σ : E →+* L) := hy
      rw [hplace] at h1
      exact h1
    · intro hy
      have h1 : y ∈ W.comap (τ : E →+* L) := hy
      rw [← hplace] at h1
      exact h1
  have hunit : ∀ (x : E) (hσx : σ x ∈ W) (hτx : τ x ∈ W),
      (IsUnit (⟨σ x, hσx⟩ : W) ↔ IsUnit (⟨τ x, hτx⟩ : W)) := by
    intro x hσx hτx
    rw [isUnit_valuationSubring_iff W hσx, isUnit_valuationSubring_iff W hτx]
    have hσinv : (σ x)⁻¹ = σ x⁻¹ := (map_inv₀ (σ : E →+* L) x).symm
    have hτinv : (τ x)⁻¹ = τ x⁻¹ := (map_inv₀ (τ : E →+* L) x).symm
    rw [hσinv, hτinv]
    have hz : σ x ≠ 0 ↔ τ x ≠ 0 := by
      constructor
      · intro hne h0
        exact hne (by rw [(map_eq_zero (τ : E →+* L)).mp h0, map_zero])
      · intro hne h0
        exact hne (by rw [(map_eq_zero (σ : E →+* L)).mp h0, map_zero])
    rw [hz, hmem x⁻¹]
  -- the two valuation subrings over the intermediate field
  have hRW₂ : ∀ r : integralClosure A M, algebraMap (integralClosure A M) L r ∈ W :=
    intermediateBase_mem M W hAW
  have hint : ∀ r : integralClosure A M, IsIntegral A (algebraMap (integralClosure A M) L r) :=
    fun r => r.property.map (IsScalarTower.toAlgHom A M L)
  have hRW₁ : ∀ r : integralClosure A M,
      algebraMap (integralClosure A M) L r ∈ W.comap (g0 : L →+* L) := by
    intro r
    show (g0 : L →+* L) (algebraMap (integralClosure A M) L r) ∈ W
    exact mem_of_isIntegral W hAW
      ((hint r).map ((g0 : L ≃ₐ[F] L).toAlgHom.restrictScalars A))
  have hcent₂ : ∀ r : integralClosure A M,
      (¬ IsUnit (⟨algebraMap (integralClosure A M) L r, hRW₂ r⟩ : W))
        ↔ r ∈ intermediateCentre M W hAW :=
    fun r => (mem_intermediateCentre_iff M W hAW r).symm
  have hcent₁ : ∀ r : integralClosure A M,
      (¬ IsUnit (⟨algebraMap (integralClosure A M) L r, hRW₁ r⟩ :
        (W.comap (g0 : L →+* L))))
        ↔ r ∈ intermediateCentre M W hAW := by
    intro r
    rw [isUnit_comap_iff]
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp ((r : M).2)
    have hxL : algebraMap (integralClosure A M) L r = σ x := hx.symm
    have hgx : (g0 : L ≃ₐ[F] L) (algebraMap (integralClosure A M) L r) = τ x := by
      rw [hxL, ← hg0 x]
    have hσx : σ x ∈ W := hxL ▸ hRW₂ r
    have hτx : τ x ∈ W :=
      hgx ▸ (hRW₁ r : (g0 : L ≃ₐ[F] L) (algebraMap (integralClosure A M) L r) ∈ W)
    calc (¬ IsUnit (⟨(g0 : L ≃ₐ[F] L) (algebraMap (integralClosure A M) L r), hRW₁ r⟩ : W))
        ↔ ¬ IsUnit (⟨τ x, hτx⟩ : W) := not_congr (isUnit_congr W _ hτx hgx)
      _ ↔ ¬ IsUnit (⟨σ x, hσx⟩ : W) := not_congr (hunit x hσx hτx).symm
      _ ↔ ¬ IsUnit (⟨algebraMap (integralClosure A M) L r, hRW₂ r⟩ : W) :=
            not_congr (isUnit_congr W hσx (hRW₂ r) hxL.symm)
      _ ↔ r ∈ intermediateCentre M W hAW := hcent₂ r
  haveI : (intermediateCentre M W hAW).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (intermediateCentre_ne_bot M W hAW p hp0 hcentA)
  obtain ⟨h, hh⟩ := exists_smul_valuationSubring_eq
    (R := integralClosure A M) (T := integralClosure A L) (M : Type _)
    (intermediateCentre M W hAW) (comap_ne_top g0 hW) hW hRW₁ hRW₂ hcent₁ hcent₂
  set hFe : L ≃ₐ[F] L := AlgEquiv.restrictScalars F h with hFedef
  have hsm : hFe • (W.comap (g0 : L →+* L)) = W := by
    rw [hFedef, restrictScalars_smul_valuationSubring]
    exact hh
  rw [comap_eq_inv_smul] at hsm
  have hsm2 : (hFe * g0⁻¹) • W = W := by rw [mul_smul]; exact hsm
  set g' : L ≃ₐ[F] L := g0 * hFe⁻¹ with hg'def
  have hone : (g0 * hFe⁻¹) * (hFe * g0⁻¹) = 1 := by group
  have hg'W : g' • W = W := by
    calc g' • W = (g0 * hFe⁻¹) • ((hFe * g0⁻¹) • W) := by rw [hsm2, hg'def]
      _ = ((g0 * hFe⁻¹) * (hFe * g0⁻¹)) • W := (mul_smul _ _ _).symm
      _ = W := by rw [hone, one_smul]
  have hg'σ : ∀ x : E, τ x = g' (σ x) := by
    intro x
    have hmemM : σ x ∈ M := AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
    have hfix : hFe⁻¹ (σ x) = σ x := (h⁻¹ : L ≃ₐ[M] L).commutes ⟨σ x, hmemM⟩
    rw [hg'def]
    show τ x = g0 (hFe⁻¹ (σ x))
    rw [hfix]
    exact hg0 x
  have hres' : ∀ b : integralClosure A M,
      g' • (algebraMap (integralClosure A M) (integralClosure A L)) b
          - (algebraMap (integralClosure A M) (integralClosure A L)) b
        ∈ centerPrime W hSW := by
    intro b
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp ((b : M).2)
    have hbL : algebraMap (integralClosure A M) L b = σ x := hx.symm
    have hσx : σ x ∈ W := hbL ▸ hRW₂ b
    have hτx : τ x ∈ W := by
      rw [hg'σ x]
      have hmm : g' (σ x) ∈ g' • W := by
        rw [ValuationSubring.mem_smul_pointwise_iff_exists]
        exact ⟨σ x, hσx, rfl⟩
      rwa [hg'W] at hmm
    rw [mem_centerPrime_iff]
    have hval : toValuationSubring W hSW
        (g' • (algebraMap (integralClosure A M) (integralClosure A L)) b
          - (algebraMap (integralClosure A M) (integralClosure A L)) b)
        = (⟨τ x, hτx⟩ : W) - ⟨σ x, hσx⟩ := by
      apply Subtype.ext
      show algebraMap (integralClosure A L) L
          (g' • (algebraMap (integralClosure A M) (integralClosure A L)) b
            - (algebraMap (integralClosure A M) (integralClosure A L)) b) = τ x - σ x
      rw [map_sub]
      have hb1 : algebraMap (integralClosure A L) L
          ((algebraMap (integralClosure A M) (integralClosure A L)) b) = σ x := hbL
      have hb2 : algebraMap (integralClosure A L) L
          (g' • (algebraMap (integralClosure A M) (integralClosure A L)) b) = τ x := by
        show g' (algebraMap (integralClosure A L) L
          ((algebraMap (integralClosure A M) (integralClosure A L)) b)) = τ x
        rw [hb1, ← hg'σ x]
      rw [hb1, hb2]
    rw [hval, ← IsLocalRing.residue_eq_zero_iff, map_sub,
      sub_eq_zero.mpr (hres x hσx hτx).symm]
  obtain ⟨i, hi, hiM⟩ := exists_mem_inertia_eq_on_intermediateField M W hAW hW hg'W hres'
  refine ⟨i, hi, fun x => ?_⟩
  have hmemM : σ x ∈ M := AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
  have hix := hiM ⟨σ x, hmemM⟩
  rw [hg'σ x]
  exact hix


/-- **The label determines the embedding up to inertia, in valuation-subgroup form.**  The
correcting element is produced inside `W.inertiaSubgroup F`, so no ideal-theoretic action is
mentioned. -/
theorem exists_mem_inertiaSubgroup_comp_eq
    (σ τ : E →ₐ[F] L) (W : ValuationSubring L) (hAW : ∀ a : A, algebraMap A L a ∈ W)
    (hW : W ≠ ⊤) (p : Ideal A) [p.IsMaximal] (hp0 : p ≠ ⊥)
    (hcentA : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ p)
    (hplace : W.comap (σ : E →+* L) = W.comap (τ : E →+* L))
    (hres : ∀ (x : E) (hσx : σ x ∈ W) (hτx : τ x ∈ W),
      residue W ⟨σ x, hσx⟩ = residue W ⟨τ x, hτx⟩) :
    ∃ i : W.decompositionSubgroup F, i ∈ W.inertiaSubgroup F ∧
      ∀ x : E, τ x = ((i : L ≃ₐ[F] L)) (σ x) := by
  haveI : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A F L (integralClosure A L)
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F L (integralClosure A L)
  have hSW := integralClosureTop_mem (A := A) W hAW
  have hact : ∀ (u : L ≃ₐ[F] L) (x : integralClosure A L),
      algebraMap (integralClosure A L) L (u • x)
        = u • algebraMap (integralClosure A L) L x := fun _ _ => rfl
  obtain ⟨i, hi, hiσ⟩ := exists_mem_inertia_comp_eq σ τ W hAW hW p hp0 hcentA hplace hres
  exact ⟨toDecomposition W hSW hact hW hi,
    toDecomposition_mem_inertiaSubgroup W hSW hact hW hi, hiσ⟩

end Main

end ValuationInertia
end GaloisForLFunctions.HTGeometry
