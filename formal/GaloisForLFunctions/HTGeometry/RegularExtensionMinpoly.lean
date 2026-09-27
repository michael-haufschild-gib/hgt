import Mathlib

/-!
# Minimal polynomials over a regular extension

If `k` is relatively algebraically closed in a field `E`, then an element `θ` algebraic over `k`
keeps its minimal polynomial over `E`: `minpoly E θ = minpoly k θ`.  The coefficients of
`minpoly E θ` are integral over `k` because it divides `minpoly k θ`; regularity puts them back in
`k`, and a monic polynomial over `k` with root `θ` is a multiple of `minpoly k θ`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- **Minimal polynomials survive a regular extension.** -/
theorem minpoly_eq_map_of_relAlgClosed {k E L : Type*} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    (hreg : ∀ y : E, IsIntegral k y → y ∈ Set.range (algebraMap k E))
    {θ : L} (hθ : IsIntegral k θ) :
    minpoly E θ = (minpoly k θ).map (algebraMap k E) := by
  have hθE : IsIntegral E θ := hθ.tower_top
  have hdvd : minpoly E θ ∣ (minpoly k θ).map (algebraMap k E) :=
    minpoly.dvd_map_of_isScalarTower k E θ
  have hcoeff : ∀ i, (minpoly E θ).coeff i ∈ Set.range (algebraMap k E) := fun i =>
    hreg _ (isIntegral_coeff_of_dvd (minpoly k θ) (minpoly E θ) (minpoly.monic hθ)
      (minpoly.monic hθE) hdvd i)
  have hlifts : minpoly E θ ∈ lifts (algebraMap k E) := (lifts_iff_coeff_lifts _).mpr hcoeff
  obtain ⟨μ₀, hμ₀, -, hμ₀mon⟩ :=
    lifts_and_degree_eq_and_monic hlifts (minpoly.monic hθE)
  have hroot : aeval θ μ₀ = 0 := by
    rw [← aeval_map_algebraMap E θ μ₀, hμ₀, minpoly.aeval]
  have hdvd' : (minpoly k θ).map (algebraMap k E) ∣ minpoly E θ := by
    rw [← hμ₀]
    exact Polynomial.map_dvd _ (minpoly.dvd k θ hroot)
  exact eq_of_monic_of_associated (minpoly.monic hθE) ((minpoly.monic hθ).map _)
    (associated_of_dvd_dvd hdvd hdvd')

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open IntermediateField

/-- The degree of a two-element adjunction, computed through the first element. -/
theorem finrank_adjoin_pair_eq_mul {K L : Type*} [Field K] [Field L] [Algebra K L] {x y : L}
    (hx : IsIntegral K x) (hy : IsIntegral K y) :
    Module.finrank K K⟮x, y⟯ =
      (minpoly K x).natDegree * (minpoly K⟮x⟯ y).natDegree := by
  have hyx : IsIntegral K⟮x⟯ y := hy.tower_top
  haveI : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
  haveI : FiniteDimensional K⟮x⟯ K⟮x⟯⟮y⟯ := adjoin.finiteDimensional hyx
  haveI : Module.Free K K⟮x⟯ := Module.Free.of_divisionRing K K⟮x⟯
  haveI : Module.Free K⟮x⟯ K⟮x⟯⟮y⟯ := Module.Free.of_divisionRing K⟮x⟯ K⟮x⟯⟮y⟯
  rw [← adjoin_simple_adjoin_simple, ← adjoin.finrank hx, ← adjoin.finrank hyx]
  exact (Module.finrank_mul_finrank K K⟮x⟯ K⟮x⟯⟮y⟯).symm

/-- **Degree exchange.**  If adjoining `x` does not lower the degree of `y`, then adjoining `y`
does not lower the degree of `x`: both products compute `[K(x,y) : K]`. -/
theorem natDegree_minpoly_le_of_exchange {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x y : L} (hx : IsIntegral K x) (hy : IsIntegral K y)
    (h : (minpoly K y).natDegree ≤ (minpoly K⟮x⟯ y).natDegree) :
    (minpoly K x).natDegree ≤ (minpoly K⟮y⟯ x).natDegree := by
  have hxy := finrank_adjoin_pair_eq_mul hx hy
  have hyx := finrank_adjoin_pair_eq_mul hy hx
  rw [Set.pair_comm] at hyx
  have hpos : 0 < (minpoly K⟮x⟯ y).natDegree := minpoly.natDegree_pos hy.tower_top
  have key : (minpoly K x).natDegree * (minpoly K⟮x⟯ y).natDegree ≤
      (minpoly K⟮x⟯ y).natDegree * (minpoly K⟮y⟯ x).natDegree := by
    rw [← hxy, hyx]
    exact Nat.mul_le_mul_right _ h
  rw [mul_comm] at key
  exact Nat.le_of_mul_le_mul_left key hpos

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- A nonzero polynomial over `F₁` vanishing at `θ` through a field map `g : F₁ → F₂` makes `θ`
algebraic over `F₂`. -/
theorem isAlgebraic_of_eval₂ {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω] [Algebra F₂ Ω]
    (g : F₁ →+* F₂) {p : Polynomial F₁} (hp : p ≠ 0) {θ : Ω}
    (hθ : p.eval₂ ((algebraMap F₂ Ω).comp g) θ = 0) : IsAlgebraic F₂ θ :=
  ⟨p.map g, Polynomial.map_ne_zero hp, by rw [aeval_def, eval₂_map]; exact hθ⟩

/-- A nonzero polynomial over `F₁` vanishing at `θ` through a field map `g : F₁ → F₂` bounds the
degree of `θ` over `F₂`. -/
theorem natDegree_minpoly_le_of_eval₂ {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω]
    [Algebra F₂ Ω] (g : F₁ →+* F₂) {p : Polynomial F₁} (hp : p ≠ 0) {θ : Ω}
    (hθ : p.eval₂ ((algebraMap F₂ Ω).comp g) θ = 0) :
    (minpoly F₂ θ).natDegree ≤ p.natDegree := by
  have hroot : aeval θ (p.map g) = 0 := by rw [aeval_def, eval₂_map]; exact hθ
  rw [← natDegree_map_eq_of_injective g.injective p]
  exact natDegree_le_natDegree
    (minpoly.degree_le_of_ne_zero F₂ θ (Polynomial.map_ne_zero hp) hroot)

/-- An element transcendental over `k` stays transcendental over every algebraic extension `K`
embedded over `k`: evaluation `K[X] → Ω` at it is injective. -/
theorem eval₂_injective_of_transcendental {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra.IsAlgebraic k K] (j : K →ₐ[k] Ω) {v : Ω}
    (hv : Transcendental k v) : Function.Injective (eval₂RingHom (j : K →+* Ω) v) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  letI : Algebra K Ω := (j : K →+* Ω).toAlgebra
  haveI : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq fun r => (j.commutes r).symm
  exact hv (IsAlgebraic.restrictScalars k ⟨p, hp0, hp⟩)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Polynomial IntermediateField

/-- A nonzero polynomial over `Ω` whose coefficients come from `E` and which vanishes at `θ` bounds
the degree of `θ` over `E`. -/
theorem natDegree_minpoly_le_of_coeff_mem_range {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    {p : Polynomial Ω} (hp : p ≠ 0) (hcoeff : ∀ n, p.coeff n ∈ Set.range (algebraMap E Ω))
    {θ : Ω} (hroot : p.eval θ = 0) : (minpoly E θ).natDegree ≤ p.natDegree := by
  obtain ⟨q, hq⟩ := (mem_lifts p).mp ((lifts_iff_coeff_lifts p).mpr hcoeff)
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hp (by rw [← hq, Polynomial.map_zero])
  have hqroot : aeval θ q = 0 := by
    rw [aeval_def, ← eval_map, hq, hroot]
  rw [← hq, natDegree_map_eq_of_injective (algebraMap E Ω).injective]
  exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero E θ hq0 hqroot)

/-- **Degree exchange over a regular extension.**  Let `k` be relatively algebraically closed in
`M ⊆ Ω`, let `F₀ ⊆ Ω` contain `k` and lie in `M`, let `w ∈ M` be algebraic over `F₀` and `θ`
algebraic over `k`.  Then adjoining `θ` to `F₀` does not lower the degree of `w`: the degree of `θ`
cannot drop over `F₀(w) ⊆ M`, because over `M` it equals the degree over `k`. -/
theorem natDegree_minpoly_le_adjoin_of_regular {k M F₀ Ω : Type*} [Field k] [Field M] [Field F₀]
    [Field Ω] [Algebra k M] [Algebra M Ω] [Algebra k Ω] [IsScalarTower k M Ω] [Algebra F₀ Ω]
    (hreg : ∀ y : M, IsIntegral k y → y ∈ Set.range (algebraMap k M))
    (g₁ : k →+* F₀) (hg₁ : (algebraMap F₀ Ω).comp g₁ = algebraMap k Ω)
    (hF₀M : ∀ x : F₀, algebraMap F₀ Ω x ∈ (algebraMap M Ω).fieldRange)
    {w θ : Ω} (hwM : w ∈ (algebraMap M Ω).fieldRange) (hw : IsIntegral F₀ w)
    (hθ : IsIntegral k θ) :
    (minpoly F₀ w).natDegree ≤ (minpoly F₀⟮θ⟯ w).natDegree := by
  have hθroot : (minpoly k θ).eval₂ ((algebraMap F₀ Ω).comp g₁) θ = 0 := by
    rw [hg₁]
    exact minpoly.aeval _ _
  have hθF₀ : IsIntegral F₀ θ :=
    (isAlgebraic_of_eval₂ g₁ (minpoly.ne_zero hθ) hθroot).isIntegral
  have hdeg₁ := natDegree_minpoly_le_of_eval₂ g₁ (minpoly.ne_zero hθ) hθroot
  have hdegM : (minpoly M θ).natDegree = (minpoly k θ).natDegree := by
    rw [minpoly_eq_map_of_relAlgClosed hreg hθ]
    exact natDegree_map_eq_of_injective (algebraMap k M).injective _
  let Mimg : IntermediateField F₀ Ω :=
    Subfield.toIntermediateField (algebraMap M Ω).fieldRange hF₀M
  have hle : F₀⟮w⟯ ≤ Mimg := IntermediateField.adjoin_simple_le_iff.mpr hwM
  have hθw : IsIntegral F₀⟮w⟯ θ := hθF₀.tower_top
  have hdeg₂ : (minpoly M θ).natDegree ≤ (minpoly F₀⟮w⟯ θ).natDegree := by
    have h := natDegree_minpoly_le_of_coeff_mem_range (E := M)
      (p := (minpoly F₀⟮w⟯ θ).map (algebraMap F₀⟮w⟯ Ω))
      (Polynomial.map_ne_zero (minpoly.ne_zero hθw))
      (fun n => by
        rw [coeff_map]
        exact RingHom.mem_fieldRange.mp (hle ((minpoly F₀⟮w⟯ θ).coeff n).2))
      (by rw [eval_map, ← aeval_def, minpoly.aeval])
    rwa [natDegree_map_eq_of_injective (algebraMap F₀⟮w⟯ Ω).injective] at h
  exact natDegree_minpoly_le_of_exchange hw hθF₀ (by omega)

/-- An embedding `j : K → Ω` over `k`, with `K = k(θ₀)`, lands in `F₀(j θ₀)` for every field
`F₀ ⊆ Ω` containing `k`. -/
theorem algHom_mem_adjoin_of_primitive {k K F₀ Ω : Type*} [Field k] [Field K] [Field F₀]
    [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra F₀ Ω] [Algebra.IsAlgebraic k K]
    (j : K →ₐ[k] Ω) (g₁ : k →+* F₀) (hg₁ : (algebraMap F₀ Ω).comp g₁ = algebraMap k Ω)
    {θ₀ : K} (hθ₀ : k⟮θ₀⟯ = ⊤) (c : K) : j c ∈ F₀⟮j θ₀⟯ := by
  have hc : c ∈ Algebra.adjoin k {θ₀} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic θ₀), hθ₀]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨p, rfl⟩ := hc
  change j (aeval θ₀ p) ∈ _
  rw [← Polynomial.aeval_algHom_apply]
  have hp : aeval (j θ₀) p = aeval (j θ₀) (p.map g₁) := by
    rw [aeval_def, aeval_def, eval₂_map, hg₁]
  have h := Polynomial.aeval_algebraMap_apply Ω (AdjoinSimple.gen F₀ (j θ₀)) (p.map g₁)
  rw [AdjoinSimple.algebraMap_gen] at h
  rw [hp, h]
  exact SetLike.coe_mem _

/-- The extension of `V ↦ v` to `K(V)` lands in any subfield containing `v` and the image of
`K`. -/
theorem isFractionRing_lift_eval₂_mem {K Ω : Type*} [Field K] [Field Ω] (T : Subfield Ω)
    (j : K →+* Ω) {v : Ω} (hj : ∀ c, j c ∈ T) (hv : v ∈ T)
    (hinj : Function.Injective (eval₂RingHom j v)) (x : RatFunc K) :
    IsFractionRing.lift hinj x ∈ T := by
  have hpoly : ∀ a : Polynomial K, eval₂ j v a ∈ T := by
    intro a
    rw [eval₂_eq_sum_range]
    exact T.sum_mem fun i _ => T.mul_mem (hj _) (T.pow_mem hv _)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (Polynomial K) x
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  exact T.div_mem (hpoly a) (hpoly b)

/-- **Irreducibility from a degree bound.**  Let `pB` be irreducible over `F₀` with root `w`, and
suppose `w` keeps its degree over an extension `T` of `F₀`.  A polynomial `Q` over a field `L`
whose image under a map `L → T` is `pB` is irreducible: a factorization would give `w` a relation
over `T` of smaller degree. -/
theorem irreducible_of_map_eq_of_natDegree_minpoly {F₀ Ω L : Type*} [Field F₀] [Field Ω]
    [Field L] [Algebra F₀ Ω] (T : IntermediateField F₀ Ω) (J : L →+* Ω) (hJ : ∀ x, J x ∈ T)
    {pB : Polynomial F₀} (hirr : Irreducible pB) {w : Ω} (hroot : aeval w pB = 0)
    (hdeg : (minpoly F₀ w).natDegree ≤ (minpoly T w).natDegree) {Q : Polynomial L}
    (hQ : Q.map J = pB.map (algebraMap F₀ Ω)) : Irreducible Q := by
  have hpB0 : pB ≠ 0 := hirr.ne_zero
  have hdegw : (minpoly F₀ w).natDegree = pB.natDegree := by
    rw [← minpoly.eq_of_irreducible hirr hroot,
      natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hpB0))]
  have hpos : 0 < pB.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hQdeg : Q.natDegree = pB.natDegree := by
    rw [← natDegree_map_eq_of_injective J.injective, hQ,
      natDegree_map_eq_of_injective (algebraMap F₀ Ω).injective]
  have hQw : Q.eval₂ J w = 0 := by
    rw [← eval_map, hQ, eval_map, ← aeval_def, hroot]
  have hbound : ∀ a : Polynomial L, a ≠ 0 → a.eval₂ J w = 0 → pB.natDegree ≤ a.natDegree := by
    intro a ha0 hax
    have h := natDegree_minpoly_le_of_coeff_mem_range (E := T) (p := a.map J)
      (Polynomial.map_ne_zero ha0) (fun n => by rw [coeff_map]; exact ⟨⟨_, hJ _⟩, rfl⟩)
      (by rw [eval_map]; exact hax)
    rw [natDegree_map_eq_of_injective J.injective] at h
    omega
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hQdeg
    omega
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    omega
  · by_contra hnot
    push Not at hnot
    obtain ⟨hau, hbu⟩ := hnot
    have ha0 : a ≠ 0 := fun h => hQ0 (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hQ0 (by rw [hab, h, mul_zero])
    have hadeg : a.natDegree ≠ 0 := fun h =>
      hau (isUnit_iff_degree_eq_zero.mpr (by simp [degree_eq_natDegree ha0, h]))
    have hbdeg : b.natDegree ≠ 0 := fun h =>
      hbu (isUnit_iff_degree_eq_zero.mpr (by simp [degree_eq_natDegree hb0, h]))
    have hsum : Q.natDegree = a.natDegree + b.natDegree := by
      rw [hab, natDegree_mul ha0 hb0]
    rw [hab, eval₂_mul, mul_eq_zero] at hQw
    rcases hQw with h | h
    · have := hbound a ha0 h
      omega
    · have := hbound b hb0 h
      omega

/-- **Irreducibility over a finite extension from a regular embedding.**  Let `k` be relatively
algebraically closed in `M ⊆ Ω = Ω̄`, let `F₀ → Ω` be a field embedding over `k` with image in
`M`, let `v ∈ F₀` be transcendental over `k`, and let `w ∈ M` have irreducible polynomial `pB`
over `F₀`.  If a polynomial `R` over `K[V]`, `K` finite over `k`, maps to `pB` under every
evaluation `K[V] → Ω`, `V ↦ v`, over `k`, then `R` is irreducible over `K(V)`. -/
theorem irreducible_map_of_regular_embedding {k M F₀ Ω K : Type*} [Field k] [CharZero k]
    [Field M] [Field F₀] [Field Ω] [IsAlgClosed Ω] [Field K]
    [Algebra k M] [Algebra M Ω] [Algebra k Ω] [IsScalarTower k M Ω]
    [Algebra k K] [FiniteDimensional k K]
    (hreg : ∀ y : M, IsIntegral k y → y ∈ Set.range (algebraMap k M))
    (ev : F₀ →+* Ω) (g₁ : k →+* F₀) (hg₁ : ev.comp g₁ = algebraMap k Ω)
    (hF₀M : ∀ x : F₀, ev x ∈ (algebraMap M Ω).fieldRange)
    {v w : Ω} (hv : Transcendental k v) (hvF₀ : v ∈ Set.range ev)
    (hwM : w ∈ (algebraMap M Ω).fieldRange)
    {pB : Polynomial F₀} (hirr : Irreducible pB) (hroot : pB.eval₂ ev w = 0)
    (R : Polynomial (Polynomial K))
    (hR : ∀ j : K →ₐ[k] Ω, R.map (eval₂RingHom (j : K →+* Ω) v) = pB.map ev) :
    Irreducible (R.map (algebraMap (Polynomial K) (RatFunc K))) := by
  letI : Algebra F₀ Ω := ev.toAlgebra
  haveI : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite _ _
  have hroot' : aeval w pB = 0 := hroot
  have hwInt : IsIntegral F₀ w := IsAlgebraic.isIntegral ⟨_, hirr.ne_zero, hroot'⟩
  let j : K →ₐ[k] Ω := IsAlgClosed.lift
  obtain ⟨θ₀, hθ₀⟩ := Field.exists_primitive_element k K
  have hθk : IsIntegral k (j θ₀) := (Algebra.IsIntegral.isIntegral θ₀).map j
  have hdeg := natDegree_minpoly_le_adjoin_of_regular hreg g₁ hg₁ hF₀M hwM hwInt hθk
  have hjT := algHom_mem_adjoin_of_primitive j g₁ hg₁ hθ₀
  have hvT : v ∈ F₀⟮j θ₀⟯ := by
    obtain ⟨x, rfl⟩ := hvF₀
    exact IntermediateField.algebraMap_mem _ x
  have hinj₀ := eval₂_injective_of_transcendental j hv
  have hJ : ∀ x, IsFractionRing.lift (K := RatFunc K) hinj₀ x ∈ F₀⟮j θ₀⟯ :=
    isFractionRing_lift_eval₂_mem (F₀⟮j θ₀⟯).toSubfield (j : K →+* Ω) hjT hvT hinj₀
  have hcomp : (IsFractionRing.lift (K := RatFunc K) hinj₀).comp
      (algebraMap (Polynomial K) (RatFunc K)) = eval₂RingHom (j : K →+* Ω) v :=
    RingHom.ext fun p => IsFractionRing.lift_algebraMap hinj₀ p
  refine irreducible_of_map_eq_of_natDegree_minpoly (F₀⟮j θ₀⟯)
    (IsFractionRing.lift (K := RatFunc K) hinj₀) hJ hirr hroot' hdeg ?_
  rw [Polynomial.map_map, hcomp]
  exact hR j

end GaloisForLFunctions.HTGeometry
