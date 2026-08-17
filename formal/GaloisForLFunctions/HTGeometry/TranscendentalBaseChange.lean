import Mathlib

/-!
# Adjoining a transcendental element preserves linear independence

A family that is linearly independent over `F` and lies inside a field `E` over which `t` is
transcendental stays linearly independent over `F(t)`.

Clearing denominators turns an `F(t)`-relation into a polynomial relation `∑ P_i(t) b_i = 0`;
collecting powers of `t` exhibits it as a polynomial in `t` with coefficients in `E`, so
transcendence kills every coefficient, and independence over `F` kills every coefficient of every
`P_i`.

This is the linear-disjointness input to base change along a free parameter: it is what makes the
degree of a finite extension, and hence its Galois group, survive the adjunction of an independent
transcendental.
-/

open Polynomial IntermediateField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- **Linear independence survives a transcendental adjunction.** -/
theorem linearIndependent_adjoin_transcendental
    (E : IntermediateField F Ω) (t : Ω) (ht : Transcendental E t)
    {ι : Type*} [Fintype ι] (b : ι → Ω) (hbE : ∀ i, b i ∈ E)
    (hind : LinearIndependent F b) :
    LinearIndependent (F⟮t⟯) b := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  -- write each coefficient as a quotient of polynomial values
  have hrep : ∀ i, ∃ r s : F[X], Polynomial.aeval t s ≠ 0 ∧
      (c i : Ω) = Polynomial.aeval t r / Polynomial.aeval t s := by
    intro i
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F (c i : Ω)).1 (c i).2
    by_cases hs : Polynomial.aeval t s = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · simp
      · rw [hrs, hs, div_zero]
        simp
    · exact ⟨r, s, hs, hrs⟩
  choose r s hs hcrs using hrep
  set S : Ω := ∏ i, Polynomial.aeval t (s i) with hS
  have hSne : S ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hs i
  -- the cleared numerators
  set P : ι → F[X] := fun i => r i * ∏ j ∈ Finset.univ.erase i, s j with hP
  have hclear : ∀ i, S * (c i : Ω) = Polynomial.aeval t (P i) := by
    intro i
    have hsplit : S = Polynomial.aeval t (s i) * ∏ j ∈ Finset.univ.erase i,
        Polynomial.aeval t (s j) := by
      rw [hS]
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hP, map_mul, map_prod, hcrs i, hsplit]
    field_simp [hs i]
  -- the relation in `Ω`
  have hrel : ∑ i, Polynomial.aeval t (P i) * b i = 0 := by
    have hc' : ∑ i, (c i : Ω) * b i = 0 := by
      have := congrArg (fun x : Ω => x) hc
      simpa [Algebra.smul_def] using hc
    calc ∑ i, Polynomial.aeval t (P i) * b i
        = ∑ i, S * ((c i : Ω) * b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hclear i]
          ring
      _ = S * ∑ i, (c i : Ω) * b i := by rw [Finset.mul_sum]
      _ = 0 := by rw [hc', mul_zero]
  -- read the relation as a polynomial over `E`
  set Q : (E)[X] := ∑ i, (P i).map (algebraMap F E) * Polynomial.C ⟨b i, hbE i⟩ with hQ
  have hQeval : Polynomial.aeval t Q = 0 := by
    rw [hQ, map_sum, ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.aeval_C]
    congr 1
    rw [Polynomial.aeval_map_algebraMap]
  have hQ0 : Q = 0 := transcendental_iff.1 ht Q hQeval
  -- every coefficient of every numerator vanishes
  have hPzero : ∀ i, P i = 0 := by
    have hcoeff : ∀ k : ℕ, ∀ i, (P i).coeff k = 0 := by
      intro k
      have hQk : Q.coeff k = 0 := by rw [hQ0, Polynomial.coeff_zero]
      have hval : ((Q.coeff k : E) : Ω) = ∑ i, algebraMap F Ω ((P i).coeff k) * b i := by
        rw [hQ]
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_map]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rfl
      have hzero : ∑ i, algebraMap F Ω ((P i).coeff k) * b i = 0 := by
        rw [← hval, hQk]
        simp
      have := Fintype.linearIndependent_iff.1 hind (fun i => (P i).coeff k) ?_
      · exact this
      · simpa [Algebra.smul_def] using hzero
    intro i
    ext k
    simpa using hcoeff k i
  -- hence every coefficient vanishes
  intro i
  have : S * (c i : Ω) = 0 := by rw [hclear i, hPzero i, map_zero]
  have hci : (c i : Ω) = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hSne
    · exact h
  exact Subtype.ext hci

/-- The `F(t)`-span of a spanning family of `E` exhausts `E(t)`. -/
theorem adjoin_le_span_of_span
    (E : IntermediateField F Ω) [FiniteDimensional F E] (t : Ω)
    {ι : Type*} [Fintype ι] (b : ι → Ω)
    (hspanE : (E : Set Ω) ⊆ (Submodule.span F (Set.range b) : Set Ω)) :
    ((IntermediateField.adjoin (↥F⟮t⟯) (E : Set Ω) : IntermediateField (↥F⟮t⟯) Ω) : Set Ω)
      ⊆ (Submodule.span (↥F⟮t⟯) (Set.range b) : Set Ω) := by
  classical
  -- every element of `E` is algebraic over `F(t)`
  have halg : ∀ x ∈ (E : Set Ω), IsAlgebraic (↥F⟮t⟯) x := by
    intro x hx
    haveI : Algebra.IsAlgebraic F ↥E := Algebra.IsAlgebraic.of_finite F ↥E
    have hxE : IsAlgebraic F (⟨x, hx⟩ : ↥E) := Algebra.IsAlgebraic.isAlgebraic _
    have hxΩ : IsAlgebraic F x := by
      simpa using hxE.algHom (E.val)
    exact hxΩ.tower_top (↥F⟮t⟯)
  have hsub := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ↥F⟮t⟯) (S := (E : Set Ω))
    halg
  -- `E` is inside the `F(t)`-span of `b`
  have hEsub : (E : Set Ω) ⊆ (Submodule.span (↥F⟮t⟯) (Set.range b) : Set Ω) := by
    intro y hy
    exact Submodule.span_le_restrictScalars F (↥F⟮t⟯) (Set.range b) (hspanE hy)
  have hspanLE : Submodule.span (↥F⟮t⟯) (E : Set Ω)
      ≤ Submodule.span (↥F⟮t⟯) (Set.range b) := Submodule.span_le.2 hEsub
  -- the multiplicative closure of `E` is `E`
  have hclosure : (Submonoid.closure (E : Set Ω) : Set Ω) ⊆ (E : Set Ω) := by
    intro z hz
    have hle : Submonoid.closure (E : Set Ω) ≤ E.toSubalgebra.toSubmonoid :=
      Submonoid.closure_le.2 fun x hx => hx
    exact hle hz
  intro x hx
  have hxalg : x ∈ Algebra.adjoin (↥F⟮t⟯) (E : Set Ω) := by
    rw [← hsub]
    exact hx
  have hxspan : x ∈ Submodule.span (↥F⟮t⟯) (E : Set Ω) := by
    have hy' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin (↥F⟮t⟯) (E : Set Ω)) := hxalg
    rw [Algebra.adjoin_eq_span] at hy'
    refine (Submodule.span_le.2 ?_) hy'
    intro z hz
    exact Submodule.subset_span (hclosure hz)
  exact hspanLE hxspan

/-- **Base change along a transcendental element preserves the degree.** -/
theorem finrank_adjoin_eq_of_transcendental
    (E : IntermediateField F Ω) [FiniteDimensional F E] (t : Ω) (ht : Transcendental E t) :
    Module.finrank (↥F⟮t⟯) ↥(IntermediateField.adjoin (↥F⟮t⟯) (E : Set Ω))
      = Module.finrank F ↥E := by
  classical
  set n : ℕ := Module.finrank F ↥E with hn
  set bas : Module.Basis (Fin n) F ↥E := Module.finBasis F ↥E with hbas
  set b : Fin n → Ω := fun i => ((bas i : ↥E) : Ω) with hb
  have hbE : ∀ i, b i ∈ E := fun i => (bas i).2
  have hindF : LinearIndependent F b := by
    have h := bas.linearIndependent
    have hmap := h.map' (E.val.toLinearMap) (by
      rw [LinearMap.ker_eq_bot]
      exact fun x y hxy => Subtype.ext hxy)
    exact hmap
  have hspanE : (E : Set Ω) ⊆ (Submodule.span F (Set.range b) : Set Ω) := by
    intro x hx
    have hxmem : (⟨x, hx⟩ : ↥E) ∈ Submodule.span F (Set.range bas) := by
      rw [bas.span_eq]
      exact Submodule.mem_top
    have himg : ((⟨x, hx⟩ : ↥E) : Ω) ∈ Submodule.map E.val.toLinearMap
        (Submodule.span F (Set.range bas)) := ⟨⟨x, hx⟩, hxmem, rfl⟩
    rw [Submodule.map_span] at himg
    have hrange : (E.val.toLinearMap '' (Set.range bas)) = Set.range b := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨bas i, ⟨i, rfl⟩, rfl⟩
    rw [hrange] at himg
    exact himg
  have hindL : LinearIndependent (↥F⟮t⟯) b :=
    linearIndependent_adjoin_transcendental E t ht b hbE hindF
  set M : IntermediateField (↥F⟮t⟯) Ω := IntermediateField.adjoin (↥F⟮t⟯) (E : Set Ω) with hM
  have hbM : ∀ i, b i ∈ M := fun i => IntermediateField.subset_adjoin _ _ (hbE i)
  set b' : Fin n → ↥M := fun i => ⟨b i, hbM i⟩ with hb'
  have hindM : LinearIndependent (↥F⟮t⟯) b' := by
    have hinj : Function.Injective (M.val : ↥M →ₐ[↥F⟮t⟯] Ω) := fun x y hxy => Subtype.ext hxy
    refine LinearIndependent.of_comp (M.val.toLinearMap) ?_
    exact hindL
  have hspanM : ⊤ ≤ Submodule.span (↥F⟮t⟯) (Set.range b') := by
    intro x _
    have hx : (x : Ω) ∈ (Submodule.span (↥F⟮t⟯) (Set.range b) : Set Ω) :=
      adjoin_le_span_of_span E t b hspanE x.2
    have hmap : Submodule.map M.val.toLinearMap (Submodule.span (↥F⟮t⟯) (Set.range b'))
        = Submodule.span (↥F⟮t⟯) (Set.range b) := by
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b' i, ⟨i, rfl⟩, rfl⟩
    have hx' : (x : Ω) ∈ Submodule.map M.val.toLinearMap
        (Submodule.span (↥F⟮t⟯) (Set.range b')) := by
      rw [hmap]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hbasis : Module.Basis (Fin n) (↥F⟮t⟯) ↥M := Module.Basis.mk hindM hspanM
  rw [Module.finrank_eq_card_basis hbasis]
  simp

/-- **A simple transcendental extension is relatively algebraically closed.**  An element of
`F(t)` algebraic over `F` already lies in `F`. -/
theorem mem_bot_of_mem_adjoin_simple_of_isAlgebraic
    (t : Ω) (ht : Transcendental F t) {x : Ω} (hx : x ∈ F⟮t⟯) (hax : IsAlgebraic F x) :
    x ∈ (⊥ : IntermediateField F Ω) := by
  classical
  set E : IntermediateField F Ω := F⟮x⟯ with hE
  haveI : FiniteDimensional F ↥E := by
    rw [hE]
    exact IntermediateField.adjoin.finiteDimensional hax.isIntegral
  have htE : Transcendental (↥E) t := by
    rw [Transcendental]
    intro halg
    haveI : Algebra.IsAlgebraic F ↥E := Algebra.IsAlgebraic.of_finite F ↥E
    haveI : Algebra.IsAlgebraic (↥E) ↥(IntermediateField.adjoin (↥E) {t}) := by
      refine IntermediateField.isAlgebraic_adjoin ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact halg.isIntegral
    haveI : Algebra.IsAlgebraic F ↥(IntermediateField.adjoin (↥E) {t}) :=
      Algebra.IsAlgebraic.trans F (↥E) _
    have hmem : t ∈ IntermediateField.adjoin (↥E) {t} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton t)
    have hta : IsAlgebraic F (⟨t, hmem⟩ : ↥(IntermediateField.adjoin (↥E) {t})) :=
      Algebra.IsAlgebraic.isAlgebraic _
    obtain ⟨p, hp0, hp⟩ := hta
    refine ht ⟨p, hp0, ?_⟩
    have hcomp := Polynomial.aeval_algHom_apply
      ((IntermediateField.adjoin (↥E) {t}).val.restrictScalars F)
      (⟨t, hmem⟩ : ↥(IntermediateField.adjoin (↥E) {t})) p
    rw [hp] at hcomp
    simpa using hcomp
  have hdeg := finrank_adjoin_eq_of_transcendental E t htE
  have hEsub : (E : Set Ω) ⊆ (F⟮t⟯ : Set Ω) := by
    rw [hE]
    refine (IntermediateField.adjoin_le_iff.2 ?_)
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hx
  have hbot : IntermediateField.adjoin (↥F⟮t⟯) (E : Set Ω) = ⊥ := by
    refine IntermediateField.adjoin_eq_bot_iff.2 ?_
    intro z hz
    have hzL : z ∈ F⟮t⟯ := hEsub hz
    exact ⟨⟨z, hzL⟩, rfl⟩
  rw [hbot] at hdeg
  have hone : Module.finrank F ↥E = 1 := by
    rw [← hdeg]
    simp
  have hEbot : E = ⊥ := by
    rwa [IntermediateField.finrank_eq_one_iff] at hone
  have hxE : x ∈ E := by
    rw [hE]
    exact IntermediateField.mem_adjoin_simple_self F x
  rwa [hEbot] at hxE

/-- **An algebraic extension meets a transcendental adjunction in the base.**  This is the
`E ⊓ M = ⊥` hypothesis of natural irrationalities. -/
theorem inf_adjoin_simple_eq_bot_of_isAlgebraic
    (N : IntermediateField F Ω) (halg : ∀ x ∈ N, IsAlgebraic F x)
    (t : Ω) (ht : Transcendental F t) :
    N ⊓ F⟮t⟯ = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  exact mem_bot_of_mem_adjoin_simple_of_isAlgebraic t ht hx.2 (halg x hx.1)

/-- Every element of a finite extension is algebraic over the base. -/
theorem isAlgebraic_of_mem_of_finiteDimensional
    (N : IntermediateField F Ω) [FiniteDimensional F N] {x : Ω} (hx : x ∈ N) :
    IsAlgebraic F x := by
  haveI : Algebra.IsAlgebraic F ↥N := Algebra.IsAlgebraic.of_finite F ↥N
  have hxN : IsAlgebraic F (⟨x, hx⟩ : ↥N) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨p, hp0, hp⟩ := hxN
  refine ⟨p, hp0, ?_⟩
  have hcomp := Polynomial.aeval_algHom_apply (N.val) (⟨x, hx⟩ : ↥N) p
  rw [hp] at hcomp
  simpa using hcomp

/-- **The base-changed extension stays finite.** -/
theorem finiteDimensional_adjoin_of_transcendental
    (N : IntermediateField F Ω) [FiniteDimensional F N] (t : Ω) (ht : Transcendental N t) :
    FiniteDimensional (↥F⟮t⟯) ↥(IntermediateField.adjoin (↥F⟮t⟯) (N : Set Ω)) := by
  have hpos : 0 < Module.finrank (↥F⟮t⟯) ↥(IntermediateField.adjoin (↥F⟮t⟯) (N : Set Ω)) := by
    rw [finrank_adjoin_eq_of_transcendental N t ht]
    exact Module.finrank_pos
  exact Module.finite_of_finrank_pos hpos

/-- The compositum of a field with a simple transcendental adjunction, as an adjunction over the
adjunction. -/
theorem adjoin_eq_top_of_sup_eq_top
    (N : IntermediateField F Ω) (t : Ω) (htop : N ⊔ F⟮t⟯ = ⊤) :
    IntermediateField.adjoin (↥F⟮t⟯) (N : Set Ω) = ⊤ := by
  rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
    IntermediateField.restrictScalars_adjoin]
  refine le_antisymm le_top ?_
  rw [← htop]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · exact IntermediateField.subset_adjoin _ _ (Or.inr hx)
  · exact IntermediateField.subset_adjoin _ _ (Or.inl hx)

/-- **The base-changed extension is Galois**, by mathlib's compositum theorem. -/
theorem isGalois_of_sup_eq_top
    (N : IntermediateField F Ω) [FiniteDimensional F N] [IsGalois F N]
    (t : Ω) (htop : N ⊔ F⟮t⟯ = ⊤) : IsGalois (↥F⟮t⟯) Ω :=
  IsGalois.sup_right N F⟮t⟯ htop

/-- **The base-changed extension is finite.** -/
theorem finiteDimensional_of_sup_eq_top
    (N : IntermediateField F Ω) [FiniteDimensional F N]
    (t : Ω) (htN : Transcendental (↥N) t) (htop : N ⊔ F⟮t⟯ = ⊤) :
    FiniteDimensional (↥F⟮t⟯) Ω := by
  have hfin := finiteDimensional_adjoin_of_transcendental N t htN
  rw [adjoin_eq_top_of_sup_eq_top N t htop] at hfin
  exact Module.Finite.equiv (IntermediateField.topEquiv (F := ↥F⟮t⟯) (E := Ω)).toLinearEquiv

end GaloisForLFunctions.HTGeometry

end
