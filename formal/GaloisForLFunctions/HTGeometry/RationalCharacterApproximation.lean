import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Order.Filter.Pi
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Finsupp.Encodable
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Injective characters of a countable rational vector space

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the construction
underlying Lemma 9.4 (`t13`).

Let `V` be a countable `ℚ`-vector space and let `H = Hom (V, ℂˣ)` carry the topology of pointwise
convergence.  Every character of `V` can be approximated, on any finite set and to any accuracy, by
a character of the special form `exp ∘ ψ` where `ψ : V →ₗ[ℚ] ℂ` is an injective linear map whose
image meets the line `ℚ · 2πi` only in `0`; such a character is injective.

The construction has four ingredients, all proved here:

* a neighbourhood in the topology of pointwise convergence contains a basic one — closeness on a
  finite set;
* a finite subset of `V` lies in the `ℤ`-span of a finite `ℚ`-linearly independent family (the
  `ℤ`-span of a finite set is a finitely generated torsion-free, hence free, `ℤ`-module);
* a finite family of complex numbers can be perturbed arbitrarily little into a `ℚ`-linearly
  independent family whose span misses a prescribed nonzero number (the `ℚ`-span of a finite set
  is countable, and a countable set has dense complement);
* prescribing a `ℚ`-linearly independent family of values on a `ℚ`-linearly independent family of
  `V` extends to an injective `ℚ`-linear map `V → ℂ` avoiding a prescribed basis line — because a
  `ℚ`-basis of `ℂ` is uncountable while a basis of `V` is countable.
-/

namespace HTGeometry

open Filter Topology Cardinal Set




/-- A neighbourhood of a character in the topology of pointwise convergence contains a basic
neighbourhood: closeness on a finite set. -/
theorem deningerChar_exists_basic_nhds {V : Type*} (φ : V → ℂˣ) {U : Set (V → ℂˣ)} (hU : U ∈ 𝓝 φ) :
    ∃ (S : Finset V) (ε : ℝ), 0 < ε ∧
      ∀ f : V → ℂˣ, (∀ s ∈ S, dist (f s : ℂ) (φ s : ℂ) < ε) → f ∈ U := by
  classical
  rw [nhds_pi] at hU
  obtain ⟨S, t, ht, hts⟩ := Filter.mem_pi'.1 hU
  have hball : ∀ i : V, ∃ r : ℝ, 0 < r ∧
      ∀ u : ℂˣ, dist (u : ℂ) (φ i : ℂ) < r → u ∈ t i := by
    intro i
    have h1 : t i ∈ Filter.comap (Units.val : ℂˣ → ℂ) (𝓝 ((φ i : ℂ))) := by
      rw [← Units.isEmbedding_val₀.toIsInducing.nhds_eq_comap]
      exact ht i
    obtain ⟨W, hW, hWt⟩ := h1
    obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.1 hW
    exact ⟨r, hr, fun u hu => hWt (hrW hu)⟩
  choose r hr hrt using hball
  refine ⟨S, (insert (1 : ℝ) (S.image r)).min' ⟨1, by simp⟩, ?_, ?_⟩
  · refine (Finset.lt_min'_iff _ _).2 ?_
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · norm_num
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hr i
  · intro f hf
    refine hts ?_
    intro s hs
    refine hrt s (f s) (lt_of_lt_of_le (hf s hs) ?_)
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs))



/-- The `ℚ`-span of a countable set of complex numbers is countable. -/
theorem countable_ratSpan {T : Set ℂ} (hT : T.Countable) :
    (Submodule.span ℚ T : Set ℂ).Countable := by
  haveI : Countable T := hT.to_subtype
  have h : Submodule.span ℚ T
      = LinearMap.range (Finsupp.linearCombination ℚ ((↑) : T → ℂ)) := by
    rw [Finsupp.range_linearCombination, Subtype.range_coe]
  rw [h]
  exact Set.countable_range _

/-- A ball in `ℂ` is not contained in a countable set. -/
theorem exists_dist_lt_notMem_of_countable {A : Set ℂ} (hA : A.Countable) (z : ℂ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ x : ℂ, dist x z < δ ∧ x ∉ A := by
  have hd : Dense Aᶜ := hA.dense_compl ℂ
  obtain ⟨x, hxA, hxb⟩ :=
    hd.exists_mem_open Metric.isOpen_ball ⟨z, Metric.mem_ball_self hδ⟩
  exact ⟨x, hxb, hxA⟩

/-- Any finite family of complex numbers can be perturbed, by an arbitrarily small amount, into a
`ℚ`-linearly independent family whose span misses a prescribed nonzero number. -/
theorem exists_linearIndependent_near (c : ℂ) (hc : c ≠ 0) :
    ∀ (n : ℕ) (u : Fin n → ℂ) (δ : ℝ), 0 < δ →
      ∃ w : Fin n → ℂ, (∀ i, dist (w i) (u i) < δ) ∧ LinearIndependent ℚ w ∧
        c ∉ Submodule.span ℚ (Set.range w) := by
  intro n
  induction n with
  | zero =>
    intro u δ hδ
    refine ⟨u, fun i => absurd i.2 (by omega), linearIndependent_empty_type, ?_⟩
    simpa using hc
  | succ n ih =>
    intro u δ hδ
    obtain ⟨w', hw'd, hw'i, hw'c⟩ := ih (Fin.tail u) δ hδ
    have hfin : (insert c (Set.range w')).Countable :=
      (Set.finite_range w').countable.insert c
    obtain ⟨x, hxd, hxs⟩ :=
      exists_dist_lt_notMem_of_countable (countable_ratSpan hfin) (u 0) hδ
    have hsub : Submodule.span ℚ (Set.range w') ≤ Submodule.span ℚ (insert c (Set.range w')) :=
      Submodule.span_mono (Set.subset_insert _ _)
    refine ⟨Fin.cons x w', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hxd
      · intro j; rw [Fin.cons_succ]; exact hw'd j
    · exact linearIndependent_finCons.2 ⟨hw'i, fun h => hxs (hsub h)⟩
    · rw [Fin.range_cons]
      intro hmem
      obtain ⟨a, y, hy, hcy⟩ := Submodule.mem_span_insert.1 hmem
      rcases eq_or_ne a 0 with rfl | ha
      · exact hw'c (by rw [hcy, zero_smul, zero_add]; exact hy)
      · refine hxs ?_
        have hx : x = a⁻¹ • (c - y) := by
          rw [← eq_sub_of_add_eq hcy.symm, inv_smul_smul₀ ha]
        rw [hx]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (hsub hy))
        exact Submodule.subset_span (Set.mem_insert _ _)


variable {V : Type*} [AddCommGroup V] [Module ℚ V]


/-- A finite subset of a `ℚ`-vector space is contained in the `ℤ`-span of a finite
`ℚ`-linearly independent family. -/
theorem exists_integral_basis_of_finset (S : Finset V) :
    ∃ (n : ℕ) (e : Fin n → V), LinearIndependent ℚ e ∧
      ∀ s ∈ S, ∃ c : Fin n → ℤ, s = ∑ i, c i • e i := by
  classical
  haveI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  set L := Submodule.span ℤ (S : Set V) with hL
  haveI : Module.Finite ℤ L := Module.Finite.span_finset (R := ℤ) S
  haveI : Module.IsTorsionFree ℤ L :=
    Function.Injective.moduleIsTorsionFree (Submodule.subtype L) Subtype.val_injective
      (fun _ _ => rfl)
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis ℤ L with hb
  haveI : Finite (Module.Free.ChooseBasisIndex ℤ L) := Module.Finite.finite_basis b
  haveI : Fintype (Module.Free.ChooseBasisIndex ℤ L) := Fintype.ofFinite _
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (Module.Free.ChooseBasisIndex ℤ L)
  refine ⟨n, fun i => (b (eqv.symm i) : V), ?_, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing (R := ℤ)]
    refine (b.linearIndependent.map' (Submodule.subtype L) (by simp)).comp _ eqv.symm.injective
  · intro s hs
    have hsL : s ∈ L := Submodule.subset_span (by exact_mod_cast hs)
    refine ⟨fun i => b.repr ⟨s, hsL⟩ (eqv.symm i), ?_⟩
    have h2 : (∑ j, (b.repr ⟨s, hsL⟩ j) • (b j : V)) = s := by
      have h1 : ∑ j, b.equivFun ⟨s, hsL⟩ j • b j = (⟨s, hsL⟩ : L) := b.sum_equivFun _
      simp only [Module.Basis.equivFun_apply] at h1
      have h3 := congrArg (Submodule.subtype L) h1
      rw [map_sum] at h3
      simpa using h3
    symm
    calc ∑ i : Fin n, (b.repr ⟨s, hsL⟩ (eqv.symm i)) • ((b (eqv.symm i) : V))
        = ∑ j, (b.repr ⟨s, hsL⟩ j) • (b j : V) :=
          Equiv.sum_comp eqv.symm (fun j => (b.repr ⟨s, hsL⟩ j) • (b j : V))
      _ = s := h2



theorem complex_not_countable : ¬ Countable ℂ := by
  intro h
  haveI := h
  have : Countable ℝ := Function.Injective.countable Complex.ofReal_injective
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2 this)

theorem ratBasis_complex_not_countable {B : Set ℂ} (b : Module.Basis ↥B ℚ ℂ) :
    ¬ B.Countable := by
  intro hB
  haveI : Countable ↥B := hB.to_subtype
  exact complex_not_countable (Function.Injective.countable b.repr.toEquiv.injective)


/-- Prescribing a `ℚ`-linearly independent family of values on a finite `ℚ`-linearly independent
family of a countable `ℚ`-vector space extends to an injective `ℚ`-linear map into `ℂ` whose image
meets the line `ℚ c` only in `0`. -/
theorem exists_linear_extension_avoiding [Countable V] (c : ℂ) {n : ℕ} (e : Fin n → V)
    (he : LinearIndependent ℚ e) (w : Fin n → ℂ)
    (hw : LinearIndependent ℚ (Fin.cons c w : Fin (n + 1) → ℂ)) :
    ∃ ψ : V →ₗ[ℚ] ℂ, (∀ i, ψ (e i) = w i) ∧ Function.Injective ψ ∧
      ∀ v : V, ψ v ∈ Submodule.span ℚ ({c} : Set ℂ) → v = 0 := by
  classical
  have hwi : LinearIndependent ℚ w := (linearIndependent_finCons.1 hw).1
  have hcnot : c ∉ Submodule.span ℚ (Set.range w) := (linearIndependent_finCons.1 hw).2
  have hcw : c ∉ Set.range w := fun h => hcnot (Submodule.subset_span h)
  -- the basis of `V` extending `e`
  have hEset : LinearIndepOn ℚ id (Set.range e) := he.linearIndepOn_id
  set BV : Set V := hEset.extend (Set.subset_univ _) with hBV
  set bV : Module.Basis ↥BV ℚ V := Module.Basis.extend hEset with hbV
  have hsubV : Set.range e ⊆ BV := hEset.subset_extend _
  -- the basis of `ℂ` extending `c` and `w`
  have hCset : LinearIndepOn ℚ id (insert c (Set.range w)) := by
    have hr : Set.range (Fin.cons c w : Fin (n + 1) → ℂ) = insert c (Set.range w) :=
      Fin.range_cons c w
    rw [← hr]
    exact hw.linearIndepOn_id
  set BC : Set ℂ := hCset.extend (Set.subset_univ _) with hBC
  set bC : Module.Basis ↥BC ℚ ℂ := Module.Basis.extend hCset with hbC
  have hsubC : insert c (Set.range w) ⊆ BC := hCset.subset_extend _
  -- the complement of the prescribed part of `BC` is infinite
  have hBCunc : ¬ BC.Countable := ratBasis_complex_not_countable bC
  have hfin : (insert c (Set.range w)).Finite := (Set.finite_range w).insert c
  have hDinf : (BC \ insert c (Set.range w)).Infinite := by
    refine Set.Infinite.sdiff ?_ hfin
    exact fun hf => hBCunc hf.countable
  haveI : Infinite ↥(BC \ insert c (Set.range w)) := hDinf.to_subtype
  haveI : Countable ↥(BV \ Set.range e) := (Set.to_countable _).to_subtype
  obtain ⟨fnat, hfnat⟩ :=
    Countable.exists_injective_nat ↥(BV \ Set.range e)
  set ι₀ : ↥(BV \ Set.range e) → ↥(BC \ insert c (Set.range w)) :=
    fun x => Infinite.natEmbedding _ (fnat x) with hι₀def
  have hι₀inj : Function.Injective ι₀ := fun a b hab =>
    hfnat ((Infinite.natEmbedding _).injective hab)
  -- the map of bases
  have hwinj : Function.Injective w := hwi.injective
  have heinj : Function.Injective e := he.injective
  set G : ↥BV → ↥BC := fun x =>
    if h : (x : V) ∈ Set.range e then ⟨w h.choose, hsubC (Set.mem_insert_of_mem _ ⟨h.choose, rfl⟩)⟩
    else ⟨(ι₀ ⟨(x : V), ⟨x.2, h⟩⟩ : ℂ), ((ι₀ ⟨(x : V), ⟨x.2, h⟩⟩).2).1⟩ with hG
  have hGe : ∀ i : Fin n, G ⟨e i, hsubV ⟨i, rfl⟩⟩ = ⟨w i, hsubC (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩ := by
    intro i
    have hmem : (e i) ∈ Set.range e := ⟨i, rfl⟩
    rw [hG]
    simp only [dif_pos hmem]
    have : hmem.choose = i := heinj hmem.choose_spec
    simp [this]
  have hGne : ∀ x : ↥BV, (G x : ℂ) ≠ c := by
    intro x
    rw [hG]
    by_cases h : (x : V) ∈ Set.range e
    · simp only [dif_pos h]
      intro hc
      exact hcw ⟨h.choose, hc⟩
    · simp only [dif_neg h]
      intro hc
      exact ((ι₀ ⟨(x : V), ⟨x.2, h⟩⟩).2).2 (by rw [hc]; exact Set.mem_insert _ _)
  have hGinj : Function.Injective G := by
    intro x y hxy
    by_cases hx : (x : V) ∈ Set.range e <;> by_cases hy : (y : V) ∈ Set.range e
    · rw [hG] at hxy
      simp only [dif_pos hx, dif_pos hy, Subtype.mk.injEq] at hxy
      have := hwinj hxy
      apply Subtype.ext
      rw [← hx.choose_spec, ← hy.choose_spec, this]
    · exfalso
      rw [hG] at hxy
      simp only [dif_pos hx, dif_neg hy, Subtype.mk.injEq] at hxy
      exact ((ι₀ ⟨(y : V), ⟨y.2, hy⟩⟩).2).2 (hxy ▸ Set.mem_insert_of_mem _ ⟨hx.choose, rfl⟩)
    · exfalso
      rw [hG] at hxy
      simp only [dif_neg hx, dif_pos hy, Subtype.mk.injEq] at hxy
      exact ((ι₀ ⟨(x : V), ⟨x.2, hx⟩⟩).2).2 (hxy ▸ Set.mem_insert_of_mem _ ⟨hy.choose, rfl⟩)
    · rw [hG] at hxy
      simp only [dif_neg hx, dif_neg hy, Subtype.mk.injEq] at hxy
      have h2 := hι₀inj (Subtype.ext hxy)
      have hval : (x : V) = (y : V) :=
        congrArg (fun z : ↥(BV \ Set.range e) => (z : V)) h2
      exact Subtype.ext hval
  -- the linear map
  set g : ↥BV → ℂ := fun x => ((G x : ℂ)) with hgdef
  have hgindep : LinearIndependent ℚ g := by
    have hbCcoe : (⇑bC : ↥BC → ℂ) = ((↑) : ↥BC → ℂ) := Module.Basis.coe_extend hCset
    have h1 : LinearIndependent ℚ ((↑) : ↥BC → ℂ) := by
      rw [← hbCcoe]; exact bC.linearIndependent
    exact h1.comp G hGinj
  set ψ : V →ₗ[ℚ] ℂ := bV.constr ℚ g with hψ
  have hψrepr : ∀ v : V, ψ v = Finsupp.linearCombination ℚ g (bV.repr v) := by
    intro v
    rw [hψ, Module.Basis.constr_apply, Finsupp.linearCombination_apply]
  have hψbasis : ∀ x : ↥BV, ψ (x : V) = g x := by
    intro x
    have hb : bV x = (x : V) := Module.Basis.extend_apply_self hEset x
    rw [← hb, hψ, Module.Basis.constr_basis]
  have hψinj : Function.Injective ψ := by
    intro v₁ v₂ hv
    apply bV.repr.injective
    apply hgindep
    rw [← hψrepr, ← hψrepr, hv]
  have hcBC : c ∈ BC := hsubC (Set.mem_insert _ _)
  set fc : ℂ →ₗ[ℚ] ℚ := bC.coord ⟨c, hcBC⟩ with hfc
  have hfcc : fc c = 1 := by
    have hb : bC ⟨c, hcBC⟩ = c := Module.Basis.extend_apply_self hCset _
    have h1 : fc (bC ⟨c, hcBC⟩) = 1 := by
      rw [hfc, Module.Basis.coord_apply, Module.Basis.repr_self]
      simp
    rwa [hb] at h1
  have hfcg : ∀ x : ↥BV, fc (g x) = 0 := by
    intro x
    have hb : bC (G x) = ((G x : ℂ)) := Module.Basis.extend_apply_self hCset _
    have hne : (⟨c, hcBC⟩ : ↥BC) ≠ G x := fun h => hGne x (congrArg Subtype.val h).symm
    rw [hgdef]
    simp only
    rw [← hb, hfc, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [hne]
  have hfcψ : ∀ v : V, fc (ψ v) = 0 := by
    intro v
    have hz : (fc.comp ψ) = 0 := by
      refine bV.ext ?_
      intro x
      have hb : bV x = (x : V) := Module.Basis.extend_apply_self hEset x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, hb, hψbasis x]
      exact hfcg x
    exact congrArg (fun L : V →ₗ[ℚ] ℚ => L v) hz
  refine ⟨ψ, ?_, hψinj, ?_⟩
  · intro i
    have h1 := hψbasis ⟨e i, hsubV ⟨i, rfl⟩⟩
    rw [h1, hgdef]
    simp only
    rw [hGe i]
  · intro v hv
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.1 hv
    have hq0 : q = 0 := by
      have h1 := hfcψ v
      rw [← hq, map_smul, hfcc, smul_eq_mul, mul_one] at h1
      exact h1
    have hzero : ψ v = 0 := by rw [← hq, hq0, zero_smul]
    exact hψinj (by rw [hzero, map_zero])


end HTGeometry
