import Mathlib
import GaloisForLFunctions.HTGeometry.ComplexAffineLineSimplyConnected
import GaloisForLFunctions.HTGeometry.BivariateSeparableResultant
import GaloisForLFunctions.HTGeometry.CountableFieldComplexEmbedding

/-!
# Algebraic simple connectedness of the affine line, over any algebraically closed field

Over an algebraically closed field `K` of characteristic zero, a monic polynomial in one variable
over `K[X]` whose specialisation at every parameter is separable splits into monic linear factors
over `K[X]`.  Equivalently, the affine line over `K` has no nontrivial connected finite étale cover.

The complex case is `ComplexAffineLineSimplyConnected`.  The general case is reduced to it: the
coefficients generate a countable subfield, whose relative algebraic closure in `K` is a countable
algebraically closed field and therefore embeds into `ℂ`; the separability hypothesis transports
because it is equivalent to the fibre resultant being a nonzero constant, which is preserved by any
ring homomorphism; and the complex root branch descends again by Lagrange interpolation, because it
maps the (infinite, algebraically closed) image field into itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-- **Lagrange descent.**  A polynomial over `L` whose values on the image of an infinite field
`E` stay inside that image is itself defined over `E`. -/
theorem exists_map_eq_of_eval_mem_range {E L : Type*} [Field E] [Field L] [Infinite E]
    (φ : E →+* L) (p : L[X]) (h : ∀ e : E, ∃ e' : E, p.eval (φ e) = φ e') :
    ∃ q : E[X], q.map φ = p := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq E (p.natDegree + 1)
  set r : E → E := fun e => (h e).choose with hr
  have hrspec : ∀ e : E, p.eval (φ e) = φ (r e) := fun e => (h e).choose_spec
  have hid : Set.InjOn (id : E → E) s := Set.injOn_of_injective Function.injective_id
  set q : E[X] := Lagrange.interpolate s id r with hq
  have hqdeg : q.degree < (s.card : WithBot ℕ) := Lagrange.degree_interpolate_lt r hid
  refine ⟨q, ?_⟩
  have hinj : Function.Injective φ := φ.injective
  have hcard : (s.image φ).card = p.natDegree + 1 := by
    rw [Finset.card_image_of_injective _ hinj, hs]
  have hdegq : (q.map φ).degree < ((s.image φ).card : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_map_le ?_
    rw [hcard, ← hs]
    exact hqdeg
  have hdegp : p.degree < ((s.image φ).card : WithBot ℕ) := by
    rw [hcard]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_self _
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s.image φ) hdegq hdegp ?_
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  have h1 : (q.map φ).eval (φ e) = φ (q.eval e) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have h2 : q.eval e = r e := by
    rw [hq]
    exact Lagrange.eval_interpolate_at_node r hid he
  rw [h1, h2, ← hrspec e]

/-- Specialising a mapped two-variable polynomial at a mapped parameter. -/
theorem biFibre_map_apply {E L : Type*} [Field E] [Field L] (φ : E →+* L)
    (f : E[X][X]) (e : E) :
    biFibre (f.map (Polynomial.mapRingHom φ)) (φ e) = (biFibre f e).map φ := by
  rw [biFibre, biFibre, Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.coe_evalRingHom]
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- Over an algebraically closed field every root of a mapped monic polynomial comes from the
source field. -/
theorem exists_preimage_of_isRoot_map {E L : Type*} [Field E] [Field L] [IsAlgClosed E]
    (φ : E →+* L) {p : E[X]} (hp : p.Monic) {z : L} (hz : (p.map φ).eval z = 0) :
    ∃ e : E, z = φ e := by
  classical
  have hsplits : p.Splits := IsAlgClosed.splits p
  obtain ⟨e, he⟩ := hsplits.mem_range_of_isRoot hp.ne_zero (i := φ) (x := z) hz
  exact ⟨e, he.symm⟩

/-- **The countable case.**  Over a countable algebraically closed field of characteristic zero,
a monic two-variable polynomial with separable fibres has a polynomial root. -/
theorem exists_isRoot_of_countable {E : Type*} [Field E] [CharZero E] [IsAlgClosed E] [Countable E]
    {f : E[X][X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hsep : ∀ s : E, (biFibre f s).Separable) :
    ∃ Q : E[X], f.eval Q = 0 := by
  classical
  obtain ⟨φ⟩ := nonempty_ringHom_complex_of_countable E
  have hinj : Function.Injective φ := φ.injective
  set g : ℂ[X][X] := f.map (Polynomial.mapRingHom φ) with hg
  have hgm : g.Monic := hf.map _
  have hgd : g.natDegree = f.natDegree := hf.natDegree_map _
  obtain ⟨c, hc, hres⟩ := exists_biResultant_eq_C hf hsep
  have hgres : biResultant g = Polynomial.C (φ c) := by
    rw [hg, biResultant_map φ hf, hres, Polynomial.map_C]
  have hgsep : ∀ s : ℂ, (biFibre g s).Separable :=
    forall_separable_of_biResultant_eq_C hgm (by simpa using hinj.ne hc) hgres
  obtain ⟨Qc, hQc⟩ := exists_polynomial_biRoot hgm (by omega) hgsep
  have hval : ∀ e : E, ∃ e' : E, Qc.eval (φ e) = φ e' := by
    intro e
    have h0 : (biFibre g (φ e)).eval (Qc.eval (φ e)) = 0 := by
      have := hQc (φ e)
      rwa [biEval_eq_eval_biFibre] at this
    rw [biFibre_map_apply φ f e] at h0
    obtain ⟨e', he'⟩ := exists_preimage_of_isRoot_map φ (biFibre_monic hf e) h0
    exact ⟨e', he'⟩
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_eval_mem_range φ Qc hval
  refine ⟨Q, ?_⟩
  have hmapinj : Function.Injective (Polynomial.map φ : E[X] → ℂ[X]) :=
    Polynomial.map_injective φ hinj
  apply hmapinj
  rw [Polynomial.map_zero]
  have hev : (f.eval Q).map φ = g.eval (Q.map φ) := by
    have h := Polynomial.hom_eval₂ f (RingHom.id E[X]) (Polynomial.mapRingHom φ) Q
    rw [RingHom.comp_id] at h
    change (Polynomial.mapRingHom φ) (Polynomial.eval₂ (RingHom.id E[X]) Q f) = _ at h
    rw [Polynomial.eval₂_id] at h
    rw [hg, Polynomial.eval_map]
    simpa [Polynomial.coe_mapRingHom] using h
  rw [hev, hQ]
  have := hQc
  have hzero : ∀ x : ℂ, (g.eval Qc).eval x = 0 := by
    intro x
    rw [eval_eval_eq_biEval]
    exact hQc x
  exact Polynomial.zero_of_eval_zero _ hzero

/-- Every subfield of a field is torsion-free as a module over itself. -/
theorem module_isTorsionFree_subfield {K : Type*} [Field K] (F : Subfield K) :
    Module.IsTorsionFree F K := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro r m hrm
  rw [Algebra.smul_def] at hrm
  rcases mul_eq_zero.mp hrm with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr h

/-- **The general one-variable case.**  Over any algebraically closed field of characteristic
zero, a monic two-variable polynomial with separable fibres has a polynomial root. -/
theorem exists_isRoot_of_forall_separable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {f : K[X][X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hsep : ∀ s : K, (biFibre f s).Separable) :
    ∃ Q : K[X], f.eval Q = 0 := by
  classical
  set S : Set K := Set.range (fun p : ℕ × ℕ => (f.coeff p.1).coeff p.2) with hS
  have hScount : S.Countable := Set.countable_range _
  set F : Subfield K := Subfield.closure S with hF
  haveI hFcount : Countable F :=
    Cardinal.mk_le_aleph0_iff.mp
      ((Subfield.cardinalMk_closure_le_max S).trans
        (max_le hScount.le_aleph0 le_rfl))
  haveI : Module.IsTorsionFree F K := module_isTorsionFree_subfield F
  set E := algebraicClosure F K with hE
  haveI hEcount : Countable E := by
    have hset : {x : K | IsAlgebraic F x}.Countable := Algebraic.countable F K
    have : Countable {x : K // IsAlgebraic F x} := hset.to_subtype
    exact Countable.of_equiv _ (Equiv.subtypeEquivRight fun x => (mem_algebraicClosure_iff).symm)
  haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  set ψ : E →+* K := algebraMap E K with hψ
  have hψinj : Function.Injective ψ := (algebraMap E K).injective
  have hcoeff : ∀ i j, (f.coeff i).coeff j ∈ Set.range ψ := by
    intro i j
    have hmemF : (f.coeff i).coeff j ∈ F :=
      Subfield.subset_closure ⟨(i, j), rfl⟩
    have hmemE : (f.coeff i).coeff j ∈ E :=
      IntermediateField.algebraMap_mem E (⟨(f.coeff i).coeff j, hmemF⟩ : F)
    exact ⟨⟨(f.coeff i).coeff j, hmemE⟩, rfl⟩
  have hlift : f ∈ Polynomial.lifts (Polynomial.mapRingHom ψ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have : f.coeff n ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro m
      exact hcoeff n m
    rw [Polynomial.lifts_iff_set_range] at this
    exact this
  obtain ⟨f₀, hmap, hdeg, hmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hf
  have hdeg₀ : f₀.natDegree = f.natDegree := by
    rw [Polynomial.natDegree, Polynomial.natDegree, hdeg]
  have hsep₀ : ∀ s : E, (biFibre f₀ s).Separable := by
    intro s
    rw [← Polynomial.separable_map ψ, ← biFibre_map_apply ψ f₀ s, hmap]
    exact hsep (ψ s)
  obtain ⟨Q₀, hQ₀⟩ := exists_isRoot_of_countable hmonic (by omega) hsep₀
  refine ⟨Q₀.map ψ, ?_⟩
  have hev : (f₀.eval Q₀).map ψ = (f₀.map (Polynomial.mapRingHom ψ)).eval (Q₀.map ψ) := by
    have h := Polynomial.hom_eval₂ f₀ (RingHom.id E[X]) (Polynomial.mapRingHom ψ) Q₀
    rw [RingHom.comp_id] at h
    change (Polynomial.mapRingHom ψ) (Polynomial.eval₂ (RingHom.id E[X]) Q₀ f₀) = _ at h
    rw [Polynomial.eval₂_id] at h
    rw [Polynomial.eval_map]
    simpa [Polynomial.coe_mapRingHom] using h
  rw [← hmap, ← hev, hQ₀, Polynomial.map_zero]

/-- **Algebraic simple connectedness of the affine line.**  Over any algebraically closed field of
characteristic zero, a monic two-variable polynomial all of whose fibres are separable splits into
monic linear factors. -/
theorem exists_multiset_prod_of_forall_separable_algClosed {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] :
    ∀ (d : ℕ) (f : K[X][X]), f.Monic → f.natDegree = d →
      (∀ s : K, (biFibre f s).Separable) →
      ∃ L : Multiset K[X], f = (L.map (fun a => X - Polynomial.C a)).prod := by
  intro d
  induction d with
  | zero =>
      intro f hf hdeg _
      exact ⟨0, by simpa using (Polynomial.eq_one_of_monic_natDegree_zero hf hdeg)⟩
  | succ n ih =>
      intro f hf hdeg hsep
      obtain ⟨Q, hQ⟩ := exists_isRoot_of_forall_separable hf (by omega) hsep
      obtain ⟨h₀, hfac⟩ : (X - Polynomial.C Q) ∣ f := (Polynomial.dvd_iff_isRoot).mpr hQ
      have hlinmonic : (X - Polynomial.C Q : K[X][X]).Monic := Polynomial.monic_X_sub_C Q
      have hh0monic : h₀.Monic := by
        have hfm := hf
        rw [hfac] at hfm
        exact hlinmonic.of_mul_monic_left hfm
      have hdeg0 : h₀.natDegree = n := by
        have hh := congrArg Polynomial.natDegree hfac
        rw [hlinmonic.natDegree_mul hh0monic, Polynomial.natDegree_X_sub_C] at hh
        omega
      have hsep0 : ∀ s : K, (biFibre h₀ s).Separable := by
        intro s
        refine (hsep s).of_dvd ?_
        rw [hfac, biFibre_mul]
        exact Dvd.intro_left _ rfl
      obtain ⟨L, hL⟩ := ih h₀ hh0monic hdeg0 hsep0
      exact ⟨Q ::ₘ L, by rw [Multiset.map_cons, Multiset.prod_cons, ← hL, hfac]⟩

end GaloisForLFunctions.HTGeometry
