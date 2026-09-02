import GaloisForLFunctions.HTGeometry.CohenMacaulayDepth
import GaloisForLFunctions.HTGeometry.FreeOfRegularSequence
import GaloisForLFunctions.HTGeometry.GradeLeDim
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Full grade makes maximal-ideal generators regular

For a finite module over a Noetherian local ring, a list generating the maximal ideal is weakly
regular as soon as the module has grade at least the length of the list.  More generally, it is
enough that the maximal ideal be contained in the radical of the sum of the list ideal and the
annihilator.

The proof excludes each head element from every associated prime.  If the head lay in an
associated prime `p`, the tail would generate the maximal ideal of `A ⧸ p`; Krull's height theorem
would bound `dim(A ⧸ p)` by the tail length, while the grade--dimension inequality would bound it
below by the full list length.  The quotient by the regular head inherits one less unit of grade,
so induction applies to the tail.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open IsLocalRing RingTheory.Sequence

universe u

set_option maxHeartbeats 800000 in
/-- Full grade relative to generators modulo the annihilator, up to radical, makes those
generators weakly regular. -/
theorem isWeaklyRegular_of_hasGradeGE_of_maximalIdeal_le_radical_sup_annihilator :
    ∀ (d : ℕ) {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      {rs : List A}, rs.length = d →
      ∀ {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M],
      (∀ r ∈ rs, r ∈ maximalIdeal A) →
      maximalIdeal A ≤ (Ideal.ofList rs ⊔ Module.annihilator A M).radical →
      HasGradeGE (maximalIdeal A) (ModuleCat.of A M) d →
      IsWeaklyRegular M rs := by
  intro d
  induction d with
  | zero =>
      intro A _ _ _ rs hlen M _ _ _ _ _ _
      have hrs : rs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hrs
      exact IsWeaklyRegular.nil A M
  | succ d ih =>
      intro A _ _ _ rs hlen M _ _ hfin hmem hspan hgrade
      obtain ⟨x, t, rfl⟩ : ∃ x t, rs = x :: t := by
        cases rs with
        | nil => simp at hlen
        | cons x t => exact ⟨x, t, rfl⟩
      have htlen : t.length = d := by simpa using hlen
      have hxmem : x ∈ maximalIdeal A := hmem x (List.mem_cons_self ..)
      have htmem : ∀ r ∈ t, r ∈ maximalIdeal A := by
        intro r hr
        exact hmem r (List.mem_cons_of_mem x hr)
      have hxreg : IsSMulRegular M x := by
        rw [isSMulRegular_iff_forall_notMem_associatedPrimes]
        intro p hp hxp
        haveI : p.IsPrime := hp.1
        let f := Ideal.Quotient.mk p
        have hann : Module.annihilator A M ≤ p := by
          intro r hr
          apply hp.annihilator_le
          rw [Submodule.mem_annihilator]
          intro z _
          have hr' : (Module.toAddMonoidEnd A M) r = 0 := hr
          exact DFunLike.congr_fun hr' z
        have htail : Ideal.ofList t ≤ maximalIdeal A := by
          rw [Ideal.ofList, Ideal.span_le]
          exact htmem
        have hpmax : p ≤ maximalIdeal A :=
          IsLocalRing.le_maximalIdeal hp.1.ne_top
        have hsmall : Ideal.ofList t ⊔ p ≤ maximalIdeal A :=
          sup_le htail hpmax
        have hlarge : maximalIdeal A ≤ (Ideal.ofList t ⊔ p).radical := by
          have hinc : Ideal.ofList (x :: t) ⊔ Module.annihilator A M ≤
              Ideal.ofList t ⊔ p := by
            rw [ofList_cons]
            refine sup_le (sup_le ?_ le_sup_left) ?_
            · exact le_sup_right.trans' (Ideal.span_le.mpr (by simpa using hxp))
            · exact hann.trans le_sup_right
          exact hspan.trans (Ideal.radical_mono hinc)
        have hrad : (Ideal.ofList t ⊔ p).radical = maximalIdeal A := by
          apply le_antisymm
          · exact (by infer_instance : (maximalIdeal A).IsPrime).radical_le_iff.mpr hsmall
          · exact hlarge
        letI : IsLocalRing (A ⧸ p) :=
          IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
        have hmaprad : Ideal.map f (Ideal.ofList t ⊔ p).radical =
            (Ideal.map f (Ideal.ofList t ⊔ p)).radical :=
          Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by
            intro r hr
            exact (show p ≤ Ideal.ofList t ⊔ p from le_sup_right)
              (Ideal.Quotient.eq_zero_iff_mem.mp hr))
        have htailrad : (Ideal.ofList (t.map f)).radical = maximalIdeal (A ⧸ p) := by
          rw [hrad, IsLocalRing.map_maximalIdeal_of_surjective f
            Ideal.Quotient.mk_surjective, Ideal.map_sup, Ideal.map_ofList,
            Ideal.map_quotient_self, sup_bot_eq] at hmaprad
          exact hmaprad.symm
        classical
        let J : Ideal (A ⧸ p) :=
          Ideal.span (((t.map f).toFinset : Finset (A ⧸ p)) : Set (A ⧸ p))
        have hJ : J = Ideal.ofList (t.map f) := by
          simp [J, Ideal.ofList]
        have hJrad : J.radical = maximalIdeal (A ⧸ p) := by
          rw [hJ]
          exact htailrad
        have hmin : maximalIdeal (A ⧸ p) ∈
            J.minimalPrimes := by
          refine ⟨⟨by infer_instance, ?_⟩, ?_⟩
          · exact Ideal.le_radical.trans_eq hJrad
          · intro q hq hqle
            have hradle : J.radical ≤ q := hq.1.radical_le_iff.mpr hq.2
            rwa [hJrad] at hradle
        have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
        have hcard : (t.map f).toFinset.card ≤ d :=
          (List.toFinset_card_le _).trans (by simpa [htlen])
        have hupper : ringKrullDim (A ⧸ p) ≤ (((d : ℕ∞) : WithBot ℕ∞)) := by
          rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
          exact_mod_cast hheight.trans (by exact_mod_cast hcard)
        have hlower := hasGradeGE_le_ringKrullDim_quotient_associated
          (d + 1) M hgrade p hp
        have hbad := hlower.trans hupper
        have : d + 1 ≤ d := by exact_mod_cast hbad
        omega
      have hMlt : maximalIdeal A • (⊤ : Submodule A M) < ⊤ := by
        haveI : Nontrivial M := by
          obtain ⟨gs, -, -, hgs⟩ := hgrade
          exact hgs.nontrivial
        exact maximalIdeal_smul_top_lt_top M
      have hxlt : x • (⊤ : Submodule A M) < ⊤ := by
        refine lt_of_le_of_lt ?_ hMlt
        rw [← Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mono (Ideal.span_le.mpr (by simpa using hxmem)) le_rfl
      let N := M ⧸ (x • (⊤ : Submodule A M))
      let hfinN : Module.Finite A N := Module.Finite.of_surjective
        (Submodule.mkQ (x • (⊤ : Submodule A M))) (Submodule.mkQ_surjective _)
      letI : Module.Finite A N := hfinN
      haveI : Nontrivial N := Submodule.Quotient.nontrivial_iff.mpr hxlt.ne
      have hNlt : maximalIdeal A • (⊤ : Submodule A N) < ⊤ :=
        @maximalIdeal_smul_top_lt_top A _ _ _ N _ _ hfinN inferInstance
      have hgradeN : HasGradeGE (maximalIdeal A) (ModuleCat.of A N) d := by
        refine hasGradeGE_quotSMulTop (ModuleCat.of A M) hxreg hMlt hNlt ?_
        simpa only [Nat.succ_eq_add_one] using hgrade
      have hspanX : Ideal.span {x} ≤ Module.annihilator A N := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        change (Module.toAddMonoidEnd A N) x = 0
        ext z
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
          (p := x • (⊤ : Submodule A M)) z
        change x • (Submodule.Quotient.mk v : M ⧸ (x • (⊤ : Submodule A M))) = 0
        rw [← Submodule.Quotient.mk_smul (x • (⊤ : Submodule A M)),
          Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
      have hannN : Module.annihilator A M ≤ Module.annihilator A N :=
        LinearMap.annihilator_le_of_surjective
          (Submodule.mkQ (x • (⊤ : Submodule A M))) (Submodule.mkQ_surjective _)
      have hspanN : maximalIdeal A ≤
          (Ideal.ofList t ⊔ Module.annihilator A N).radical := by
        have hinc : Ideal.ofList (x :: t) ⊔ Module.annihilator A M ≤
            Ideal.ofList t ⊔ Module.annihilator A N := by
          rw [ofList_cons]
          refine sup_le (sup_le ?_ le_sup_left) ?_
          · exact hspanX.trans le_sup_right
          · exact hannN.trans le_sup_right
        exact hspan.trans (Ideal.radical_mono hinc)
      rw [isWeaklyRegular_cons_iff]
      exact ⟨hxreg, ih htlen htmem hspanN hgradeN⟩

/-- Full grade relative to generators modulo the annihilator makes those generators weakly
regular. -/
theorem isWeaklyRegular_of_hasGradeGE_of_maximalIdeal_le_sup_annihilator
    (d : ℕ) {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {rs : List A} (hlen : rs.length = d)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A)
    (hspan : maximalIdeal A ≤ Ideal.ofList rs ⊔ Module.annihilator A M)
    (hgrade : HasGradeGE (maximalIdeal A) (ModuleCat.of A M) d) :
    IsWeaklyRegular M rs :=
  isWeaklyRegular_of_hasGradeGE_of_maximalIdeal_le_radical_sup_annihilator
    d hlen hmem (hspan.trans Ideal.le_radical) hgrade

/-- A maximal-ideal generating list of full module grade is weakly regular. -/
theorem isWeaklyRegular_of_hasGradeGE_of_ofList_eq_maximalIdeal
    (d : ℕ) {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {rs : List A} (hlen : rs.length = d)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hspan : Ideal.ofList rs = maximalIdeal A)
    (hgrade : HasGradeGE (maximalIdeal A) (ModuleCat.of A M) d) :
    IsWeaklyRegular M rs := by
  apply isWeaklyRegular_of_hasGradeGE_of_maximalIdeal_le_sup_annihilator d hlen
  · intro r hr
    rw [← hspan]
    exact Ideal.subset_span hr
  · rw [← hspan]
    exact le_sup_left
  · exact hgrade

/-- A finite module of full grade over a Noetherian local ring is free once a list of that length
generates the maximal ideal. -/
theorem free_of_hasGradeGE_of_ofList_eq_maximalIdeal
    (d : ℕ) {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {rs : List A} (hlen : rs.length = d)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hspan : Ideal.ofList rs = maximalIdeal A)
    (hgrade : HasGradeGE (maximalIdeal A) (ModuleCat.of A M) d) :
    Module.Free A M :=
  free_of_isWeaklyRegular_of_ofList_eq_maximalIdeal d hlen hspan
    (isWeaklyRegular_of_hasGradeGE_of_ofList_eq_maximalIdeal d hlen hspan hgrade)

end GaloisForLFunctions.HTGeometry
