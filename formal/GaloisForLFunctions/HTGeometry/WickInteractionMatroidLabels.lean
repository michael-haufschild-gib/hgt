import GaloisForLFunctions.HTGeometry.WickContractedInteractionMatroid
import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# The labeled Wick interaction matroid

Pulling the algebraic matroid of a field extension back along a labeled evaluation map keeps
distinct labels apart even when their evaluated values coincide: coincident labels become parallel
elements rather than being identified.  Contracting a base label packet and restricting to the
signal labels produces the interaction matroid of the labeled family.

This file supplies

* the relative-rank law for contraction of an arbitrary matroid, and its labeled form: the rank of
  a signal set in the interaction matroid is the rank of the evaluated signal-plus-base packet
  minus the rank of the evaluated base packet;
* invariance of the labeled matroid under an injective algebra map of the target field;
* freeness of the vertical jet pullback exactly at a differentially transcendental element.
-/

open Matroid Set

namespace GaloisForLFunctions.HTGeometry

section MatroidRank

variable {α : Type*}

/-- Deleting labels disjoint from a set leaves its rank unchanged. -/
theorem eRk_delete_eq_of_disjoint (M : Matroid α) {D X : Set α} (h : Disjoint X D) :
    (M ＼ D).eRk X = M.eRk X := by
  have hset : X ∩ (M.E \ D) = X ∩ M.E := by
    ext a
    constructor
    · rintro ⟨hx, hE, -⟩
      exact ⟨hx, hE⟩
    · rintro ⟨hx, hE⟩
      exact ⟨hx, hE, fun hD => Set.disjoint_left.mp h hx hD⟩
  rw [Matroid.delete_eq_restrict, Matroid.restrict_eRk_eq', hset, M.eRk_inter_ground]

/-- **Relative-rank law for contraction.**  For a signal set disjoint from the contracted base,
the rank in the contraction plus the rank of the base is the rank of their union. -/
theorem contract_eRk_add_eRk_eq (M : Matroid α) {C X : Set α}
    (hC : C ⊆ M.E) (hX : X ⊆ M.E) (hdisj : Disjoint X C) :
    (M ／ C).eRk X + M.eRk C = M.eRk (X ∪ C) := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis C hC
  have hJC : J ⊆ C := hJ.subset
  have hXJ : Disjoint X J := hdisj.mono_right hJC
  have hdel : (M ／ C).eRk X = (M ／ J).eRk X := by
    rw [hJ.contract_eq_contract_delete]
    exact eRk_delete_eq_of_disjoint (M ／ J) (hdisj.mono_right Set.sdiff_subset)
  have hXground : X ⊆ (M ／ J).E := by
    rw [Matroid.contract_ground]
    exact Set.subset_sdiff.mpr ⟨hX, hXJ⟩
  obtain ⟨K, hK⟩ := (M ／ J).exists_isBasis X hXground
  have hKJ : Disjoint K J := by
    refine Set.disjoint_left.mpr fun a ha haJ => ?_
    have hmem := hK.indep.subset_ground ha
    rw [Matroid.contract_ground] at hmem
    exact hmem.2 haJ
  have hbasis : M.IsBasis (K ∪ J) (X ∪ J) :=
    hJ.indep.union_isBasis_union_of_contract_isBasis hK
  have h1 : M.eRk (X ∪ J) = K.encard + J.encard := by
    rw [← hbasis.encard_eq_eRk, Set.encard_union_eq hKJ]
  have h2 : M.eRk (X ∪ C) = M.eRk (X ∪ J) := by
    rw [← M.eRk_closure_eq (X ∪ C), ← M.eRk_closure_eq (X ∪ J),
      Matroid.closure_union_congr_right hJ.closure_eq_closure]
  rw [hdel, h2, h1, ← hK.encard_eq_eRk, ← hJ.encard_eq_eRk]

end MatroidRank

section Labels

variable {K L E ι : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]

/-- The labeled algebraic matroid of an evaluation map: a labeled set is independent exactly when
the evaluation is injective on it and its image is algebraically independent. -/
def wickLabelMatroid (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (ev : ι → L) : Matroid ι :=
  (AlgebraicIndependent.matroid K L).comap ev

@[simp]
theorem wickLabelMatroid_ground (ev : ι → L) :
    (wickLabelMatroid K ev).E = Set.univ := by
  simp [wickLabelMatroid]

theorem wickLabelMatroid_indep_iff (ev : ι → L) {I : Set ι} :
    (wickLabelMatroid K ev).Indep I ↔
      AlgebraicIndepOn K id (ev '' I) ∧ Set.InjOn ev I := Iff.rfl

theorem wickLabelMatroid_eRk (ev : ι → L) (X : Set ι) :
    (wickLabelMatroid K ev).eRk X = (AlgebraicIndependent.matroid K L).eRk (ev '' X) :=
  Matroid.eRk_comap _ _

/-- The labeled interaction matroid: contract the base labels, keep the signal labels. -/
def wickInteractionMatroid (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (ev : ι → L) (base signal : Set ι) : Matroid ι :=
  wickContractedInteractionMatroid (wickLabelMatroid K ev) base signal

/-- **Relative-rank law.**  On the signal labels, the interaction matroid measures exactly the
rank the signal packet adds to the evaluated base packet. -/
theorem wickInteractionMatroid_eRk_add_eRk_eq (ev : ι → L) {base signal T : Set ι}
    (hT : T ⊆ signal) (hdisj : Disjoint signal base) :
    (wickInteractionMatroid K ev base signal).eRk T +
        (AlgebraicIndependent.matroid K L).eRk (ev '' base) =
      (AlgebraicIndependent.matroid K L).eRk (ev '' (T ∪ base)) := by
  have hrestrict : (wickInteractionMatroid K ev base signal).eRk T =
      (wickLabelMatroid K ev ／ base).eRk T := by
    unfold wickInteractionMatroid wickContractedInteractionMatroid
    exact Matroid.restrict_eRk_eq _ hT
  have h1 : (AlgebraicIndependent.matroid K L).eRk (ev '' base) =
      (wickLabelMatroid K ev).eRk base := (wickLabelMatroid_eRk ev base).symm
  have h2 : (AlgebraicIndependent.matroid K L).eRk (ev '' (T ∪ base)) =
      (wickLabelMatroid K ev).eRk (T ∪ base) := (wickLabelMatroid_eRk ev (T ∪ base)).symm
  rw [hrestrict, h1, h2]
  exact contract_eRk_add_eRk_eq _ (by simp) (by simp) (hdisj.mono_left hT)

/-- **Relative-rank law, subtractive form.**  For finite label packets the interaction rank of a
signal set is the difference of the two evaluated packet ranks. -/
theorem wickInteractionMatroid_eRk_toNat_eq_sub (ev : ι → L) {base signal T : Set ι}
    (hT : T ⊆ signal) (hdisj : Disjoint signal base)
    (hbase : base.Finite) (hTfin : T.Finite) :
    ((wickInteractionMatroid K ev base signal).eRk T).toNat =
      ((AlgebraicIndependent.matroid K L).eRk (ev '' (T ∪ base))).toNat -
        ((AlgebraicIndependent.matroid K L).eRk (ev '' base)).toNat := by
  have hkey := wickInteractionMatroid_eRk_add_eRk_eq (K := K) ev hT hdisj
  have hbaseTop : (AlgebraicIndependent.matroid K L).eRk (ev '' base) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ ((AlgebraicIndependent.matroid K L).eRk_le_encard (ev '' base))
    exact (hbase.image ev).encard_lt_top.ne
  have hsignalTop : (wickInteractionMatroid K ev base signal).eRk T ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ ((wickInteractionMatroid K ev base signal).eRk_le_encard T)
    exact hTfin.encard_lt_top.ne
  have htoNat := congrArg ENat.toNat hkey
  rw [ENat.toNat_add hsignalTop hbaseTop] at htoNat
  omega
theorem wickLabelMatroid_algHom (φ : L →ₐ[K] E) (hφ : Function.Injective φ) (ev : ι → L) :
    wickLabelMatroid K (fun i => φ (ev i)) = wickLabelMatroid K ev := by
  refine Matroid.ext_indep (by simp) fun I _ => ?_
  rw [wickLabelMatroid_indep_iff, wickLabelMatroid_indep_iff]
  constructor
  · rintro ⟨hindep, hinj⟩
    refine ⟨?_, fun a ha b hb hab => hinj ha hb (by simp [hab])⟩
    have himage : (fun i => φ (ev i)) '' I = φ '' (ev '' I) := by
      rw [Set.image_image]
    rw [himage] at hindep
    have hcomp : AlgebraicIndependent K
        (fun y : (ev '' I) => φ ((id : L → L) y)) := by
      refine hindep.comp (fun y : (ev '' I) => ⟨φ (y : L), ⟨(y : L), y.2, rfl⟩⟩) ?_
      intro y z hyz
      exact Subtype.ext (hφ (congrArg Subtype.val hyz))
    exact AlgebraicIndependent.of_comp φ hcomp
  · rintro ⟨hindep, hinj⟩
    refine ⟨?_, fun a ha b hb hab => hinj ha hb (hφ hab)⟩
    have himage : (fun i => φ (ev i)) '' I = φ '' (ev '' I) := by
      rw [Set.image_image]
    have hmap : AlgebraicIndependent K (fun y : (ev '' I) => φ ((id : L → L) y)) :=
      hindep.map' hφ
    have hrange : φ '' (ev '' I) = Set.range (fun y : (ev '' I) => φ ((id : L → L) y)) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨(y : L), y.2, rfl⟩
    rw [himage, hrange]
    exact (algebraicIndependent_subtype_range
      (fun a b hab => Subtype.ext (hφ hab))).mpr hmap

/-- **Wick-collapse law.**  If every evaluated signal label is algebraic over the algebra generated
by the evaluated base labels, then every signal label is a loop of the interaction matroid. -/
theorem wickInteractionMatroid_eq_loopyOn (ev : ι → L) {base signal : Set ι}
    (hdisj : Disjoint signal base)
    (halg : ∀ s ∈ signal, IsAlgebraic (Algebra.adjoin K (ev '' base)) (ev s)) :
    wickInteractionMatroid K ev base signal = Matroid.loopyOn signal := by
  refine wickContractedInteractionMatroid_eq_loopyOn_of_signal_subset_closure _ hdisj ?_
  intro s hs
  rw [wickLabelMatroid, Matroid.comap_closure_eq, Set.mem_preimage,
    AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure]
  exact halg s hs

/-- **Full counterterm neutrality.**  Counterterm labels whose values are algebraic over the
evaluated base leave the whole interaction matroid on the signal labels unchanged. -/
theorem wickInteractionMatroid_counterterm_neutral (ev : ι → L)
    {base counterterms signal : Set ι}
    (hcb : Disjoint counterterms base) (hcs : Disjoint counterterms signal)
    (halg : ∀ c ∈ counterterms, IsAlgebraic (Algebra.adjoin K (ev '' base)) (ev c)) :
    wickInteractionMatroid K ev (base ∪ counterterms) signal =
      wickInteractionMatroid K ev base signal := by
  refine wickContractedInteractionMatroid_eq_of_counterterms_subset_closure _ hcb hcs ?_
  intro c hc
  rw [wickLabelMatroid, Matroid.comap_closure_eq, Set.mem_preimage,
    AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure]
  exact halg c hc

/-- **Vertical freeness.**  The pullback of the algebraic matroid along a sequence is the free
matroid exactly when the sequence is algebraically independent. -/
theorem wickLabelMatroid_eq_freeOn_iff (j : ℕ → L) :
    wickLabelMatroid K j = Matroid.freeOn Set.univ ↔ AlgebraicIndependent K j := by
  constructor
  · intro h
    have huniv : (wickLabelMatroid K j).Indep Set.univ := by
      rw [h]
      simp
    rw [wickLabelMatroid_indep_iff] at huniv
    obtain ⟨hindep, hinj⟩ := huniv
    have hinj' : Function.Injective j := fun a b hab =>
      hinj (Set.mem_univ a) (Set.mem_univ b) hab
    have hrange : j '' Set.univ = Set.range j := Set.image_univ
    rw [hrange] at hindep
    exact (algebraicIndependent_subtype_range hinj').mp hindep
  · intro h
    refine Matroid.ext_indep (by simp) fun I _ => ?_
    rw [wickLabelMatroid_indep_iff, Matroid.freeOn_indep_iff]
    simp only [Set.subset_univ, iff_true]
    refine ⟨?_, fun a _ b _ hab => h.injective hab⟩
    have hsub : AlgebraicIndependent K (fun i : I => j (i : ℕ)) :=
      h.comp (fun i : I => (i : ℕ)) Subtype.val_injective
    have himage : AlgebraicIndependent K
        ((↑) : Set.range (fun i : I => j (i : ℕ)) → L) :=
      (algebraicIndependent_subtype_range
        (fun a b hab => Subtype.ext (h.injective hab))).mpr hsub
    have hrange : Set.range (fun i : I => j (i : ℕ)) = j '' I := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(i : ℕ), i.2, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, rfl⟩
    rw [hrange] at himage
    exact himage

end Labels

section VerticalJets

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]

/-- An algebra map commuting with the derivations preserves every jet order. -/
private theorem differentialJet_algHom {E : Type*} [Field E] [Algebra K E] [Differential E]
    (φ : L →ₐ[K] E) (hφ : ∀ y : L, φ (Differential.deriv y) = Differential.deriv (φ y))
    (n : ℕ) (y : L) : φ (differentialJet n y) = differentialJet n (φ y) := by
  induction n with
  | zero => simp [differentialJet]
  | succ n ih =>
      simp only [differentialJet, Function.iterate_succ_apply'] at ih ⊢
      rw [hφ, ih]

/-- **Vertical hypertranscendence law.**  The labeled matroid of the vertical jet tower of an
element is free exactly when that element is differentially transcendental. -/
theorem wickLabelMatroid_differentialJet_eq_freeOn_iff (x : L) :
    wickLabelMatroid K (fun n : ℕ => differentialJet n x) = Matroid.freeOn Set.univ ↔
      DifferentialIndependent K (fun _ : Unit => x) := by
  rw [wickLabelMatroid_eq_freeOn_iff]
  have hcomp : ((fun n : ℕ => differentialJet n x) ∘ (Equiv.punitProd ℕ)) =
      fun p : Unit × ℕ => differentialJet p.2 x := by
    funext p
    rfl
  rw [DifferentialIndependent, ← hcomp]
  exact (algebraicIndependent_equiv (Equiv.punitProd ℕ)).symm

end VerticalJets

end GaloisForLFunctions.HTGeometry
