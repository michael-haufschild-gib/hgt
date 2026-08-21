import GaloisForLFunctions.HTGeometry.BorelWeil.CechHomotopy
import GaloisForLFunctions.HTGeometry.BorelWeil.BottProjectiveSpace
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Čech complexes relative to a support function

The Čech computation for line bundles on projective space used only one feature of the situation:
each basis vector of the sections (there, a Laurent monomial) is regular on the charts of a
prescribed subset, and the differential is the alternating sum over the cover.  This file isolates
that structure for an arbitrary cover index `T`, an arbitrary basis index `A`, and an arbitrary
*support function* `supp : A → Finset T` recording the charts on which a basis vector fails to be
regular.

This is the shape the Čech complex of the Bruhat cover of a flag variety takes as well, with `T`
the Weyl group and `A` the torus weights; so the vanishing proved here is the general mechanism
behind Bott-type theorems, not only the projective-space case.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.IsCechCochainOf`
* `GaloisForLFunctions.HTGeometry.BorelWeil.cechDeltaOf`

## Main results

* `cech_vanishing_of_supp_ne_univ` — a cocycle supported on basis vectors whose support sets are
  proper subsets of the cover is a coboundary, in every positive degree.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Finset

variable {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T]
variable {A : Type*} [DecidableEq A] {k : Type*} [Field k]

/-- The Čech cochain conditions relative to a support function. -/
structure IsCechCochainOf (supp : A → Finset T) (p : ℕ) (ω : Finset T → (A →₀ k)) : Prop where
  card : ∀ I : Finset T, I.card ≠ p + 1 → ω I = 0
  chart : ∀ (I : Finset T) (a : A), a ∈ (ω I).support → supp a ⊆ I

/-- The Čech differential. -/
noncomputable def cechDeltaOf (ω : Finset T → (A →₀ k)) : Finset T → (A →₀ k) :=
  fun I => ∑ u ∈ I, (cechSign I u : k) • ω (I.erase u)

theorem cechDeltaOf_apply (ω : Finset T → (A →₀ k)) (I : Finset T) (a : A) :
    (cechDeltaOf ω I) a = cechD (fun J => (ω J) a) I := by
  classical
  rw [cechDeltaOf, Finsupp.finsetSum_apply, cechD]
  exact Finset.sum_congr rfl fun u _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-- **Vanishing away from the extreme support.**  A Čech cocycle of positive degree, all of whose
basis vectors have support a proper subset of the cover, is a coboundary. -/
theorem cech_vanishing_of_supp_ne_univ [Nonempty T] {supp : A → Finset T} {p : ℕ} (hp : 1 ≤ p)
    {ω : Finset T → (A →₀ k)} (hω : IsCechCochainOf supp p ω) (hδ : cechDeltaOf ω = 0)
    (hne : ∀ (I : Finset T) (a : A), a ∈ (ω I).support → supp a ≠ Finset.univ) :
    ∃ η : Finset T → (A →₀ k), IsCechCochainOf supp (p - 1) η ∧ cechDeltaOf η = ω := by
  classical
  have hlocal : ∀ a : A, cechD (fun J => (ω J) a) = 0 := by
    intro a
    funext I
    have hI := congrFun hδ I
    rw [← cechDeltaOf_apply ω I a, hI]
    simp
  -- a contracting index outside the support set, for every basis vector that occurs
  have hchoice : ∀ a : A, ∃ u : T,
      ((∃ I : Finset T, a ∈ (ω I).support) → u ∉ supp a) := by
    intro a
    by_cases hex : ∃ I : Finset T, a ∈ (ω I).support
    · obtain ⟨I, hI⟩ := hex
      have hproper : supp a ≠ Finset.univ := hne I a hI
      have hnonempty : (Finset.univ \ supp a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
        have hle : (supp a).card ≤ Fintype.card T := by
          simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (supp a))
        have hlt : (supp a).card ≠ Fintype.card T := by
          intro hcon
          exact hproper (Finset.eq_univ_of_card _ (by simpa [Finset.card_univ] using hcon))
        omega
      obtain ⟨u, hu⟩ := hnonempty
      exact ⟨u, fun _ => (Finset.mem_sdiff.mp hu).2⟩
    · exact ⟨Classical.arbitrary T, fun h => absurd h hex⟩
  choose u₀ hu₀ using hchoice
  set S : Finset A := Finset.univ.biUnion (fun J : Finset T => (ω J).support) with hS
  have hmemS : ∀ (I : Finset T) (a : A),
      (cechH (u₀ a) (fun J => (ω J) a)) I ≠ 0 → a ∈ S := by
    intro I a ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have hne0 : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at ha
        exact ha rfl
      exact Finset.mem_biUnion.mpr ⟨insert (u₀ a) I, Finset.mem_univ _,
        Finsupp.mem_support_iff.mpr hne0⟩
  refine ⟨fun I => Finsupp.onFinset S (fun a => (cechH (u₀ a) (fun J => (ω J) a)) I)
    (fun a ha => hmemS I a ha), ⟨?_, ?_⟩, ?_⟩
  · intro I hI
    ext a
    simp only [Finsupp.onFinset_apply, Finsupp.coe_zero, Pi.zero_apply]
    rw [cechH]
    by_cases h : u₀ a ∈ I
    · rw [if_pos h]
    · rw [if_neg h]
      have hcard : (insert (u₀ a) I).card ≠ p + 1 := by
        rw [Finset.card_insert_of_notMem h]
        omega
      rw [hω.card _ hcard]
      simp
  · intro I a ha
    rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have hne0 : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz; rw [hz, mul_zero] at ha; exact ha rfl
      have hsub := hω.chart _ a (Finsupp.mem_support_iff.mpr hne0)
      have hnot : u₀ a ∉ supp a := hu₀ a ⟨insert (u₀ a) I, Finsupp.mem_support_iff.mpr hne0⟩
      intro j hj
      rcases Finset.mem_insert.mp (hsub hj) with rfl | hji
      · exact absurd hj hnot
      · exact hji
  · funext I
    ext a
    rw [cechDeltaOf_apply]
    have hfun : (fun J => (Finsupp.onFinset S
        (fun b => (cechH (u₀ b) (fun K => (ω K) b)) J) (fun b hb => hmemS J b hb)) a)
        = cechH (u₀ a) (fun K => (ω K) a) := by
      funext J
      rw [Finsupp.onFinset_apply]
    rw [hfun]
    have hid := cechD_cechH_add (u₀ a) (fun K => (ω K) a) I
    rw [hlocal a] at hid
    simpa using hid

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Finset

variable {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T]
variable {A : Type*} [DecidableEq A] {k : Type*} [Field k]

theorem cechDeltaOf_pair (ω : Finset T → (A →₀ k)) {u v : T} (h : u < v) :
    cechDeltaOf ω {u, v} = ω {v} - ω {u} := by
  have hne : u ≠ v := ne_of_lt h
  have he1 : ({u, v} : Finset T).erase u = {v} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, rfl | rfl⟩
      · exact absurd rfl hw
      · rfl
    · rintro rfl; exact ⟨fun hc => hne hc.symm, Or.inr rfl⟩
  have he2 : ({u, v} : Finset T).erase v = {u} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, rfl | rfl⟩
      · rfl
      · exact absurd rfl hw
    · rintro rfl; exact ⟨hne, Or.inl rfl⟩
  rw [cechDeltaOf, Finset.sum_pair hne, he1, he2, cechSign_pair_left (k := k) h,
    cechSign_pair_right (k := k) h, one_smul, neg_smul, one_smul, ← sub_eq_add_neg]

/-- **Degree zero: a cocycle is the same on every chart.** -/
theorem cechOf_H0_const {ω : Finset T → (A →₀ k)} (hδ : cechDeltaOf ω = 0) (u v : T) :
    ω {u} = ω {v} := by
  rcases lt_trichotomy u v with h | rfl | h
  · have hc := congrFun hδ {u, v}
    rw [cechDeltaOf_pair ω h] at hc
    exact (sub_eq_zero.mp hc).symm
  · rfl
  · have hc := congrFun hδ {v, u}
    rw [cechDeltaOf_pair ω h] at hc
    exact sub_eq_zero.mp hc

/-- **Degree zero: the basis vectors of a cocycle are regular on every chart.** -/
theorem cechOf_H0_supp_eq_empty (hT : 1 < Fintype.card T) {supp : A → Finset T}
    {ω : Finset T → (A →₀ k)} (hω : IsCechCochainOf supp 0 ω) (hδ : cechDeltaOf ω = 0)
    (u : T) {a : A} (ha : a ∈ (ω {u}).support) : supp a = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hT j
  have ha' : a ∈ (ω {w}).support := by
    rw [cechOf_H0_const hδ w u]
    exact ha
  have hjmem : j ∈ ({w} : Finset T) := hω.chart {w} a ha' hj
  rw [Finset.mem_singleton] at hjmem
  exact hw hjmem.symm

/-- **Top degree: the basis vectors of a coboundary miss at least one chart index.** -/
theorem cechDeltaOf_top_supp_ne_univ {supp : A → Finset T} {p : ℕ}
    {η : Finset T → (A →₀ k)} (hη : IsCechCochainOf supp p η)
    {a : A} (ha : a ∈ (cechDeltaOf η Finset.univ).support) : supp a ≠ Finset.univ := by
  classical
  intro hcon
  have hzero : ∀ u ∈ (Finset.univ : Finset T),
      (cechSign (Finset.univ : Finset T) u : k) * (η (Finset.univ.erase u)) a = 0 := by
    intro u _
    have hnot : (η (Finset.univ.erase u)) a = 0 := by
      by_contra hne
      have hsub := hη.chart _ a (Finsupp.mem_support_iff.mpr hne)
      have humem : u ∈ supp a := by rw [hcon]; exact Finset.mem_univ u
      exact (Finset.notMem_erase u Finset.univ) (hsub humem)
    rw [hnot, mul_zero]
  rw [Finsupp.mem_support_iff, cechDeltaOf_apply, cechD] at ha
  exact ha (Finset.sum_eq_zero hzero)

end GaloisForLFunctions.HTGeometry.BorelWeil
