import GaloisForLFunctions.HTGeometry.BorelWeil.CechHomotopy
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Bott's theorem for projective space: middle-degree vanishing

Let `T` index the homogeneous coordinates of `ℙⁿ`, `n + 1 = #T`, and let `O(d)` be the `d`-th Serre
twist.  The Čech complex of the standard affine cover `{X_u ≠ 0}_{u ∈ T}` has, in degree `p`, the
module `⊕_{#I = p+1} (k[X^{±}_{u ∈ I}, X_j])_d`.  Writing a Laurent monomial by its exponent vector
`a : T → ℤ`, the monomial `X^a` lies in the `I`-chart exactly when `negSet a ⊆ I`, so a Čech
`p`-cochain is a family `ω : Finset T → ((T → ℤ) →₀ k)` with

* `ω I = 0` unless `#I = p + 1`,
* every exponent in the support of `ω I` has total degree `d` and satisfies `negSet a ⊆ I`.

This file proves the **middle-degree vanishing** half of Bott's theorem in this model: for
`1 ≤ p` and `p + 1 < #T` every cocycle is a coboundary.  The proof is the contracting homotopy of
`CechHomotopy`, applied separately in each multidegree with the contracting index chosen outside
`negSet a` — possible exactly because `negSet a` is a proper subset of `T` in that range.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.negSet`
* `GaloisForLFunctions.HTGeometry.BorelWeil.IsCechCochain`
* `GaloisForLFunctions.HTGeometry.BorelWeil.cechDelta`

## Main results

* `cech_middle_vanishing`
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Finset

variable {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T] {k : Type*} [Field k]

/-- The coordinates at which a multidegree is negative. -/
def negSet (a : T → ℤ) : Finset T := Finset.univ.filter (fun j => a j < 0)

theorem mem_negSet {a : T → ℤ} {j : T} : j ∈ negSet a ↔ a j < 0 := by
  simp [negSet]

/-- The Čech cochain conditions for `O(d)` in degree `p`. -/
structure IsCechCochain (d : ℤ) (p : ℕ)
    (ω : Finset T → ((T → ℤ) →₀ k)) : Prop where
  card : ∀ I : Finset T, I.card ≠ p + 1 → ω I = 0
  deg : ∀ (I : Finset T) (a : T → ℤ), a ∈ (ω I).support → ∑ j, a j = d
  chart : ∀ (I : Finset T) (a : T → ℤ), a ∈ (ω I).support → negSet a ⊆ I

/-- The Čech differential. -/
noncomputable def cechDelta (ω : Finset T → ((T → ℤ) →₀ k)) :
    Finset T → ((T → ℤ) →₀ k) :=
  fun I => ∑ u ∈ I, (cechSign I u : k) • ω (I.erase u)

theorem cechDelta_apply (ω : Finset T → ((T → ℤ) →₀ k)) (I : Finset T) (a : T → ℤ) :
    (cechDelta ω I) a = cechD (fun J => (ω J) a) I := by
  classical
  rw [cechDelta, Finsupp.finsetSum_apply, cechD]
  exact Finset.sum_congr rfl fun u _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-- **Middle-degree vanishing.**  For `1 ≤ p` and `p + 1 < #T`, every Čech cocycle of degree `p`
is a coboundary. -/
theorem cech_middle_vanishing [Nonempty T] {d : ℤ} {p : ℕ} (hp : 1 ≤ p)
    (hpn : p + 1 < Fintype.card T)
    {ω : Finset T → ((T → ℤ) →₀ k)} (hω : IsCechCochain d p ω) (hδ : cechDelta ω = 0) :
    ∃ η : Finset T → ((T → ℤ) →₀ k), IsCechCochain d (p - 1) η ∧ cechDelta η = ω := by
  classical
  -- the local cocycle condition
  have hlocal : ∀ a : T → ℤ, cechD (fun J => (ω J) a) = 0 := by
    intro a
    funext I
    have := congrFun hδ I
    rw [← cechDelta_apply ω I a, this]
    simp
  -- a contracting index outside `negSet a`, chosen for every multidegree occurring
  have hchoice : ∀ a : T → ℤ, ∃ u : T,
      ((∃ I : Finset T, a ∈ (ω I).support) → u ∉ negSet a) := by
    intro a
    by_cases hex : ∃ I : Finset T, a ∈ (ω I).support
    · obtain ⟨I, hI⟩ := hex
      have hsub : negSet a ⊆ I := hω.chart I a hI
      have hcard : I.card = p + 1 := by
        by_contra hc
        rw [hω.card I hc] at hI
        simp at hI
      have hlt : (negSet a).card < Fintype.card T := by
        have := Finset.card_le_card hsub
        omega
      have hne : (Finset.univ \ negSet a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
        omega
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, fun _ => (Finset.mem_sdiff.mp hu).2⟩
    · exact ⟨Classical.arbitrary T, fun h => absurd h hex⟩
  choose u₀ hu₀ using hchoice
  -- the candidate primitive
  set S : Finset (T → ℤ) := Finset.univ.biUnion (fun J : Finset T => (ω J).support) with hS
  have hmemS : ∀ (I : Finset T) (a : T → ℤ),
      (cechH (u₀ a) (fun J => (ω J) a)) I ≠ 0 → a ∈ S := by
    intro I a ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at ha
        exact ha rfl
      exact Finset.mem_biUnion.mpr ⟨insert (u₀ a) I, Finset.mem_univ _,
        Finsupp.mem_support_iff.mpr this⟩
  refine ⟨fun I => Finsupp.onFinset S (fun a => (cechH (u₀ a) (fun J => (ω J) a)) I)
    (fun a ha => hmemS I a ha), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- support in cardinality `p`
    intro I hI
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
  · -- total degree
    intro I a ha
    rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have hne : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz; rw [hz, mul_zero] at ha; exact ha rfl
      exact hω.deg _ a (Finsupp.mem_support_iff.mpr hne)
  · -- chart condition
    intro I a ha
    rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have hne : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz; rw [hz, mul_zero] at ha; exact ha rfl
      have hsub := hω.chart _ a (Finsupp.mem_support_iff.mpr hne)
      have hnot : u₀ a ∉ negSet a := hu₀ a ⟨insert (u₀ a) I, Finsupp.mem_support_iff.mpr hne⟩
      intro j hj
      rcases Finset.mem_insert.mp (hsub hj) with rfl | hji
      · exact absurd hj hnot
      · exact hji
  · -- the homotopy identity
    funext I
    ext a
    rw [cechDelta_apply]
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

variable {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T] {k : Type*} [Field k]

theorem cechSign_pair_left {u v : T} (h : u < v) : (cechSign {u, v} u : k) = 1 := by
  have hfil : ({u, v} : Finset T).filter (fun w => w < u) = ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    rintro (rfl | rfl)
    · exact lt_irrefl _
    · exact fun hc => absurd (lt_trans h hc) (lt_irrefl _)
  rw [cechSign, belowCard, hfil]
  simp

theorem cechSign_pair_right {u v : T} (h : u < v) : (cechSign {u, v} v : k) = -1 := by
  have hfil : ({u, v} : Finset T).filter (fun w => w < v) = {u} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hw⟩
      · rfl
      · exact absurd hw (lt_irrefl _)
    · rintro rfl
      exact ⟨Or.inl rfl, h⟩
  rw [cechSign, belowCard, hfil]
  simp

theorem cechDelta_pair (ω : Finset T → ((T → ℤ) →₀ k)) {u v : T} (h : u < v) :
    cechDelta ω {u, v} = ω {v} - ω {u} := by
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
  rw [cechDelta, Finset.sum_pair hne, he1, he2, cechSign_pair_left (k := k) h,
    cechSign_pair_right (k := k) h, one_smul, neg_smul, one_smul, ← sub_eq_add_neg]

/-- **`H⁰` is the diagonal.**  A Čech `0`-cocycle takes the same value on every chart. -/
theorem cech_H0_const {ω : Finset T → ((T → ℤ) →₀ k)} (hδ : cechDelta ω = 0) (u v : T) :
    ω {u} = ω {v} := by
  rcases lt_trichotomy u v with h | rfl | h
  · have hc := congrFun hδ {u, v}
    rw [cechDelta_pair ω h] at hc
    exact (sub_eq_zero.mp hc).symm
  · rfl
  · have hc := congrFun hδ {v, u}
    rw [cechDelta_pair ω h] at hc
    exact sub_eq_zero.mp hc

/-- **`H⁰` consists of the honest degree-`d` forms.**  Every exponent occurring in a Čech
`0`-cocycle is nonnegative. -/
theorem cech_H0_nonneg (hT : 1 < Fintype.card T) {d : ℤ}
    {ω : Finset T → ((T → ℤ) →₀ k)} (hω : IsCechCochain d 0 ω) (hδ : cechDelta ω = 0)
    (u : T) {a : T → ℤ} (ha : a ∈ (ω {u}).support) (j : T) : 0 ≤ a j := by
  by_contra hj
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hT j
  have ha' : a ∈ (ω {w}).support := by
    rw [cech_H0_const hδ w u]
    exact ha
  have hsub := hω.chart {w} a ha'
  have hjmem : j ∈ ({w} : Finset T) := hsub (mem_negSet.mpr (by omega))
  rw [Finset.mem_singleton] at hjmem
  exact hw hjmem.symm

/-- **The image of the Čech differential in top degree.**  Every exponent of a top-degree
coboundary is nonnegative in at least one coordinate. -/
theorem cechDelta_top_exists_nonneg {d : ℤ} {p : ℕ}
    {η : Finset T → ((T → ℤ) →₀ k)} (hη : IsCechCochain d p η)
    {a : T → ℤ} (ha : a ∈ (cechDelta η Finset.univ).support) : ∃ u : T, 0 ≤ a u := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : ∀ u ∈ (Finset.univ : Finset T),
      (cechSign (Finset.univ : Finset T) u : k) * (η (Finset.univ.erase u)) a = 0 := by
    intro u _
    have hnot : (η (Finset.univ.erase u)) a = 0 := by
      by_contra hne
      have hsub := hη.chart _ a (Finsupp.mem_support_iff.mpr hne)
      have humem : u ∈ negSet a := mem_negSet.mpr (hcon u)
      exact (Finset.notMem_erase u Finset.univ) (hsub humem)
    rw [hnot, mul_zero]
  rw [Finsupp.mem_support_iff, cechDelta_apply, cechD] at ha
  exact ha (Finset.sum_eq_zero hzero)

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Finset

variable {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T] {k : Type*} [Field k]

theorem univ_erase_injective : Function.Injective (fun v : T => Finset.univ.erase v) := by
  intro x y hxy
  by_contra hne
  have hxy' : Finset.univ.erase x = Finset.univ.erase y := hxy
  have hy : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨fun hc => hne hc.symm,
    Finset.mem_univ y⟩
  rw [hxy'] at hy
  exact (Finset.notMem_erase y Finset.univ) hy

/-- **The image of the Čech differential in top degree, converse direction.**  Any family of
exponents that is nonnegative in at least one coordinate is a top-degree coboundary. -/
theorem exists_cechDelta_top {d : ℤ} {n : ℕ} (hcard : Fintype.card T = n + 1) (hn : 1 ≤ n)
    {s : (T → ℤ) →₀ k} (hdeg : ∀ a ∈ s.support, ∑ j, a j = d)
    (hpos : ∀ a ∈ s.support, ∃ u : T, 0 ≤ a u) :
    ∃ η : Finset T → ((T → ℤ) →₀ k),
      IsCechCochain d (n - 1) η ∧ cechDelta η Finset.univ = s := by
  classical
  haveI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hchoice : ∀ a : T → ℤ, ∃ u : T, (a ∈ s.support → 0 ≤ a u) := by
    intro a
    by_cases ha : a ∈ s.support
    · obtain ⟨u, hu⟩ := hpos a ha
      exact ⟨u, fun _ => hu⟩
    · exact ⟨Classical.arbitrary T, fun h => absurd h ha⟩
  · choose u hu using hchoice
    refine ⟨fun I => Finsupp.onFinset s.support
      (fun a => if Finset.univ.erase (u a) = I then (cechSign Finset.univ (u a) : k) * s a else 0)
      (fun a ha => ?_), ⟨?_, ?_, ?_⟩, ?_⟩
    · by_cases h : Finset.univ.erase (u a) = I
      · rw [if_pos h] at ha
        exact Finsupp.mem_support_iff.mpr fun hz => ha (by rw [hz, mul_zero])
      · rw [if_neg h] at ha
        exact absurd rfl ha
    · -- cardinality
      intro I hI
      ext a
      simp only [Finsupp.onFinset_apply, Finsupp.coe_zero, Pi.zero_apply]
      by_cases h : Finset.univ.erase (u a) = I
      · exfalso
        apply hI
        rw [← h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
        omega
      · rw [if_neg h]
    · -- total degree
      intro I a ha
      rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
      by_cases h : Finset.univ.erase (u a) = I
      · rw [if_pos h] at ha
        exact hdeg a (Finsupp.mem_support_iff.mpr fun hz => ha (by rw [hz, mul_zero]))
      · rw [if_neg h] at ha; exact absurd rfl ha
    · -- chart condition
      intro I a ha
      rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
      by_cases h : Finset.univ.erase (u a) = I
      · rw [if_pos h] at ha
        have hs : a ∈ s.support := Finsupp.mem_support_iff.mpr fun hz => ha (by rw [hz, mul_zero])
        rw [← h]
        intro j hj
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
        intro hcon
        have h1 : a j < 0 := mem_negSet.mp hj
        have h2 : 0 ≤ a (u a) := hu a hs
        rw [hcon] at h1
        omega
      · rw [if_neg h] at ha; exact absurd rfl ha
    · -- the differential recovers `s`
      ext a
      rw [cechDelta_apply, cechD]
      have hterm : ∀ v ∈ (Finset.univ : Finset T),
          (cechSign (Finset.univ : Finset T) v : k)
              * (Finsupp.onFinset s.support
                (fun b => if Finset.univ.erase (u b) = Finset.univ.erase v then
                  (cechSign Finset.univ (u b) : k) * s b else 0)
                (fun b hb => by
                  by_cases h : Finset.univ.erase (u b) = Finset.univ.erase v
                  · rw [if_pos h] at hb
                    exact Finsupp.mem_support_iff.mpr fun hz => hb (by rw [hz, mul_zero])
                  · rw [if_neg h] at hb; exact absurd rfl hb)) a
          = if u a = v then s a else 0 := by
        intro v _
        rw [Finsupp.onFinset_apply]
        by_cases h : u a = v
        · subst h
          rw [if_pos rfl, if_pos rfl, ← mul_assoc, cechSign_mul_self, one_mul]
        · rw [if_neg (fun hc => h (univ_erase_injective hc)), if_neg h, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq Finset.univ (u a) (fun _ => s a),
        if_pos (Finset.mem_univ _)]

end GaloisForLFunctions.HTGeometry.BorelWeil
