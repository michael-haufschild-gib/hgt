import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Multi-directional telescoping of a finitely supported divisor

A finitely supported `ℂ`-valued function on an abelian group whose sums along every line in a
finite family of infinite-order directions vanish is an iterated difference in those directions.

This is the combinatorial core of the all-depth pair-face descent: the bottom charge of a member of
the mixed-constraint class is a finitely supported divisor on the elliptic quotient whose orbit sums
vanish in every surviving direction, and the descent needs it written as the full difference cube of
another finitely supported divisor.

* `telescopeCube` — the iterated difference operator, in closed cube form;
* `telescopeCube_empty`, **`telescopeCube_insert`**;
* **`exists_telescope_one_direction`** — the one-direction peel, keeping finiteness and every other
  line-sum hypothesis;
* **`exists_telescopeCube`** — the full statement.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [AddCommGroup A]

/-- The iterated difference operator `∏_(i ∈ s) (T_(w i) − 1)`, in closed cube form. -/
def telescopeCube {ι : Type*} [DecidableEq ι] (w : ι → A) (s : Finset ι) (C : A → ℂ) :
    A → ℂ :=
  fun p => ∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) * C (p - ∑ i ∈ E, w i)

@[simp] theorem telescopeCube_empty {ι : Type*} [DecidableEq ι] (w : ι → A) (C : A → ℂ) :
    telescopeCube w (∅ : Finset ι) C = C := by
  funext p
  simp [telescopeCube]

theorem telescopeCube_insert {ι : Type*} [DecidableEq ι] (w : ι → A) {s : Finset ι} {q : ι}
    (hq : q ∉ s) (C : A → ℂ) :
    telescopeCube w (insert q s) C =
      fun p => telescopeCube w s C (p - w q) - telescopeCube w s C p := by
  classical
  funext p
  rw [telescopeCube, telescopeCube, telescopeCube,
    Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
  · have hcard : (insert q s).card = s.card + 1 := Finset.card_insert_of_notMem hq
    have hleft : ∑ E ∈ s.powerset,
        (-1 : ℂ) ^ ((insert q s).card - E.card) * C (p - ∑ i ∈ E, w i) =
        -∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) * C (p - ∑ i ∈ E, w i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun E hE => ?_
      have hEs : E.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hE)
      rw [hcard, show s.card + 1 - E.card = (s.card - E.card) + 1 by omega, pow_succ]
      ring
    have hright : ∑ E ∈ s.powerset,
        (-1 : ℂ) ^ ((insert q s).card - (insert q E).card) *
          C (p - ∑ i ∈ insert q E, w i) =
        ∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) * C (p - w q - ∑ i ∈ E, w i) := by
      refine Finset.sum_congr rfl fun E hE => ?_
      have hEsub : E ⊆ s := Finset.mem_powerset.mp hE
      have hqE : q ∉ E := fun h => hq (hEsub h)
      rw [Finset.card_insert_of_notMem hqE, hcard, Finset.sum_insert hqE,
        show p - (w q + ∑ i ∈ E, w i) = p - w q - ∑ i ∈ E, w i by abel]
      congr 2
      omega
    rw [hleft, hright]
    ring
  · intro E hE E' hE' hEE'
    have hqE : q ∉ E := fun h => hq (Finset.mem_powerset.mp hE h)
    have hqE' : q ∉ E' := fun h => hq (Finset.mem_powerset.mp hE' h)
    have h1 : (insert q E).erase q = E := Finset.erase_insert hqE
    have h2 : (insert q E').erase q = E' := Finset.erase_insert hqE'
    rw [← h1, hEE', h2]
  · rw [Finset.disjoint_right]
    intro E hE hEs
    obtain ⟨E', -, rfl⟩ := Finset.mem_image.mp hE
    exact hq (Finset.mem_powerset.mp hEs (Finset.mem_insert_self q E'))

/-! ## The one-direction peel -/

/-- Along an infinite-order direction, a line meets a finite set in finitely many places. -/
theorem finite_lineIndex {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0) (S : Finset A) (p : A) :
    {m : ℤ | p + m • w ∈ S}.Finite := by
  have hinj : Function.Injective (fun m : ℤ => p + m • w) := by
    intro m n hmn
    have hz : (m - n) • w = 0 := by
      have h := sub_eq_zero_of_eq hmn
      simpa [sub_smul, sub_eq_zero] using h
    have := hw _ hz
    omega
  have hpre : {m : ℤ | p + m • w ∈ S} = (fun m : ℤ => p + m • w) ⁻¹' (↑S : Set A) := rfl
  rw [hpre]
  exact Set.Finite.preimage (hinj.injOn) S.finite_toSet

/-- The forward tail of a divisor along a direction. -/
def lineTail (w : A) (D : A → ℂ) (p : A) : ℂ :=
  ∑ᶠ m : ℤ, if 1 ≤ m then D (p + m • w) else 0

theorem support_lineSummand_finite {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S) (p : A) (c : ℤ → Prop)
    [DecidablePred c] :
    (Function.support (fun m : ℤ => if c m then D (p + m • w) else 0)).Finite := by
  refine Set.Finite.subset (finite_lineIndex hw S p) ?_
  intro m hm
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hm
  obtain ⟨_, hne⟩ := hm
  exact hsupp _ hne

theorem lineTail_sub {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S) (p : A) :
    lineTail w D (p - w) - lineTail w D p = D p := by
  classical
  have hshift : lineTail w D (p - w) =
      ∑ᶠ m : ℤ, if 0 ≤ m then D (p + m • w) else 0 := by
    rw [lineTail]
    have hfun : ∀ m : ℤ,
        (if 1 ≤ m then D (p - w + m • w) else 0) =
          ((fun n : ℤ => if 0 ≤ n then D (p + n • w) else 0) ∘
            (Equiv.subRight (1 : ℤ))) m := by
      intro m
      by_cases hm : 1 ≤ m
      · have h0 : 0 ≤ m - 1 := by omega
        simp only [Function.comp_apply, Equiv.subRight_apply, if_pos hm, if_pos h0]
        congr 1
        rw [sub_smul, one_smul]
        abel
      · have h0 : ¬ (0 ≤ m - 1) := by omega
        simp only [Function.comp_apply, Equiv.subRight_apply, if_neg hm, if_neg h0]
    rw [finsum_congr hfun]
    exact finsum_comp_equiv (Equiv.subRight (1 : ℤ))
      (f := fun n : ℤ => if 0 ≤ n then D (p + n • w) else 0)
  rw [hshift, lineTail, ← finsum_sub_distrib
    (support_lineSummand_finite hw hsupp p (fun m => 0 ≤ m))
    (support_lineSummand_finite hw hsupp p (fun m => 1 ≤ m))]
  have hterm : ∀ m : ℤ,
      ((if 0 ≤ m then D (p + m • w) else 0) - (if 1 ≤ m then D (p + m • w) else 0)) =
        if m = 0 then D p else 0 := by
    intro m
    by_cases h0 : 0 ≤ m
    · by_cases h1 : 1 ≤ m
      · have hm0 : m ≠ 0 := by omega
        simp [h0, h1, hm0]
      · have hm0 : m = 0 := by omega
        subst hm0
        simp
    · have h1 : ¬ (1 ≤ m) := by omega
      have hm0 : m ≠ 0 := by omega
      simp [h0, h1, hm0]
  rw [finsum_congr hterm]
  simpa using finsum_eq_single (fun m : ℤ => if m = 0 then D p else 0) (0 : ℤ)
    (fun m hm => by simp [hm])

theorem lineTail_eq_zero_of_forall_pos {w : A} {D : A → ℂ} (p : A)
    (h : ∀ m : ℤ, 1 ≤ m → D (p + m • w) = 0) : lineTail w D p = 0 := by
  rw [lineTail]
  have hz : ∀ m : ℤ, (if 1 ≤ m then D (p + m • w) else 0) = (0 : ℂ) := by
    intro m
    by_cases hm : 1 ≤ m
    · simp [hm, h m hm]
    · simp [hm]
  rw [finsum_congr hz, finsum_zero]

theorem lineTail_eq_neg_head {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S)
    (hsum : ∀ p, ∑ᶠ m : ℤ, D (p + m • w) = 0) (p : A) :
    lineTail w D p = -∑ᶠ m : ℤ, (if m ≤ 0 then D (p + m • w) else 0) := by
  classical
  have hsplit : ∀ m : ℤ, D (p + m • w) =
      (if 1 ≤ m then D (p + m • w) else 0) + (if m ≤ 0 then D (p + m • w) else 0) := by
    intro m
    by_cases hm : 1 ≤ m
    · have hm' : ¬ (m ≤ 0) := by omega
      simp [hm, hm']
    · have hm' : m ≤ 0 := by omega
      simp [hm, hm']
  have hz := hsum p
  rw [finsum_congr hsplit, finsum_add_distrib
    (support_lineSummand_finite hw hsupp p (fun m => 1 ≤ m))
    (support_lineSummand_finite hw hsupp p (fun m => m ≤ 0))] at hz
  rw [lineTail]
  linear_combination hz

theorem lineTail_eq_zero_of_forall_nonpos {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S)
    (hsum : ∀ p, ∑ᶠ m : ℤ, D (p + m • w) = 0) (p : A)
    (h : ∀ m : ℤ, m ≤ 0 → D (p + m • w) = 0) : lineTail w D p = 0 := by
  rw [lineTail_eq_neg_head hw hsupp hsum p]
  have hz : ∀ m : ℤ, (if m ≤ 0 then D (p + m • w) else 0) = (0 : ℂ) := by
    intro m
    by_cases hm : m ≤ 0
    · simp [hm, h m hm]
    · simp [hm]
  rw [finsum_congr hz, finsum_zero, neg_zero]

/-- A point in the support of the tail lies on a line meeting the support of the divisor on both
sides. -/
theorem lineTail_support_two_sided {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S)
    (hsum : ∀ p, ∑ᶠ m : ℤ, D (p + m • w) = 0) {p : A} (hp : lineTail w D p ≠ 0) :
    (∃ m : ℤ, 1 ≤ m ∧ p + m • w ∈ S) ∧ (∃ m : ℤ, m ≤ 0 ∧ p + m • w ∈ S) := by
  constructor
  · by_contra hcon
    push_neg at hcon
    exact hp (lineTail_eq_zero_of_forall_pos p fun m hm => by
      by_contra hne
      exact hcon m hm (hsupp _ hne))
  · by_contra hcon
    push_neg at hcon
    exact hp (lineTail_eq_zero_of_forall_nonpos hw hsupp hsum p fun m hm => by
      by_contra hne
      exact hcon m hm (hsupp _ hne))

/-- **The tail of a finitely supported divisor with vanishing line sums is finitely
supported.** -/
theorem exists_finset_support_lineTail [DecidableEq A] {w : A}
    (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S)
    (hsum : ∀ p, ∑ᶠ m : ℤ, D (p + m • w) = 0) :
    ∃ S' : Finset A, ∀ p, lineTail w D p ≠ 0 → p ∈ S' := by
  classical
  have hbound : ∀ pr : A × A, ∃ N : ℤ, ∀ n : ℤ, pr.1 - pr.2 = n • w → n ≤ N := by
    intro pr
    by_cases h : ∃ n : ℤ, pr.1 - pr.2 = n • w
    · obtain ⟨n0, hn0⟩ := h
      refine ⟨n0, fun n hn => ?_⟩
      have hz : (n - n0) • w = 0 := by
        rw [sub_smul, ← hn, ← hn0, sub_self]
      have := hw _ hz
      omega
    · exact ⟨0, fun n hn => absurd ⟨n, hn⟩ h⟩
  choose Nf hNf using hbound
  set N : ℤ := (((S ×ˢ S).sup (fun pr => (Nf pr).toNat) : ℕ) : ℤ) with hN
  have hNle : ∀ pr ∈ S ×ˢ S, Nf pr ≤ N := by
    intro pr hpr
    have h1 : Nf pr ≤ ((Nf pr).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (Nf pr).toNat ≤ ((S ×ˢ S).sup (fun pr => (Nf pr).toNat)) :=
      Finset.le_sup (f := fun pr : A × A => (Nf pr).toNat) hpr
    refine h1.trans ?_
    rw [hN]
    exact_mod_cast h2
  refine ⟨S.biUnion (fun d => (Finset.Icc (1 : ℤ) N).image (fun m => d - m • w)), ?_⟩
  intro p hp
  obtain ⟨⟨m₁, hm₁, hd₁⟩, ⟨m₂, hm₂, hd₂⟩⟩ :=
    lineTail_support_two_sided hw hsupp hsum hp
  have hgap : (p + m₁ • w) - (p + m₂ • w) = (m₁ - m₂) • w := by
    rw [sub_smul]
    abel
  have hpr : ((p + m₁ • w, p + m₂ • w) : A × A) ∈ S ×ˢ S :=
    Finset.mem_product.mpr ⟨hd₁, hd₂⟩
  have hle : m₁ - m₂ ≤ N := (hNf _ _ hgap).trans (hNle _ hpr)
  have hm₁N : m₁ ≤ N := by omega
  refine Finset.mem_biUnion.mpr ⟨p + m₁ • w, hd₁, ?_⟩
  refine Finset.mem_image.mpr ⟨m₁, Finset.mem_Icc.mpr ⟨hm₁, hm₁N⟩, ?_⟩
  abel

/-- **The tail inherits every transverse line-sum vanishing.** -/
theorem finsum_lineTail_eq_zero {w v : A}
    (hfree : ∀ n m : ℤ, n • v + m • w = 0 → n = 0 ∧ m = 0)
    {D : A → ℂ} {S : Finset A} (hsupp : ∀ p, D p ≠ 0 → p ∈ S)
    (hv : ∀ q, ∑ᶠ n : ℤ, D (q + n • v) = 0) (p : A) :
    ∑ᶠ n : ℤ, lineTail w D (p + n • v) = 0 := by
  classical
  set g : ℤ × ℤ → ℂ :=
    fun nm => if 1 ≤ nm.2 then D (p + nm.1 • v + nm.2 • w) else 0 with hg
  have hginj : Function.Injective (fun nm : ℤ × ℤ => p + nm.1 • v + nm.2 • w) := by
    rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
    dsimp only at h
    have h2 : p + (n₁ • v + m₁ • w) = p + (n₂ • v + m₂ • w) := by
      rw [← add_assoc, ← add_assoc]
      exact h
    have h3 := add_left_cancel h2
    have hz : (n₁ - n₂) • v + (m₁ - m₂) • w = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]
      exact h3
    obtain ⟨ha, hb⟩ := hfree _ _ hz
    have hn : n₁ = n₂ := by omega
    have hm : m₁ = m₂ := by omega
    simp [hn, hm]
  have hgfin : (Function.support g).Finite := by
    refine Set.Finite.subset (Set.Finite.preimage (hginj.injOn) S.finite_toSet) ?_
    intro nm hnm
    have hne : D (p + nm.1 • v + nm.2 • w) ≠ 0 := by
      intro h0
      apply hnm
      simp only [hg]
      by_cases hc : 1 ≤ nm.2
      · rw [if_pos hc, h0]
      · rw [if_neg hc]
    exact hsupp _ hne
  have hleft : ∀ n : ℤ, lineTail w D (p + n • v) = ∑ᶠ m : ℤ, g (n, m) := fun n => rfl
  rw [finsum_congr hleft, ← finsum_curry g hgfin]
  have hswap : ∑ᶠ nm : ℤ × ℤ, g nm = ∑ᶠ mn : ℤ × ℤ, g (Equiv.prodComm ℤ ℤ mn) :=
    (finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := g)).symm
  rw [hswap]
  have hgfin' : (Function.support (fun mn : ℤ × ℤ => g (Equiv.prodComm ℤ ℤ mn))).Finite := by
    have hpre : Function.support (fun mn : ℤ × ℤ => g (Equiv.prodComm ℤ ℤ mn))
        = (Equiv.prodComm ℤ ℤ) ⁻¹' (Function.support g) := rfl
    rw [hpre]
    exact Set.Finite.preimage ((Equiv.prodComm ℤ ℤ).injective.injOn) hgfin
  rw [finsum_curry _ hgfin']
  have hrow : ∀ m : ℤ, (∑ᶠ n : ℤ, g (Equiv.prodComm ℤ ℤ (m, n))) = 0 := by
    intro m
    by_cases hm : 1 ≤ m
    · have hval : ∀ n : ℤ, g (Equiv.prodComm ℤ ℤ (m, n)) = D (p + m • w + n • v) := by
        intro n
        simp only [hg, Equiv.prodComm_apply, Prod.swap_prod_mk, if_pos hm]
        congr 1
        abel
      rw [finsum_congr hval]
      exact hv (p + m • w)
    · have hval : ∀ n : ℤ, g (Equiv.prodComm ℤ ℤ (m, n)) = 0 := by
        intro n
        simp only [hg, Equiv.prodComm_apply, Prod.swap_prod_mk, if_neg hm]
      rw [finsum_congr hval, finsum_zero]
  rw [finsum_congr hrow, finsum_zero]

/-! ## The full multi-directional telescoping -/

set_option maxHeartbeats 1000000 in
/-- **Multi-directional telescoping.**  A finitely supported divisor whose line sums vanish in
every direction of a finite family of pairwise free, infinite-order directions is the full
difference cube of a finitely supported divisor. -/
theorem exists_telescopeCube {ι : Type*} [DecidableEq ι] [DecidableEq A] (w : ι → A) :
    ∀ (s : Finset ι),
      (∀ i ∈ s, ∀ n : ℤ, n • w i = 0 → n = 0) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ n m : ℤ, n • w i + m • w j = 0 → n = 0 ∧ m = 0) →
      ∀ (D : A → ℂ) (S : Finset A), (∀ p, D p ≠ 0 → p ∈ S) →
      (∀ i ∈ s, ∀ p, ∑ᶠ m : ℤ, D (p + m • w i) = 0) →
      ∃ (C : A → ℂ) (S' : Finset A), (∀ p, C p ≠ 0 → p ∈ S') ∧
        ∀ p, telescopeCube w s C p = D p := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ D S hsupp _
      exact ⟨D, S, hsupp, fun p => by simp⟩
  | @insert q s' hq ih =>
      intro hw hfree D S hsupp hsum
      have hwq : ∀ n : ℤ, n • w q = 0 → n = 0 := hw q (Finset.mem_insert_self q s')
      have hsumq : ∀ p, ∑ᶠ m : ℤ, D (p + m • w q) = 0 :=
        hsum q (Finset.mem_insert_self q s')
      obtain ⟨S'', hS''⟩ := exists_finset_support_lineTail hwq hsupp hsumq
      have hEsum : ∀ i ∈ s', ∀ p, ∑ᶠ n : ℤ, lineTail (w q) D (p + n • w i) = 0 := by
        intro i hi p
        have hiq : i ≠ q := fun h => hq (h ▸ hi)
        refine finsum_lineTail_eq_zero (v := w i) (w := w q) ?_ hsupp
          (hsum i (Finset.mem_insert_of_mem hi)) p
        intro n m hnm
        exact hfree i (Finset.mem_insert_of_mem hi) q (Finset.mem_insert_self q s') hiq n m hnm
      obtain ⟨C, S₃, hS₃, hC⟩ := ih
        (fun i hi => hw i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hfree i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij)
        (lineTail (w q) D) S'' hS'' hEsum
      refine ⟨C, S₃, hS₃, ?_⟩
      intro p
      rw [telescopeCube_insert w hq C]
      show telescopeCube w s' C (p - w q) - telescopeCube w s' C p = D p
      rw [hC, hC]
      exact lineTail_sub hwq hsupp p

/-! ## Invariance under an infinite-order translation kills a finite divisor -/

/-- **A finitely supported divisor invariant under an infinite-order translation vanishes.** -/
theorem eq_zero_of_invariant_of_finite_support {R : A → ℂ} {S : Finset A}
    (hsupp : ∀ p, R p ≠ 0 → p ∈ S) {t : A} (ht : ∀ n : ℤ, n • t = 0 → n = 0)
    (hinv : ∀ p, R (p + t) = R p) (p : A) : R p = 0 := by
  classical
  by_contra hne
  have hstep : ∀ n : ℤ, R (p + n • t) = R p := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        have harg : p + ((k : ℤ) + 1) • t = (p + (k : ℤ) • t) + t := by
          rw [add_smul, one_smul]
          abel
        rw [harg, hinv, ih]
    | pred k ih =>
        have harg : (p + (-(k : ℤ) - 1) • t) + t = p + (-(k : ℤ)) • t := by
          rw [sub_smul, one_smul]
          abel
        have hh := hinv (p + (-(k : ℤ) - 1) • t)
        rw [harg, ih] at hh
        exact hh.symm
  have hinj : Function.Injective (fun n : ℤ => p + n • t) := by
    intro m n hmn
    have hz : (m - n) • t = 0 := by
      have h2 : p + (m • t) = p + (n • t) := hmn
      have h3 := add_left_cancel h2
      rw [sub_smul, sub_eq_zero]
      exact h3
    have := ht _ hz
    omega
  have hmaps : ∀ n : ℤ, (fun n : ℤ => p + n • t) n ∈ S := by
    intro n
    refine hsupp _ ?_
    rw [hstep n]
    exact hne
  have hsub : ((fun n : ℤ => p + n • t) '' Set.univ) ⊆ (↑S : Set A) := by
    rintro x ⟨n, -, rfl⟩
    exact hmaps n
  have himg := Set.Finite.subset S.finite_toSet hsub
  have hfin : (Set.univ : Set ℤ).Finite :=
    Set.Finite.of_finite_image himg hinj.injOn
  exact absurd hfin Set.infinite_univ.not_finite

/-- **A divisor with finitely many nonzero classes modulo a subgroup, invariant under a
translation of infinite order modulo that subgroup, vanishes.** -/
theorem eq_zero_of_invariant_of_finite_classes {R : A → ℂ} {S : Finset A}
    {H : AddSubgroup A}
    (hsupp : ∀ p, R p ≠ 0 → ∃ s ∈ S, p - s ∈ H)
    {t : A} (ht : ∀ n : ℤ, n • t ∈ H → n = 0)
    (hinv : ∀ p, R (p + t) = R p) (p : A) : R p = 0 := by
  classical
  by_contra hne
  have hstep : ∀ n : ℤ, R (p + n • t) = R p := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        have harg : p + ((k : ℤ) + 1) • t = (p + (k : ℤ) • t) + t := by
          rw [add_smul, one_smul]
          abel
        rw [harg, hinv, ih]
    | pred k ih =>
        have harg : (p + (-(k : ℤ) - 1) • t) + t = p + (-(k : ℤ)) • t := by
          rw [sub_smul, one_smul]
          abel
        have hh := hinv (p + (-(k : ℤ) - 1) • t)
        rw [harg, ih] at hh
        exact hh.symm
  have hchoice : ∀ n : ℤ, ∃ s ∈ S, p + n • t - s ∈ H := by
    intro n
    refine hsupp _ ?_
    rw [hstep n]
    exact hne
  choose f hfS hfH using hchoice
  have hmaps : Set.MapsTo f (Set.univ : Set ℤ) (↑S : Set A) := fun n _ => hfS n
  obtain ⟨m, -, n, -, hmn, hfeq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo Set.infinite_univ hmaps S.finite_toSet
  have hdiff : (m - n) • t ∈ H := by
    have h1 := hfH m
    have h2 := hfH n
    have h3 : (p + m • t - f m) - (p + n • t - f n) ∈ H := H.sub_mem h1 h2
    have harg : (p + m • t - f m) - (p + n • t - f n) = (m - n) • t := by
      rw [hfeq, sub_smul]
      abel
    rwa [harg] at h3
  exact hmn (by have := ht _ hdiff; omega)

end

end GaloisForLFunctions.HTGeometry
