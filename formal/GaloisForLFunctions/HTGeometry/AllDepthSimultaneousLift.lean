import GaloisForLFunctions.HTGeometry.AllDepthTelescope

/-!
# Simultaneous lifting of a compatible family of finite divisors

Fix one direction and a finite family of transverse directions, all of infinite order and pairwise
free.  A family of divisors, one for each transverse direction and each invariant along its own
direction, whose pairwise orbit sums agree, is the family of orbit-sum pushforwards of a single
finitely supported divisor.

The proof is the exactness statement behind the pair-face normal form: lift all but the last
component, subtract, and observe that the error has vanishing orbit sums in every earlier
direction; multi-directional telescoping on the quotient by the last direction then writes it as a
full difference cube, whose lift disturbs no earlier component.

* `orbitSum`, `orbitSum_invariant`, `orbitSum_finite_classes`;
* `orbitSum_telescopeCube_eq_zero` — a full difference cube has no orbit sum in its own directions;
* **`exists_simultaneous_lift`**.
-/

open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [AddCommGroup A]

/-! ## Orbit sums -/

/-- The orbit sum of a divisor along one direction. -/
def orbitSum (w : A) (B : A → ℂ) (p : A) : ℂ := ∑ᶠ n : ℤ, B (p + n • w)

theorem orbitSum_invariant (w : A) (B : A → ℂ) (p : A) :
    orbitSum w B (p + w) = orbitSum w B p := by
  rw [orbitSum, orbitSum]
  have hterm : ∀ n : ℤ, B (p + w + n • w) = B (p + ((n + 1 : ℤ)) • w) := by
    intro n
    congr 1
    rw [add_smul, one_smul]
    abel
  rw [finsum_congr hterm]
  exact finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun n : ℤ => B (p + n • w))

/-- A function invariant under one step is invariant under the whole line. -/
theorem invariant_zsmul {w : A} {B : A → ℂ} (h : ∀ p, B (p + w) = B p) (p : A) (n : ℤ) :
    B (p + n • w) = B p := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have harg : p + ((k : ℤ) + 1) • w = (p + (k : ℤ) • w) + w := by
        rw [add_smul, one_smul]
        abel
      rw [harg, h, ih]
  | pred k ih =>
      have harg : (p + (-(k : ℤ) - 1) • w) + w = p + (-(k : ℤ)) • w := by
        rw [sub_smul, one_smul]
        abel
      have hh := h (p + (-(k : ℤ) - 1) • w)
      rw [harg, ih] at hh
      exact hh.symm

theorem orbitSum_finite_classes {B : A → ℂ} {S : Finset A} (hS : ∀ p, B p ≠ 0 → p ∈ S)
    (w : A) {p : A} (h : orbitSum w B p ≠ 0) : ∃ q ∈ S, ∃ n : ℤ, p = q + n • w := by
  classical
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [orbitSum]
  refine finsum_eq_zero_of_forall_eq_zero fun n => ?_
  by_contra hne
  exact hcon (p + n • w) (hS _ hne) (-n) (by rw [neg_smul]; abel)

/-- A one-step difference of a finitely supported divisor has vanishing orbit sum. -/
theorem orbitSum_step_eq_zero {G : A → ℂ} {S : Finset A} (hS : ∀ p, G p ≠ 0 → p ∈ S)
    {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0) (p : A) :
    orbitSum w (fun q => G (q - w) - G q) p = 0 := by
  classical
  set g : ℤ → ℂ := fun n => G (p + n • w) with hg
  have hgsupp : (Function.support g).Finite := by
    refine Set.Finite.subset (finite_lineIndex hw S p) ?_
    intro n hn
    exact hS _ hn
  have hshift : (Function.support fun n : ℤ => g (n - 1)).Finite := by
    have := hgsupp.image (fun n : ℤ => n + 1)
    refine Set.Finite.subset this ?_
    intro n hn
    exact ⟨n - 1, hn, by ring⟩
  have hterm : ∀ n : ℤ, G (p + n • w - w) - G (p + n • w) = g (n - 1) - g n := by
    intro n
    have harg : p + n • w - w = p + (n - 1) • w := by
      rw [sub_smul, one_smul]
      abel
    rw [harg]
  rw [orbitSum, finsum_congr hterm, finsum_sub_distrib hshift hgsupp]
  have hre : ∑ᶠ n : ℤ, g (n - 1) = ∑ᶠ n : ℤ, g n :=
    finsum_comp_equiv (Equiv.subRight (1 : ℤ)) (f := g)
  rw [hre, sub_self]

theorem finite_support_telescopeCube {ι : Type*} [DecidableEq ι] (w : ι → A) (s : Finset ι)
    {C : A → ℂ} {S : Finset A} (hS : ∀ p, C p ≠ 0 → p ∈ S) :
    ∃ S' : Finset A, ∀ p, telescopeCube w s C p ≠ 0 → p ∈ S' := by
  classical
  refine ⟨s.powerset.biUnion fun E => S.image fun q => q + ∑ i ∈ E, w i, ?_⟩
  intro p hp
  rw [telescopeCube] at hp
  obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  have hC : C (p - ∑ i ∈ E, w i) ≠ 0 := by
    intro hcon
    exact hne (by rw [hcon, mul_zero])
  refine Finset.mem_biUnion.mpr ⟨E, hE, Finset.mem_image.mpr ⟨_, hS _ hC, by abel⟩⟩

/-- **A full difference cube has vanishing orbit sum in each of its own directions.** -/
theorem orbitSum_telescopeCube_eq_zero {ι : Type*} [DecidableEq ι] (w : ι → A) (s : Finset ι)
    {i : ι} (hi : i ∈ s) (hw : ∀ n : ℤ, n • w i = 0 → n = 0)
    {C : A → ℂ} {S : Finset A} (hS : ∀ p, C p ≠ 0 → p ∈ S) (p : A) :
    orbitSum (w i) (telescopeCube w s C) p = 0 := by
  classical
  obtain ⟨S', hS'⟩ := finite_support_telescopeCube w (s.erase i) hS
  have hstep : telescopeCube w s C
      = fun q => telescopeCube w (s.erase i) C (q - w i) - telescopeCube w (s.erase i) C q := by
    have hins := telescopeCube_insert w (Finset.notMem_erase i s) C
    rwa [Finset.insert_erase hi] at hins
  rw [hstep]
  exact orbitSum_step_eq_zero hS' hw p

/-! ## Finiteness along a transverse line -/

/-- A divisor with finitely many nonzero classes along one direction meets every transverse line
finitely. -/
theorem finite_line_support_of_finite_classes {D : A → ℂ} {S : Finset A} {v u : A}
    (hS : ∀ p, D p ≠ 0 → ∃ q ∈ S, ∃ n : ℤ, p = q + n • u)
    (hfree : ∀ n m : ℤ, n • v + m • u = 0 → n = 0 ∧ m = 0) (p : A) :
    (Function.support fun n : ℤ => D (p + n • v)).Finite := by
  classical
  have hsub : (Function.support fun n : ℤ => D (p + n • v))
      ⊆ ⋃ q ∈ (S : Set A), {n : ℤ | ∃ m : ℤ, p + n • v = q + m • u} := by
    intro n hn
    obtain ⟨q, hq, m, hm⟩ := hS _ hn
    exact Set.mem_biUnion (by exact_mod_cast hq) ⟨m, hm⟩
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun q _ => ?_) hsub
  refine Set.Subsingleton.finite ?_
  rintro n₁ ⟨m₁, h₁⟩ n₂ ⟨m₂, h₂⟩
  have hrel : (n₁ - n₂) • v + (m₂ - m₁) • u = 0 := by
    rw [sub_smul, sub_smul]
    have : n₁ • v - n₂ • v + (m₂ • u - m₁ • u) = (p + n₁ • v) - (p + n₂ • v)
        - ((q + m₁ • u) - (q + m₂ • u)) := by abel
    rw [this, h₁, h₂]
    abel
  have := (hfree _ _ hrel).1
  omega

/-- Orbit sums are additive on differences with finite line support. -/
theorem orbitSum_sub {f g : A → ℂ} {u : A} (p : A)
    (hf : (Function.support fun n : ℤ => f (p + n • u)).Finite)
    (hg : (Function.support fun n : ℤ => g (p + n • u)).Finite) :
    orbitSum u (fun q => f q - g q) p = orbitSum u f p - orbitSum u g p := by
  rw [orbitSum, orbitSum, orbitSum]
  exact finsum_sub_distrib hf hg

/-- **Orbit sums in two free directions commute.** -/
theorem orbitSum_comm {B : A → ℂ} {S : Finset A} (hS : ∀ p, B p ≠ 0 → p ∈ S)
    {u v : A} (hfree : ∀ n m : ℤ, n • u + m • v = 0 → n = 0 ∧ m = 0) (p : A) :
    orbitSum u (orbitSum v B) p = orbitSum v (orbitSum u B) p := by
  classical
  set T : ℤ × ℤ → ℂ := fun x => B (p + x.1 • u + x.2 • v) with hT
  have hinj : Function.Injective fun x : ℤ × ℤ => p + x.1 • u + x.2 • v := by
    rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
    have hrel : (n₁ - n₂) • u + (m₁ - m₂) • v = 0 := by
      rw [sub_smul, sub_smul]
      have hh : n₁ • u - n₂ • u + (m₁ • v - m₂ • v)
          = (p + n₁ • u + m₁ • v) - (p + n₂ • u + m₂ • v) := by abel
      have hb : p + n₁ • u + m₁ • v = p + n₂ • u + m₂ • v := h
      rw [hh, hb]
      abel
    obtain ⟨h1, h2⟩ := hfree _ _ hrel
    have hn : n₁ = n₂ := by omega
    have hm : m₁ = m₂ := by omega
    simp [hn, hm]
  have hTfin : (Function.support T).Finite := by
    have hpre : (Function.support T)
        ⊆ (fun x : ℤ × ℤ => p + x.1 • u + x.2 • v) ⁻¹' (S : Set A) := by
      intro x hx
      exact hS _ hx
    refine Set.Finite.subset ?_ hpre
    exact Set.Finite.preimage (hinj.injOn) S.finite_toSet
  have hcurry := finsum_curry T hTfin
  set T' : ℤ × ℤ → ℂ := fun x => B (p + x.1 • v + x.2 • u) with hT'
  have hswap : ∀ x : ℤ × ℤ, T' x = T (Prod.swap x) := by
    rintro ⟨n, m⟩
    show B (p + n • v + m • u) = B (p + m • u + n • v)
    congr 1
    abel
  have hT'fin : (Function.support T').Finite := by
    have := hTfin.preimage (Equiv.prodComm ℤ ℤ).injective.injOn
    refine Set.Finite.subset this ?_
    intro x hx
    rw [Set.mem_preimage]
    show T (Prod.swap x) ≠ 0
    rw [← hswap x]
    exact hx
  have hcurry' := finsum_curry T' hT'fin
  have hsame : ∑ᶠ x : ℤ × ℤ, T' x = ∑ᶠ x : ℤ × ℤ, T x := by
    rw [finsum_congr hswap]
    exact finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := T)
  have hL : orbitSum u (orbitSum v B) p = ∑ᶠ (a : ℤ) (b : ℤ), T (a, b) := by
    rw [orbitSum]
    exact finsum_congr fun n => by rw [orbitSum]
  have hR : orbitSum v (orbitSum u B) p = ∑ᶠ (a : ℤ) (b : ℤ), T' (a, b) := by
    rw [orbitSum]
    exact finsum_congr fun n => by rw [orbitSum]
  rw [hL, hR, ← hcurry, ← hcurry', hsame]

/-! ## The transversal lift -/

/-- The canonical transversal lift of a divisor on the quotient by one direction. -/
def transversalLift (w : A) (Cb : (A ⧸ AddSubgroup.zmultiples w) → ℂ) : A → ℂ :=
  fun p => if p = Quotient.out (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples w)
    then Cb (QuotientAddGroup.mk p) else 0

theorem mk_add_zsmul (w : A) (p : A) (n : ℤ) :
    (QuotientAddGroup.mk (p + n • w) : A ⧸ AddSubgroup.zmultiples w)
      = QuotientAddGroup.mk p := by
  refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
  rw [show p + n • w - p = n • w from by abel]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩

theorem exists_support_transversalLift {w : A} {Cb : (A ⧸ AddSubgroup.zmultiples w) → ℂ}
    {Sb : Finset (A ⧸ AddSubgroup.zmultiples w)} (hSb : ∀ c, Cb c ≠ 0 → c ∈ Sb) :
    ∃ S : Finset A, ∀ p, transversalLift w Cb p ≠ 0 → p ∈ S := by
  classical
  refine ⟨Sb.image Quotient.out, ?_⟩
  intro p hp
  rw [transversalLift] at hp
  by_cases hcase : p = Quotient.out (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples w)
  · rw [if_pos hcase] at hp
    exact Finset.mem_image.mpr ⟨_, hSb _ hp, hcase.symm⟩
  · rw [if_neg hcase] at hp
    exact absurd rfl hp

/-- **The orbit sum of the transversal lift is the original divisor.** -/
theorem orbitSum_transversalLift {w : A} (hw : ∀ n : ℤ, n • w = 0 → n = 0)
    (Cb : (A ⧸ AddSubgroup.zmultiples w) → ℂ) (p : A) :
    orbitSum w (transversalLift w Cb) p = Cb (QuotientAddGroup.mk p) := by
  classical
  set r : A := Quotient.out (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples w) with hr
  have hmkr : (QuotientAddGroup.mk r : A ⧸ AddSubgroup.zmultiples w)
      = QuotientAddGroup.mk p := QuotientAddGroup.out_eq' _
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, p + n₀ • w = r := by
    have hmem : r - p ∈ AddSubgroup.zmultiples w :=
      QuotientAddGroup.eq_iff_sub_mem.mp hmkr
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    exact ⟨k, by rw [hk]; abel⟩
  have hterm : ∀ n : ℤ, transversalLift w Cb (p + n • w)
      = if p + n • w = r then Cb (QuotientAddGroup.mk p) else 0 := by
    intro n
    rw [transversalLift, mk_add_zsmul, ← hr]
  rw [orbitSum, finsum_congr hterm]
  have hsingle : ∀ n : ℤ, n ≠ n₀ →
      (if p + n • w = r then Cb (QuotientAddGroup.mk p) else 0) = 0 := by
    intro n hn
    refine if_neg fun hcon => hn ?_
    have : (n - n₀) • w = 0 := by
      rw [sub_smul]
      have h1 : p + n • w = p + n₀ • w := by rw [hcon, hn₀]
      have := add_left_cancel h1
      rw [this]
      abel
    have := hw _ this
    omega
  rw [finsum_eq_single _ n₀ hsingle, if_pos hn₀]

theorem orbitSum_add {f g : A → ℂ} {u : A} (p : A)
    (hf : (Function.support fun n : ℤ => f (p + n • u)).Finite)
    (hg : (Function.support fun n : ℤ => g (p + n • u)).Finite) :
    orbitSum u (fun q => f q + g q) p = orbitSum u f p + orbitSum u g p := by
  rw [orbitSum, orbitSum, orbitSum]
  exact finsum_add_distrib hf hg

theorem finite_line_support_of_finite_support {B : A → ℂ} {S : Finset A}
    (hS : ∀ p, B p ≠ 0 → p ∈ S) {u : A} (hu : ∀ n : ℤ, n • u = 0 → n = 0) (p : A) :
    (Function.support fun n : ℤ => B (p + n • u)).Finite := by
  refine Set.Finite.subset (finite_lineIndex hu S p) ?_
  intro n hn
  exact hS _ hn

/-! ## The simultaneous lift -/

set_option maxHeartbeats 2000000 in
/-- **Simultaneous lifting of a compatible family of finite divisors.**  A family of divisors, one
per direction, each invariant along its own direction and finitely supported modulo it, whose
pairwise orbit sums agree, is the family of orbit-sum pushforwards of one finitely supported
divisor. -/
theorem exists_simultaneous_lift {ι : Type*} [DecidableEq ι] [DecidableEq A] (w : ι → A) :
    ∀ (s : Finset ι),
      (∀ i ∈ s, ∀ n : ℤ, n • w i = 0 → n = 0) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ n m : ℤ, n • w i + m • w j = 0 → n = 0 ∧ m = 0) →
      (∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i ≠ j → i ≠ k → j ≠ k → ∀ n m l : ℤ,
        n • w i + m • w j + l • w k = 0 → n = 0 ∧ m = 0 ∧ l = 0) →
      ∀ D : ι → A → ℂ,
      (∀ i ∈ s, ∀ p, D i (p + w i) = D i p) →
      (∀ i ∈ s, ∃ S : Finset A, ∀ p, D i p ≠ 0 → ∃ q ∈ S, ∃ n : ℤ, p = q + n • w i) →
      (∀ i ∈ s, ∀ j ∈ s, ∀ p, orbitSum (w j) (D i) p = orbitSum (w i) (D j) p) →
      ∃ (B : A → ℂ) (S : Finset A), (∀ p, B p ≠ 0 → p ∈ S) ∧
        ∀ i ∈ s, ∀ p, orbitSum (w i) B p = D i p := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _ D _ _ _
      exact ⟨fun _ => 0, ∅, fun p hp => absurd rfl hp, by simp⟩
  | @insert r s' hr ih =>
      intro hone hpair htriple D hinv hsupp hcomp
      have hmem : ∀ i ∈ s', i ∈ insert r s' := fun i hi => Finset.mem_insert_of_mem hi
      have hrmem : r ∈ insert r s' := Finset.mem_insert_self r s'
      have hne : ∀ i ∈ s', i ≠ r := fun i hi hcon => hr (hcon ▸ hi)
      obtain ⟨B₀, S₀, hS₀, hB₀⟩ := ih
        (fun i hi => hone i (hmem i hi))
        (fun i hi j hj => hpair i (hmem i hi) j (hmem j hj))
        (fun i hi j hj k hk => htriple i (hmem i hi) j (hmem j hj) k (hmem k hk))
        D (fun i hi => hinv i (hmem i hi)) (fun i hi => hsupp i (hmem i hi))
        (fun i hi j hj => hcomp i (hmem i hi) j (hmem j hj))
      obtain ⟨SDr, hSDr⟩ := hsupp r hrmem
      -- the error term
      set E : A → ℂ := fun p => D r p - orbitSum (w r) B₀ p with hE
      have hEinv : ∀ p, E (p + w r) = E p := by
        intro p
        rw [hE]
        show D r (p + w r) - orbitSum (w r) B₀ (p + w r) = D r p - orbitSum (w r) B₀ p
        rw [hinv r hrmem p, orbitSum_invariant]
      have hEsupp : ∀ p, E p ≠ 0 → ∃ q ∈ SDr ∪ S₀, ∃ n : ℤ, p = q + n • w r := by
        intro p hp
        by_cases hd : D r p = 0
        · have horb : orbitSum (w r) B₀ p ≠ 0 := by
            intro hcon
            exact hp (by rw [hE]; show D r p - orbitSum (w r) B₀ p = 0; rw [hd, hcon, sub_zero])
          obtain ⟨q, hq, n, hn⟩ := orbitSum_finite_classes hS₀ (w r) horb
          exact ⟨q, Finset.mem_union_right _ hq, n, hn⟩
        · obtain ⟨q, hq, n, hn⟩ := hSDr p hd
          exact ⟨q, Finset.mem_union_left _ hq, n, hn⟩
      have hDrline : ∀ i ∈ s', ∀ p : A,
          (Function.support fun n : ℤ => D r (p + n • w i)).Finite := by
        intro i hi p
        refine finite_line_support_of_finite_classes hSDr ?_ p
        intro n m hnm
        exact hpair i (hmem i hi) r hrmem (hne i hi) n m hnm
      have hOrbline : ∀ i ∈ s', ∀ p : A,
          (Function.support fun n : ℤ => orbitSum (w r) B₀ (p + n • w i)).Finite := by
        intro i hi p
        refine finite_line_support_of_finite_classes
          (S := S₀) (fun q hq => orbitSum_finite_classes hS₀ (w r) hq) ?_ p
        intro n m hnm
        exact hpair i (hmem i hi) r hrmem (hne i hi) n m hnm
      have hEline : ∀ i ∈ s', ∀ p : A, orbitSum (w i) E p = 0 := by
        intro i hi p
        rw [hE, orbitSum_sub p (hDrline i hi p) (hOrbline i hi p)]
        have h1 : orbitSum (w i) (D r) p = orbitSum (w r) (D i) p :=
          hcomp r hrmem i (hmem i hi) p
        have hfun : orbitSum (w i) B₀ = D i := funext fun q => hB₀ i hi q
        have h2 : orbitSum (w i) (orbitSum (w r) B₀) p = orbitSum (w r) (D i) p := by
          rw [orbitSum_comm hS₀ (u := w i) (v := w r) ?_ p, hfun]
          intro n m hnm
          exact hpair i (hmem i hi) r hrmem (hne i hi) n m hnm
        rw [h1, h2, sub_self]
      -- descend to the quotient by the last direction
      have hEclass : ∀ (p : A) (n : ℤ), E (p + n • w r) = E p := invariant_zsmul hEinv
      set Ebar : (A ⧸ AddSubgroup.zmultiples (w r)) → ℂ :=
        fun c => E (Quotient.out c) with hEbar
      have hEbar_mk : ∀ p : A,
          Ebar (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples (w r)) = E p := by
        intro p
        have hmk : (QuotientAddGroup.mk
            (Quotient.out (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples (w r)))
              : A ⧸ AddSubgroup.zmultiples (w r)) = QuotientAddGroup.mk p :=
          QuotientAddGroup.out_eq' _
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
          (QuotientAddGroup.eq_iff_sub_mem.mp hmk)
        rw [hEbar]
        show E (Quotient.out (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples (w r))) = E p
        rw [show Quotient.out (QuotientAddGroup.mk p : A ⧸ AddSubgroup.zmultiples (w r))
          = p + k • w r from by rw [hk]; abel]
        exact hEclass p k
      have hEbarsupp : ∀ c, Ebar c ≠ 0 →
          c ∈ (SDr ∪ S₀).image
            (fun q => (QuotientAddGroup.mk q : A ⧸ AddSubgroup.zmultiples (w r))) := by
        intro c hc
        obtain ⟨q, hq, n, hn⟩ := hEsupp (Quotient.out c) hc
        refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
        have : (QuotientAddGroup.mk (Quotient.out c) : A ⧸ AddSubgroup.zmultiples (w r))
            = QuotientAddGroup.mk q := by
          rw [hn, mk_add_zsmul]
        rw [← this]
        exact QuotientAddGroup.out_eq' c
      set wq : ι → (A ⧸ AddSubgroup.zmultiples (w r)) :=
        fun i => QuotientAddGroup.mk (w i) with hwq
      have hwq_smul : ∀ (n : ℤ) (i : ι), n • wq i
          = (QuotientAddGroup.mk (n • w i) : A ⧸ AddSubgroup.zmultiples (w r)) := by
        intro n i
        rw [hwq]
        exact (QuotientAddGroup.mk_zsmul _ _ _).symm
      have hwq_zero : ∀ y : A,
          (QuotientAddGroup.mk y : A ⧸ AddSubgroup.zmultiples (w r)) = 0 ↔
            ∃ k : ℤ, k • w r = y := by
        intro y
        constructor
        · intro h
          refine AddSubgroup.mem_zmultiples_iff.mp ?_
          have : y - 0 ∈ AddSubgroup.zmultiples (w r) :=
            QuotientAddGroup.eq_iff_sub_mem.mp (by simpa using h)
          simpa using this
        · intro ⟨k, hk⟩
          have : y - 0 ∈ AddSubgroup.zmultiples (w r) := by
            simpa using AddSubgroup.mem_zmultiples_iff.mpr ⟨k, hk⟩
          have h2 : (QuotientAddGroup.mk y : A ⧸ AddSubgroup.zmultiples (w r))
              = QuotientAddGroup.mk 0 := QuotientAddGroup.eq_iff_sub_mem.mpr this
          simpa using h2
      have hwq_one : ∀ i ∈ s', ∀ n : ℤ, n • wq i = 0 → n = 0 := by
        intro i hi n hn
        rw [hwq_smul] at hn
        obtain ⟨k, hk⟩ := (hwq_zero _).mp hn
        refine (hpair i (hmem i hi) r hrmem (hne i hi) n (-k) ?_).1
        rw [neg_smul, hk]
        abel
      have hwq_pair : ∀ i ∈ s', ∀ j ∈ s', i ≠ j → ∀ n m : ℤ,
          n • wq i + m • wq j = 0 → n = 0 ∧ m = 0 := by
        intro i hi j hj hij n m hnm
        rw [hwq_smul, hwq_smul, ← QuotientAddGroup.mk_add] at hnm
        obtain ⟨k, hk⟩ := (hwq_zero _).mp hnm
        obtain ⟨h1, h2, -⟩ := htriple i (hmem i hi) j (hmem j hj) r hrmem hij
          (hne i hi) (hne j hj) n m (-k) (by rw [neg_smul, hk]; abel)
        exact ⟨h1, h2⟩
      have hEbarlines : ∀ i ∈ s', ∀ c : A ⧸ AddSubgroup.zmultiples (w r),
          ∑ᶠ n : ℤ, Ebar (c + n • wq i) = 0 := by
        intro i hi c
        have hterm : ∀ n : ℤ, Ebar (c + n • wq i)
            = E (Quotient.out c + n • w i) := by
          intro n
          have harg : c + n • wq i
              = (QuotientAddGroup.mk (Quotient.out c + n • w i)
                  : A ⧸ AddSubgroup.zmultiples (w r)) := by
            rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', hwq_smul]
          rw [harg, hEbar_mk]
        rw [finsum_congr hterm]
        exact hEline i hi (Quotient.out c)
      obtain ⟨Cbar, Sbar, hSbar, hCbar⟩ := exists_telescopeCube wq s' hwq_one hwq_pair
        Ebar _ hEbarsupp hEbarlines
      -- the lift
      obtain ⟨SC, hCsupp⟩ := exists_support_transversalLift (w := w r) hSbar
      obtain ⟨S₁, hS₁⟩ := finite_support_telescopeCube w s' hCsupp
      have hB1 : ∀ p : A, orbitSum (w r) (telescopeCube w s' (transversalLift (w r) Cbar)) p = E p := by
        intro p
        have hexp : ∀ n : ℤ, telescopeCube w s' (transversalLift (w r) Cbar) (p + n • w r)
            = ∑ F ∈ s'.powerset,
                (-1 : ℂ) ^ (s'.card - F.card) * (transversalLift (w r) Cbar) ((p - ∑ i ∈ F, w i) + n • w r) := by
          intro n
          rw [telescopeCube]
          refine Finset.sum_congr rfl fun F _ => ?_
          congr 2
          abel
        have hfin : ∀ F ∈ s'.powerset, Function.HasFiniteSupport
            fun n : ℤ => (-1 : ℂ) ^ (s'.card - F.card) * (transversalLift (w r) Cbar) ((p - ∑ i ∈ F, w i) + n • w r) := by
          intro F _
          refine Set.Finite.subset
            (finite_line_support_of_finite_support hCsupp (hone r hrmem)
              (p - ∑ i ∈ F, w i)) ?_
          intro n hn hcon
          refine hn ?_
          have hc : transversalLift (w r) Cbar (p - ∑ i ∈ F, w i + n • w r) = 0 := hcon
          show (-1 : ℂ) ^ (s'.card - F.card)
            * transversalLift (w r) Cbar (p - ∑ i ∈ F, w i + n • w r) = 0
          rw [hc, mul_zero]
        have hterm : ∀ F ∈ s'.powerset,
            (∑ᶠ n : ℤ, (-1 : ℂ) ^ (s'.card - F.card) * (transversalLift (w r) Cbar) ((p - ∑ i ∈ F, w i) + n • w r))
              = (-1 : ℂ) ^ (s'.card - F.card) *
                  Cbar (QuotientAddGroup.mk (p - ∑ i ∈ F, w i)) := by
          intro F _
          rw [← mul_finsum]
          congr 1
          exact orbitSum_transversalLift (hone r hrmem) Cbar _
        have hmkF : ∀ F : Finset ι,
            (QuotientAddGroup.mk (p - ∑ i ∈ F, w i) : A ⧸ AddSubgroup.zmultiples (w r))
              = QuotientAddGroup.mk p - ∑ i ∈ F, wq i := by
          intro F
          show (QuotientAddGroup.mk' (AddSubgroup.zmultiples (w r))) (p - ∑ i ∈ F, w i)
            = (QuotientAddGroup.mk' (AddSubgroup.zmultiples (w r))) p - ∑ i ∈ F, wq i
          rw [map_sub]
          congr 1
          rw [hwq]
          exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (w r))) _ F
        rw [orbitSum, finsum_congr hexp, finsum_sum_comm s'.powerset _ hfin,
          Finset.sum_congr rfl hterm]
        have hcube : ∑ F ∈ s'.powerset, (-1 : ℂ) ^ (s'.card - F.card) *
            Cbar (QuotientAddGroup.mk (p - ∑ i ∈ F, w i))
            = telescopeCube wq s' Cbar (QuotientAddGroup.mk p) := by
          rw [telescopeCube]
          exact Finset.sum_congr rfl fun F _ => by rw [hmkF F]
        rw [hcube, hCbar, hEbar_mk]
      refine ⟨fun p => B₀ p + telescopeCube w s' (transversalLift (w r) Cbar) p, S₀ ∪ S₁, ?_, ?_⟩
      · intro p hp
        by_cases h0 : B₀ p = 0
        · refine Finset.mem_union_right _ (hS₁ p ?_)
          intro hcon
          exact hp (by show B₀ p + telescopeCube w s' (transversalLift (w r) Cbar) p = 0; rw [h0, hcon, add_zero])
        · exact Finset.mem_union_left _ (hS₀ p h0)
      · intro i hi p
        have hone_i : ∀ n : ℤ, n • w i = 0 → n = 0 := hone i hi
        have hfin0 := finite_line_support_of_finite_support hS₀ hone_i p
        have hfin1 := finite_line_support_of_finite_support hS₁ hone_i p
        rw [orbitSum_add p hfin0 hfin1]
        rcases Finset.mem_insert.mp hi with heq | hi''
        · subst heq
          rw [hB1 p, hE]
          show orbitSum (w i) B₀ p + (D i p - orbitSum (w i) B₀ p) = D i p
          ring
        · rw [hB₀ i hi'',
            orbitSum_telescopeCube_eq_zero w s' hi'' hone_i hCsupp p, add_zero]
end

end GaloisForLFunctions.HTGeometry
