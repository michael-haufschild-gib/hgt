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

theorem support_transversalLift {w : A} {Cb : (A ⧸ AddSubgroup.zmultiples w) → ℂ}
    {Sb : Finset (A ⧸ AddSubgroup.zmultiples w)} (hSb : ∀ c, Cb c ≠ 0 → c ∈ Sb) :
    ∀ p, transversalLift w Cb p ≠ 0 → p ∈ Sb.image Quotient.out := by
  classical
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

end

end GaloisForLFunctions.HTGeometry
