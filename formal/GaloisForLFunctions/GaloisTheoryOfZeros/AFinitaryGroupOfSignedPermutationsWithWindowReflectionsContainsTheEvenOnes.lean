import GaloisForLFunctions.GaloisTheoryOfZeros.AFinitaryGroupOnTheIntegersWithWindowReflectionsContainsEveryThreeCycle

/-!
# A finitary group of signed permutations with window reflections contains the even ones

Let `Ω` carry an involution whose orbits (the pairs) are numbered by the integers, and let `G` be
a group of permutations of `Ω` that commute with the involution, move finitely many points, act
on the pairs of every window `[-K, K]` as the reflections `m ↦ -m - 1` and `m ↦ -m`, and send
one point to its partner (`IsWindowedSignedGroup`). Then `G` contains

* the signed 3-cycle `p → q → r → p`, `p' → q' → r' → p'` of any three points in distinct pairs
  (`IsWindowedSignedGroup.hasSignedCycle`),
* the double flip `p ↔ p'`, `q ↔ q'` of any two points in distinct pairs
  (`IsWindowedSignedGroup.hasDoubleFlip`).

These generate the signed permutations of finite support that are even on the points and even on
the pairs.

Proof. The group induced on the pairs contains every 3-cycle. If `g` induces a 3-cycle of pairs,
`g²` is the identity off the three pairs and `g⁶` is the identity on them, so `g⁴` is a signed
3-cycle. A conjugate of the given flip sends `p` to its partner; conjugating a signed 3-cycle
through `p` and two pairs it does not move by it flips the sign at `p`, and the quotient of the
two cycles is a double flip. Double flips correct the signs of the cycles.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-- An involution `flip` of `Ω` whose orbits are numbered by `pair`. -/
structure PairCoordinate (Ω : Type*) where
  /-- the involution -/
  flip : Ω → Ω
  /-- the number of the orbit of a point -/
  pair : Ω → ℤ
  flip_flip : ∀ x, flip (flip x) = x
  pair_eq_iff : ∀ x y, pair x = pair y ↔ y = x ∨ y = flip x

variable {Ω : Type*} {P : PairCoordinate Ω} {G : Subgroup (Perm Ω)}

theorem PairCoordinate.pair_flip (P : PairCoordinate Ω) (x : Ω) : P.pair (P.flip x) = P.pair x :=
  ((P.pair_eq_iff x (P.flip x)).mpr (Or.inr rfl)).symm

/-- `G` contains the signed 3-cycle `p → q → r → p`: an element with these values that is the
identity off the three pairs. -/
def HasSignedCycle (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) (p q r : Ω) : Prop :=
  ∃ T ∈ G, T p = q ∧ T q = r ∧ T r = p ∧
    ∀ x, P.pair x ≠ P.pair p → P.pair x ≠ P.pair q → P.pair x ≠ P.pair r → T x = x

/-- `G` contains the double flip of the pairs of `p` and `q`: an element that sends `p` and `q`
to their partners and is the identity off the two pairs. -/
def HasDoubleFlip (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) (p q : Ω) : Prop :=
  ∃ T ∈ G, T p = P.flip p ∧ T q = P.flip q ∧
    ∀ x, P.pair x ≠ P.pair p → P.pair x ≠ P.pair q → T x = x

/-- The group of the permutations of the pairs induced by elements of `G`. -/
def inducedPairGroup (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) : Subgroup (Perm ℤ) where
  carrier := {T | ∃ g ∈ G, ∀ x, P.pair (g x) = T (P.pair x)}
  mul_mem' := by
    rintro T₁ T₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    exact ⟨g₁ * g₂, G.mul_mem hg₁ hg₂, fun x => by
      show P.pair (g₁ (g₂ x)) = T₁ (T₂ (P.pair x))
      rw [h₁, h₂]⟩
  one_mem' := ⟨1, G.one_mem, fun _ => rfl⟩
  inv_mem' := by
    rintro T ⟨g, hg, h⟩
    refine ⟨g⁻¹, G.inv_mem hg, fun x => ?_⟩
    rw [Perm.eq_inv_iff_eq, ← h, perm_apply_inv_self]

theorem mem_inducedPairGroup {T : Perm ℤ} :
    T ∈ inducedPairGroup P G ↔ ∃ g ∈ G, ∀ x, P.pair (g x) = T (P.pair x) :=
  Iff.rfl

/-- A group of permutations that commute with the involution, move finitely many points, act on
the pairs of every window as the two reflections, and send one point to its partner. -/
structure IsWindowedSignedGroup (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) : Prop where
  comm : ∀ g ∈ G, ∀ x, g (P.flip x) = P.flip (g x)
  finite : ∀ g ∈ G, {x | g x ≠ x}.Finite
  window : ∀ K : ℤ, ∃ a ∈ G, ∃ b ∈ G, ∀ x, |P.pair x| ≤ K →
    P.pair (a x) = -P.pair x - 1 ∧ P.pair (b x) = -P.pair x
  flips : ∃ g ∈ G, ∃ x, g x = P.flip x

namespace IsWindowedSignedGroup

variable (hG : IsWindowedSignedGroup P G)
include hG

/-- An element of `G` maps pairs to pairs. -/
theorem pair_apply_eq_iff {g : Perm Ω} (hg : g ∈ G) {x y : Ω} :
    P.pair (g x) = P.pair (g y) ↔ P.pair x = P.pair y := by
  constructor
  · intro h
    rcases (P.pair_eq_iff (g x) (g y)).mp h with h' | h'
    · rw [g.injective h']
    · rw [← hG.comm g hg] at h'
      rw [g.injective h', P.pair_flip]
  · intro h
    rcases (P.pair_eq_iff x y).mp h with h' | h'
    · rw [h']
    · rw [h', hG.comm g hg, P.pair_flip]

theorem apply_flip_of_pair_eq {T : Perm Ω} (hT : T ∈ G) {t y : Ω} (ht : T t = P.flip t)
    (hy : P.pair y = P.pair t) : T y = P.flip y := by
  rcases (P.pair_eq_iff t y).mp hy.symm with h | h
  · rw [h]
    exact ht
  · rw [h, hG.comm T hT, ht]

/-! ## The pairs -/

theorem exists_pair_add_one (x : Ω) : ∃ y, P.pair y = P.pair x + 1 := by
  obtain ⟨a, _, b, _, hab⟩ := hG.window (|P.pair x| + 1)
  have h1 := (hab x (by linarith [abs_nonneg (P.pair x)])).1
  have h2 := (hab (a x) (by
    rw [h1, abs_le]
    constructor <;> linarith [neg_abs_le (P.pair x), le_abs_self (P.pair x)])).2
  exact ⟨b (a x), by rw [h2, h1]; ring⟩

theorem exists_pair_sub_one (x : Ω) : ∃ y, P.pair y = P.pair x - 1 := by
  obtain ⟨a, _, b, _, hab⟩ := hG.window (|P.pair x| + 1)
  have h1 := (hab x (by linarith [abs_nonneg (P.pair x)])).2
  have h2 := (hab (b x) (by
    rw [h1, abs_neg]
    linarith [abs_nonneg (P.pair x)])).1
  exact ⟨a (b x), by rw [h2, h1]; ring⟩

/-- Every integer numbers a pair. -/
theorem surjective : Function.Surjective P.pair := by
  obtain ⟨_, _, x₀, _⟩ := hG.flips
  have hup : ∀ n : ℕ, ∃ x, P.pair x = P.pair x₀ + n := by
    intro n
    induction n with
    | zero => exact ⟨x₀, by simp⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hy⟩ := hG.exists_pair_add_one x
      exact ⟨y, by rw [hy, hx]; push_cast; ring⟩
  have hdown : ∀ n : ℕ, ∃ x, P.pair x = P.pair x₀ - n := by
    intro n
    induction n with
    | zero => exact ⟨x₀, by simp⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hy⟩ := hG.exists_pair_sub_one x
      exact ⟨y, by rw [hy, hx]; push_cast; ring⟩
  intro m
  obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg (m - P.pair x₀)
  · obtain ⟨x, hx⟩ := hup n
    exact ⟨x, by rw [hx]; linarith⟩
  · obtain ⟨x, hx⟩ := hdown n
    exact ⟨x, by rw [hx]; linarith⟩

/-- The permutation of the pairs induced by an element of `G`. -/
theorem exists_pairPerm {g : Perm Ω} (hg : g ∈ G) :
    ∃ T : Perm ℤ, ∀ x, P.pair (g x) = T (P.pair x) := by
  obtain ⟨s, hs⟩ : ∃ s : ℤ → Ω, ∀ m, P.pair (s m) = m :=
    ⟨Function.surjInv hG.surjective, Function.surjInv_eq hG.surjective⟩
  have key : ∀ {h : Perm Ω}, h ∈ G → ∀ x, P.pair (h x) = P.pair (h (s (P.pair x))) :=
    fun hh x => (hG.pair_apply_eq_iff hh).mpr (hs _).symm
  refine ⟨⟨fun m => P.pair (g (s m)), fun m => P.pair (g⁻¹ (s m)), fun m => ?_, fun m => ?_⟩,
    fun x => key hg x⟩
  · show P.pair (g⁻¹ (s (P.pair (g (s m))))) = m
    rw [← key (G.inv_mem hg), perm_inv_apply_self, hs]
  · show P.pair (g (s (P.pair (g⁻¹ (s m))))) = m
    rw [← key hg, perm_apply_inv_self, hs]

theorem inducedPairGroup_finite {T : Perm ℤ} (hT : T ∈ inducedPairGroup P G) :
    {m : ℤ | T m ≠ m}.Finite := by
  obtain ⟨g, hg, h⟩ := mem_inducedPairGroup.mp hT
  refine ((hG.finite g hg).image P.pair).subset fun m hm => ?_
  obtain ⟨x, rfl⟩ := hG.surjective m
  exact ⟨x, fun e => hm (by rw [← h, e]), rfl⟩

theorem inducedPairGroup_window : HasWindowReflections (inducedPairGroup P G) := by
  intro K
  obtain ⟨a, ha, b, hb, hab⟩ := hG.window K
  obtain ⟨Ta, hTa⟩ := hG.exists_pairPerm ha
  obtain ⟨Tb, hTb⟩ := hG.exists_pairPerm hb
  refine ⟨Ta, mem_inducedPairGroup.mpr ⟨a, ha, hTa⟩, Tb, mem_inducedPairGroup.mpr ⟨b, hb, hTb⟩,
    fun m hm => ?_⟩
  obtain ⟨x, rfl⟩ := hG.surjective m
  rw [← hTa, ← hTb]
  exact hab x hm

/-! ## Signed 3-cycles -/

/-- **A signed 3-cycle on three given pairs.** If `g` induces the 3-cycle of the pairs, `g⁴` is
a signed 3-cycle. -/
theorem exists_hasSignedCycle_of_pairs (p : Ω) {j k : ℤ} (hpj : P.pair p ≠ j) (hjk : j ≠ k)
    (hpk : P.pair p ≠ k) : ∃ q r, P.pair q = j ∧ P.pair r = k ∧ HasSignedCycle P G p q r := by
  obtain ⟨-, -, -, T, hT, t1, t2, t3, t4⟩ :=
    hasCycle_of_windowReflections (fun T hT => hG.inducedPairGroup_finite hT)
      hG.inducedPairGroup_window
      hpj hjk hpk
  obtain ⟨g, hg, hgT⟩ := mem_inducedPairGroup.mp hT
  have hc := hG.comm g hg
  -- off the three pairs `g` preserves every pair, so `g²` is the identity there
  have F1 : ∀ x, P.pair x ≠ P.pair p → P.pair x ≠ j → P.pair x ≠ k → g (g x) = x := by
    intro x h1 h2 h3
    have hpx : P.pair x = P.pair (g x) := by rw [hgT, t4 _ h1 h2 h3]
    rcases (P.pair_eq_iff x (g x)).mp hpx with h | h
    · rw [h, h]
    · rw [h, hc, h, P.flip_flip]
  -- on the three pairs `g³` preserves every pair, so `g⁶` is the identity there
  have hcc : ∀ x, g (g (g (P.flip x))) = P.flip (g (g (g x))) := fun x => by rw [hc, hc, hc]
  have hp3 : ∀ x, P.pair x = P.pair p ∨ P.pair x = j ∨ P.pair x = k →
      P.pair (g (g (g x))) = P.pair x := by
    intro x hx
    rw [hgT, hgT, hgT]
    rcases hx with h | h | h
    · rw [h, t1, t2, t3]
    · rw [h, t2, t3, t1]
    · rw [h, t3, t1, t2]
  have F2 : ∀ x, P.pair x = P.pair p ∨ P.pair x = j ∨ P.pair x = k →
      g (g (g (g (g (g x))))) = x := by
    intro x hx
    rcases (P.pair_eq_iff x (g (g (g x)))).mp (hp3 x hx).symm with h | h
    · rw [h, h]
    · rw [h, hcc, h, P.flip_flip]
  have hq : P.pair (g (g (g (g p)))) = j := by rw [hgT, hgT, hgT, hgT, t1, t2, t3, t1]
  have hr : P.pair (g (g p)) = k := by rw [hgT, hgT, t1, t2]
  refine ⟨g (g (g (g p))), g (g p), hq, hr, g * g * g * g,
    G.mul_mem (G.mul_mem (G.mul_mem hg hg) hg) hg, rfl, ?_, ?_, fun x h1 h2 h3 => ?_⟩
  · show g (g (g (g (g (g (g (g p))))))) = g (g p)
    rw [F2 p (Or.inl rfl)]
  · show g (g (g (g (g (g p))))) = p
    exact F2 p (Or.inl rfl)
  · have e := F1 x h1 (fun h => h2 (h.trans hq.symm)) (fun h => h3 (h.trans hr.symm))
    show g (g (g (g x))) = x
    rw [e, e]

/-- Conjugation by `g` carries the signed cycle on `(p, q, r)` to the one on
`(g p, g q, g r)`. -/
theorem hasSignedCycle_conj {p q r : Ω} (h : HasSignedCycle P G p q r) {g : Perm Ω}
    (hg : g ∈ G) : HasSignedCycle P G (g p) (g q) (g r) := by
  obtain ⟨T, hT, h1, h2, h3, h4⟩ := h
  refine ⟨g * T * g⁻¹, G.mul_mem (G.mul_mem hg hT) (G.inv_mem hg), ?_, ?_, ?_,
    fun x hx1 hx2 hx3 => ?_⟩
  · show g (T (g⁻¹ (g p))) = g q
    rw [perm_inv_apply_self, h1]
  · show g (T (g⁻¹ (g q))) = g r
    rw [perm_inv_apply_self, h2]
  · show g (T (g⁻¹ (g r))) = g p
    rw [perm_inv_apply_self, h3]
  · have e : ∀ y, P.pair x ≠ P.pair (g y) → P.pair (g⁻¹ x) ≠ P.pair y := fun y hy e' => hy (by
      have := (hG.pair_apply_eq_iff hg).mpr e'
      rwa [perm_apply_inv_self] at this)
    show g (T (g⁻¹ x)) = x
    rw [h4 _ (e p hx1) (e q hx2) (e r hx3), perm_apply_inv_self]

/-! ## Flips -/

/-- Every point is sent to its partner by an element of `G`: a conjugate of the given flip. -/
theorem exists_flip_apply (p : Ω) : ∃ g ∈ G, g p = P.flip p := by
  obtain ⟨g₀, hg₀, x₀, hx₀⟩ := hG.flips
  obtain ⟨c, hc, hcp⟩ : ∃ c ∈ G, P.pair (c x₀) = P.pair p := by
    by_cases h : P.pair x₀ = P.pair p
    · exact ⟨1, G.one_mem, h⟩
    · have hk1 : P.pair p ≠ |P.pair x₀| + |P.pair p| + 1 :=
        ne_of_lt (by linarith [le_abs_self (P.pair p), abs_nonneg (P.pair x₀)])
      have hk2 : P.pair x₀ ≠ |P.pair x₀| + |P.pair p| + 1 :=
        ne_of_lt (by linarith [le_abs_self (P.pair x₀), abs_nonneg (P.pair p)])
      obtain ⟨q, r, hq, -, T, hT, h1, -⟩ := hG.exists_hasSignedCycle_of_pairs x₀ h hk1 hk2
      exact ⟨T, hT, by rw [h1, hq]⟩
  have hmem : c * g₀ * c⁻¹ ∈ G := G.mul_mem (G.mul_mem hc hg₀) (G.inv_mem hc)
  have hy : (c * g₀ * c⁻¹) (c x₀) = P.flip (c x₀) := by
    show c (g₀ (c⁻¹ (c x₀))) = P.flip (c x₀)
    rw [perm_inv_apply_self, hx₀, hG.comm c hc]
  exact ⟨c * g₀ * c⁻¹, hmem, hG.apply_flip_of_pair_eq hmem hy hcp.symm⟩

/-- **A double flip with a far pair.** A signed cycle through `p` and two pairs that the flip
at `p` does not move, divided by its conjugate under the flip. -/
theorem exists_hasDoubleFlip_far (p : Ω) :
    ∃ J : ℤ, ∀ j, J ≤ j → ∃ t, P.pair t = j ∧ HasDoubleFlip P G p t := by
  obtain ⟨g, hg, hgp⟩ := hG.exists_flip_apply p
  obtain ⟨M, hM⟩ := ((hG.finite g hg).image P.pair).bddAbove
  have fixg : ∀ x, M < P.pair x → g x = x := fun x hx => by
    by_contra hne
    have : P.pair x ≤ M := hM ⟨x, hne, rfl⟩
    linarith
  refine ⟨|M| + |P.pair p| + 1, fun j hj => ?_⟩
  have hMj : M < j := by linarith [le_abs_self M, abs_nonneg (P.pair p)]
  have hpj : P.pair p < j := by linarith [le_abs_self (P.pair p), abs_nonneg M]
  obtain ⟨q, r, hq, hr, hcyc⟩ := hG.exists_hasSignedCycle_of_pairs p (j := j) (k := j + 1)
    (ne_of_lt hpj) (by omega) (ne_of_lt (by linarith))
  have hcyc' := hG.hasSignedCycle_conj hcyc hg
  rw [hgp, fixg q (by rw [hq]; exact hMj), fixg r (by rw [hr]; linarith)] at hcyc'
  obtain ⟨T, hT, a1, a2, a3, a4⟩ := hcyc
  obtain ⟨T', hT', b1, b2, b3, b4⟩ := hcyc'
  have cT := hG.comm T hT
  have cT' := hG.comm T' hT'
  refine ⟨q, hq, T * T'⁻¹, G.mul_mem hT (G.inv_mem hT'), ?_, ?_, fun x hx1 hx2 => ?_⟩
  · have e : T'⁻¹ p = P.flip r := by rw [Perm.inv_eq_iff_eq, cT', b3, P.flip_flip]
    show T (T'⁻¹ p) = P.flip p
    rw [e, cT, a3]
  · have e : T'⁻¹ q = P.flip p := by rw [Perm.inv_eq_iff_eq, b1]
    show T (T'⁻¹ q) = P.flip q
    rw [e, cT, a1]
  · by_cases hxr : P.pair x = P.pair r
    · rcases (P.pair_eq_iff r x).mp hxr.symm with h | h
      · have e : T'⁻¹ r = q := by rw [Perm.inv_eq_iff_eq, b2]
        show T (T'⁻¹ x) = x
        rw [h, e, a2]
      · have e : T'⁻¹ (P.flip r) = P.flip q := by rw [Perm.inv_eq_iff_eq, cT', b2]
        show T (T'⁻¹ x) = x
        rw [h, e, cT, a2]
    · have e : T'⁻¹ x = x := by
        rw [Perm.inv_eq_iff_eq]
        exact (b4 x (by rw [P.pair_flip]; exact hx1) hx2 hxr).symm
      show T (T'⁻¹ x) = x
      rw [e, a4 x hx1 hx2 hxr]

/-- **`G` contains every double flip.** -/
theorem hasDoubleFlip {p q : Ω} (h : P.pair p ≠ P.pair q) : HasDoubleFlip P G p q := by
  obtain ⟨J₁, h₁⟩ := hG.exists_hasDoubleFlip_far p
  obtain ⟨J₂, h₂⟩ := hG.exists_hasDoubleFlip_far q
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = |J₁| + |J₂| + |P.pair p| + |P.pair q| + 1 := ⟨_, rfl⟩
  have hJ₁ : J₁ ≤ j := by
    linarith [le_abs_self J₁, abs_nonneg J₂, abs_nonneg (P.pair p), abs_nonneg (P.pair q)]
  have hJ₂ : J₂ ≤ j := by
    linarith [le_abs_self J₂, abs_nonneg J₁, abs_nonneg (P.pair p), abs_nonneg (P.pair q)]
  have hpj : P.pair p ≠ j := ne_of_lt (by
    linarith [le_abs_self (P.pair p), abs_nonneg J₁, abs_nonneg J₂, abs_nonneg (P.pair q)])
  have hqj : P.pair q ≠ j := ne_of_lt (by
    linarith [le_abs_self (P.pair q), abs_nonneg J₁, abs_nonneg J₂, abs_nonneg (P.pair p)])
  obtain ⟨t₁, ht₁, E₁, hE₁, a1, a2, a3⟩ := h₁ j hJ₁
  obtain ⟨t₂, ht₂, E₂, hE₂, b1, b2, b3⟩ := h₂ j hJ₂
  refine ⟨E₁ * E₂, G.mul_mem hE₁ hE₂, ?_, ?_, fun x hx1 hx2 => ?_⟩
  · show E₁ (E₂ p) = P.flip p
    rw [b3 p h (by rw [ht₂]; exact hpj), a1]
  · show E₁ (E₂ q) = P.flip q
    rw [b1, a3 (P.flip q) (by rw [P.pair_flip]; exact h.symm)
      (by rw [P.pair_flip, ht₁]; exact hqj)]
  · show E₁ (E₂ x) = x
    by_cases hxj : P.pair x = j
    · rw [hG.apply_flip_of_pair_eq hE₂ b2 (hxj.trans ht₂.symm),
        hG.apply_flip_of_pair_eq hE₁ a2 (by rw [P.pair_flip, hxj, ht₁]), P.flip_flip]
    · rw [b3 x hx2 (by rw [ht₂]; exact hxj), a3 x hx1 (by rw [ht₁]; exact hxj)]

/-- A double flip, or the identity, that moves a point to a prescribed point of its pair and
fixes two other pairs. -/
theorem exists_fix_lift {q q₁ : Ω} (h : P.pair q₁ = P.pair q) {u v : ℤ} (hu : u ≠ P.pair q)
    (hv : v ≠ P.pair q) :
    ∃ D ∈ G, D q₁ = q ∧ ∀ x, P.pair x = u ∨ P.pair x = v → D x = x := by
  rcases (P.pair_eq_iff q q₁).mp h.symm with h' | h'
  · exact ⟨1, G.one_mem, h', fun _ _ => rfl⟩
  · obtain ⟨t, ht⟩ := hG.surjective (|u| + |v| + |P.pair q| + 1)
    have hqt : P.pair q ≠ P.pair t := by
      rw [ht]
      exact ne_of_lt (by linarith [le_abs_self (P.pair q), abs_nonneg u, abs_nonneg v])
    obtain ⟨D, hD, d1, -, d3⟩ := hG.hasDoubleFlip hqt
    refine ⟨D, hD, ?_, fun x hx => d3 x ?_ ?_⟩
    · rw [h', hG.comm D hD, d1, P.flip_flip]
    · rcases hx with hx | hx
      · rw [hx]
        exact hu
      · rw [hx]
        exact hv
    · rw [ht]
      rcases hx with hx | hx
      · rw [hx]
        exact ne_of_lt (by linarith [le_abs_self u, abs_nonneg v, abs_nonneg (P.pair q)])
      · rw [hx]
        exact ne_of_lt (by linarith [le_abs_self v, abs_nonneg u, abs_nonneg (P.pair q)])

/-- **`G` contains every signed 3-cycle.** -/
theorem hasSignedCycle {p q r : Ω} (hpq : P.pair p ≠ P.pair q) (hqr : P.pair q ≠ P.pair r)
    (hpr : P.pair p ≠ P.pair r) : HasSignedCycle P G p q r := by
  obtain ⟨q₁, r₁, hq₁, hr₁, hcyc⟩ := hG.exists_hasSignedCycle_of_pairs p hpq hqr hpr
  obtain ⟨D₁, hD₁, d1, d1'⟩ :=
    hG.exists_fix_lift hq₁ (u := P.pair p) (v := P.pair r) hpq hqr.symm
  have h1 := hG.hasSignedCycle_conj hcyc hD₁
  rw [d1' p (Or.inl rfl), d1, d1' r₁ (Or.inr hr₁)] at h1
  obtain ⟨D₂, hD₂, d2, d2'⟩ := hG.exists_fix_lift hr₁ (u := P.pair p) (v := P.pair q) hpr hqr
  have h2 := hG.hasSignedCycle_conj h1 hD₂
  rwa [d2' p (Or.inl rfl), d2' q (Or.inr rfl), d2] at h2

end IsWindowedSignedGroup

/-! ## Transfer along an equivalence -/

section Transfer

variable {Ω' : Type*}

/-- A pair coordinate carried along an equivalence that intertwines the involutions. -/
def PairCoordinate.map (P : PairCoordinate Ω) (φ : Ω ≃ Ω') (flip' : Ω' → Ω')
    (h : ∀ x, φ (P.flip x) = flip' (φ x)) : PairCoordinate Ω' where
  flip := flip'
  pair y := P.pair (φ.symm y)
  flip_flip y := by
    have e := h (φ.symm y)
    rw [φ.apply_symm_apply] at e
    rw [← e, ← h, P.flip_flip, φ.apply_symm_apply]
  pair_eq_iff x y := by
    have e := h (φ.symm x)
    rw [φ.apply_symm_apply] at e
    show P.pair (φ.symm x) = P.pair (φ.symm y) ↔ y = x ∨ y = flip' x
    rw [P.pair_eq_iff, φ.symm_apply_eq, φ.symm_apply_eq, φ.apply_symm_apply, e]

/-- A windowed signed group is carried along an equivalence that intertwines the involutions to
a windowed signed group. -/
theorem IsWindowedSignedGroup.map (hG : IsWindowedSignedGroup P G) (φ : Ω ≃ Ω')
    {flip' : Ω' → Ω'} (h : ∀ x, φ (P.flip x) = flip' (φ x)) {G' : Subgroup (Perm Ω')}
    (hmem : ∀ g ∈ G, φ.permCongr g ∈ G') (hcomm : ∀ g ∈ G', ∀ x, g (flip' x) = flip' (g x))
    (hfin : ∀ g ∈ G', {x | g x ≠ x}.Finite) : IsWindowedSignedGroup (P.map φ flip' h) G' := by
  refine ⟨hcomm, hfin, fun K => ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hG.window K
    refine ⟨φ.permCongr a, hmem a ha, φ.permCongr b, hmem b hb, fun x hx => ?_⟩
    have e := hab (φ.symm x) hx
    constructor
    · show P.pair (φ.symm (φ.permCongr a x)) = -P.pair (φ.symm x) - 1
      rw [Equiv.permCongr_apply, φ.symm_apply_apply]
      exact e.1
    · show P.pair (φ.symm (φ.permCongr b x)) = -P.pair (φ.symm x)
      rw [Equiv.permCongr_apply, φ.symm_apply_apply]
      exact e.2
  · obtain ⟨g, hg, x, hx⟩ := hG.flips
    refine ⟨φ.permCongr g, hmem g hg, φ x, ?_⟩
    show φ.permCongr g (φ x) = flip' (φ x)
    rw [Equiv.permCongr_apply, φ.symm_apply_apply, hx, h]

end Transfer

end GaloisForLFunctions.GaloisTheoryOfZeros
