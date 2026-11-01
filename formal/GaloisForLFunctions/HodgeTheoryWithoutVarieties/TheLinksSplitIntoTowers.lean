import Mathlib

/-!
# The links of the dilation complex split into prime towers

Two positive integers are joined by a dilation edge when their ratio is a prime power
(`DilationAdj`); the edge then lies on the tower of that prime (`TowerNeighbor`). Garland's method
and trickle-down derive a global spectral gap or signature from the links of the vertices, and both
need **connected** links.

* **Towers do not meet locally** (`not_dilationAdj_of_towerNeighbor`): two neighbours of `n` on
  the towers of distinct primes `p ≠ q` are never adjacent. A dilation edge changes the
  factorization in exactly one prime, while these two neighbours differ in two.
* **Each tower is a clique** (`dilationAdj_of_towerNeighbor_same`): distinct neighbours of `n` on
  the same tower are adjacent.
* **Links are disconnected** (`not_preconnected_linkGraph`): as soon as `n` has neighbours on two
  towers, its link has at least two components. The tower of a neighbour is invariant along
  every walk in the link.

**Contrast with a curve** (`degreeLink_adj`). Over `𝔽_q` all closed points have positions in one
copy of `ℤ`, the degrees. When every degree carries points, as for a curve with a rational point,
the steps are all nonzero integers. Two distinct neighbours of a degree then always differ by a
step, so every link is a complete graph. Commensurable towers have connected links. Over `ℤ` the
positions `log p` are linearly independent, the towers are incommensurable, and the links split.
-/

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- `m` is a neighbour of `n` along the tower of `p`: `m = n p^i` or `n = m p^i`, `i ≥ 1`. -/
def TowerNeighbor (n p m : ℕ) : Prop := ∃ i : ℕ, 1 ≤ i ∧ (m = n * p ^ i ∨ n = m * p ^ i)

/-- A dilation edge: the ratio of the endpoints is a prime power. -/
def DilationAdj (a b : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ TowerNeighbor a p b

theorem TowerNeighbor.symm {n p m : ℕ} (h : TowerNeighbor n p m) : TowerNeighbor m p n := by
  obtain ⟨i, hi, h | h⟩ := h
  · exact ⟨i, hi, Or.inr h⟩
  · exact ⟨i, hi, Or.inl h⟩

theorem DilationAdj.symm {a b : ℕ} (h : DilationAdj a b) : DilationAdj b a := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p, hp, h.symm⟩

theorem TowerNeighbor.ne_zero {n p m : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : TowerNeighbor n p m) :
    m ≠ 0 := by
  obtain ⟨i, -, h | h⟩ := h
  · rw [h]; exact mul_ne_zero hn (pow_ne_zero _ hp.ne_zero)
  · rintro rfl; simp at h; exact hn h

/-- A tower step changes the factorization exactly at its prime. -/
theorem TowerNeighbor.factorization {n p m : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : TowerNeighbor n p m) :
    (∀ q, q ≠ p → m.factorization q = n.factorization q) ∧
      m.factorization p ≠ n.factorization p := by
  obtain ⟨i, hi, h | h⟩ := h
  · subst h
    rw [Nat.factorization_mul hn (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
    refine ⟨fun q hq => ?_, ?_⟩
    · simp [Ne.symm hq]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
  · have hm : m ≠ 0 := by rintro rfl; simp at h; exact hn h
    subst h
    rw [Nat.factorization_mul hm (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
    refine ⟨fun q hq => ?_, ?_⟩
    · simp [Ne.symm hq]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega

/-- **Towers do not meet locally.** Neighbours of `n` on the towers of two distinct primes are not
joined by a dilation edge. -/
theorem not_dilationAdj_of_towerNeighbor {n p q a b : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (ha : TowerNeighbor n p a) (hb : TowerNeighbor n q b) :
    ¬ DilationAdj a b := by
  rintro ⟨r, hr, hab⟩
  have ha0 := ha.ne_zero hp hn
  obtain ⟨ha1, ha2⟩ := ha.factorization hp hn
  obtain ⟨hb1, hb2⟩ := hb.factorization hq hn
  obtain ⟨hab1, -⟩ := hab.factorization hr ha0
  have hrp : r = p := by
    by_contra h
    exact ha2 ((hab1 p (Ne.symm h)).symm.trans (hb1 p hpq))
  have hrq : r = q := by
    by_contra h
    exact hb2 ((hab1 q (Ne.symm h)).trans (ha1 q (Ne.symm hpq)))
  exact hpq (hrp.symm.trans hrq)

/-- **Each tower is a clique**: distinct neighbours of `n` on the tower of `p` are adjacent. -/
theorem dilationAdj_of_towerNeighbor_same {n p a b : ℕ} (hp : p.Prime)
    (ha : TowerNeighbor n p a) (hb : TowerNeighbor n p b) (hab : a ≠ b) : DilationAdj a b := by
  have hp0 : 0 < p := hp.pos
  refine ⟨p, hp, ?_⟩
  obtain ⟨i, hi, ha | ha⟩ := ha <;> obtain ⟨j, hj, hb | hb⟩ := hb
  · -- `a = n p^i`, `b = n p^j`
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine ⟨j - i, by omega, Or.inl ?_⟩
      rw [ha, hb, mul_assoc, ← pow_add, Nat.add_sub_cancel' hij.le]
    · exact absurd (ha.trans hb.symm) hab
    · refine ⟨i - j, by omega, Or.inr ?_⟩
      rw [ha, hb, mul_assoc, ← pow_add, Nat.add_sub_cancel' hij.le]
  · -- `a = n p^i`, `n = b p^j`
    exact ⟨i + j, by omega, Or.inr (by rw [ha, hb, mul_assoc, ← pow_add, add_comm])⟩
  · -- `n = a p^i`, `b = n p^j`
    exact ⟨i + j, by omega, Or.inl (by rw [hb, ha, mul_assoc, ← pow_add])⟩
  · -- `n = a p^i = b p^j`
    have hpos : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp0 k
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine ⟨j - i, by omega, Or.inr ?_⟩
      have : a * p ^ i = b * p ^ (j - i) * p ^ i := by
        rw [← ha, hb, mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]
      exact Nat.eq_of_mul_eq_mul_right (hpos i) this
    · exact absurd (Nat.eq_of_mul_eq_mul_right (hpos i) (ha.symm.trans hb)) hab
    · refine ⟨i - j, by omega, Or.inl ?_⟩
      have : b * p ^ j = a * p ^ (i - j) * p ^ j := by
        rw [← hb, ha, mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]
      exact Nat.eq_of_mul_eq_mul_right (hpos j) this

/-- The **link** of `n`: its dilation neighbours, adjacent when they are joined by a dilation
edge. -/
def linkGraph (n : ℕ) : SimpleGraph {m : ℕ // DilationAdj n m} :=
  SimpleGraph.fromRel fun a b => DilationAdj a.1 b.1

theorem linkGraph_adj {n : ℕ} {a b : {m : ℕ // DilationAdj n m}} :
    (linkGraph n).Adj a b ↔ a ≠ b ∧ DilationAdj a.1 b.1 := by
  rw [linkGraph, SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ => ⟨fun h => h.elim id DilationAdj.symm, Or.inl⟩

/-- Along every walk in the link the tower of the current neighbour is constant. -/
theorem towerNeighbor_of_walk {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    {u v : {m : ℕ // DilationAdj n m}} (w : (linkGraph n).Walk u v)
    (hu : TowerNeighbor n p u.1) : TowerNeighbor n p v.1 := by
  induction w with
  | nil => exact hu
  | @cons a b c hadj _ ih =>
    apply ih
    obtain ⟨r, hr, hbr⟩ := b.2
    by_cases hrp : r = p
    · exact hrp ▸ hbr
    · exact absurd (linkGraph_adj.mp hadj).2
        (not_dilationAdj_of_towerNeighbor hn hp hr (Ne.symm hrp) hu hbr)

/-- A vertex cannot be a neighbour on two distinct towers. -/
theorem not_towerNeighbor_two {n p q m : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hmp : TowerNeighbor n p m) (hmq : TowerNeighbor n q m) : False :=
  (hmp.factorization hp hn).2 ((hmq.factorization hq hn).1 p hpq)

/-- **Links are disconnected.** If `n` has neighbours on the towers of two distinct primes, its link
is not connected. -/
theorem not_preconnected_linkGraph {n p q a b : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : TowerNeighbor n p a) (hb : TowerNeighbor n q b) :
    ¬ (linkGraph n).Preconnected := by
  intro hconn
  obtain ⟨w⟩ := hconn ⟨a, p, hp, ha⟩ ⟨b, q, hq, hb⟩
  exact not_towerNeighbor_two hn hp hq hpq (towerNeighbor_of_walk hn hp w ha) hb

/-- Every `n ≥ 2` has neighbours on the towers of `2` and `3` upward, so its link is disconnected. -/
theorem not_preconnected_linkGraph_of_pos {n : ℕ} (hn : n ≠ 0) : ¬ (linkGraph n).Preconnected :=
  not_preconnected_linkGraph hn Nat.prime_two Nat.prime_three (by norm_num)
    ⟨1, le_rfl, Or.inl rfl⟩ ⟨1, le_rfl, Or.inl rfl⟩

/-! ### Contrast: commensurable towers -/

/-- Over a curve the positions are degrees in `ℤ`; when every positive degree is a step, two
positions are adjacent iff they differ. -/
def DegreeAdj (a b : ℤ) : Prop := a ≠ b

/-- **Commensurable towers have complete links**: two distinct neighbours of a degree are adjacent.
-/
theorem degreeLink_adj {n a b : ℤ} (_ha : DegreeAdj n a) (_hb : DegreeAdj n b) (hab : a ≠ b) :
    DegreeAdj a b := hab

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
