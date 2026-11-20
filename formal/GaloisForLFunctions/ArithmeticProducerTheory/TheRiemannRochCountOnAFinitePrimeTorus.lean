import Mathlib

/-!
# The Riemann–Roch count on a finite prime torus

On the torus of `k` primes `p_1, …, p_k` the sections of weight at most `d` are the monomials
`Π p_i^{α_i}` with `Σ α_i log p_i ≤ d`, that is the integers `≤ e^d` composed of these primes
(`mem_simplexPoints_log`). They are the lattice points of a weighted simplex, `simplexPoints`.

* `card_simplexPoints_bounds` (**Riemann–Roch**): for positive weights `w` and `d ≥ 0`
  `d^k ≤ k! · Π w_i · N(d) ≤ (d + Σ w_i)^k`.
  The leading constant is `1 / (Γ(k+1) Π w_i)`, the volume of the simplex; the count lies between
  the volumes at degrees `d` and `d + Σ w_i`.
* `card_filter_pos_simplexPoints` (**duality**): the points with all coordinates positive are the
  points of degree `d − Σ w_i`. The canonical degree of the torus is `Σ w_i = Σ log p_i`.
* `graph_injOn`: on the graph of the Adams operation `ψ_a` the product sections
  `(α, β) ↦ α + a β` stay distinct as long as `d₁ < a · w_i` for every `i` (for primes:
  `e^{d₁} < 2^a`), the condition `m < q` of Bombieri's construction.
* `card_image_add_lt_card_product`: on the diagonal the product sections of bidegree `(d₁, d₂)`
  span at most `N(d₁ + d₂)` dimensions, fewer than `N(d₁) N(d₂)` once
  `k! Π w_i (d₁ + d₂ + Σ w_i)^k < (d₁ d₂)^k`: sections vanishing on the diagonal exist by the
  same count as on a curve, product against sum.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticProducerTheory

/-- The lattice points `α ∈ ℕ^k` of the weighted simplex `Σ α_i w_i ≤ d`, sliced along the first
coordinate. -/
def simplexPoints : (k : ℕ) → (Fin k → ℝ) → ℝ → Finset (Fin k → ℕ)
  | 0, _, d => if 0 ≤ d then {fun i => i.elim0} else ∅
  | k + 1, w, d => (Finset.range (⌊d / w 0⌋₊ + 1)).biUnion fun e =>
      (simplexPoints k (Fin.tail w) (d - e * w 0)).image
        fun β : Fin k → ℕ => (Fin.cons e β : Fin (k + 1) → ℕ)

theorem mem_simplexPoints {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 < w i) {d : ℝ}
    {α : Fin k → ℕ} : α ∈ simplexPoints k w d ↔ ∑ i, (α i : ℝ) * w i ≤ d := by
  induction k generalizing d with
  | zero =>
    simp only [simplexPoints, Fin.sum_univ_zero]
    split_ifs with h
    · simp only [Finset.mem_singleton, h, iff_true]
      exact funext fun i => i.elim0
    · simp only [Finset.notMem_empty, h]
  | succ k ih =>
    simp only [simplexPoints, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      Fin.sum_univ_succ]
    constructor
    · rintro ⟨e, -, β, hβ, rfl⟩
      have h := (ih (fun i => hw i.succ)).mp hβ
      simp only [Fin.cons_zero, Fin.cons_succ]
      linarith
    · intro h
      have htail : 0 ≤ ∑ i : Fin k, (α i.succ : ℝ) * w i.succ :=
        Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hw _).le
      have h0 : 0 ≤ (α 0 : ℝ) * w 0 := mul_nonneg (Nat.cast_nonneg _) (hw 0).le
      refine ⟨α 0, ?_, Fin.tail α, ?_, Fin.cons_self_tail α⟩
      · rw [Nat.lt_succ_iff, Nat.le_floor_iff (div_nonneg (by linarith) (hw 0).le),
          le_div_iff₀ (hw 0)]
        linarith
      · refine (ih (fun i => hw i.succ)).mpr ?_
        show ∑ i : Fin k, (α i.succ : ℝ) * w i.succ ≤ d - α 0 * w 0
        linarith

theorem card_simplexPoints_succ {k : ℕ} (w : Fin (k + 1) → ℝ) (d : ℝ) :
    (simplexPoints (k + 1) w d).card =
      ∑ e ∈ Finset.range (⌊d / w 0⌋₊ + 1), (simplexPoints k (Fin.tail w) (d - e * w 0)).card := by
  simp only [simplexPoints]
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.card_image_of_injective _ fun β β' h => ?_
    have h' := congrArg Fin.tail h
    simpa only [Fin.tail_cons] using h'
  · intro e _ e' _ hne
    refine Finset.disjoint_left.mpr fun α h1 h2 => hne ?_
    obtain ⟨β, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨β', _, h⟩ := Finset.mem_image.mp h2
    have h0 := congrFun h 0
    simpa using h0.symm

/-- For `0 ≤ w ≤ y`: `y^(n+1) − (n+1) w y^n ≤ (y − w)^(n+1)`. -/
private theorem pow_succ_sub_le {y w : ℝ} (hw : 0 ≤ w) (hwy : w ≤ y) (n : ℕ) :
    y ^ (n + 1) - (n + 1) * w * y ^ n ≤ (y - w) ^ (n + 1) := by
  have hy : 0 ≤ y := hw.trans hwy
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hwy)
    have h2 : 0 ≤ ((n : ℝ) + 1) * w * w * y ^ n :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hw) hw) (pow_nonneg hy n)
    have e1 : y ^ (n + 1) = y ^ n * y := pow_succ y n
    have e2 : y ^ (n + 1 + 1) = y ^ n * y * y := by rw [pow_succ, pow_succ]
    rw [pow_succ (y - w) (n + 1), e2, e1]
    rw [e1] at h1
    push_cast
    linarith

/-- For `0 ≤ y`, `0 ≤ w`: `y^(n+1) + (n+1) w y^n ≤ (y + w)^(n+1)`. -/
private theorem pow_succ_add_le {y w : ℝ} (hy : 0 ≤ y) (hw : 0 ≤ w) (n : ℕ) :
    y ^ (n + 1) + (n + 1) * w * y ^ n ≤ (y + w) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := mul_le_mul_of_nonneg_right ih (add_nonneg hy hw)
    have h2 : 0 ≤ ((n : ℝ) + 1) * w * w * y ^ n :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hw) hw) (pow_nonneg hy n)
    have e1 : y ^ (n + 1) = y ^ n * y := pow_succ y n
    have e2 : y ^ (n + 1 + 1) = y ^ n * y * y := by rw [pow_succ, pow_succ]
    rw [pow_succ (y + w) (n + 1), e2, e1]
    rw [e1] at h1
    push_cast
    linarith

/-- The slices of `x^(n+1)`: telescoping `(x − e w)₊^(n+1)` over `e ≤ ⌊x/w⌋`. -/
private theorem le_sum_slices {x w : ℝ} (hx : 0 ≤ x) (hw : 0 < w) (n : ℕ) :
    x ^ (n + 1) ≤ ((n : ℝ) + 1) * w * ∑ e ∈ Finset.range (⌊x / w⌋₊ + 1), (x - e * w) ^ n := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ e : ℕ, g e = (max (x - e * w) 0) ^ (n + 1) :=
    ⟨fun e => (max (x - e * w) 0) ^ (n + 1), fun _ => rfl⟩
  have hstep : ∀ e ∈ Finset.range (⌊x / w⌋₊ + 1),
      g e - g (e + 1) ≤ ((n : ℝ) + 1) * w * (x - e * w) ^ n := by
    intro e he
    have heE : e ≤ ⌊x / w⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
    have hy : 0 ≤ x - e * w := by
      have h1 : (e : ℝ) ≤ x / w :=
        (Nat.cast_le.mpr heE).trans (Nat.floor_le (div_nonneg hx hw.le))
      rw [le_div_iff₀ hw] at h1
      linarith
    have hpow : 0 ≤ (x - e * w) ^ n := pow_nonneg hy n
    have e3 : x - ((e + 1 : ℕ) : ℝ) * w = x - e * w - w := by
      push_cast
      ring
    rw [hg, hg, e3, max_eq_left hy]
    rcases le_or_gt w (x - e * w) with hwy | hwy
    · rw [max_eq_left (sub_nonneg.mpr hwy)]
      have h := pow_succ_sub_le hw.le hwy n
      linarith
    · rw [max_eq_right (by linarith : x - e * w - w ≤ 0), zero_pow (Nat.succ_ne_zero n),
        sub_zero, pow_succ]
      have h1 : (x - e * w) ^ n * (x - e * w) ≤ (x - e * w) ^ n * w :=
        mul_le_mul_of_nonneg_left hwy.le hpow
      have h2 : 0 ≤ (n : ℝ) * w * (x - e * w) ^ n :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hw.le) hpow
      linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub', ← Finset.mul_sum] at hsum
  have hg0 : g 0 = x ^ (n + 1) := by
    rw [hg, Nat.cast_zero, zero_mul, sub_zero, max_eq_left hx]
  have hgE : g (⌊x / w⌋₊ + 1) = 0 := by
    have h1 : x / w < (⌊x / w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (x / w)
    rw [div_lt_iff₀ hw] at h1
    rw [hg, max_eq_right (by push_cast; linarith), zero_pow (Nat.succ_ne_zero n)]
  rw [hg0, hgE, sub_zero] at hsum
  exact hsum

/-- The slices of `(x + W + w)^(n+1)`: telescoping `(x + W + w − e w)^(n+1)` over `e ≤ ⌊x/w⌋`. -/
private theorem sum_slices_le {x w W : ℝ} (hx : 0 ≤ x) (hw : 0 < w) (hW : 0 ≤ W) (n : ℕ) :
    ((n : ℝ) + 1) * w * ∑ e ∈ Finset.range (⌊x / w⌋₊ + 1), (x - e * w + W) ^ n
      ≤ (x + W + w) ^ (n + 1) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ e : ℕ, g e = (x + W + w - e * w) ^ (n + 1) :=
    ⟨fun e => (x + W + w - e * w) ^ (n + 1), fun _ => rfl⟩
  have hnn : ∀ e : ℕ, e ≤ ⌊x / w⌋₊ → 0 ≤ x - e * w + W := by
    intro e heE
    have h1 : (e : ℝ) ≤ x / w :=
      (Nat.cast_le.mpr heE).trans (Nat.floor_le (div_nonneg hx hw.le))
    rw [le_div_iff₀ hw] at h1
    linarith
  have hstep : ∀ e ∈ Finset.range (⌊x / w⌋₊ + 1),
      ((n : ℝ) + 1) * w * (x - e * w + W) ^ n ≤ g e - g (e + 1) := by
    intro e he
    have hy := hnn e (Nat.lt_succ_iff.mp (Finset.mem_range.mp he))
    have h := pow_succ_add_le hy hw.le n
    have e1 : x + W + w - (e : ℝ) * w = x - e * w + W + w := by ring
    have e2 : x + W + w - ((e + 1 : ℕ) : ℝ) * w = x - e * w + W := by
      push_cast
      ring
    rw [hg, hg, e1, e2]
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub', ← Finset.mul_sum] at hsum
  have hg0 : g 0 = (x + W + w) ^ (n + 1) := by
    rw [hg, Nat.cast_zero, zero_mul, sub_zero]
  have hgE : 0 ≤ g (⌊x / w⌋₊ + 1) := by
    have e2 : x + W + w - ((⌊x / w⌋₊ + 1 : ℕ) : ℝ) * w = x - (⌊x / w⌋₊ : ℝ) * w + W := by
      push_cast
      ring
    rw [hg, e2]
    exact pow_nonneg (hnn _ le_rfl) _
  rw [hg0] at hsum
  linarith

/-- **Riemann–Roch on a finite torus.** The number `N(d)` of lattice points of the weighted
simplex satisfies `d^k ≤ k! · Π w_i · N(d) ≤ (d + Σ w_i)^k`. -/
theorem card_simplexPoints_bounds : ∀ (k : ℕ) (w : Fin k → ℝ), (∀ i, 0 < w i) → ∀ d : ℝ, 0 ≤ d →
    d ^ k ≤ (k.factorial : ℝ) * (∏ i, w i) * (simplexPoints k w d).card ∧
      (k.factorial : ℝ) * (∏ i, w i) * (simplexPoints k w d).card ≤ (d + ∑ i, w i) ^ k
  | 0, w, _, d, hd => by
    simp [simplexPoints, hd]
  | k + 1, w, hw, d, hd => by
    have ih := card_simplexPoints_bounds k (Fin.tail w) (fun i => hw i.succ)
    have hw0 := hw 0
    have hslice : ∀ e ∈ Finset.range (⌊d / w 0⌋₊ + 1), 0 ≤ d - e * w 0 := by
      intro e he
      have heE : e ≤ ⌊d / w 0⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
      have h1 : (e : ℝ) ≤ d / w 0 :=
        (Nat.cast_le.mpr heE).trans (Nat.floor_le (div_nonneg hd hw0.le))
      rw [le_div_iff₀ hw0] at h1
      linarith
    have hprod : ∏ i, w i = w 0 * ∏ i, Fin.tail w i := Fin.prod_univ_succ w
    have hsum : ∑ i, w i = w 0 + ∑ i, Fin.tail w i := Fin.sum_univ_succ w
    have hWnn : 0 ≤ ∑ i, Fin.tail w i := Finset.sum_nonneg fun i _ => (hw i.succ).le
    have hc : (0 : ℝ) ≤ ((k : ℝ) + 1) * w 0 := mul_nonneg (by positivity) hw0.le
    rw [card_simplexPoints_succ, hprod, hsum, Nat.factorial_succ]
    push_cast
    constructor
    · have h1 := le_sum_slices hd hw0 k
      have h2 : ∑ e ∈ Finset.range (⌊d / w 0⌋₊ + 1), (d - e * w 0) ^ k ≤
          ∑ e ∈ Finset.range (⌊d / w 0⌋₊ + 1), (k.factorial : ℝ) * (∏ i, Fin.tail w i) *
            (simplexPoints k (Fin.tail w) (d - e * w 0)).card :=
        Finset.sum_le_sum fun e he => (ih _ (hslice e he)).1
      have h3 := mul_le_mul_of_nonneg_left h2 hc
      rw [← Finset.mul_sum] at h3
      exact h1.trans (h3.trans (le_of_eq (by ring)))
    · have h2 : ∑ e ∈ Finset.range (⌊d / w 0⌋₊ + 1), (k.factorial : ℝ) * (∏ i, Fin.tail w i) *
            (simplexPoints k (Fin.tail w) (d - e * w 0)).card ≤
          ∑ e ∈ Finset.range (⌊d / w 0⌋₊ + 1), (d - e * w 0 + ∑ i, Fin.tail w i) ^ k :=
        Finset.sum_le_sum fun e he => (ih _ (hslice e he)).2
      have h3 := mul_le_mul_of_nonneg_left h2 hc
      rw [← Finset.mul_sum] at h3
      have h4 := sum_slices_le hd hw0 hWnn k
      exact (le_of_eq (by ring)).trans (h3.trans (h4.trans (le_of_eq (by ring))))

/-- **Duality.** The lattice points with all coordinates positive are the lattice points of the
degree lowered by `Σ w_i`. -/
theorem card_filter_pos_simplexPoints {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 < w i) (d : ℝ) :
    ((simplexPoints k w d).filter fun α => ∀ i, 1 ≤ α i).card =
      (simplexPoints k w (d - ∑ i, w i)).card := by
  have himg : (simplexPoints k w (d - ∑ i, w i)).image (fun β i => β i + 1) =
      (simplexPoints k w d).filter fun α => ∀ i, 1 ≤ α i := by
    ext α
    simp only [Finset.mem_image, Finset.mem_filter, mem_simplexPoints hw]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨?_, fun i => Nat.le_add_left 1 (β i)⟩
      show ∑ i, ((β i + 1 : ℕ) : ℝ) * w i ≤ d
      have e : ∑ i, ((β i + 1 : ℕ) : ℝ) * w i = ∑ i, (β i : ℝ) * w i + ∑ i, w i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by push_cast; ring
      rw [e]
      linarith
    · rintro ⟨hα, hpos⟩
      refine ⟨fun i => α i - 1, ?_, funext fun i => Nat.sub_add_cancel (hpos i)⟩
      show ∑ i, ((α i - 1 : ℕ) : ℝ) * w i ≤ d - ∑ i, w i
      have e : ∑ i, ((α i - 1 : ℕ) : ℝ) * w i = ∑ i, (α i : ℝ) * w i - ∑ i, w i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Nat.cast_sub (hpos i), Nat.cast_one]
          ring
      rw [e]
      linarith
  rw [← himg]
  exact Finset.card_image_of_injective _ fun β β' h => funext fun i => by
    have hi := congrFun h i
    simpa using hi

/-- Degrees add under multiplication of sections. -/
theorem add_mem_simplexPoints {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 < w i) {d₁ d₂ : ℝ}
    {α β : Fin k → ℕ} (hα : α ∈ simplexPoints k w d₁) (hβ : β ∈ simplexPoints k w d₂) :
    α + β ∈ simplexPoints k w (d₁ + d₂) := by
  rw [mem_simplexPoints hw] at hα hβ ⊢
  have e : ∑ i, ((α + β) i : ℝ) * w i = ∑ i, (α i : ℝ) * w i + ∑ i, (β i : ℝ) * w i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Pi.add_apply]
      push_cast
      ring
  rw [e]
  linarith

/-- **Sections on the graph of `ψ_a` stay distinct below the first collision.** If
`d₁ < a · w_i` for every `i`, the map `(α, β) ↦ α + a β` is injective on sections of first degree
at most `d₁`. -/
theorem graph_injOn {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 < w i) {a : ℕ} {d₁ : ℝ}
    (ha : ∀ i, d₁ < a * w i) {α α' β β' : Fin k → ℕ} (hα : α ∈ simplexPoints k w d₁)
    (hα' : α' ∈ simplexPoints k w d₁) (h : α + a • β = α' + a • β') : α = α' ∧ β = β' := by
  rw [mem_simplexPoints hw] at hα hα'
  have hlt : ∀ γ : Fin k → ℕ, ∑ i, (γ i : ℝ) * w i ≤ d₁ → ∀ i, γ i < a := by
    intro γ hγ i
    have h1 : (γ i : ℝ) * w i ≤ ∑ j, (γ j : ℝ) * w j :=
      Finset.single_le_sum (f := fun j => (γ j : ℝ) * w j)
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hw j).le) (Finset.mem_univ i)
    have h2 : (γ i : ℝ) * w i < a * w i := lt_of_le_of_lt (h1.trans hγ) (ha i)
    exact_mod_cast lt_of_mul_lt_mul_right h2 (hw i).le
  have hcoord : ∀ i, α i = α' i ∧ β i = β' i := by
    intro i
    have hi : α i + a * β i = α' i + a * β' i := by
      have := congrFun h i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    have h1 := hlt α hα i
    have h2 := hlt α' hα' i
    have hmod : α i = α' i := by
      have e1 : (α i + a * β i) % a = α i := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
      have e2 : (α' i + a * β' i) % a = α' i := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
      rw [← e1, hi, e2]
    refine ⟨hmod, ?_⟩
    rw [hmod] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < a) (Nat.add_left_cancel hi)
  exact ⟨funext fun i => (hcoord i).1, funext fun i => (hcoord i).2⟩

/-- **Bombieri's count on the torus.** On the diagonal, the product sections of bidegree
`(d₁, d₂)` take at most `N(d₁ + d₂)` values, fewer than their number `N(d₁) N(d₂)` as soon as
`k! Π w_i (d₁ + d₂ + Σ w_i)^k < (d₁ d₂)^k`. -/
theorem card_image_add_lt_card_product {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 < w i) {d₁ d₂ : ℝ}
    (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂)
    (h : (k.factorial : ℝ) * (∏ i, w i) * (d₁ + d₂ + ∑ i, w i) ^ k < (d₁ * d₂) ^ k) :
    ((simplexPoints k w d₁ ×ˢ simplexPoints k w d₂).image fun p => p.1 + p.2).card <
      (simplexPoints k w d₁ ×ˢ simplexPoints k w d₂).card := by
  have hsub : ((simplexPoints k w d₁ ×ˢ simplexPoints k w d₂).image fun p => p.1 + p.2) ⊆
      simplexPoints k w (d₁ + d₂) := by
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hγ
    rw [Finset.mem_product] at hp
    exact add_mem_simplexPoints hw hp.1 hp.2
  refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
  rw [Finset.card_product]
  have b1 := (card_simplexPoints_bounds k w hw d₁ h1).1
  have b2 := (card_simplexPoints_bounds k w hw d₂ h2).1
  have b12 := (card_simplexPoints_bounds k w hw (d₁ + d₂) (add_nonneg h1 h2)).2
  have hc : (0 : ℝ) < (k.factorial : ℝ) * ∏ i, w i :=
    mul_pos (by exact_mod_cast Nat.factorial_pos k) (Finset.prod_pos fun i _ => hw i)
  have h3 : (d₁ * d₂) ^ k ≤
      ((k.factorial : ℝ) * (∏ i, w i) * (simplexPoints k w d₁).card) *
        ((k.factorial : ℝ) * (∏ i, w i) * (simplexPoints k w d₂).card) := by
    rw [mul_pow]
    exact mul_le_mul b1 b2 (pow_nonneg h2 k) ((pow_nonneg h1 k).trans b1)
  have h4 := mul_le_mul_of_nonneg_left b12 hc.le
  have h5 : (k.factorial : ℝ) * (∏ i, w i) * ((k.factorial : ℝ) * ∏ i, w i) *
        ((simplexPoints k w (d₁ + d₂)).card : ℝ) <
      (k.factorial : ℝ) * (∏ i, w i) * ((k.factorial : ℝ) * ∏ i, w i) *
        (((simplexPoints k w d₁).card : ℝ) * (simplexPoints k w d₂).card) := by
    linarith
  have key := lt_of_mul_lt_mul_left h5 (mul_pos hc hc).le
  exact_mod_cast key

/-- With the weights `log p_i` the lattice points of degree `log X` are the monomials
`Π p_i^{α_i} ≤ X`. -/
theorem mem_simplexPoints_log {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {X : ℝ} (hX : 0 < X)
    {α : Fin k → ℕ} :
    α ∈ simplexPoints k (fun i => Real.log (p i)) (Real.log X) ↔
      ((∏ i, p i ^ α i : ℕ) : ℝ) ≤ X := by
  have hp1 : ∀ i, (1 : ℝ) < p i := fun i => by
    have := hp i
    exact_mod_cast (by omega : 1 < p i)
  have hw : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (hp1 i)
  have hpos : (0 : ℝ) < ((∏ i, p i ^ α i : ℕ) : ℝ) := by
    push_cast
    exact Finset.prod_pos fun i _ => pow_pos (by linarith [hp1 i]) _
  have e : Real.log ((∏ i, p i ^ α i : ℕ) : ℝ) = ∑ i, (α i : ℝ) * Real.log (p i) := by
    push_cast
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
    · intro i _
      exact pow_ne_zero _ (by linarith [hp1 i])
  rw [mem_simplexPoints hw, ← Real.log_le_log_iff hpos hX, e]

end GaloisForLFunctions.ArithmeticProducerTheory
