import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumDiscreteSecondMoment

set_option autoImplicit false

/-!
# Dyadic classes of the difference multiplicities of a point set

The combinatorial half of Guth–Maynard Lemma 11.6. For a finite `W ⊂ ℝ` and a pair
`p = (t₁, t₂) ∈ W²` let `u(p) = ⌊t₁ − t₂⌋` and `r(u) = #{p ∈ W² : u(p) = u}`. The pairs are split
into the dyadic classes `P_j = {p : ⌊log₂ r(u(p))⌋ = j}`, `j < J = ⌊log₂ |W|²⌋ + 1`, and
`U_j = u(P_j)` are the integers of class `j`. Then:

* `|R(v)|² = Σ_{j < J} R_j(v)`, `R_j(v) = Σ_{p ∈ P_j} v^{i(t₁−t₂)}` (`normSq_lagSum_eq_sum_classes`);
* `2^j |U_j| ≤ |W|²` and `4^j |U_j| ≤ E(W)` (pairs with equal `⌊t₁ − t₂⌋` are additive
  quadruples) — Guth–Maynard's `B|U_B| ≤ |W|²`, `B²|U_B| ≤ E(W)`;
* every fibre of `u` in `P_j` has fewer than `2^{j+1}` points, so for `Φ ≥ 0`
  `Σ_{p,q ∈ P_j} Φ(u(p) − u(q)) ≤ 4^{j+1} Σ_{u₁,u₂ ∈ U_j} Φ(u₁ − u₂)`.
-/

open Finset ComplexConjugate

namespace RHTower.GuthMaynard

noncomputable section

/-- `u(p) = ⌊t₁ − t₂⌋`. -/
def diffFloor (p : ℝ × ℝ) : ℤ := ⌊p.1 - p.2⌋

/-- `r(u) = #{p ∈ W² : ⌊t₁ − t₂⌋ = u}`. -/
def diffMult (W : Finset ℝ) (u : ℤ) : ℕ := ((W ×ˢ W).filter fun p => diffFloor p = u).card

/-- The dyadic class `⌊log₂ r(u(p))⌋` of a pair. -/
def diffClass (W : Finset ℝ) (p : ℝ × ℝ) : ℕ := Nat.log 2 (diffMult W (diffFloor p))

/-- The pairs of class `j`. -/
def diffClassSet (W : Finset ℝ) (j : ℕ) : Finset (ℝ × ℝ) :=
  (W ×ˢ W).filter fun p => diffClass W p = j

/-- The integers `U_j = u(P_j)`. -/
def diffClassValues (W : Finset ℝ) (j : ℕ) : Finset ℤ := (diffClassSet W j).image diffFloor

/-- The number of classes `J = ⌊log₂ |W|²⌋ + 1`. -/
def diffClassCount (W : Finset ℝ) : ℕ := Nat.log 2 (W.card ^ 2) + 1

theorem one_le_diffMult {W : Finset ℝ} {p : ℝ × ℝ} (hp : p ∈ W ×ˢ W) :
    1 ≤ diffMult W (diffFloor p) :=
  card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, rfl⟩⟩

theorem diffMult_le (W : Finset ℝ) (u : ℤ) : diffMult W u ≤ W.card ^ 2 := by
  unfold diffMult
  refine (card_filter_le _ _).trans ?_
  rw [card_product, sq]

theorem diffClass_lt (W : Finset ℝ) (p : ℝ × ℝ) : diffClass W p < diffClassCount W :=
  Nat.lt_succ_of_le (Nat.log_mono_right (diffMult_le W _))

/-- The class of a pair depends only on `u(p)`. -/
theorem diffClass_eq_of_diffFloor_eq {W : Finset ℝ} {p q : ℝ × ℝ}
    (h : diffFloor p = diffFloor q) : diffClass W p = diffClass W q := by
  unfold diffClass; rw [h]

theorem two_pow_le_diffMult {W : Finset ℝ} {j : ℕ} {u : ℤ} (hu : u ∈ diffClassValues W j) :
    2 ^ j ≤ diffMult W u := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
  obtain ⟨hpW, hj⟩ := mem_filter.mp hp
  rw [← hj]
  exact Nat.pow_log_le_self 2 (by have := one_le_diffMult hpW; omega)

theorem diffMult_lt_two_pow {W : Finset ℝ} {j : ℕ} {u : ℤ} (hu : u ∈ diffClassValues W j) :
    diffMult W u < 2 ^ (j + 1) := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
  obtain ⟨_, hj⟩ := mem_filter.mp hp
  rw [← hj]
  exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- On `U_j` the fibre of `u` inside `P_j` is the whole fibre in `W²`. -/
theorem card_filter_diffClassSet {W : Finset ℝ} {j : ℕ} {u : ℤ} (hu : u ∈ diffClassValues W j) :
    ((diffClassSet W j).filter fun p => diffFloor p = u).card = diffMult W u := by
  obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hu
  unfold diffMult diffClassSet
  rw [filter_filter]
  congr 1
  refine filter_congr fun q _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [diffClass_eq_of_diffFloor_eq h]
  exact (mem_filter.mp hp₀).2

/-- `Σ_{u ∈ u(W²)} r(u) = |W|²`. -/
theorem sum_diffMult_eq (W : Finset ℝ) :
    ∑ u ∈ (W ×ˢ W).image diffFloor, diffMult W u = W.card ^ 2 := by
  simp only [diffMult]
  rw [← card_eq_sum_card_fiberwise (fun p hp => mem_image_of_mem diffFloor hp), card_product, sq]

/-- `Σ_{u} r(u)² = #{(p, q) ∈ (W²)² : ⌊t₁ − t₂⌋ = ⌊t₃ − t₄⌋} ≤ E(W)`. -/
theorem sum_diffMult_sq_le (W : Finset ℝ) :
    ∑ u ∈ (W ×ˢ W).image diffFloor, diffMult W u ^ 2 ≤ additiveEnergy W := by
  classical
  set P := W ×ˢ W
  set Q := (P ×ˢ P).filter fun pq => diffFloor pq.1 = diffFloor pq.2
  have hfib : ∀ u ∈ P.image diffFloor,
      (Q.filter fun pq => diffFloor pq.1 = u).card = diffMult W u ^ 2 := by
    intro u _
    have : (Q.filter fun pq => diffFloor pq.1 = u) =
        (P.filter fun p => diffFloor p = u) ×ˢ (P.filter fun p => diffFloor p = u) := by
      ext ⟨p, q⟩
      simp only [Q, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨hp, hq⟩, hpq⟩, hu⟩
        exact ⟨⟨hp, hu⟩, hq, hpq ▸ hu⟩
      · rintro ⟨⟨hp, hu⟩, hq, hu'⟩
        exact ⟨⟨⟨hp, hq⟩, hu.trans hu'.symm⟩, hu⟩
    rw [this, card_product, sq]; rfl
  have hQ : Q.card = ∑ u ∈ P.image diffFloor, diffMult W u ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun pq : (ℝ × ℝ) × (ℝ × ℝ) => diffFloor pq.1)
      (t := P.image diffFloor) (fun pq hpq => mem_image_of_mem diffFloor
        (mem_product.mp (mem_filter.mp hpq).1).1)]
    exact sum_congr rfl hfib
  rw [← hQ]
  unfold additiveEnergy
  refine card_le_card_of_injOn (fun pq => (pq.1.1, pq.2.2, pq.1.2, pq.2.1)) ?_ ?_
  · intro pq hpq
    obtain ⟨hmem, hfl⟩ := mem_filter.mp (mem_coe.mp hpq)
    obtain ⟨hp, hq⟩ := mem_product.mp hmem
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    obtain ⟨hq1, hq2⟩ := mem_product.mp hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product]
    refine ⟨⟨hp1, hq2, hp2, hq1⟩, ?_⟩
    have := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    have e : pq.1.1 + pq.2.2 - pq.1.2 - pq.2.1 = (pq.1.1 - pq.1.2) - (pq.2.1 - pq.2.2) := by ring
    rw [e]; exact this.le
  · intro pq _ pq' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1 h.2.2.1) (Prod.ext h.2.2.2 h.2.1)

/-- Guth–Maynard's `B |U_B| ≤ |W|²` with `B = 2^j`. -/
theorem two_pow_mul_card_diffClassValues_le (W : Finset ℝ) (j : ℕ) :
    2 ^ j * (diffClassValues W j).card ≤ W.card ^ 2 := by
  have hsub : diffClassValues W j ⊆ (W ×ˢ W).image diffFloor :=
    image_subset_image (filter_subset _ _)
  calc 2 ^ j * (diffClassValues W j).card = ∑ _u ∈ diffClassValues W j, 2 ^ j := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ u ∈ diffClassValues W j, diffMult W u := sum_le_sum fun u hu => two_pow_le_diffMult hu
    _ ≤ ∑ u ∈ (W ×ˢ W).image diffFloor, diffMult W u :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    _ = W.card ^ 2 := sum_diffMult_eq W

/-- Guth–Maynard's `B² |U_B| ≤ E(W)` with `B = 2^j`. -/
theorem four_pow_mul_card_diffClassValues_le (W : Finset ℝ) (j : ℕ) :
    (2 ^ j) ^ 2 * (diffClassValues W j).card ≤ additiveEnergy W := by
  have hsub : diffClassValues W j ⊆ (W ×ˢ W).image diffFloor :=
    image_subset_image (filter_subset _ _)
  calc (2 ^ j) ^ 2 * (diffClassValues W j).card = ∑ _u ∈ diffClassValues W j, (2 ^ j) ^ 2 := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ u ∈ diffClassValues W j, diffMult W u ^ 2 :=
        sum_le_sum fun u hu => Nat.pow_le_pow_left (two_pow_le_diffMult hu) 2
    _ ≤ ∑ u ∈ (W ×ˢ W).image diffFloor, diffMult W u ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    _ ≤ additiveEnergy W := sum_diffMult_sq_le W

/-- **Regrouping by `u`.** For `Φ ≥ 0`:
`Σ_{p,q ∈ P_j} Φ(u(p) − u(q)) ≤ 4^{j+1} Σ_{u₁,u₂ ∈ U_j} Φ(u₁ − u₂)`. -/
theorem sum_sum_diffClassSet_le (W : Finset ℝ) (j : ℕ) {Φ : ℤ → ℝ} (hΦ : ∀ u, 0 ≤ Φ u) :
    ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j, Φ (diffFloor p - diffFloor q) ≤
      ((2 : ℝ) ^ (j + 1)) ^ 2 *
        ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j, Φ (u₁ - u₂) := by
  classical
  set c : ℤ → ℝ := fun u => (((diffClassSet W j).filter fun p => diffFloor p = u).card : ℝ)
  have hc : ∀ u ∈ diffClassValues W j, c u ≤ (2 : ℝ) ^ (j + 1) := by
    intro u hu
    simp only [c]
    rw [card_filter_diffClassSet hu]
    exact_mod_cast (diffMult_lt_two_pow hu).le
  have hc0 : ∀ u, 0 ≤ c u := fun u => Nat.cast_nonneg _
  -- regroup a sum over `P_j` of a function of `u(p)`
  have hregroup : ∀ h : ℤ → ℝ, ∑ p ∈ diffClassSet W j, h (diffFloor p) =
      ∑ u ∈ diffClassValues W j, c u * h u := by
    intro h
    rw [sum_comp h diffFloor]
    refine sum_congr rfl fun u _ => ?_
    simp only [c, nsmul_eq_mul]
  calc ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j, Φ (diffFloor p - diffFloor q)
      = ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j, c u₁ * (c u₂ * Φ (u₁ - u₂)) := by
        rw [hregroup (fun u₁ => ∑ q ∈ diffClassSet W j, Φ (u₁ - diffFloor q))]
        refine sum_congr rfl fun u₁ _ => ?_
        rw [hregroup (fun u₂ => Φ (u₁ - u₂)), mul_sum]
    _ ≤ ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j,
          (2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ (j + 1) * Φ (u₁ - u₂)) := by
        refine sum_le_sum fun u₁ hu₁ => sum_le_sum fun u₂ hu₂ => ?_
        have h1 := hc u₁ hu₁
        have h2 := hc u₂ hu₂
        have := hΦ (u₁ - u₂)
        gcongr
    _ = ((2 : ℝ) ^ (j + 1)) ^ 2 *
          ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j, Φ (u₁ - u₂) := by
        rw [mul_sum]
        refine sum_congr rfl fun u₁ _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun u₂ _ => ?_
        ring

/-- **Class decomposition of `|R|²`.** `|R(v)|² = Σ_{j < J} Σ_{p ∈ P_j} v^{i(t₁−t₂)}`. -/
theorem normSq_lagSum_eq_sum_classes (W : Finset ℝ) (v : ℝ) :
    ((‖lagSum W v‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ range (diffClassCount W),
      labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) v := by
  rw [← labelledLagSum_id, normSq_labelledLagSum_eq]
  have hmaps : ∀ p ∈ W ×ˢ W, diffClass W p ∈ range (diffClassCount W) :=
    fun p _ => mem_range.mpr (diffClass_lt W p)
  rw [← sum_product', ← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun j _ => ?_
  unfold labelledLagSum diffClassSet
  refine sum_congr rfl fun p _ => ?_
  push_cast
  rfl

/-- `u(p) ∈ [−T−1, T]` for `p ∈ W²`, `W ⊆ [T₀, T₀ + T]`. -/
theorem diffFloor_mem {W : Finset ℝ} {T₀ T : ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    {p : ℝ × ℝ} (hp : p ∈ W ×ˢ W) :
    -T - 1 ≤ (diffFloor p : ℝ) ∧ (diffFloor p : ℝ) ≤ -T - 1 + (2 * T + 1) := by
  obtain ⟨h1, h2⟩ := mem_product.mp hp
  have a := hW _ h1
  have b := hW _ h2
  have hf1 := Int.floor_le (p.1 - p.2)
  have hf2 := Int.lt_floor_add_one (p.1 - p.2)
  unfold diffFloor
  constructor <;> linarith

end

end RHTower.GuthMaynard
