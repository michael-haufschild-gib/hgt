import Mathlib

/-!
# The Euler product tensorizes the dilation complex

With the measure `n^{−σ}` on the integers whose exponents lie in a box `0 ≤ v_p(n) ≤ A_p`, `p ∈ S`,
the valuations are independent: the measure is the product of the truncated geometric measures
`π_p(a) ∝ p^{−aσ}` (the Euler product). The dilation edges `(n, p^j n)` change one coordinate.
Their weights are `Λ(p^j) p^{−jσ}` against the vertex mass `n^{−σ}`. So the dilation energy is the
sum over `p ∈ S` of a **tower energy** in the coordinate `p`, averaged over the other coordinates.
This is an exact Künneth structure, and here, unlike in links, local spectral gaps do pass to the
whole complex.

* **Law of total variance** (`pvar_prod_eq`) and **convexity of the variance** (`pvar_avg_le`) give
  the two-factor Efron–Stein inequality (`pvar_prod_le`).
* **The Künneth step** (`gap_prod_ge`): if two factors satisfy Poincaré inequalities with constant
  `λ`, their product does too, for the summed Dirichlet form. Adding a prime to a sieve never
  lowers the gap below the gap of the new tower.
* **The gap of one tower** (`towerEnergy_ge`, `towerEnergy_valuationStep`): on the box
  `0 ≤ a ≤ A` with weights `π(a) = r^a/Z`, `Z = Σ_{a ≤ A} r^a`, the tower energy
  `Σ_{a<b} ℓ π(b) (f(b) − f(a))²` dominates `ℓ Z` times the variance, term by term. The valuation
  step `1_{a ≥ 1}` attains it, so the gap is exactly `ℓ Z`. With `ℓ = log p`, `r = p^{−σ}` and
  `A → ∞` it is `log p/(1 − p^{−σ})`. The minimum over primes sits at `p = 2`, and at `σ = 1` it
  is `2 log 2`, the gap that RAPT proves at the horizon with its approximate tensorization.

The obstructions to an exact local-to-global gap for Weil's form are therefore the horizon, which
replaces the box by a simplex and couples the valuations, and the successor edges, which do not
respect the product structure. Neither is a property of the links.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-! ### Variance under probability weights -/

section Variance

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The variance `Σ μ f² − (Σ μ f)²` under weights `μ`. -/
def pvar (μ : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, μ x * f x ^ 2 - (∑ x, μ x * f x) ^ 2

/-- For probability weights the variance is the half pair-sum `½ Σ μ_x μ_y (f x − f y)²`. -/
theorem pvar_eq_pairs {μ : X → ℝ} (hμ : ∑ x, μ x = 1) (f : X → ℝ) :
    pvar μ f = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
  have hexp : ∀ x y, μ x * μ y * (f x - f y) ^ 2 =
      μ y * (μ x * f x ^ 2) + μ x * (μ y * f y ^ 2) - 2 * (μ x * f x) * (μ y * f y) :=
    fun x y => by ring
  rw [pvar]
  simp only [hexp, sum_sub_distrib, sum_add_distrib, ← sum_mul, ← mul_sum, hμ, one_mul]
  ring

theorem pvar_nonneg {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ : ∑ x, μ x = 1) (f : X → ℝ) :
    0 ≤ pvar μ f := by
  rw [pvar_eq_pairs hμ]
  exact mul_nonneg (by norm_num) (sum_nonneg fun x _ => sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (hμ0 x) (hμ0 y)) (sq_nonneg _))

/-- **Convexity of the variance**: the variance of a `ν`-average is at most the `ν`-average of the
variances. -/
theorem pvar_avg_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ : ∑ x, μ x = 1) {ν : Y → ℝ}
    (hν0 : ∀ y, 0 ≤ ν y) (hν : ∑ y, ν y = 1) (F : X → Y → ℝ) :
    pvar μ (fun x => ∑ y, ν y * F x y) ≤ ∑ y, ν y * pvar μ (fun x => F x y) := by
  have hdiff : ∀ x x', (∑ y, ν y * F x y) - ∑ y, ν y * F x' y = ∑ y, ν y * (F x y - F x' y) :=
    fun x x' => by rw [← sum_sub_distrib]; exact sum_congr rfl fun y _ => by ring
  -- Jensen: `(Σ ν a)² ≤ Σ ν a²`, i.e. the variance of `a` under `ν` is nonnegative.
  have hJ : ∀ x x', (∑ y, ν y * (F x y - F x' y)) ^ 2 ≤ ∑ y, ν y * (F x y - F x' y) ^ 2 :=
    fun x x' => by have := pvar_nonneg hν0 hν (fun y => F x y - F x' y); rw [pvar] at this; linarith
  have hx : ∀ x x', μ x * μ x' * ∑ y, ν y * (F x y - F x' y) ^ 2 =
      ∑ y, ν y * (μ x * μ x' * (F x y - F x' y) ^ 2) :=
    fun x x' => by rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  calc pvar μ (fun x => ∑ y, ν y * F x y)
      = 1 / 2 * ∑ x, ∑ x', μ x * μ x' * (∑ y, ν y * (F x y - F x' y)) ^ 2 := by
        rw [pvar_eq_pairs hμ]; simp only [hdiff]
    _ ≤ 1 / 2 * ∑ x, ∑ x', μ x * μ x' * ∑ y, ν y * (F x y - F x' y) ^ 2 := by
        gcongr with x _ x' _
        · exact mul_nonneg (hμ0 x) (hμ0 x')
        · exact hJ x x'
    _ = 1 / 2 * ∑ x, ∑ x', ∑ y, ν y * (μ x * μ x' * (F x y - F x' y) ^ 2) := by simp only [hx]
    _ = 1 / 2 * ∑ y, ∑ x, ∑ x', ν y * (μ x * μ x' * (F x y - F x' y) ^ 2) := by
        rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
    _ = ∑ y, ν y * pvar μ (fun x => F x y) := by
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [pvar_eq_pairs hμ, mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun x' _ => by ring

/-- The product weights `μ ⊗ ν` on `X × Y`. -/
def prodWeight (μ : X → ℝ) (ν : Y → ℝ) (p : X × Y) : ℝ := μ p.1 * ν p.2

/-- **Law of total variance** for product weights. -/
theorem pvar_prod_eq (μ : X → ℝ) (ν : Y → ℝ) (F : X × Y → ℝ) :
    pvar (prodWeight μ ν) F =
      ∑ y, ν y * pvar μ (fun x => F (x, y)) + pvar ν (fun y => ∑ x, μ x * F (x, y)) := by
  simp only [pvar, prodWeight, Fintype.sum_prod_type]
  have h1 : ∑ x, ∑ y, μ x * ν y * F (x, y) ^ 2 = ∑ y, ν y * ∑ x, μ x * F (x, y) ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun y _ => by
      rw [mul_sum]; exact sum_congr rfl (fun x _ => by ring)
  have h2 : ∑ x, ∑ y, μ x * ν y * F (x, y) = ∑ y, ν y * ∑ x, μ x * F (x, y) := by
    rw [sum_comm]
    exact sum_congr rfl fun y _ => by
      rw [mul_sum]; exact sum_congr rfl (fun x _ => by ring)
  rw [h1, h2]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- **Two-factor Efron–Stein.** -/
theorem pvar_prod_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ : ∑ x, μ x = 1) {ν : Y → ℝ}
    (hν0 : ∀ y, 0 ≤ ν y) (hν : ∑ y, ν y = 1) (F : X × Y → ℝ) :
    pvar (prodWeight μ ν) F ≤
      ∑ y, ν y * pvar μ (fun x => F (x, y)) + ∑ x, μ x * pvar ν (fun y => F (x, y)) := by
  rw [pvar_prod_eq μ ν]
  have := pvar_avg_le hν0 hν hμ0 hμ (fun y x => F (x, y))
  linarith

/-- **The Künneth step for spectral gaps.** Poincaré inequalities with constant `λ` on two factors
give the Poincaré inequality with constant `λ` on the product, for the summed Dirichlet form. -/
theorem gap_prod_ge {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ : ∑ x, μ x = 1) {ν : Y → ℝ}
    (hν0 : ∀ y, 0 ≤ ν y) (hν : ∑ y, ν y = 1) {E₁ : (X → ℝ) → ℝ} {E₂ : (Y → ℝ) → ℝ} {lam : ℝ}
    (hlam : 0 ≤ lam) (h₁ : ∀ f, lam * pvar μ f ≤ E₁ f) (h₂ : ∀ g, lam * pvar ν g ≤ E₂ g)
    (F : X × Y → ℝ) :
    lam * pvar (prodWeight μ ν) F ≤
      ∑ y, ν y * E₁ (fun x => F (x, y)) + ∑ x, μ x * E₂ (fun y => F (x, y)) := by
  have hES := pvar_prod_le hμ0 hμ hν0 hν F
  have hA : ∑ y, ν y * (lam * pvar μ fun x => F (x, y)) ≤ ∑ y, ν y * E₁ fun x => F (x, y) :=
    sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h₁ _) (hν0 y)
  have hB : ∑ x, μ x * (lam * pvar ν fun y => F (x, y)) ≤ ∑ x, μ x * E₂ fun y => F (x, y) :=
    sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h₂ _) (hμ0 x)
  have hA' : ∑ y, ν y * (lam * pvar μ fun x => F (x, y)) =
      lam * ∑ y, ν y * pvar μ fun x => F (x, y) := by
    rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  have hB' : ∑ x, μ x * (lam * pvar ν fun y => F (x, y)) =
      lam * ∑ x, μ x * pvar ν fun y => F (x, y) := by
    rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
  nlinarith [mul_le_mul_of_nonneg_left hES hlam]

/-- **The gap of a product is at most the gap of each factor**: functions of one coordinate keep
their variance and their energy, when the other Dirichlet form vanishes on constants. -/
theorem pvar_prod_comp_fst {μ : X → ℝ} {ν : Y → ℝ} (hν : ∑ y, ν y = 1) (f : X → ℝ) :
    pvar (prodWeight μ ν) (fun p => f p.1) = pvar μ f := by
  rw [pvar_prod_eq μ ν]
  simp only [pvar, ← sum_mul, hν, one_mul]
  ring_nf

end Variance

/-! ### The gap of one tower -/

section Tower

variable {A : ℕ}

/-- The truncated geometric normalization `Z = Σ_{a ≤ A} r^a`. -/
def towerMass (r : ℝ) (A : ℕ) : ℝ := ∑ a : Fin (A + 1), r ^ (a : ℕ)

/-- The tower weights `π(a) = r^a/Z` on `0 ≤ a ≤ A`. -/
def towerWeight (r : ℝ) (A : ℕ) (a : Fin (A + 1)) : ℝ := r ^ (a : ℕ) / towerMass r A

/-- The tower energy `Σ_{a<b} ℓ π(b) (f(b) − f(a))²`: the edge `(a, b)` has weight `ℓ r^{b−a}`
against the vertex mass `π(a)`, and `π(a) r^{b−a} = π(b)`. -/
def towerEnergy (ℓ r : ℝ) (A : ℕ) (f : Fin (A + 1) → ℝ) : ℝ :=
  ∑ a, ∑ b, if a < b then ℓ * towerWeight r A b * (f b - f a) ^ 2 else 0

theorem towerMass_pos {r : ℝ} (hr : 0 < r) (A : ℕ) : 0 < towerMass r A :=
  sum_pos (fun _ _ => pow_pos hr _) univ_nonempty

theorem sum_towerWeight {r : ℝ} (hr : 0 < r) (A : ℕ) : ∑ a, towerWeight r A a = 1 := by
  simp only [towerWeight, ← sum_div]
  exact div_self (towerMass_pos hr A).ne'

theorem towerWeight_nonneg {r : ℝ} (hr : 0 < r) (a : Fin (A + 1)) : 0 ≤ towerWeight r A a :=
  div_nonneg (pow_pos hr _).le (towerMass_pos hr A).le

/-- A symmetric pair sum with zero diagonal is twice its strictly ordered half. -/
theorem sum_sum_symm_eq_two_mul {n : ℕ} (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a)
    (hd : ∀ a, g a a = 0) :
    ∑ a, ∑ b, g a b = 2 * ∑ a, ∑ b, if a < b then g a b else 0 := by
  have hsplit : ∀ a b, g a b = (if a < b then g a b else 0) + (if b < a then g a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · rw [if_neg (lt_irrefl a), add_zero, hd]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  have hswap : ∑ a, ∑ b, (if b < a then g a b else 0) = ∑ a, ∑ b, if a < b then g a b else 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [hg]
  calc ∑ a, ∑ b, g a b
      = ∑ a, ∑ b, ((if a < b then g a b else 0) + (if b < a then g a b else 0)) :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => hsplit a b
    _ = _ := by simp only [sum_add_distrib, hswap]; ring

/-- **The gap of a tower.** For `0 < r ≤ 1` and `ℓ ≥ 0`, the tower energy dominates `ℓ Z` times the
variance, term by term. -/
theorem towerEnergy_ge {ℓ r : ℝ} (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hr1 : r ≤ 1) (f : Fin (A + 1) → ℝ) :
    ℓ * towerMass r A * pvar (towerWeight r A) f ≤ towerEnergy ℓ r A f := by
  have hL : ℓ * towerMass r A * pvar (towerWeight r A) f = ∑ a, ∑ b, if a < b then
      ℓ * towerMass r A * (towerWeight r A a * towerWeight r A b * (f a - f b) ^ 2) else 0 := by
    rw [pvar_eq_pairs (sum_towerWeight hr A),
      sum_sum_symm_eq_two_mul (fun a b => towerWeight r A a * towerWeight r A b * (f a - f b) ^ 2)
        (fun a b => by ring) (fun _ => by ring)]
    rw [show ∀ S : ℝ, ℓ * towerMass r A * (1 / 2 * (2 * S)) = ℓ * towerMass r A * S from
      fun S => by ring, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [hL, towerEnergy]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  split_ifs with hab
  · -- `ℓ Z π(a) π(b) = ℓ r^a π(b) ≤ ℓ π(b)`.
    have hZ := (towerMass_pos hr A).ne'
    have hπa : towerMass r A * towerWeight r A a = r ^ (a : ℕ) := by
      rw [towerWeight]; field_simp
    have hra : r ^ (a : ℕ) ≤ 1 := pow_le_one₀ hr.le hr1
    have hπb := towerWeight_nonneg (A := A) hr b
    have hsq : (f a - f b) ^ 2 = (f b - f a) ^ 2 := by ring
    calc ℓ * towerMass r A * (towerWeight r A a * towerWeight r A b * (f a - f b) ^ 2)
        = ℓ * (towerMass r A * towerWeight r A a) * towerWeight r A b * (f b - f a) ^ 2 := by
          rw [hsq]; ring
      _ ≤ ℓ * 1 * towerWeight r A b * (f b - f a) ^ 2 := by
          rw [hπa]; gcongr
      _ = ℓ * towerWeight r A b * (f b - f a) ^ 2 := by ring
  · exact le_rfl

/-- The valuation step `1_{a ≥ 1}`. -/
def valuationStep (a : Fin (A + 1)) : ℝ := if (a : ℕ) = 0 then 0 else 1

/-- **The valuation step attains the tower gap**: its energy is exactly `ℓ Z` times its variance. -/
theorem towerEnergy_valuationStep {ℓ r : ℝ} (hr : 0 < r) :
    towerEnergy ℓ r A valuationStep = ℓ * towerMass r A * pvar (towerWeight r A) valuationStep := by
  have hsum := sum_towerWeight hr A
  rw [Fin.sum_univ_succ] at hsum
  have h0 : towerWeight r A 0 * towerMass r A = 1 := by
    have := towerMass_pos hr A
    simp only [towerWeight, Fin.val_zero, pow_zero]; field_simp
  have hs0 : valuationStep (0 : Fin (A + 1)) = 0 := by simp [valuationStep]
  have hs1 : ∀ i : Fin A, valuationStep i.succ = 1 := fun i => by
    simp [valuationStep, Fin.val_succ]
  -- Only the pairs `(0, b)`, `b ≥ 1`, carry energy.
  have hE : towerEnergy ℓ r A valuationStep = ℓ * ∑ i : Fin A, towerWeight r A i.succ := by
    rw [towerEnergy, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hrest : ∑ i : Fin A, ∑ b : Fin (A + 1), (if i.succ < b then
        ℓ * towerWeight r A b * (valuationStep b - valuationStep i.succ) ^ 2 else 0) = 0 := by
      refine sum_eq_zero fun i _ => sum_eq_zero fun b _ => ?_
      split_ifs with hib
      · have hb : b ≠ 0 := fun h => by rw [h] at hib; exact absurd hib (Fin.not_lt_zero _)
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hb
        rw [hs1, hs1]; ring
      · rfl
    rw [hrest, add_zero, if_neg (lt_irrefl 0), zero_add, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [if_pos (Fin.succ_pos i), hs1, hs0]
    ring
  have hV : pvar (towerWeight r A) valuationStep =
      towerWeight r A 0 * ∑ i : Fin A, towerWeight r A i.succ := by
    rw [pvar, Fin.sum_univ_succ, Fin.sum_univ_succ, hs0]
    simp only [hs1, one_pow, mul_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    have hrest : ∑ i : Fin A, towerWeight r A i.succ = 1 - towerWeight r A 0 := by linarith
    linear_combination (-(∑ i : Fin A, towerWeight r A i.succ)) * hrest
  rw [hE, hV]
  have hrest : ∑ i : Fin A, towerWeight r A i.succ = 1 - towerWeight r A 0 := by linarith
  rw [hrest]
  have : ℓ * towerMass r A * (towerWeight r A 0 * (1 - towerWeight r A 0)) =
      ℓ * (towerWeight r A 0 * towerMass r A) * (1 - towerWeight r A 0) := by ring
  rw [this, h0]
  ring

end Tower

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
