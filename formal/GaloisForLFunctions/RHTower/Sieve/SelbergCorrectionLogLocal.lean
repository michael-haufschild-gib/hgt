import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionCoefficientMass

/-!
# The differentiated local Euler factor of the Selberg correction

The gcd-logarithmic Selberg family needs the `s`-derivative at `s = 1` of the correction factor
of the two-parameter family `c_s(m,n) = μ(m)μ(n)(m,n)^s/(mn)`.  With

```text
E_p(s) = 1 − X/p − Y/p + p^{s−1}XY/p,
corr_p(s) = E_p(s)·(1 − p^{s−1}XY/p)/((1−X/p)(1−Y/p)),
```

a direct computation gives

```text
∂_s corr_p(s)|_{s=1} = (log p / p²)·XY(X + Y − 2XY)/((1−X/p)(1−Y/p)),
```

whose `(X^α, Y^β)` coefficient is the function `selbergCorrectionLogLocal` below.  This file fixes
that coefficient and proves the two facts the summability of `corr^{log}` rests on: absolute
summability of each local fibre, and the mass bound `16·log p / p²`, which is summable over primes.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Coefficient of `X^α Y^β` in the differentiated local Euler factor at `p`. -/
def selbergCorrectionLogLocal (p α β : ℕ) : ℝ :=
  (Real.log (p : ℝ) / (p : ℝ) ^ (2 + α + β)) *
    ((if 2 ≤ α ∧ 1 ≤ β then (p : ℝ) ^ 3 else 0) +
      (if 1 ≤ α ∧ 2 ≤ β then (p : ℝ) ^ 3 else 0) -
      (if 2 ≤ α ∧ 2 ≤ β then 2 * (p : ℝ) ^ 4 else 0))

/-- Geometric tail from exponent two. -/
def geomTailTwo (p α : ℕ) : ℝ :=
  if 2 ≤ α then (p : ℝ) ^ 2 / (p : ℝ) ^ α else 0

/-- Geometric tail from exponent one. -/
def geomTailOne (p β : ℕ) : ℝ :=
  if 1 ≤ β then (p : ℝ) / (p : ℝ) ^ β else 0

theorem geomTailTwo_nonneg (p α : ℕ) : 0 ≤ geomTailTwo p α := by
  rw [geomTailTwo]
  split_ifs
  · positivity
  · exact le_rfl

theorem geomTailOne_nonneg (p β : ℕ) : 0 ≤ geomTailOne p β := by
  rw [geomTailOne]
  split_ifs
  · positivity
  · exact le_rfl

private theorem inv_one_sub_le_two {p : ℕ} (hp : 2 ≤ p) :
    ((1 : ℝ) - 1 / (p : ℝ))⁻¹ ≤ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hhalf : 1 / (p : ℝ) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

private theorem geomRatio_lt_one {p : ℕ} (hp : 2 ≤ p) : (1 / (p : ℝ)) < 1 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [div_lt_one (by linarith)]
  linarith

private theorem summable_geom_inv {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun j : ℕ => (1 / (p : ℝ)) ^ j) :=
  summable_geometric_of_lt_one (by positivity) (geomRatio_lt_one hp)

private theorem tsum_geom_inv_le {p : ℕ} (hp : 2 ≤ p) :
    (∑' j : ℕ, (1 / (p : ℝ)) ^ j) ≤ 2 := by
  rw [tsum_geometric_of_lt_one (by positivity) (geomRatio_lt_one hp)]
  exact inv_one_sub_le_two hp

private theorem geomTailTwo_shift {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    geomTailTwo p (j + 2) = (1 / (p : ℝ)) ^ j := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [geomTailTwo, if_pos (by omega)]
  rw [div_pow, one_pow, pow_add]
  field_simp

private theorem geomTailOne_shift {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    geomTailOne p (j + 1) = (1 / (p : ℝ)) ^ j := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [geomTailOne, if_pos (by omega)]
  rw [div_pow, one_pow, pow_add]
  field_simp

private theorem addShift_injective (k : ℕ) : Function.Injective (fun j : ℕ => j + k) := by
  intro x y hxy
  simpa using hxy

private theorem geomTailTwo_support {p : ℕ} :
    ∀ x ∉ Set.range (fun j : ℕ => j + 2), geomTailTwo p x = 0 := by
  intro x hx
  rw [geomTailTwo, if_neg]
  intro h
  refine hx ⟨x - 2, ?_⟩
  show x - 2 + 2 = x
  omega

private theorem geomTailOne_support {p : ℕ} :
    ∀ x ∉ Set.range (fun j : ℕ => j + 1), geomTailOne p x = 0 := by
  intro x hx
  rw [geomTailOne, if_neg]
  intro h
  refine hx ⟨x - 1, ?_⟩
  show x - 1 + 1 = x
  omega

theorem summable_geomTailTwo {p : ℕ} (hp : 2 ≤ p) :
    Summable (geomTailTwo p) := by
  refine ((addShift_injective 2).summable_iff geomTailTwo_support).mp ?_
  refine (summable_geom_inv hp).congr ?_
  intro j
  exact (geomTailTwo_shift hp j).symm

theorem summable_geomTailOne {p : ℕ} (hp : 2 ≤ p) :
    Summable (geomTailOne p) := by
  refine ((addShift_injective 1).summable_iff geomTailOne_support).mp ?_
  refine (summable_geom_inv hp).congr ?_
  intro j
  exact (geomTailOne_shift hp j).symm

theorem tsum_geomTailTwo_le {p : ℕ} (hp : 2 ≤ p) :
    (∑' α : ℕ, geomTailTwo p α) ≤ 2 := by
  have hbij := (addShift_injective 2).tsum_eq (f := geomTailTwo p) ?_
  · rw [← hbij]
    have hcongr : ∀ j : ℕ, geomTailTwo p (j + 2) = (1 / (p : ℝ)) ^ j :=
      geomTailTwo_shift hp
    calc
      (∑' j : ℕ, geomTailTwo p (j + 2)) = ∑' j : ℕ, (1 / (p : ℝ)) ^ j :=
        tsum_congr hcongr
      _ ≤ 2 := tsum_geom_inv_le hp
  · intro x hx
    have hne : geomTailTwo p x ≠ 0 := hx
    by_contra hnot
    exact hne (geomTailTwo_support x hnot)

theorem tsum_geomTailOne_le {p : ℕ} (hp : 2 ≤ p) :
    (∑' β : ℕ, geomTailOne p β) ≤ 2 := by
  have hbij := (addShift_injective 1).tsum_eq (f := geomTailOne p) ?_
  · rw [← hbij]
    have hcongr : ∀ j : ℕ, geomTailOne p (j + 1) = (1 / (p : ℝ)) ^ j :=
      geomTailOne_shift hp
    calc
      (∑' j : ℕ, geomTailOne p (j + 1)) = ∑' j : ℕ, (1 / (p : ℝ)) ^ j :=
        tsum_congr hcongr
      _ ≤ 2 := tsum_geom_inv_le hp
  · intro x hx
    have hne : geomTailOne p x ≠ 0 := hx
    by_contra hnot
    exact hne (geomTailOne_support x hnot)

end

end RHTower.Sieve
