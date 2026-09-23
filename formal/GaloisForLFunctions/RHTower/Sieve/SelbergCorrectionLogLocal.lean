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
    ((if 2 ≤ α ∧ 1 ≤ β then (p : ℝ) ^ (3 : ℕ) else 0) +
      (if 1 ≤ α ∧ 2 ≤ β then (p : ℝ) ^ (3 : ℕ) else 0) -
      (if 2 ≤ α ∧ 2 ≤ β then 2 * (p : ℝ) ^ (4 : ℕ) else 0))

/-- Geometric tail from exponent two. -/
def geomTailTwo (p α : ℕ) : ℝ :=
  if 2 ≤ α then (p : ℝ) ^ (2 : ℕ) / (p : ℝ) ^ α else 0

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

/-- The explicit majorant of the differentiated local factor. -/
def selbergCorrectionLogMajorant (p α β : ℕ) : ℝ :=
  (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
    (geomTailTwo p α * geomTailOne p β + geomTailOne p α * geomTailTwo p β +
      2 * (geomTailTwo p α * geomTailTwo p β))

/-- **Exact product form of the differentiated local factor.** -/
theorem selbergCorrectionLogLocal_eq_geomTails {p : ℕ} (hp : 0 < p) (α β : ℕ) :
    selbergCorrectionLogLocal p α β =
      Real.log (p : ℝ) *
        ((1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailTwo p α * geomTailOne p β) +
          (1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailOne p α * geomTailTwo p β) -
          (1 / (p : ℝ) ^ (2 : ℕ)) * (2 * (geomTailTwo p α * geomTailTwo p β))) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hA : (if 2 ≤ α ∧ 1 ≤ β then (p : ℝ) ^ (3 : ℕ) else 0) / (p : ℝ) ^ (2 + α + β) =
      (1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailTwo p α * geomTailOne p β) := by
    rw [geomTailTwo, geomTailOne]
    by_cases hab : 2 ≤ α ∧ 1 ≤ β
    · rw [if_pos hab, if_pos hab.1, if_pos hab.2]
      field_simp
      ring
    · rw [if_neg hab]
      rcases not_and_or.mp hab with h | h
      · rw [if_neg h]; simp
      · rw [if_neg h]; simp
  have hB : (if 1 ≤ α ∧ 2 ≤ β then (p : ℝ) ^ (3 : ℕ) else 0) / (p : ℝ) ^ (2 + α + β) =
      (1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailOne p α * geomTailTwo p β) := by
    rw [geomTailTwo, geomTailOne]
    by_cases hab : 1 ≤ α ∧ 2 ≤ β
    · rw [if_pos hab, if_pos hab.1, if_pos hab.2]
      field_simp
      ring
    · rw [if_neg hab]
      rcases not_and_or.mp hab with h | h
      · rw [if_neg h]; simp
      · rw [if_neg h]; simp
  have hC : (if 2 ≤ α ∧ 2 ≤ β then 2 * (p : ℝ) ^ (4 : ℕ) else 0) / (p : ℝ) ^ (2 + α + β) =
      (1 / (p : ℝ) ^ (2 : ℕ)) * (2 * (geomTailTwo p α * geomTailTwo p β)) := by
    simp only [geomTailTwo]
    by_cases hab : 2 ≤ α ∧ 2 ≤ β
    · rw [if_pos hab, if_pos hab.1, if_pos hab.2]
      field_simp
      ring
    · rw [if_neg hab]
      rcases not_and_or.mp hab with h | h
      · rw [if_neg h]; simp
      · rw [if_neg h]; simp
  rw [selbergCorrectionLogLocal, ← hA, ← hB, ← hC]
  field_simp

/-- **The differentiated local factor is dominated termwise by the explicit majorant.** -/
theorem abs_selbergCorrectionLogLocal_le {p : ℕ} (hp : 2 ≤ p) (α β : ℕ) :
    |selbergCorrectionLogLocal p α β| ≤ selbergCorrectionLogMajorant p α β := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hlogp : 0 ≤ Real.log (p : ℝ) := by
    refine Real.log_nonneg ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [selbergCorrectionLogLocal_eq_geomTails (by omega) α β,
    selbergCorrectionLogMajorant, abs_mul, abs_of_nonneg hlogp]
  have hnn1 : 0 ≤ geomTailTwo p α * geomTailOne p β :=
    mul_nonneg (geomTailTwo_nonneg p α) (geomTailOne_nonneg p β)
  have hnn2 : 0 ≤ geomTailOne p α * geomTailTwo p β :=
    mul_nonneg (geomTailOne_nonneg p α) (geomTailTwo_nonneg p β)
  have hnn3 : 0 ≤ geomTailTwo p α * geomTailTwo p β :=
    mul_nonneg (geomTailTwo_nonneg p α) (geomTailTwo_nonneg p β)
  have hinv : (0 : ℝ) < 1 / (p : ℝ) ^ (2 : ℕ) := by positivity
  have hbound : |(1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailTwo p α * geomTailOne p β) +
      (1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailOne p α * geomTailTwo p β) -
      (1 / (p : ℝ) ^ (2 : ℕ)) * (2 * (geomTailTwo p α * geomTailTwo p β))| ≤
      (1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailTwo p α * geomTailOne p β +
        geomTailOne p α * geomTailTwo p β +
        2 * (geomTailTwo p α * geomTailTwo p β)) := by
    rw [abs_le]
    constructor <;> nlinarith [hnn1, hnn2, hnn3, hinv]
  calc
    Real.log (p : ℝ) * |(1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailTwo p α * geomTailOne p β) +
        (1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailOne p α * geomTailTwo p β) -
        (1 / (p : ℝ) ^ (2 : ℕ)) * (2 * (geomTailTwo p α * geomTailTwo p β))|
        ≤ Real.log (p : ℝ) * ((1 / (p : ℝ) ^ (2 : ℕ)) * (geomTailTwo p α * geomTailOne p β +
            geomTailOne p α * geomTailTwo p β +
            2 * (geomTailTwo p α * geomTailTwo p β))) :=
      mul_le_mul_of_nonneg_left hbound hlogp
    _ = Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) *
        (geomTailTwo p α * geomTailOne p β + geomTailOne p α * geomTailTwo p β +
          2 * (geomTailTwo p α * geomTailTwo p β)) := by ring

private theorem summable_pair_TwoOne {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => geomTailTwo p ab.1 * geomTailOne p ab.2) :=
  (summable_geomTailTwo hp).mul_of_nonneg (summable_geomTailOne hp)
    (fun i => geomTailTwo_nonneg p i) (fun i => geomTailOne_nonneg p i)

private theorem summable_pair_OneTwo {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => geomTailOne p ab.1 * geomTailTwo p ab.2) :=
  (summable_geomTailOne hp).mul_of_nonneg (summable_geomTailTwo hp)
    (fun i => geomTailOne_nonneg p i) (fun i => geomTailTwo_nonneg p i)

private theorem summable_pair_TwoTwo {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => geomTailTwo p ab.1 * geomTailTwo p ab.2) :=
  (summable_geomTailTwo hp).mul_of_nonneg (summable_geomTailTwo hp)
    (fun i => geomTailTwo_nonneg p i) (fun i => geomTailTwo_nonneg p i)

theorem selbergCorrectionLogMajorant_nonneg {p : ℕ} (hp : 2 ≤ p) (α β : ℕ) :
    0 ≤ selbergCorrectionLogMajorant p α β := by
  have hlogp : 0 ≤ Real.log (p : ℝ) := by
    refine Real.log_nonneg ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [selbergCorrectionLogMajorant]
  have h1 := mul_nonneg (geomTailTwo_nonneg p α) (geomTailOne_nonneg p β)
  have h2 := mul_nonneg (geomTailOne_nonneg p α) (geomTailTwo_nonneg p β)
  have h3 := mul_nonneg (geomTailTwo_nonneg p α) (geomTailTwo_nonneg p β)
  have hc : 0 ≤ Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) := by positivity
  nlinarith [h1, h2, h3, hc]

theorem summable_selbergCorrectionLogMajorant {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => selbergCorrectionLogMajorant p ab.1 ab.2) := by
  have h := (((summable_pair_TwoOne hp).add (summable_pair_OneTwo hp)).add
    ((summable_pair_TwoTwo hp).mul_left 2)).mul_left
      (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ))
  refine h.congr ?_
  intro ab
  rw [selbergCorrectionLogMajorant]

/-- **The differentiated local factor has `ℓ¹` mass at most `16 log p / p²`.** -/
theorem tsum_selbergCorrectionLogMajorant_le {p : ℕ} (hp : 2 ≤ p) :
    (∑' ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2) ≤
      16 * Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) := by
  have hlogp : 0 ≤ Real.log (p : ℝ) := by
    refine Real.log_nonneg ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hc : 0 ≤ Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) := by positivity
  have hTO : (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) ≤ 4 := by
    rw [← (summable_geomTailTwo hp).tsum_mul_tsum (summable_geomTailOne hp)
      (summable_pair_TwoOne hp)]
    have h1 := tsum_geomTailTwo_le hp
    have h2 := tsum_geomTailOne_le hp
    have hnn1 : 0 ≤ ∑' α : ℕ, geomTailTwo p α :=
      tsum_nonneg fun α => geomTailTwo_nonneg p α
    have hnn2 : 0 ≤ ∑' β : ℕ, geomTailOne p β :=
      tsum_nonneg fun β => geomTailOne_nonneg p β
    nlinarith [h1, h2, hnn1, hnn2]
  have hOT : (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) ≤ 4 := by
    rw [← (summable_geomTailOne hp).tsum_mul_tsum (summable_geomTailTwo hp)
      (summable_pair_OneTwo hp)]
    have h1 := tsum_geomTailOne_le hp
    have h2 := tsum_geomTailTwo_le hp
    have hnn1 : 0 ≤ ∑' α : ℕ, geomTailOne p α :=
      tsum_nonneg fun α => geomTailOne_nonneg p α
    have hnn2 : 0 ≤ ∑' β : ℕ, geomTailTwo p β :=
      tsum_nonneg fun β => geomTailTwo_nonneg p β
    nlinarith [h1, h2, hnn1, hnn2]
  have hTT : (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2) ≤ 4 := by
    rw [← (summable_geomTailTwo hp).tsum_mul_tsum (summable_geomTailTwo hp)
      (summable_pair_TwoTwo hp)]
    have h1 := tsum_geomTailTwo_le hp
    have hnn1 : 0 ≤ ∑' α : ℕ, geomTailTwo p α :=
      tsum_nonneg fun α => geomTailTwo_nonneg p α
    nlinarith [h1, hnn1]
  have hexpand : (∑' ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2) =
      (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
        ((∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) +
          (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) +
          2 * (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2)) := by
    calc
      (∑' ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2)
          = ∑' ab : ℕ × ℕ, (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
              (geomTailTwo p ab.1 * geomTailOne p ab.2 +
                geomTailOne p ab.1 * geomTailTwo p ab.2 +
                2 * (geomTailTwo p ab.1 * geomTailTwo p ab.2)) :=
            tsum_congr fun ab => by rw [selbergCorrectionLogMajorant]
      _ = (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
            ∑' ab : ℕ × ℕ, (geomTailTwo p ab.1 * geomTailOne p ab.2 +
              geomTailOne p ab.1 * geomTailTwo p ab.2 +
              2 * (geomTailTwo p ab.1 * geomTailTwo p ab.2)) := tsum_mul_left
      _ = _ := by
            congr 1
            rw [((summable_pair_TwoOne hp).add (summable_pair_OneTwo hp)).tsum_add
                ((summable_pair_TwoTwo hp).mul_left 2),
              (summable_pair_TwoOne hp).tsum_add (summable_pair_OneTwo hp),
              tsum_mul_left]
  rw [hexpand]
  have hsum : (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) +
      (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) +
      2 * (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2) ≤ 16 := by
    linarith [hTO, hOT, hTT]
  calc
    (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
        ((∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) +
          (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) +
          2 * (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2))
        ≤ (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) * 16 :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = 16 * Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) := by ring

/-- **Absolute summability of the differentiated local factor, with its mass bound.** -/
theorem summable_abs_selbergCorrectionLogLocal {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => |selbergCorrectionLogLocal p ab.1 ab.2|) := by
  refine Summable.of_nonneg_of_le (fun ab => abs_nonneg _) (fun ab => ?_)
    (summable_selbergCorrectionLogMajorant hp)
  exact abs_selbergCorrectionLogLocal_le hp ab.1 ab.2

theorem tsum_abs_selbergCorrectionLogLocal_le {p : ℕ} (hp : 2 ≤ p) :
    (∑' ab : ℕ × ℕ, |selbergCorrectionLogLocal p ab.1 ab.2|) ≤
      16 * Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) := by
  refine le_trans ?_ (tsum_selbergCorrectionLogMajorant_le hp)
  exact Summable.tsum_le_tsum (fun ab => abs_selbergCorrectionLogLocal_le hp ab.1 ab.2)
    (summable_abs_selbergCorrectionLogLocal hp)
    (summable_selbergCorrectionLogMajorant hp)

end

end RHTower.Sieve
