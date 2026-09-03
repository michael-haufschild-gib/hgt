import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamare
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# Exact geometric schedule for Menon's final prime range

The distinguished final range is divided into the paper's `H`-adic blocks with
`H = (log X)^10`.  The natural depth is the ceiling of the exact logarithmic endpoint ratio.
This file proves literal coverage and both cofactor-endpoint conditions used by the harmonic
Ramaré ladder.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- Fixed polylogarithmic resolution for Menon's final-range Ramaré ladder. -/
def menonFinalRangeLadderH (x : ℝ) : ℝ := (Real.log x) ^ (10 : ℕ)

/-- Multiplicative increment `exp(1/H) - 1`. -/
def menonFinalRangeLadderEta (x : ℝ) : ℝ :=
  Real.exp (1 / menonFinalRangeLadderH x) - 1

/-- Exact real lower endpoint of the final-range ladder. -/
def menonFinalRangeLadderBase (x : ℝ) : ℝ :=
  (menonFinalRangePrimeCutoffNat x : ℝ)

/-- First natural depth whose geometric endpoint reaches the literal natural top. -/
def menonFinalRangeLadderSteps (x : ℝ) : ℕ :=
  ⌈menonFinalRangeLadderH x *
      Real.log ((menonFinalRangeTopNat x : ℝ) / menonFinalRangeLadderBase x)⌉₊

theorem one_add_menonFinalRangeLadderEta (x : ℝ) :
    1 + menonFinalRangeLadderEta x = Real.exp (1 / menonFinalRangeLadderH x) := by
  rw [menonFinalRangeLadderEta]
  ring

theorem menonFinalRangeLadderBase_pos {x : ℝ}
    (hQ : 1 < menonFinalRangeLadderBase x) :
    0 < menonFinalRangeLadderBase x := by
  linarith

theorem menonFinalRangeLadderEta_nonneg {x : ℝ}
    (hH : 0 < menonFinalRangeLadderH x) :
    0 ≤ menonFinalRangeLadderEta x := by
  rw [menonFinalRangeLadderEta]
  exact sub_nonneg.mpr (Real.one_le_exp (by positivity))

theorem menonFinalRangeLadder_pow_eq_exp {x : ℝ}
    (j : ℕ) :
    (1 + menonFinalRangeLadderEta x) ^ j =
      Real.exp ((j : ℝ) / menonFinalRangeLadderH x) := by
  rw [one_add_menonFinalRangeLadderEta]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem geometric_ceil_depth_pos
    {H Q B : ℝ} (hH : 0 < H) (hQ : 0 < Q) (hQB : Q < B) :
    1 ≤ ⌈H * Real.log (B / Q)⌉₊ := by
  rw [Nat.one_le_ceil_iff]
  exact mul_pos hH (Real.log_pos (by rwa [one_lt_div hQ]))

private theorem geometric_ceil_depth_cover
    {H Q B : ℝ} (hH : 0 < H) (hQ : 0 < Q) (hQB : Q < B) :
    B ≤ Q * Real.exp ((⌈H * Real.log (B / Q)⌉₊ : ℝ) / H) := by
  have hratio : 0 < B / Q := div_pos (lt_trans hQ hQB) hQ
  have hceil : H * Real.log (B / Q) ≤ (⌈H * Real.log (B / Q)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hlog : Real.log (B / Q) ≤ (⌈H * Real.log (B / Q)⌉₊ : ℝ) / H := by
    rw [le_div_iff₀ hH]
    simpa [mul_comm] using hceil
  have hexp : Real.exp (Real.log (B / Q)) ≤
      Real.exp ((⌈H * Real.log (B / Q)⌉₊ : ℝ) / H) :=
    Real.exp_le_exp.2 hlog
  calc
    B = Q * Real.exp (Real.log (B / Q)) := by
      rw [Real.exp_log hratio]
      field_simp
    _ ≤ Q * Real.exp ((⌈H * Real.log (B / Q)⌉₊ : ℝ) / H) :=
      mul_le_mul_of_nonneg_left hexp hQ.le

private theorem geometric_before_ceil_depth_lt
    {H Q B : ℝ} (hH : 0 < H) (hQ : 0 < Q) (hQB : Q < B)
    {j : ℕ} (hj : j < ⌈H * Real.log (B / Q)⌉₊) :
    Q * Real.exp ((j : ℝ) / H) < B := by
  have hratio : 0 < B / Q := div_pos (lt_trans hQ hQB) hQ
  have hjreal : (j : ℝ) < H * Real.log (B / Q) := Nat.lt_ceil.mp hj
  have hdiv : (j : ℝ) / H < Real.log (B / Q) := by
    rw [div_lt_iff₀ hH]
    simpa [mul_comm] using hjreal
  have hexp : Real.exp ((j : ℝ) / H) < Real.exp (Real.log (B / Q)) :=
    Real.exp_lt_exp.2 hdiv
  rw [Real.exp_log hratio] at hexp
  have := mul_lt_mul_of_pos_left hexp hQ
  calc
    Q * Real.exp ((j : ℝ) / H) < Q * (B / Q) := this
    _ = B := by field_simp

/-- Eventually the paper schedule has positive resolution, nonnegative increment, nonzero depth,
and its base lies strictly between one and the literal final endpoint. -/
theorem eventually_menonFinalRangeLadder_basic :
    ∀ᶠ x : ℝ in atTop,
      1 < x ∧
      0 < menonFinalRangeLadderH x ∧
      1 < menonFinalRangeLadderBase x ∧
      menonFinalRangeLadderBase x < (menonFinalRangeTopNat x : ℝ) ∧
      0 ≤ menonFinalRangeLadderEta x ∧
      1 ≤ menonFinalRangeLadderSteps x := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonFinalRangePrimeCutoff_le_x] with x hx hQtwo hcut
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hH : 0 < menonFinalRangeLadderH x := by
    rw [menonFinalRangeLadderH]
    positivity
  have hQ : 1 < menonFinalRangeLadderBase x := by
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hQtwo
  have hQcut : menonFinalRangeLadderBase x ≤ menonFinalRangePrimeCutoff x := by
    rw [menonFinalRangeLadderBase, menonFinalRangePrimeCutoffNat]
    exact Nat.floor_le (menonFinalRangePrimeCutoff_pos x).le
  have hQx : menonFinalRangeLadderBase x ≤ x := hQcut.trans hcut
  have htop : menonFinalRangeLadderBase x < (menonFinalRangeTopNat x : ℝ) := by
    have hnat : menonFinalRangePrimeCutoffNat x + 1 ≤ menonFinalRangeTopNat x := by
      rw [menonFinalRangeTopNat]
      apply Nat.le_floor
      rw [Nat.cast_add, Nat.cast_one]
      simpa only [menonFinalRangeLadderBase] using (by linarith :
        menonFinalRangeLadderBase x + 1 ≤ 3 * x)
    rw [menonFinalRangeLadderBase]
    exact_mod_cast (Nat.lt_of_succ_le hnat)
  have heta := menonFinalRangeLadderEta_nonneg hH
  have hL : 1 ≤ menonFinalRangeLadderSteps x := by
    rw [menonFinalRangeLadderSteps]
    exact geometric_ceil_depth_pos hH (menonFinalRangeLadderBase_pos hQ) htop
  exact ⟨hx, hH, hQ, htop, heta, hL⟩

/-- Literal final-range primes are covered by the exact `H`-adic ladder. -/
theorem eventually_menonFinalRangePrimes_ladder_range :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ menonFinalRangePrimes x,
      menonFinalRangeLadderBase x < (p : ℝ) ∧
      (p : ℝ) ≤ menonFinalRangeLadderBase x *
        (1 + menonFinalRangeLadderEta x) ^ menonFinalRangeLadderSteps x := by
  filter_upwards [eventually_menonFinalRangeLadder_basic] with x hx p hp
  rcases hx with ⟨_, hH, hQ, htop, _, _⟩
  have hpRange := mem_primesRange.1 hp
  have hpLower : menonFinalRangeLadderBase x < (p : ℝ) := by
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hpRange.2.1
  have hcover := geometric_ceil_depth_cover hH (menonFinalRangeLadderBase_pos hQ) htop
  rw [← menonFinalRangeLadder_pow_eq_exp] at hcover
  have hpTop : (p : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) := by
    exact_mod_cast hpRange.2.2
  exact ⟨hpLower, hpTop.trans hcover⟩

/-- Every retained ladder step has nonempty natural cofactor endpoints on Menon's literal shell. -/
theorem eventually_menonFinalRangeLadder_cofactor_endpoints :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
      1 ≤ ⌈(⌈x⌉₊ : ℝ) /
        ((menonFinalRangeLadderBase x *
            (1 + menonFinalRangeLadderEta x) ^ j) *
          (1 + menonFinalRangeLadderEta x))⌉₊ ∧
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) /
        (menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ j)⌋₊ := by
  filter_upwards [eventually_menonFinalRangeLadder_basic] with x hx j hj
  rcases hx with ⟨hxone, hH, hQ, htop, _, _⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have hstep0 : 0 < 1 + menonFinalRangeLadderEta x := by
    rw [one_add_menonFinalRangeLadderEta]
    positivity
  have hden0 : 0 < menonFinalRangeLadderBase x *
      (1 + menonFinalRangeLadderEta x) ^ j := mul_pos hbase0 (pow_pos hstep0 _)
  constructor
  · rw [Nat.one_le_ceil_iff]
    exact div_pos (by
      exact_mod_cast (Nat.one_le_ceil_iff.2 (by linarith : 0 < x)))
      (mul_pos hden0 hstep0)
  · apply Nat.le_floor
    have hjlt : j < menonFinalRangeLadderSteps x := Finset.mem_range.1 hj
    have hprev := geometric_before_ceil_depth_lt hH hbase0 htop hjlt
    rw [← menonFinalRangeLadder_pow_eq_exp] at hprev
    rw [le_div_iff₀ hden0]
    simpa using hprev.le

end

end RHTower.Sieve
