/-
# SpurMidpoint — the doc 27 §3 midpoint-push lemma `θ < 1/2` (task #143 / #138 substrate)

Doc 27 (27-drift-hierarchy.md) §3 `[PROVED HERE]`: under nondecreasing gaps and
`i ≥ (d−1)/2`, the equilibrium field is positive at the midpoint `m` of the gap
`(α_i, α_{i+1})`, so — the field being strictly decreasing on the gap — the critical point
sits in the right half: `θ_i := (α_{i+1} − c)/Δ_i < 1/2`. Flat grading: a finite-sum pairing
inequality + one antitone/IVT bridge; nothing new.

The mechanism: the two gap neighbors cancel exactly at `m`; each further-left charge (the
`j`-th, at distance `L_j = Δ_i/2 + Δ_{i−1} + … + Δ_{i−j}`) is paired with the `j`-th further
right (distance `R_j = Δ_i/2 + Δ_{i+1} + … + Δ_{i+j}`); nondecreasing gaps give `L_j ≤ R_j`
termwise, so `1/L_j ≥ 1/R_j` and each pair contributes `≥ 0`; the surplus left charges (present
when `i ≥ (d−1)/2`) each add a strictly positive `1/L`, giving `F(m) > 0`.

* `leftDist` / `rightDist` — the cumulative gap-sum distances `L_j`, `R_j`.
* `leftDist_pos` — `L_j > 0`.
* `leftDist_le_rightDist` — **nondecreasing gaps ⟹ `L_j ≤ R_j`** (the pairing domination).
* `midpoint_pairing` — the paired reciprocal field `Σ_j (1/L_j − 1/R_j) ≥ 0`.
* `midpoint_field_pos` — adding any strictly positive surplus term gives `> 0` (the `F(m) > 0`).
* `crit_gt_mid` — **the bridge**: `F(m) > 0`, `F` strictly decreasing on the gap, `F(c) = 0`
  ⟹ `c > m` (the critical point is right of the midpoint).
* `theta_lt_half` — the arithmetic close: `c > m = (a+b)/2` ⟹ `(b − c)/(b − a) < 1/2`.
-/
import Mathlib

noncomputable section

namespace RHTower

open Finset

/-- Cumulative distance from the gap midpoint to the `j`-th charge to the left:
`L_j = Δ_i/2 + Δ_{i−1} + … + Δ_{i−j}` (doc 27 §3). -/
def leftDist (Δ : ℕ → ℝ) (i j : ℕ) : ℝ := Δ i / 2 + ∑ l ∈ Finset.Icc 1 j, Δ (i - l)

/-- Cumulative distance to the `j`-th charge to the right:
`R_j = Δ_i/2 + Δ_{i+1} + … + Δ_{i+j}` (doc 27 §3). -/
def rightDist (Δ : ℕ → ℝ) (i j : ℕ) : ℝ := Δ i / 2 + ∑ l ∈ Finset.Icc 1 j, Δ (i + l)

/-- `L_j > 0` (positive gaps). -/
theorem leftDist_pos {Δ : ℕ → ℝ} (hpos : ∀ k, 0 < Δ k) (i j : ℕ) : 0 < leftDist Δ i j := by
  unfold leftDist
  have hsum : 0 ≤ ∑ l ∈ Finset.Icc 1 j, Δ (i - l) :=
    Finset.sum_nonneg fun l _ => (hpos (i - l)).le
  linarith [hpos i]

/-- **Pairing domination**: nondecreasing gaps make each left distance `≤` its right partner,
`L_j ≤ R_j` — because `i − l ≤ i + l`, so `Δ_{i−l} ≤ Δ_{i+l}` termwise (doc 27 §3). -/
theorem leftDist_le_rightDist {Δ : ℕ → ℝ} (hmono : Monotone Δ) (i j : ℕ) :
    leftDist Δ i j ≤ rightDist Δ i j := by
  unfold leftDist rightDist
  gcongr with l _
  exact hmono (by omega)

/-- **The midpoint pairing** `Σ_{j=1}^{n} (1/L_j − 1/R_j) ≥ 0` — each paired term is
nonnegative since `0 < L_j ≤ R_j` (doc 27 §3). This is the field contribution of the paired
charges at the gap midpoint. -/
theorem midpoint_pairing {Δ : ℕ → ℝ} (hmono : Monotone Δ) (hpos : ∀ k, 0 < Δ k) (i n : ℕ) :
    0 ≤ ∑ j ∈ Finset.Icc 1 n, (1 / leftDist Δ i j - 1 / rightDist Δ i j) := by
  apply Finset.sum_nonneg
  intro j _
  have hL : 0 < leftDist Δ i j := leftDist_pos hpos i j
  have hLR : leftDist Δ i j ≤ rightDist Δ i j := leftDist_le_rightDist hmono i j
  have : 1 / rightDist Δ i j ≤ 1 / leftDist Δ i j := one_div_le_one_div_of_le hL hLR
  linarith

/-- **`F(m) > 0`**: the paired field is `≥ 0` (`midpoint_pairing`) and the surplus left charges
present when `i ≥ (d−1)/2` add a strictly positive `1/L`-term, so the total midpoint field is
strictly positive (doc 27 §3). -/
theorem midpoint_field_pos {Δ : ℕ → ℝ} (hmono : Monotone Δ) (hpos : ∀ k, 0 < Δ k) (i n : ℕ)
    {surplus : ℝ} (hsurplus : 0 < surplus) :
    0 < (∑ j ∈ Finset.Icc 1 n, (1 / leftDist Δ i j - 1 / rightDist Δ i j)) + surplus := by
  have hpair := midpoint_pairing hmono hpos i n
  linarith

/-- **The bridge**: if `F` is strictly decreasing on the closed gap, vanishes at the critical
point `c`, and is positive at the midpoint `m`, then `c > m` — the critical point lies in the
right half of the gap (doc 27 §3). -/
theorem crit_gt_mid {F : ℝ → ℝ} {a b c m : ℝ} (hanti : StrictAntiOn F (Set.Icc a b))
    (hc_mem : c ∈ Set.Icc a b) (hm_mem : m ∈ Set.Icc a b) (hc : F c = 0) (hFm : 0 < F m) :
    m < c := by
  by_contra hcon
  have h : c ≤ m := not_lt.mp hcon
  have hle : F m ≤ F c := hanti.antitoneOn hc_mem hm_mem h
  rw [hc] at hle
  linarith

/-- **The `θ < 1/2` close**: with `m = (a+b)/2` the gap midpoint (`a = α_i`, `b = α_{i+1}`),
`c > m` gives `θ := (b − c)/(b − a) < 1/2` (doc 27 §3). -/
theorem theta_lt_half {a b c : ℝ} (hab : a < b) (hmc : (a + b) / 2 < c) :
    (b - c) / (b - a) < 1 / 2 := by
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

end RHTower
