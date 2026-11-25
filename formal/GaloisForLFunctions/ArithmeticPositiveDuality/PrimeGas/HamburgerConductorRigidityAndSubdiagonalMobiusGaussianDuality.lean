import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CrossHeightGaussianMechanismAndTemperedFirewallFailure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalAmplificationAndMultiPointWitnessExclusion
import GaloisForLFunctions.HTGeometry.HamburgerFunctionalEquation
import GaloisForLFunctions.StripBochnerWeilForcing.TheSimplePoleClassIsZeta
import GaloisForLFunctions.RHTower.RectangleCauchyFormulaOn
import Mathlib.NumberTheory.Bertrand

/-!
# Asymmetric Conductor-`4` Cross-Height Firewall, Arbitrary-Conductor Hamburger Rigidity Below Conductor `5`, Pure-Direct Dual-Annihilating Witnesses, and Strictly Sub-Diagonal Reflected-Möbius Duality on `Ω_open`

In `CrossHeightGaussianMechanismAndTemperedFirewallFailure`, simultaneously invoking unit-bounded
coefficients `‖a(n)‖ ≤ 1`, `‖b(m)‖ ≤ 1`, global pole-freeness across `0 < Re s < 1 / 2` (and off
`s = 1`), and cross-height functional reflection `F(z) = ω Q^{1/2 - z} zetaChi(z) G(1 - z)`
(`UnitPoleFreeCrossHeightDatum`) refutes `posTruncatedZeta` and all single-ordinate countermodels
while yielding sublinear `O(|Im s|^{1/2 + η})` two-series witnesses on the remaining strip
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}`.

This module resolves the exact structural boundary of `UnitPoleFreeCrossHeightDatum` and couples the
cross-height Gaussian mechanism with reflected Möbius inversion (`‖μ(d)‖ ≤ 1`), establishing four
unconditional theorem packages:

1. **Asymmetric conductor-`4` cross-height firewall at every point of `0 < Re s < 1 / 2`
   (`norm_asymTwinParam_pos_and_lt_one`,
   `exists_asymmetric_conductor_four_crossHeight_countermodel_at_every_leftStrip_point`):**
   Without self-duality (`b = star ∘ a`) or unit-boundedness of the dual Dirichlet inverse,
   `UnitPoleFreeCrossHeightDatum` together with coprime multiplicativity (`a(1) = 1`, `a(n) = 1` on
   odd `n`) and positive residue `R = 1 / 2` does **not** force nonvanishing off `ζ`-zeros: at
   **every** `s₀` with `0 < Re s₀ < 1 / 2`, setting `w₀ = (1 - 2^{-s₀}) / (2^{-s₀}(2 · 2^{-s₀} - 1))`
   satisfies `0 < ‖w₀‖ < 1` and yields an explicit conductor-`4` pair `(a, b)` with `‖b(1)‖ = ‖w₀‖ < 1`
   such that `F(s₀) = 0` and `crossHeightGaussianTwoSeries a b (1/2) 4 ω s₀ x = 0` across all `x > 0`,
   while its dual partner `G(1 - s₀) = 0` has an exponentially growing Dirichlet inverse on `Re z > 1/2`.

2. **Arbitrary-conductor Hamburger–Laplace periodicity and sub-conductor-`5` self-dual rigidity
   without multiplicativity (`coeffTheta_relation_of_unitPoleFreeCrossHeightDatum`,
   `hamburgerSeries_periodic_conductor`,
   `conductor_nat_and_periodic_even_of_unitPoleFreeCrossHeightDatum`,
   `eq_const_mul_riemannZeta_of_conductor_lt_two`,
   `selfDual_conductor_lt_five_classification`):**
   Extending Hamburger's Laplace–residue method to arbitrary real conductor `Q > 0` proves that every
   `UnitPoleFreeCrossHeightDatum` satisfies `L_a(t + i Q) - L_a(t) = F(0)/(π(t + i Q)) - F(0)/(π t)`
   on `Re t > 0`. Consequently:
   * if `Q ∉ ℕ_{≥ 1}`, then `a = b = 0`, `R = 0`, and `F = 0` off `1`;
   * if `Q = q ∈ ℕ_{≥ 1}`, both `a` and `b` are `q`-periodic and reflection-even (`a(q - k) = a(k)`
     for `1 ≤ k < q`) without assuming multiplicativity;
   * for `0 < Q < 2`, every nonzero `UnitPoleFreeCrossHeightDatum` has `Q = 1` and `F = R · ζ`;
   * for `0 < Q < 5` with `‖a(1)‖ = ‖b(1)‖ = 1` (in particular every normalized self-dual datum,
     **without** assuming multiplicativity), `Q ∈ {1, 2, 3, 4}`, `F(z) = ζ(z) D_Q(z)`, and every zero
     of `D_Q` lies on `Re z = 1 / 2`, so `F` and `ζ` have identical off-line zeros everywhere on
     `ℂ \ {1}`. Both thresholds (`‖b(1)‖ = 1` and `Q < 5`, where `L(s, χ₅)` enters) are sharp.

3. **Dual-annihilating pure-direct Gaussian witnesses and uniform dual-vacuum extraction
   (`exists_pure_direct_gaussian_witness_on_remaining_strip`,
   `rh_iff_pure_direct_gaussian_witness_on_remaining_strip`,
   `exists_norm_smoothAFEZetaDualCoefficientGeneral_zero_add_zetaChi_le`):**
   At over-horizon scale `x = |Im s|^{1 + δ}` (`δ > 0`), both the entire infinite dual series (`m ≥ 0`)
   and the shifted pole residue decay faster than `|Im s|^{-B}` across `Ω_open`, reducing `ζ(s)` to a
   pure direct Gaussian Dirichlet polynomial of length `⌈|Im s|^{1 + 2δ}⌉₊`. Conversely, shifting
   only the `m = 0` dual vacuum mode rightward across `w = 0` to `Re(s + w) = 3 / 4` proves
   `‖smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s‖ ≤ C_vac x^{3/4 - Re s}` uniformly across
   all `0 < Re s < 1 / 2` and `x > 0`.

4. **Pole-cleared reflected-Möbius cross-height Gaussian sieve, strictly sub-diagonal annihilation,
   and trans-horizon Vaughan forcing across every point of `Ω_open`
   (`poleCleared_reflected_moebius_crossHeight_eq`,
   `exists_subdiagonal_moebius_gaussian_duality_on_remaining_strip`,
   `rh_iff_subdiagonal_moebius_gaussian_separation_on_remaining_strip`,
   `strict_primeGas_witness_of_subdiagonal_domination_on_remaining_strip`,
   `subdiagonal_vaughan_typeI_or_typeII_forced_above_spira_floor_of_zeta_eq_zero`):**
   Weighting `crossHeight_gaussian_two_tsum_eq` at scales `d x` and `2 d x` by `μ(d) d^{-(1 - s)}`
   (`1 ≤ d ≤ D`) cancels the `s = 1` pole residue identically, annihilates all dual modes `3 ≤ k ≤ D`
   by Möbius inversion while isolating `(1 - 2^{-(1 - s)}) zetaChi(s)`, and at decaying scale
   `x = c_δ |Im s|^{-δ}` annihilates the entire diagonal `n = d`, all super-diagonal pairs `2 n > d`,
   and all low divisors `d < ⌈2 (|Im s| / 184)^{δ / 2}⌉₊` within `< (1 / 16) (|Im s| / 184)^{-δ / 4}`
   at **every** point of `Ω_open`. Decomposing surviving `μ(d)` via `moebius_vaughan_apply_of_gt`
   forces at least one strictly sub-diagonal Vaughan Type-I or Type-II bilinear sum above
   `((1 / 4) (|Im s| / 7)^{1/2 - Re s} - 1 / 16) / 2 > 3 / 32` at any zero of `ζ` in `Ω_open`.
-/

noncomputable section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Asymmetric Conductor-`4` Cross-Height Firewall Across `0 < Re s < 1 / 2` -/

section Part1AsymmetricFirewall

/-- Explicit complex parameter `w₀(s₀) = (1 - 2^{-s₀}) / (2^{-s₀} (2 · 2^{-s₀} - 1))` Solving
`1 + (w₀ - 1) 2^{-s₀} - 2 w₀ · 4^{-s₀} = 0` at an arbitrary left-strip point `s₀`. -/
def asymTwinParam (s₀ : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-s₀)) / ((2 : ℂ) ^ (-s₀) * (2 * (2 : ℂ) ^ (-s₀) - 1))

/-- Across the entire open left critical strip `0 < Re s₀ < 1 / 2`, `asymTwinParam s₀` satisfies
strict unit-disk confinement `0 < ‖asymTwinParam s₀‖ < 1`. -/
theorem norm_asymTwinParam_pos_and_lt_one {s₀ : ℂ} (h0 : 0 < s₀.re) (h_half : s₀.re < 1 / 2) :
    0 < ‖asymTwinParam s₀‖ ∧ ‖asymTwinParam s₀‖ < 1 := by
  set X : ℂ := (2 : ℂ) ^ (-s₀)
  have hX_norm : ‖X‖ = (2 : ℝ) ^ (-s₀.re) := by
    dsimp only [X]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re]
  have hX_pos : 0 < ‖X‖ := by rw [hX_norm]; positivity
  have hX_lt1 : ‖X‖ < 1 := by
    rw [hX_norm]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hX_sq_gt : 1 / 2 < Complex.normSq X := by
    rw [Complex.normSq_eq_norm_sq, hX_norm, ← Real.rpow_natCast ((2 : ℝ) ^ (-s₀.re)) 2,
      ← Real.rpow_mul two_pos.le]
    have hgt : (2 : ℝ) ^ (-1 : ℝ) < (2 : ℝ) ^ (-s₀.re * ((2 : ℕ) : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by push_cast; linarith)
    have hm1 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num
    rwa [hm1] at hgt
  have h1X_ne : 1 - X ≠ 0 := fun h => by
    have h1 : X = 1 := (sub_eq_zero.mp h).symm
    rw [h1, norm_one] at hX_lt1
    exact lt_irrefl 1 hX_lt1
  have hnsq_gap : Complex.normSq (1 - X) < Complex.normSq (X * (2 * X - 1)) := by
    rw [map_mul, Complex.normSq_apply (1 - X), Complex.normSq_apply X,
      Complex.normSq_apply (2 * X - 1)]
    have h1re : (1 - X).re = 1 - X.re := by simp
    have h1im : (1 - X).im = -X.im := by simp
    have h2re : (2 * X - 1).re = 2 * X.re - 1 := by simp
    have h2im : (2 * X - 1).im = 2 * X.im := by simp
    rw [h1re, h1im, h2re, h2im]
    have hid : (X.re * X.re + X.im * X.im) *
          ((2 * X.re - 1) * (2 * X.re - 1) + (2 * X.im) * (2 * X.im)) -
        ((1 - X.re) * (1 - X.re) + (-X.im) * (-X.im)) =
        (2 * (X.re * X.re + X.im * X.im) - 1) *
          (2 * (X.re - 1 / 2) ^ 2 + 2 * X.im ^ 2 + 1 / 2) := by ring
    have hnsq_coord : X.re * X.re + X.im * X.im = Complex.normSq X := (Complex.normSq_apply X).symm
    have hpos1 : 0 < 2 * (X.re * X.re + X.im * X.im) - 1 := by linarith
    have hpos2 : 0 < 2 * (X.re - 1 / 2) ^ 2 + 2 * X.im ^ 2 + 1 / 2 := by positivity
    linarith [mul_pos hpos1 hpos2]
  have hden_pos : 0 < Complex.normSq (X * (2 * X - 1)) :=
    lt_of_le_of_lt (Complex.normSq_nonneg _) hnsq_gap
  have hden_ne : X * (2 * X - 1) ≠ 0 := fun h => by
    rw [h, map_zero] at hden_pos; exact lt_irrefl 0 hden_pos
  have hw_ne : asymTwinParam s₀ ≠ 0 := by
    unfold asymTwinParam
    exact div_ne_zero h1X_ne hden_ne
  have hw_nsq_lt1 : Complex.normSq (asymTwinParam s₀) < 1 := by
    unfold asymTwinParam
    rw [map_div₀]
    exact (div_lt_one hden_pos).mpr hnsq_gap
  rw [Complex.normSq_eq_norm_sq] at hw_nsq_lt1
  exact ⟨norm_pos_iff.mpr hw_ne, by nlinarith [norm_nonneg (asymTwinParam s₀)]⟩

/-- General `4`-periodic even sequence `(α₁, α₂, α₁, α₄, …)` (`0` at `0`). -/
def fourPeriodicEvenSeq (α₁ α₂ α₄ : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else if n % 2 = 1 then α₁ else if n % 4 = 2 then α₂ else α₄

/-- Exact `LSeries` factorization of any `4`-periodic even sequence on `Re z > 1`. -/
theorem fourPeriodicEvenSeq_tsum_eq (α₁ α₂ α₄ : ℂ) {z : ℂ} (hz : 1 < z.re) :
    (∑' n : ℕ, fourPeriodicEvenSeq α₁ α₂ α₄ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-z)) =
      riemannZeta z * (α₁ + (α₂ - α₁) * (2 : ℂ) ^ (-z) + (α₄ - α₂) * (4 : ℂ) ^ (-z)) := by
  set g : ℕ → ℂ := fun d =>
    (if d = 1 then α₁ else 0) + (if d = 2 then α₂ - α₁ else 0) + (if d = 4 then α₄ - α₂ else 0)
  have hconv : ∀ n : ℕ, n ≠ 0 → LSeries.convolution 1 g n = fourPeriodicEvenSeq α₁ α₂ α₄ n := by
    intro n hn0
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (1 : ℕ → ℂ) x * g y)]
    simp only [Pi.one_apply, one_mul]
    have hsum_pt : ∀ (d₀ : ℕ) (c : ℂ),
        (∑ d ∈ n.divisors, if d = d₀ then c else 0) = if d₀ ∣ n then c else 0 := by
      intro d₀ c
      rw [Finset.sum_ite_eq' n.divisors d₀ (fun _ => c)]
      by_cases hd : d₀ ∣ n
      · rw [if_pos (Nat.mem_divisors.mpr ⟨hd, hn0⟩), if_pos hd]
      · rw [if_neg (fun hm => hd (Nat.dvd_of_mem_divisors hm)), if_neg hd]
    dsimp only [g]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_pt 1 α₁, hsum_pt 2 (α₂ - α₁),
      hsum_pt 4 (α₄ - α₂), if_pos (one_dvd n)]
    simp only [Nat.dvd_iff_mod_eq_zero]
    unfold fourPeriodicEvenSeq
    rw [if_neg hn0]
    by_cases h2 : n % 2 = 1
    · have hn2 : n % 2 ≠ 0 := by omega
      have hn4 : n % 4 ≠ 0 := by omega
      rw [if_pos h2, if_neg hn2, if_neg hn4]; ring
    · have hev : n % 2 = 0 := by omega
      rw [if_neg h2, if_pos hev]
      by_cases h42 : n % 4 = 2
      · have hn4 : n % 4 ≠ 0 := by omega
        rw [if_pos h42, if_neg hn4]; ring
      · have hdiv4 : n % 4 = 0 := by omega
        rw [if_neg h42, if_pos hdiv4]; ring
  have hg_supp : ∀ d : ℕ, d ∉ ({1, 2, 4} : Finset ℕ) → LSeries.term g z d = 0 := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact LSeries.term_zero g z
    · rw [LSeries.term_of_ne_zero hd0]
      have hd1 : d ≠ 1 := fun h => hd (by simp [h])
      have hd2 : d ≠ 2 := fun h => hd (by simp [h])
      have hd4 : d ≠ 4 := fun h => hd (by simp [h])
      have hg0 : g d = 0 := by dsimp only [g]; rw [if_neg hd1, if_neg hd2, if_neg hd4]; ring
      rw [hg0, zero_div]
  have hsum_g : LSeriesSummable g z := summable_of_ne_finset_zero hg_supp
  have hsum_1 : LSeriesSummable 1 z := LSeriesSummable_one_iff.mpr hz
  have hLg : LSeries g z = α₁ + (α₂ - α₁) * (2 : ℂ) ^ (-z) + (α₄ - α₂) * (4 : ℂ) ^ (-z) := by
    unfold LSeries
    rw [tsum_eq_sum hg_supp]
    have hset : ({1, 2, 4} : Finset ℕ) = insert 1 (insert 2 {4}) := rfl
    rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      LSeries.term_of_ne_zero one_ne_zero, LSeries.term_of_ne_zero (by omega : 2 ≠ 0),
      LSeries.term_of_ne_zero (by omega : 4 ≠ 0)]
    dsimp only [g]
    norm_num
    simp only [div_eq_mul_inv, ← Complex.cpow_neg]
    ring
  have htsum_L : (∑' n : ℕ, fourPeriodicEvenSeq α₁ α₂ α₄ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-z)) =
      LSeries (fourPeriodicEvenSeq α₁ α₂ α₄) z := by
    have hsum_f : Summable (LSeries.term (fourPeriodicEvenSeq α₁ α₂ α₄) z) :=
      (hsum_1.convolution hsum_g).congr fun n => by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp
        · simp only [LSeries.term_of_ne_zero hn0, hconv n hn0]
    unfold LSeries
    rw [hsum_f.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), div_eq_mul_inv, ← Complex.cpow_neg]
  rw [htsum_L, LSeries_congr (fun {n} hn0 => (hconv n hn0).symm) z,
    LSeries_convolution' hsum_1 hsum_g, LSeries_one_eq_riemannZeta hz, hLg]

/-- General `3`-periodic even sequence `(α₁, α₁, α₃, …)` (`0` at `0`). -/
def threePeriodicEvenSeq (α₁ α₃ : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else if n % 3 = 0 then α₃ else α₁

/-- Exact `LSeries` factorization of any `3`-periodic even sequence on `Re z > 1`. -/
theorem threePeriodicEvenSeq_tsum_eq (α₁ α₃ : ℂ) {z : ℂ} (hz : 1 < z.re) :
    (∑' n : ℕ, threePeriodicEvenSeq α₁ α₃ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-z)) =
      riemannZeta z * (α₁ + (α₃ - α₁) * (3 : ℂ) ^ (-z)) := by
  set g : ℕ → ℂ := fun d => (if d = 1 then α₁ else 0) + (if d = 3 then α₃ - α₁ else 0)
  have hconv : ∀ n : ℕ, n ≠ 0 → LSeries.convolution 1 g n = threePeriodicEvenSeq α₁ α₃ n := by
    intro n hn0
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (1 : ℕ → ℂ) x * g y)]
    simp only [Pi.one_apply, one_mul]
    have hsum_pt : ∀ (d₀ : ℕ) (c : ℂ),
        (∑ d ∈ n.divisors, if d = d₀ then c else 0) = if d₀ ∣ n then c else 0 := by
      intro d₀ c
      rw [Finset.sum_ite_eq' n.divisors d₀ (fun _ => c)]
      by_cases hd : d₀ ∣ n
      · rw [if_pos (Nat.mem_divisors.mpr ⟨hd, hn0⟩), if_pos hd]
      · rw [if_neg (fun hm => hd (Nat.dvd_of_mem_divisors hm)), if_neg hd]
    dsimp only [g]
    rw [Finset.sum_add_distrib, hsum_pt 1 α₁, hsum_pt 3 (α₃ - α₁), if_pos (one_dvd n)]
    simp only [Nat.dvd_iff_mod_eq_zero]
    unfold threePeriodicEvenSeq
    rw [if_neg hn0]
    by_cases h3 : n % 3 = 0
    · rw [if_pos h3, if_pos h3]; ring
    · rw [if_neg h3, if_neg h3]; ring
  have hg_supp : ∀ d : ℕ, d ∉ ({1, 3} : Finset ℕ) → LSeries.term g z d = 0 := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact LSeries.term_zero g z
    · rw [LSeries.term_of_ne_zero hd0]
      have hd1 : d ≠ 1 := fun h => hd (by simp [h])
      have hd3 : d ≠ 3 := fun h => hd (by simp [h])
      have hg0 : g d = 0 := by dsimp only [g]; rw [if_neg hd1, if_neg hd3]; ring
      rw [hg0, zero_div]
  have hsum_g : LSeriesSummable g z := summable_of_ne_finset_zero hg_supp
  have hsum_1 : LSeriesSummable 1 z := LSeriesSummable_one_iff.mpr hz
  have hLg : LSeries g z = α₁ + (α₃ - α₁) * (3 : ℂ) ^ (-z) := by
    unfold LSeries
    rw [tsum_eq_sum hg_supp, Finset.sum_pair (by decide : (1 : ℕ) ≠ 3),
      LSeries.term_of_ne_zero one_ne_zero, LSeries.term_of_ne_zero (by omega : 3 ≠ 0)]
    dsimp only [g]
    norm_num
    simp only [div_eq_mul_inv, ← Complex.cpow_neg]
  have htsum_L : (∑' n : ℕ, threePeriodicEvenSeq α₁ α₃ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-z)) =
      LSeries (threePeriodicEvenSeq α₁ α₃) z := by
    have hsum_f : Summable (LSeries.term (threePeriodicEvenSeq α₁ α₃) z) :=
      (hsum_1.convolution hsum_g).congr fun n => by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp
        · simp only [LSeries.term_of_ne_zero hn0, hconv n hn0]
    unfold LSeries
    rw [hsum_f.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), div_eq_mul_inv, ← Complex.cpow_neg]
  rw [htsum_L, LSeries_congr (fun {n} hn0 => (hconv n hn0).symm) z,
    LSeries_convolution' hsum_1 hsum_g, LSeries_one_eq_riemannZeta hz, hLg]

/-- **Asymmetric conductor-`4` cross-height firewall at every point of `0 < Re s₀ < 1 / 2`:**
without self-duality (`b = star ∘ a`) or unit-boundedness of the dual Dirichlet inverse, at
**every** point `s₀` in `0 < Re s₀ < 1 / 2` (in particular every `s₀ ∈ Ω_open`), there exists an
explicit coprime-multiplicative arithmetic function `a` (`a(1) = 1`, `a(n) = 1` on odd `n`), a
`4`-periodic dual sequence `b` with `‖b(1)‖ < 1`, a root number `ω` (`‖ω‖ = 1`), and `F` satisfying
`UnitPoleFreeCrossHeightDatum F a b (1 / 2) 4 ω` across all vertical heights such that `F(s₀) = 0`
and `crossHeightGaussianTwoSeries a b (1 / 2) 4 ω s₀ x = 0` for all `x > 0`. -/
theorem exists_asymmetric_conductor_four_crossHeight_countermodel_at_every_leftStrip_point
    {s₀ : ℂ} (h0 : 0 < s₀.re) (h_half : s₀.re < 1 / 2) :
    ∃ (a : ArithmeticFunction ℂ) (b : ℕ → ℂ) (F : ℂ → ℂ) (ω : ℂ),
      a.IsMultiplicative ∧
      (∀ n : ℕ, n % 2 = 1 → a n = 1) ∧
      UnitPoleFreeCrossHeightDatum F a b (1 / 2) 4 ω ∧
      0 < ‖b 1‖ ∧ ‖b 1‖ < 1 ∧
      F s₀ = 0 ∧
      (∀ x : ℝ, 0 < x → crossHeightGaussianTwoSeries a b (1 / 2) 4 ω s₀ x = 0) := by
  obtain ⟨hw_pos, hw_lt1⟩ := norm_asymTwinParam_pos_and_lt_one h0 h_half
  set w₀ : ℂ := asymTwinParam s₀
  set r₀ : ℝ := ‖w₀‖
  have hr₀_ne : (r₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw_pos.ne'
  set u₀ : ℂ := w₀ / (r₀ : ℂ)
  have hu₀_norm : ‖u₀‖ = 1 := by
    dsimp only [u₀, r₀]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw_pos, div_self hw_pos.ne']
  set ω₀ : ℂ := -u₀
  have hω₀_norm : ‖ω₀‖ = 1 := by dsimp only [ω₀]; rw [norm_neg, hu₀_norm]
  set a : ArithmeticFunction ℂ := ⟨fourPeriodicEvenSeq 1 w₀ (-w₀), rfl⟩
  have ha_app : ∀ n : ℕ, a n = fourPeriodicEvenSeq 1 w₀ (-w₀) n := fun _ => rfl
  set b : ℕ → ℂ := fourPeriodicEvenSeq (r₀ : ℂ) (star u₀) (-star u₀)
  set Da : ℂ → ℂ := fun z => 1 + (w₀ - 1) * (2 : ℂ) ^ (-z) - 2 * w₀ * (4 : ℂ) ^ (-z)
  set F : ℂ → ℂ := fun z => riemannZeta z * Da z
  -- 1. Coprime multiplicativity of `a` and odd-integer agreement with `1`.
  have ha_odd : ∀ n : ℕ, n % 2 = 1 → a n = 1 := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    rw [ha_app]; unfold fourPeriodicEvenSeq; rw [if_neg hn0, if_pos hn]
  have ha_mul : a.IsMultiplicative := by
    refine ⟨ha_odd 1 rfl, ?_⟩
    intro m n hcop
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    have hnot_both_even : ¬(m % 2 = 0 ∧ n % 2 = 0) := by
      rintro ⟨hm2, hn2⟩
      have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero hm2
      have h2n : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn2
      have h21 : 2 ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd h2m h2n
      omega
    have hmod_case : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → x % 2 = 1 →
        fourPeriodicEvenSeq 1 w₀ (-w₀) (x * y) =
          fourPeriodicEvenSeq 1 w₀ (-w₀) x * fourPeriodicEvenSeq 1 w₀ (-w₀) y := by
      intro x y hx0 hy0 hx_odd
      have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
      unfold fourPeriodicEvenSeq
      rw [if_neg hxy0, if_neg hx0, if_neg hy0, if_pos hx_odd, one_mul,
        Nat.mul_mod x y 2, hx_odd, one_mul, Nat.mod_mod]
      by_cases hy_odd : y % 2 = 1
      · simp only [hy_odd, ↓reduceIte]
      · simp only [hy_odd, ↓reduceIte]
        rw [Nat.mul_mod x y 4]
        have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by omega
        have hy4 : y % 4 = 0 ∨ y % 4 = 2 := by omega
        rcases hx4 with hx1 | hx3
        · rcases hy4 with hy04 | hy24
          · simp [hx1, hy04]
          · simp [hx1, hy24]
        · rcases hy4 with hy04 | hy24
          · simp [hx3, hy04]
          · simp [hx3, hy24]
    rw [ha_app, ha_app, ha_app]
    by_cases hm_odd : m % 2 = 1
    · exact hmod_case m n hm0 hn0 hm_odd
    · have hn_odd : n % 2 = 1 := by omega
      rw [mul_comm m n, mul_comm (fourPeriodicEvenSeq 1 w₀ (-w₀) m)]
      exact hmod_case n m hn0 hm0 hn_odd
  -- 2. Unit bounds on `a` and `b`.
  have ha_unit : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1 := by
    intro n hn
    rw [ha_app]; unfold fourPeriodicEvenSeq; rw [if_neg (by omega)]
    split_ifs
    · simp
    · exact hw_lt1.le
    · rw [norm_neg]; exact hw_lt1.le
  have hb_unit : ∀ m : ℕ, 1 ≤ m → ‖b m‖ ≤ 1 := by
    intro m hm
    dsimp only [b]; unfold fourPeriodicEvenSeq; rw [if_neg (by omega)]
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw_pos]; exact hw_lt1.le
    · rw [norm_star, hu₀_norm]
    · rw [norm_neg, norm_star, hu₀_norm]
  -- 3. `UnitPoleFreeCrossHeightDatum F a b (1 / 2) 4 ω₀`.
  have hDa_diff : Differentiable ℂ Da := by
    haveI : NeZero (2 : ℂ) := ⟨by norm_num⟩
    haveI : NeZero (4 : ℂ) := ⟨by norm_num⟩
    have hd2 : Differentiable ℂ (fun z : ℂ => (2 : ℂ) ^ (-z)) :=
      (differentiable_const_cpow_of_neZero (2 : ℂ)).comp differentiable_id.neg
    have hd4 : Differentiable ℂ (fun z : ℂ => (4 : ℂ) ^ (-z)) :=
      (differentiable_const_cpow_of_neZero (4 : ℂ)).comp differentiable_id.neg
    exact ((differentiable_const 1).add (hd2.const_mul (w₀ - 1))).sub (hd4.const_mul (2 * w₀))
  have hDa_one : Da 1 = 1 / 2 := by
    dsimp only [Da]
    have h2 : (2 : ℂ) ^ (-1 : ℂ) = 1 / 2 := by rw [Complex.cpow_neg_one]; norm_num
    have h4 : (4 : ℂ) ^ (-1 : ℂ) = 1 / 4 := by rw [Complex.cpow_neg_one]; norm_num
    rw [h2, h4]; ring
  have hdatum : UnitPoleFreeCrossHeightDatum F a b (1 / 2) 4 ω₀ := by
    refine ⟨by norm_num, hω₀_norm, ha_unit, hb_unit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hts := fourPeriodicEvenSeq_tsum_eq 1 w₀ (-w₀) hz
      have halg : 1 + (w₀ - 1) * (2 : ℂ) ^ (-z) + (-w₀ - w₀) * (4 : ℂ) ^ (-z) = Da z := by
        dsimp only [Da]; ring
      dsimp only [F]
      rw [← halg, ← hts]
      exact tsum_congr fun n => by rw [ha_app]
    · intro z _ hz_lt
      exact (differentiableAt_riemannZeta (fun h => by rw [h] at hz_lt; norm_num at hz_lt)).mul
        (hDa_diff z)
    · intro z _ hne
      exact (differentiableAt_riemannZeta hne).mul (hDa_diff z)
    · intro z hz
      exact (differentiableAt_riemannZeta (fun h => by rw [h] at hz; norm_num at hz)).mul
        (hDa_diff z)
    · have hlim := riemannZeta_residue_one.mul hDa_diff.continuous.continuousAt.continuousWithinAt
      rw [one_mul, hDa_one] at hlim
      exact hlim.congr fun z => by dsimp only [F]; ring
    · intro B
      obtain ⟨Cζ, Nζ, hCζ0, hCζ⟩ := exists_bound_norm_riemannZeta_strip B
      set K_Da : ℝ := 1 + 2 * (2 : ℝ) ^ |B| + 2 * (4 : ℝ) ^ |B|
      refine ⟨Cζ * K_Da, Nζ, by positivity, fun σ t hσ ht => ?_⟩
      set z : ℂ := (σ : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ := by simp [z]
      have hneg_σ : -σ ≤ |B| := by linarith [(abs_le.mp hσ).1, le_abs_self B]
      have h2_bd : ‖(2 : ℂ) ^ (-z)‖ ≤ (2 : ℝ) ^ |B| := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
          Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re, hz_re]
        exact Real.rpow_le_rpow_of_exponent_le one_lt_two.le hneg_σ
      have h4_bd : ‖(4 : ℂ) ^ (-z)‖ ≤ (4 : ℝ) ^ |B| := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
          Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re, hz_re]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hneg_σ
      have hw1_bd : ‖w₀ - 1‖ ≤ 2 := (norm_sub_le w₀ 1).trans (by rw [norm_one]; linarith)
      have h2w_bd : ‖2 * w₀‖ ≤ 2 := by rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
      have hDa_bd : ‖Da z‖ ≤ K_Da := by
        dsimp only [Da, K_Da]
        have ht1 := norm_sub_le (1 + (w₀ - 1) * (2 : ℂ) ^ (-z)) (2 * w₀ * (4 : ℂ) ^ (-z))
        have ht2 := norm_add_le (1 : ℂ) ((w₀ - 1) * (2 : ℂ) ^ (-z))
        rw [norm_mul] at ht1
        rw [norm_one, norm_mul] at ht2
        have hm1 : ‖w₀ - 1‖ * ‖(2 : ℂ) ^ (-z)‖ ≤ 2 * (2 : ℝ) ^ |B| :=
          mul_le_mul hw1_bd h2_bd (norm_nonneg _) zero_le_two
        have hm2 : ‖2 * w₀‖ * ‖(4 : ℂ) ^ (-z)‖ ≤ 2 * (4 : ℝ) ^ |B| :=
          mul_le_mul h2w_bd h4_bd (norm_nonneg _) zero_le_two
        linarith
      dsimp only [F]
      rw [norm_mul]
      calc ‖riemannZeta z‖ * ‖Da z‖
          ≤ (Cζ * |t| ^ Nζ) * K_Da :=
            mul_le_mul (hCζ σ t hσ ht) hDa_bd (norm_nonneg _) (by positivity)
        _ = (Cζ * K_Da) * |t| ^ Nζ := by ring
    · -- Cross-height reflection `F z = ω₀ * 4^{1/2 - z} * zetaChi z * ∑' m, b (m + 1) * (m + 1)^{-(1 - z)}`
      intro z hz
      have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
      have hz1 : z ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
      have h1z : 1 < (1 - z).re := by simp; linarith
      have hG : Complex.Gammaℝ (1 - z) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      have hts_b := fourPeriodicEvenSeq_tsum_eq (r₀ : ℂ) (star u₀) (-star u₀) h1z
      have hζ_fe := zeta_eq_zetaChi_mul hz0 hz1 hG
      -- Verify polynomial reflection `Da z = ω₀ * 4^{1/2 - z} * Db (1 - z)`.
      have h4_pow : ((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) = 2 * (4 : ℂ) ^ (-z) := by
        have h40 : (4 : ℂ) ≠ 0 := by norm_num
        have h4half : (4 : ℂ) ^ (1 / 2 : ℂ) = 2 := by
          rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
            show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
          norm_num
        rw [Complex.ofReal_ofNat, show (1 / 2 : ℂ) - z = (1 / 2 : ℂ) + (-z) by ring,
          Complex.cpow_add _ _ h40, h4half]
      have h2_1z : (2 : ℂ) ^ (-(1 - z)) = (1 / 2 : ℂ) * (2 : ℂ) ^ z := by
        rw [show -(1 - z) = (-1 : ℂ) + z by ring,
          Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_neg_one]
        norm_num
      have h4_1z : (4 : ℂ) ^ (-(1 - z)) = (1 / 4 : ℂ) * (4 : ℂ) ^ z := by
        rw [show -(1 - z) = (-1 : ℂ) + z by ring,
          Complex.cpow_add _ _ (by norm_num : (4 : ℂ) ≠ 0), Complex.cpow_neg_one]
        norm_num
      have h4z_inv : (4 : ℂ) ^ (-z) * (4 : ℂ) ^ z = 1 := by
        rw [← Complex.cpow_add _ _ (by norm_num : (4 : ℂ) ≠ 0), neg_add_cancel, Complex.cpow_zero]
      have h42z : (4 : ℂ) ^ (-z) * (2 : ℂ) ^ z = (2 : ℂ) ^ (-z) := by
        have h4_eq_22 : (4 : ℂ) ^ (-z) = (2 : ℂ) ^ (-z) * (2 : ℂ) ^ (-z) := by
          rw [show (4 : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) by norm_num,
            Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le (-z)]
          norm_num
        have h2z_inv : (2 : ℂ) ^ (-z) * (2 : ℂ) ^ z = 1 := by
          rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), neg_add_cancel, Complex.cpow_zero]
        rw [h4_eq_22, mul_assoc, h2z_inv, mul_one]
      have hu_star : u₀ * star u₀ = 1 := by
        rw [mul_comm, Complex.star_def, Complex.conj_mul', hu₀_norm, Complex.ofReal_one, one_pow]
      have hur₀ : u₀ * (r₀ : ℂ) = w₀ := div_mul_cancel₀ w₀ hr₀_ne
      have hu_sub : u₀ * (star u₀ - (r₀ : ℂ)) = 1 - w₀ := by rw [mul_sub, hu_star, hur₀]
      have hpoly_fe : Da z = ω₀ * ((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) *
          ((r₀ : ℂ) + (star u₀ - (r₀ : ℂ)) * (2 : ℂ) ^ (-(1 - z)) +
            (-star u₀ - star u₀) * (4 : ℂ) ^ (-(1 - z))) := by
        rw [h4_pow, h2_1z, h4_1z]
        dsimp only [Da, ω₀]
        calc 1 + (w₀ - 1) * (2 : ℂ) ^ (-z) - 2 * w₀ * (4 : ℂ) ^ (-z)
            = (u₀ * star u₀) * ((4 : ℂ) ^ (-z) * (4 : ℂ) ^ z) -
                (u₀ * (star u₀ - (r₀ : ℂ))) * ((4 : ℂ) ^ (-z) * (2 : ℂ) ^ z) -
                2 * (u₀ * (r₀ : ℂ)) * (4 : ℂ) ^ (-z) := by
              rw [h4z_inv, h42z, hu_star, hur₀, hu_sub]; ring
          _ = -u₀ * (2 * (4 : ℂ) ^ (-z)) *
                ((r₀ : ℂ) + (star u₀ - (r₀ : ℂ)) * ((1 / 2 : ℂ) * (2 : ℂ) ^ z) +
                  (-star u₀ - star u₀) * ((1 / 4 : ℂ) * (4 : ℂ) ^ z)) := by ring
      dsimp only [F]
      rw [hζ_fe, hts_b, hpoly_fe]
      ring
  have hDa_s₀ : Da s₀ = 0 := by
    set X : ℂ := (2 : ℂ) ^ (-s₀)
    have h4X : (4 : ℂ) ^ (-s₀) = X ^ 2 := by
      dsimp only [X]
      rw [pow_two, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le (-s₀)]
      norm_num
    have hden_ne : X * (2 * X - 1) ≠ 0 := by
      intro h0_den
      have h0_w : asymTwinParam s₀ = 0 := by
        unfold asymTwinParam; change (1 - X) / (X * (2 * X - 1)) = 0; rw [h0_den, div_zero]
      have hw0_pos : 0 < ‖asymTwinParam s₀‖ := hw_pos
      rw [h0_w, norm_zero] at hw0_pos
      exact lt_irrefl 0 hw0_pos
    have hw₀_eq : w₀ = (1 - X) / (X * (2 * X - 1)) := rfl
    change 1 + (w₀ - 1) * X - 2 * w₀ * (4 : ℂ) ^ (-s₀) = 0
    rw [h4X]
    apply mul_right_cancel₀ hden_ne
    rw [zero_mul]
    calc (1 + (w₀ - 1) * X - 2 * w₀ * X ^ 2) * (X * (2 * X - 1))
        = (1 - X) * (X * (2 * X - 1)) - (w₀ * (X * (2 * X - 1))) * (X * (2 * X - 1)) := by ring
      _ = 0 := by rw [hw₀_eq, div_mul_cancel₀ (1 - X) hden_ne, sub_self]
  have hF_s₀ : F s₀ = 0 := by dsimp only [F]; rw [hDa_s₀, mul_zero]
  have hb1_norm : ‖b 1‖ = r₀ := by
    dsimp only [b]; unfold fourPeriodicEvenSeq; simp [r₀]
  refine ⟨a, b, F, ω₀, ha_mul, ha_odd, hdatum, ?_, ?_, hF_s₀, fun x hx => ?_⟩
  · rw [hb1_norm]; exact hw_pos
  · rw [hb1_norm]; exact hw_lt1
  · rw [← crossHeight_gaussian_two_tsum_eq hdatum hx h0 h_half, hF_s₀]

end Part1AsymmetricFirewall

/-! ### Part 2: Arbitrary-Conductor Hamburger–Laplace Periodicity & Sub-Conductor-`5` Critical-Line Rigidity -/

section Part2HamburgerConductorRigidity

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.StripBochnerWeilForcing

private theorem summable_unit_div_rpow {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ := by
  have hbase : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
    have h := Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
    exact (summable_nat_add_iff 1).mpr h
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hbase
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, Real.rpow_neg hn_pos.le, ← one_div]
  exact div_le_div_of_nonneg_right (ha (n + 1) (Nat.succ_pos n)) (by positivity)

private theorem differentiableAt_datum_of_ne_one
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) {z : ℂ} (hz : z ≠ 1) :
    DifferentiableAt ℂ F z := by
  rcases le_or_gt z.re 0 with hle0 | hgt0
  · exact hD.holo_nonpos z hle0
  · rcases lt_or_ge z.re (1 / 2) with hlt_half | hge_half
    · exact hD.holo_leftStrip z hgt0 hlt_half
    · exact hD.holo_rightOffOne z hge_half hz

private theorem differentiable_regularized_datum
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) :
    Differentiable ℂ (Function.update (fun z => (z - 1) * F z) 1 R) := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hraw : DifferentiableAt ℂ (fun u => (u - 1) * F u) w :=
        (differentiableAt_id.sub_const 1).mul (differentiableAt_datum_of_ne_one hD hw)
      refine hraw.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hw] with u hu
      exact Function.update_of_ne hu _ _
    · simpa only [continuousAt_update_same] using hD.pole_res
  · have hraw : DifferentiableAt ℂ (fun u => (u - 1) * F u) z :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_datum_of_ne_one hD hz)
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with u hu
    exact Function.update_of_ne hu _ _

private theorem two_mul_gammaℝNum_eq_mul_Gammaℝ {z : ℂ} (hz : z ≠ 0) :
    2 * gammaℝNum z = z * Complex.Gammaℝ z := by
  have hreg := gammaℝReg_eq hz
  unfold gammaℝReg at hreg
  rw [dslope_of_ne _ hz, slope_def_field, gammaℝNum_zero, sub_zero] at hreg
  have hmul := congrArg (fun w => z * w) hreg
  have hlhs : z * (2 * ((gammaℝNum z - 1) / z)) = 2 * gammaℝNum z - 2 := by
    field_simp [hz]
  have hrhs : z * (Complex.Gammaℝ z - 2 / z) = z * Complex.Gammaℝ z - 2 := by
    field_simp [hz]
  rw [hlhs, hrhs] at hmul
  linear_combination hmul

private theorem two_mul_gammaℝNum_one : 2 * gammaℝNum 1 = 1 := by
  rw [two_mul_gammaℝNum_eq_mul_Gammaℝ one_ne_zero, one_mul, Complex.Gammaℝ_one]

/-- **Exact rescaled theta transformation law for arbitrary `UnitPoleFreeCrossHeightDatum`:**
for every real conductor `Q > 0`, removing both polar parts `F(0) Γ_ℝ(s)` and `(R / 2) Γ_ℝ(s - 1)`
across `verticalStrip (-1 / 2) (3 / 2)` yields the exact theta identity
`θ_a(x) = ω Q^{-1/2} x^{-1/2} θ_b(1 / (Q² x)) + F(0) + (R / 2) x^{-1/2}` (`x > 0`). -/
theorem coeffTheta_relation_of_unitPoleFreeCrossHeightDatum
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) {x : ℝ} (hx : 0 < x) :
    coeffTheta a x =
      (ω * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
        ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹)) +
        F 0 + (R / 2) * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hQ : 0 < Q := hD.Q_pos
  have hQ2_inv : 0 < 1 / Q ^ 2 := by positivity
  have ha_sum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun _ hσ => summable_unit_div_rpow hD.unit_a hσ
  have hb_sum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun _ hσ => summable_unit_div_rpow hD.unit_b hσ
  set regF : ℂ → ℂ := Function.update (fun z => (z - 1) * F z) 1 R
  have hregF : Differentiable ℂ regF := differentiable_regularized_datum hD
  set α : ℂ := F 0
  set β : ℂ := R / 2
  set N : ℂ → ℂ := fun z => 2 * gammaℝNum z * regF z
  set E : ℂ → ℂ := fun z =>
    dslope (dslope N 0) 1 z - α * gammaℝReg z - β * gammaℝReg (z - 1)
  -- Pointwise identification of `E` off `0` and `1`.
  have hE_eq : ∀ z : ℂ, z ≠ 0 → z ≠ 1 →
      E z = Complex.Gammaℝ z * F z - (α * Complex.Gammaℝ z + β * Complex.Gammaℝ (z - 1)) := by
    intro z hz0 hz1
    have hz10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hN0 : N 0 = -2 * α := by
      dsimp only [N, regF, α]
      rw [gammaℝNum_zero, Function.update_of_ne (by norm_num : (0 : ℂ) ≠ 1)]
      ring
    have hN1 : N 1 = 2 * β := by
      dsimp only [N, regF, β]
      rw [two_mul_gammaℝNum_one, one_mul, Function.update_self]
      ring
    have hNz : N z = z * (z - 1) * (Complex.Gammaℝ z * F z) := by
      dsimp only [N, regF]
      rw [two_mul_gammaℝNum_eq_mul_Gammaℝ hz0, Function.update_of_ne hz1]
      ring
    dsimp only [E]
    rw [dslope_of_ne _ hz1, slope_def_field, dslope_of_ne _ hz0, slope_def_field,
      dslope_of_ne _ (one_ne_zero : (1 : ℂ) ≠ 0), slope_def_field, sub_zero,
      hN0, hN1, hNz, gammaℝReg_eq hz0, gammaℝReg_eq hz10]
    field_simp [hz0, hz10]
    ring
  -- Holomorphy of `E` on `verticalStrip (-1 / 2) (3 / 2)`.
  have hU₂_open : IsOpen {z : ℂ | -2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h0_U₂ : (0 : ℂ) ∈ {z : ℂ | -2 < z.re} := by simp
  have h1_U₂ : (1 : ℂ) ∈ {z : ℂ | -2 < z.re} := by simp; norm_num
  have hN_diff : DifferentiableOn ℂ N {z : ℂ | -2 < z.re} :=
    ((differentiableOn_gammaℝNum.const_mul 2).mul hregF.differentiableOn).congr
      (fun _ _ => by dsimp only [N, Pi.mul_apply])
  have hds1 : DifferentiableOn ℂ (dslope N 0) {z : ℂ | -2 < z.re} :=
    (Complex.differentiableOn_dslope (hU₂_open.mem_nhds h0_U₂)).mpr hN_diff
  have hds2 : DifferentiableOn ℂ (dslope (dslope N 0) 1) {z : ℂ | -2 < z.re} :=
    (Complex.differentiableOn_dslope (hU₂_open.mem_nhds h1_U₂)).mpr hds1
  have hE_diff_open : DifferentiableOn ℂ E {z : ℂ | -1 < z.re} := by
    have hsub2 : {z : ℂ | -1 < z.re} ⊆ {z : ℂ | -2 < z.re} := fun z hz => by
      change -2 < z.re; change -1 < z.re at hz; linarith
    have hg0 : DifferentiableOn ℂ gammaℝReg {z : ℂ | -1 < z.re} :=
      differentiableOn_gammaℝReg.mono hsub2
    have hg1 : DifferentiableOn ℂ (fun z => gammaℝReg (z - 1)) {z : ℂ | -1 < z.re} := by
      intro z hz
      change -1 < z.re at hz
      have hm : -2 < (z - 1).re := by simp; linarith
      exact ((differentiableOn_gammaℝReg.differentiableAt (hU₂_open.mem_nhds hm)).comp z
        (differentiableAt_id.sub_const 1)).differentiableWithinAt
    exact ((hds2.mono hsub2).sub (hg0.const_mul α)).sub (hg1.const_mul β)
  have hstrip_sub : HTGeometry.verticalStrip (-1 / 2) (3 / 2) ⊆ {z : ℂ | -1 < z.re} := by
    intro z hz
    rw [HTGeometry.mem_verticalStrip] at hz
    change -1 < z.re
    linarith [hz.1]
  have hE_diff : DifferentiableOn ℂ E (HTGeometry.verticalStrip (-1 / 2) (3 / 2)) :=
    hE_diff_open.mono hstrip_sub
  -- `O(1 / (1 + s.im ^ 2))` decay of `E` on `HTGeometry.verticalStrip (-1 / 2) (3 / 2)`.
  obtain ⟨CF, NF, hCF0, hCF⟩ := hD.poly_growth (3 / 2)
  obtain ⟨Cg1, Ng1, hCg1, hg1⟩ := exists_sharp_bound_norm_Gamma_strip (-1 / 4) (3 / 4)
  obtain ⟨Cg2, Ng2, hCg2, hg2⟩ := exists_sharp_bound_norm_Gamma_strip (-3 / 4) (1 / 4)
  obtain ⟨K1, hK1_nn, hK1⟩ := RHTower.exists_bound_pow_mul_exp_neg (Ng1 + NF + 2)
  obtain ⟨K2, hK2_nn, hK2⟩ := RHTower.exists_bound_pow_mul_exp_neg (Ng2 + 2)
  set K_box : Set ℂ := Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-4 : ℝ) 4
  have hK_comp : IsCompact K_box := isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K_box ⊆ HTGeometry.verticalStrip (-1 / 2) (3 / 2) := fun z hz =>
    HTGeometry.mem_verticalStrip.mpr (Complex.mem_reProdIm.mp hz).1
  obtain ⟨M_box, hM_box⟩ := hK_comp.exists_bound_of_continuousOn (hE_diff.continuousOn.mono hK_sub)
  set C_high1 : ℝ := Real.pi ^ (1 / 4 : ℝ) * Cg1 * (CF + ‖α‖)
  set C_high2 : ℝ := ‖β‖ * Real.pi ^ (3 / 4 : ℝ) * Cg2
  set C_tot : ℝ := max (17 * max M_box 0) (C_high1 * K1 + C_high2 * K2)
  have hE_decay : ∀ s ∈ HTGeometry.verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C_tot / (1 + s.im ^ 2) := by
    intro s hs
    have hs_strip := hs
    rw [HTGeometry.mem_verticalStrip] at hs_strip
    have hden_pos : 0 < 1 + s.im ^ 2 := by positivity
    by_cases ht : 4 ≤ |s.im|
    · have hs0 : s ≠ 0 := fun h => by rw [h] at ht; simp at ht; linarith
      have hs1 : s ≠ 1 := fun h => by rw [h] at ht; simp at ht; linarith
      set τ : ℝ := |s.im|
      have hτ0 : 0 ≤ τ := abs_nonneg _
      have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
      -- Bound `‖F s‖ + ‖α‖ ≤ (CF + ‖α‖) * (τ + 4) ^ NF`.
      have hFs : ‖F s‖ ≤ CF * (τ + 4) ^ NF := by
        have hs_pt : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
        have hre_abs : |s.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hs_strip.1], hs_strip.2⟩
        have hb := hCF s.re s.im hre_abs hτ1
        rw [hs_pt] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hτ0 (by linarith) NF) hCF0)
      have hF_sub_α : ‖F s - α‖ ≤ (CF + ‖α‖) * (τ + 4) ^ NF := by
        have h1 : (1 : ℝ) ≤ (τ + 4) ^ NF := one_le_pow₀ (by linarith)
        calc ‖F s - α‖ ≤ ‖F s‖ + ‖α‖ := norm_sub_le _ _
          _ ≤ CF * (τ + 4) ^ NF + ‖α‖ * (τ + 4) ^ NF :=
              add_le_add hFs (le_mul_of_one_le_right (norm_nonneg _) h1)
          _ = (CF + ‖α‖) * (τ + 4) ^ NF := by ring
      -- Bound `‖Complex.Gammaℝ s‖`.
      have hΓs : ‖Complex.Gammaℝ s‖ ≤
          Real.pi ^ (1 / 4 : ℝ) * Cg1 * (τ + 4) ^ Ng1 * Real.exp (-(Real.pi * τ / 4)) := by
        rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        have hpi_le : Real.pi ^ ((-s / 2).re) ≤ Real.pi ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
            (by simp; linarith [hs_strip.1])
        have him_half : |(s / 2).im| = τ / 2 := by dsimp only [τ]; simp [abs_div]
        have hg := hg1 (s / 2) (by simp; linarith [hs_strip.1]) (by simp; linarith [hs_strip.2])
          (by rw [him_half]; linarith)
        rw [him_half, show -(Real.pi * (τ / 2) / 2) = -(Real.pi * τ / 4) by ring] at hg
        have hpow_le : (τ / 2) ^ Ng1 ≤ (τ + 4) ^ Ng1 :=
          pow_le_pow_left₀ (by positivity) (by linarith) Ng1
        calc Real.pi ^ ((-s / 2).re) * ‖Complex.Gamma (s / 2)‖
            ≤ Real.pi ^ (1 / 4 : ℝ) * (Cg1 * (τ / 2) ^ Ng1 * Real.exp (-(Real.pi * τ / 4))) :=
              mul_le_mul hpi_le hg (norm_nonneg _) (by positivity)
          _ ≤ Real.pi ^ (1 / 4 : ℝ) * (Cg1 * (τ + 4) ^ Ng1 * Real.exp (-(Real.pi * τ / 4))) := by
              gcongr
          _ = Real.pi ^ (1 / 4 : ℝ) * Cg1 * (τ + 4) ^ Ng1 * Real.exp (-(Real.pi * τ / 4)) := by ring
      -- Bound `‖Complex.Gammaℝ (s - 1)‖`.
      have hΓs1 : ‖Complex.Gammaℝ (s - 1)‖ ≤
          Real.pi ^ (3 / 4 : ℝ) * Cg2 * (τ + 4) ^ Ng2 * Real.exp (-(Real.pi * τ / 4)) := by
        rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        have hpi_le : Real.pi ^ ((-(s - 1) / 2).re) ≤ Real.pi ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
            (by simp; linarith [hs_strip.1])
        have him_half : |((s - 1) / 2).im| = τ / 2 := by dsimp only [τ]; simp [abs_div]
        have hg := hg2 ((s - 1) / 2) (by simp; linarith [hs_strip.1])
          (by simp; linarith [hs_strip.2]) (by rw [him_half]; linarith)
        rw [him_half, show -(Real.pi * (τ / 2) / 2) = -(Real.pi * τ / 4) by ring] at hg
        have hpow_le : (τ / 2) ^ Ng2 ≤ (τ + 4) ^ Ng2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) Ng2
        calc Real.pi ^ ((-(s - 1) / 2).re) * ‖Complex.Gamma ((s - 1) / 2)‖
            ≤ Real.pi ^ (3 / 4 : ℝ) * (Cg2 * (τ / 2) ^ Ng2 * Real.exp (-(Real.pi * τ / 4))) :=
              mul_le_mul hpi_le hg (norm_nonneg _) (by positivity)
          _ ≤ Real.pi ^ (3 / 4 : ℝ) * (Cg2 * (τ + 4) ^ Ng2 * Real.exp (-(Real.pi * τ / 4))) := by
              gcongr
          _ = Real.pi ^ (3 / 4 : ℝ) * Cg2 * (τ + 4) ^ Ng2 * Real.exp (-(Real.pi * τ / 4)) := by ring
      have hdec1 := RHTower.pow_mul_exp_neg_le_div (N := Ng1 + NF) hK1 hτ0
      have hdec2 := RHTower.pow_mul_exp_neg_le_div (N := Ng2) hK2 hτ0
      dsimp only [τ] at hdec1 hdec2
      rw [sq_abs] at hdec1 hdec2
      rw [hE_eq s hs0 hs1,
        show Complex.Gammaℝ s * F s - (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) =
          Complex.Gammaℝ s * (F s - α) - β * Complex.Gammaℝ (s - 1) by ring]
      have hterm1 : ‖Complex.Gammaℝ s * (F s - α)‖ ≤ C_high1 * (K1 / (1 + s.im ^ 2)) := by
        rw [norm_mul]
        calc ‖Complex.Gammaℝ s‖ * ‖F s - α‖
            ≤ (Real.pi ^ (1 / 4 : ℝ) * Cg1 * (τ + 4) ^ Ng1 * Real.exp (-(Real.pi * τ / 4))) *
                ((CF + ‖α‖) * (τ + 4) ^ NF) :=
              mul_le_mul hΓs hF_sub_α (norm_nonneg _) (by positivity)
          _ = C_high1 * ((|s.im| + 4) ^ (Ng1 + NF) * Real.exp (-(Real.pi * |s.im| / 4))) := by
              dsimp only [C_high1, τ]; rw [pow_add]; ring
          _ ≤ C_high1 * (K1 / (1 + s.im ^ 2)) :=
              mul_le_mul_of_nonneg_left hdec1 (by dsimp only [C_high1]; positivity)
      have hterm2 : ‖β * Complex.Gammaℝ (s - 1)‖ ≤ C_high2 * (K2 / (1 + s.im ^ 2)) := by
        rw [norm_mul]
        calc ‖β‖ * ‖Complex.Gammaℝ (s - 1)‖
            ≤ ‖β‖ * (Real.pi ^ (3 / 4 : ℝ) * Cg2 * (τ + 4) ^ Ng2 * Real.exp (-(Real.pi * τ / 4))) :=
              mul_le_mul_of_nonneg_left hΓs1 (norm_nonneg _)
          _ = C_high2 * ((|s.im| + 4) ^ Ng2 * Real.exp (-(Real.pi * |s.im| / 4))) := by
              dsimp only [C_high2, τ]; ring
          _ ≤ C_high2 * (K2 / (1 + s.im ^ 2)) :=
              mul_le_mul_of_nonneg_left hdec2 (by dsimp only [C_high2]; positivity)
      calc ‖Complex.Gammaℝ s * (F s - α) - β * Complex.Gammaℝ (s - 1)‖
          ≤ ‖Complex.Gammaℝ s * (F s - α)‖ + ‖β * Complex.Gammaℝ (s - 1)‖ := norm_sub_le _ _
        _ ≤ C_high1 * (K1 / (1 + s.im ^ 2)) + C_high2 * (K2 / (1 + s.im ^ 2)) :=
            add_le_add hterm1 hterm2
        _ = (C_high1 * K1 + C_high2 * K2) / (1 + s.im ^ 2) := by ring
        _ ≤ C_tot / (1 + s.im ^ 2) :=
            div_le_div_of_nonneg_right (le_max_right _ _) hden_pos.le
    · have hsmall : |s.im| < 4 := lt_of_not_ge ht
      have hsK : s ∈ K_box := Complex.mem_reProdIm.mpr ⟨hs_strip, abs_le.mp hsmall.le⟩
      have hsq : s.im ^ 2 ≤ 16 := by nlinarith [sq_abs s.im, abs_nonneg s.im, hsmall.le]
      calc ‖E s‖ ≤ max M_box 0 := (hM_box s hsK).trans (le_max_left _ _)
        _ ≤ (17 * max M_box 0) / (1 + s.im ^ 2) := by
            rw [le_div_iff₀ hden_pos]
            nlinarith [mul_le_mul_of_nonneg_left hsq (le_max_right M_box 0)]
        _ ≤ C_tot / (1 + s.im ^ 2) :=
            div_le_div_of_nonneg_right (le_max_left _ _) hden_pos.le
  -- Apply `converse_theta_relation` to `θ₁ = coeffTheta a` and `θ₂ u = coeffTheta b ((1 / Q ^ 2) * u)`.
  set θ₂ : ℝ → ℂ := fun u => coeffTheta b ((1 / Q ^ 2) * u)
  have hθ₁_cont : ContinuousOn (coeffTheta a) (Ioi 0) :=
    continuousOn_coeffTheta a (ha_sum 2 (by norm_num))
  have hθ₂_cont : ContinuousOn θ₂ (Ioi 0) :=
    (continuousOn_coeffTheta b (hb_sum 2 (by norm_num))).comp
      (continuousOn_const.mul continuousOn_id) (fun u (hu : 0 < u) => mul_pos hQ2_inv hu)
  have hθ₁_mel : MellinConvergent (coeffTheta a) (3 / 4) :=
    mellinConvergent_coeffTheta a ha_sum (by norm_num) (by norm_num)
  have hθ₂_mel : MellinConvergent θ₂ (3 / 4) :=
    (MellinConvergent.comp_mul_left hQ2_inv).mpr
      (mellinConvergent_coeffTheta b hb_sum (by norm_num) (by norm_num))
  refine converse_theta_relation hθ₁_cont hθ₂_cont hθ₁_mel hθ₂_mel hE_diff hE_decay
    (fun s hs => ?_) (fun s hs => ?_) hx
  · -- Right line `Re s = 3 / 2`.
    have hs_gt1 : 1 < s.re := by rw [hs]; norm_num
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    rw [mellin_coeffTheta a ha_sum hs_gt1]
    have hdir : coeffDirichlet a s = F s := by
      unfold coeffDirichlet
      rw [hD.dirichlet_eq s hs_gt1]
      refine tsum_congr fun n => ?_
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      push_cast; ring
    rw [hdir, hE_eq s hs0 hs1]; ring
  · -- Left line `Re s = -1 / 2`.
    have hs_lt0 : s.re < 0 := by rw [hs]; norm_num
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have h1s_gt1 : 1 < (1 - s).re := by simp [hs]; norm_num
    rw [show θ₂ = fun u => coeffTheta b ((1 / Q ^ 2) * u) from rfl,
      mellin_comp_mul_left _ _ hQ2_inv, smul_eq_mul,
      mellin_coeffTheta b hb_sum (s := 1 - s) h1s_gt1]
    have hQ_pow_eq : ((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (((1 / Q ^ 2 : ℝ) : ℂ) ^ (-((1 - s) / 2))) = (Q : ℂ) ^ ((1 / 2 : ℂ) - s) := by
      have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
      have hQ20 : ((1 / Q ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ2_inv.ne'
      have h1 : ((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          Complex.exp (((-(1 / 2 : ℝ) * Real.log Q : ℝ) : ℂ)) := by
        rw [Real.rpow_def_of_pos hQ, Complex.ofReal_exp]
        congr 1; push_cast; ring
      have hlog_inv : Real.log (1 / Q ^ 2) = -2 * Real.log Q := by
        rw [one_div, Real.log_inv, Real.log_pow]; ring
      rw [h1, Complex.cpow_def_of_ne_zero hQ20, Complex.cpow_def_of_ne_zero hQ0,
        ← Complex.ofReal_log hQ2_inv.le, ← Complex.ofReal_log hQ.le, hlog_inv,
        ← Complex.exp_add]
      congr 1; push_cast; ring
    have hΓs_ne : Complex.Gammaℝ s ≠ 0 := by
      have hpt : (((-1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I) = s := by
        have := Complex.re_add_im s; rwa [hs] at this
      rw [← hpt]
      exact Gammaℝ_vertical_ne_zero (by norm_num) (by norm_num)
    have hG_b : coeffDirichlet b (1 - s) = ∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) := by
      unfold coeffDirichlet
      refine tsum_congr fun m => ?_
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      push_cast; ring
    have hrefl_mul : Complex.Gammaℝ s * F s =
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) * Complex.Gammaℝ (1 - s) * coeffDirichlet b (1 - s) := by
      rw [hD.crossHeight_refl s hs_lt0, ← hG_b]
      unfold zetaChi
      field_simp [hΓs_ne]
    calc (ω * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          ((((1 / Q ^ 2 : ℝ) : ℂ) ^ (-((1 - s) / 2))) *
            (Complex.Gammaℝ (1 - s) * coeffDirichlet b (1 - s)))
        = ω * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((1 / Q ^ 2 : ℝ) : ℂ) ^ (-((1 - s) / 2)))) *
            Complex.Gammaℝ (1 - s) * coeffDirichlet b (1 - s) := by ring
      _ = ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) * Complex.Gammaℝ (1 - s) * coeffDirichlet b (1 - s) := by
            rw [hQ_pow_eq]
      _ = Complex.Gammaℝ s * F s := hrefl_mul.symm
      _ = E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by
            rw [hE_eq s hs0 hs1]; ring

private theorem hasSum_integral_rescaled_dual_coeffTheta_mul_exp (b : ℕ → ℂ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t) :
    HasSum (fun n : ℕ => b (n + 1) *
        ((1 / t * Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) / Q) * t)) : ℝ) : ℂ))
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹) *
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun n x => b (n + 1) * ((x ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(Real.pi * (((n : ℝ) + 1) / Q) ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ)
  have hm : ∀ n : ℕ, 0 < ((n : ℝ) + 1) / Q := fun _ => by positivity
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((integrableOn_rpow_neg_half_mul_exp_theta_dual (hm n) ht).ofReal).const_mul _
  have hFnorm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖F n x‖ =
      ‖b (n + 1)‖ * (1 / t * Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) / Q) * t))) := by
    intro n
    have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖F n x‖ = ‖b (n + 1)‖ * (x ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(Real.pi * (((n : ℝ) + 1) / Q) ^ 2 / x) - Real.pi * t ^ 2 * x)) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, MeasureTheory.integral_const_mul,
      integral_rpow_neg_half_mul_exp_theta_dual (hm n) ht]
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp_rw [hFnorm]
    refine ((hb 2 (by norm_num)).mul_left (Q ^ 2 / (2 * Real.pi ^ 2 * t ^ 3))).of_nonneg_of_le
      (fun _ => by positivity) fun n => ?_
    have hy : 0 < 2 * Real.pi * (((n : ℝ) + 1) / Q) * t := by positivity
    have he := exp_neg_le_two_div_sq hy
    rw [show (((n : ℝ) + 1) ^ (2 : ℝ)) = ((n : ℝ) + 1) ^ 2 by norm_cast]
    calc ‖b (n + 1)‖ * (1 / t * Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) / Q) * t)))
        ≤ ‖b (n + 1)‖ * (1 / t * (2 / (2 * Real.pi * (((n : ℝ) + 1) / Q) * t) ^ 2)) := by gcongr
      _ = Q ^ 2 / (2 * Real.pi ^ 2 * t ^ 3) * (‖b (n + 1)‖ / ((n : ℝ) + 1) ^ 2) := by
          field_simp [hQ.ne', ht.ne', Real.pi_ne_zero]
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsum
  have hval : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), F n x =
      b (n + 1) * ((1 / t * Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) / Q) * t)) : ℝ) : ℂ) := by
    intro n
    dsimp only [F]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
      integral_rpow_neg_half_mul_exp_theta_dual (hm n) ht]
  have hsumF : ∀ x ∈ Ioi (0 : ℝ), ∑' n : ℕ, F n x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹) *
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
    rw [coeffTheta, ← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    dsimp only [F]
    rw [hcpow]
    have hexp_eq : -(Real.pi * (((n : ℝ) + 1) / Q) ^ 2 / x) - Real.pi * t ^ 2 * x =
        -Real.pi * ((n : ℝ) + 1) ^ 2 * ((1 / Q ^ 2) * x⁻¹) + -(Real.pi * t ^ 2) * x := by
      field_simp [hQ.ne', hx0.ne']; ring
    rw [hexp_eq, Real.exp_add]
    push_cast; ring
  simp_rw [hval] at h
  rwa [setIntegral_congr_fun measurableSet_Ioi hsumF] at h

private theorem integrableOn_rescaled_dual_coeffTheta_mul_exp (b : ℕ → ℂ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹) *
      ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) := by
  have hS : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) :=
    hb _ (by norm_num)
  set S : ℝ := ∑' n : ℕ, ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) with hSdef
  have hdom : IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) *
      Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl (by positivity)
  refine (hdom.const_mul (Q ^ 2 * S / Real.pi)).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    refine (((continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')).mul ?_).mul
      (by fun_prop : Continuous fun x : ℝ =>
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)).continuousAt).continuousWithinAt
    have hmul_inv : ContinuousAt (fun y : ℝ => (1 / Q ^ 2) * y⁻¹) x :=
      continuousAt_const.mul (continuousAt_inv₀ hx0.ne')
    exact ContinuousAt.comp (g := coeffTheta b) (f := fun y : ℝ => (1 / Q ^ 2) * y⁻¹)
      ((continuousOn_coeffTheta b (by simpa using hS)).continuousAt
        (Ioi_mem_nhds (by positivity : 0 < (1 / Q ^ 2) * x⁻¹))) hmul_inv
  · have hx0 : (0 : ℝ) < x := hx
    have hθ := norm_coeffTheta_le b (by positivity : 0 < (1 / Q ^ 2) * x⁻¹) zero_le_one le_rfl hS
    rw [← hSdef, Real.rpow_neg_one] at hθ
    have hinv : (Real.pi * ((1 / Q ^ 2) * x⁻¹))⁻¹ = Q ^ 2 * x / Real.pi := by
      field_simp [hQ.ne', hx0.ne', Real.pi_ne_zero]
    rw [hinv] at hθ
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one,
      show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
    have hpow : x ^ (-(1 / 2 : ℝ)) * x = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hx0.ne']; norm_num
    calc x ^ (-(1 / 2 : ℝ)) * ‖coeffTheta b ((1 / Q ^ 2) * x⁻¹)‖ * Real.exp (-(Real.pi * t ^ 2) * x)
        ≤ x ^ (-(1 / 2 : ℝ)) * (Q ^ 2 * x / Real.pi * S) * Real.exp (-(Real.pi * t ^ 2) * x) := by
          gcongr
      _ = Q ^ 2 * S / Real.pi * ((x ^ (-(1 / 2 : ℝ)) * x) * Real.exp (-(Real.pi * t ^ 2) * x)) := by ring
      _ = Q ^ 2 * S / Real.pi * (x ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi * t ^ 2) * x)) := by rw [hpow]

/-- **Arbitrary-conductor Hamburger periodicity identity on `Re t > 0`:**
under the rescaled theta transformation law at conductor `Q > 0`, the Hamburger partial-fraction
series satisfies `L_a(t + i Q) - L_a(t) = α / (π (t + i Q)) - α / (π t)` throughout `Re t > 0`. -/
theorem hamburgerSeries_periodic_conductor (a b : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {Q : ℝ} (hQ : 0 < Q) {ε α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹)) +
        α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a (t + (Q : ℂ) * I) - hamburgerSeries a t =
      α / Real.pi / (t + (Q : ℂ) * I) - α / Real.pi / t := by
  have hQ0c : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  -- Step 1: Identity on positive real axis `u > 0`.
  have hreal : ∀ u : ℝ, 0 < u →
      hamburgerSeries a u =
        ε * (∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * ((u : ℂ) / (Q : ℂ))))) +
          α / (Real.pi * (u : ℂ)) + β := by
    intro u hu
    set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * u ^ 2) * x) : ℝ) : ℂ)
    have hB : 0 < Real.pi * u ^ 2 := by positivity
    have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
    have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
        ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * u ^ 2) * x)) : ℝ) : ℂ) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      dsimp only [e]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
    have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
      have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
          Real.exp (-(Real.pi * u ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
      have h1 : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
          Real.exp (-((Real.pi * u ^ 2) * x))) (Ioi 0) := by
        simpa only [Real.rpow_one, neg_mul] using h
      exact IntegrableOn.congr_fun h1.ofReal (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
    have hD_int := integrableOn_rescaled_dual_coeffTheta_mul_exp b hb hQ hu
    have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * u ^ 2) : ℝ) : ℂ) := by
      dsimp only [e]; rw [integral_complex_ofReal, HTGeometry.integral_Ioi_exp_neg_mul hB]
    have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / u : ℝ) : ℂ) := by
      rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
        integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq hu]
    have hpt : ∀ x ∈ Ioi (0 : ℝ), coeffTheta a x * e x =
        ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹) * e x) +
          (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) := fun x hx => by
      rw [htheta x hx]; ring
    have hsplit : ∫ x in Ioi (0 : ℝ), coeffTheta a x * e x =
        ε * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹) * e x) +
          (α * ∫ x in Ioi (0 : ℝ), e x) +
            β * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x := by
      have hD_int' : IntegrableOn (fun x : ℝ =>
          (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹) * e x) (Ioi 0) :=
        hD_int
      have h1 := MeasureTheory.integral_add (hD_int'.const_mul ε)
        ((he_int.const_mul α).add (hhe_int.const_mul β))
      have h2 := MeasureTheory.integral_add (he_int.const_mul α) (hhe_int.const_mul β)
      dsimp only [Pi.add_apply] at h1 h2
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, h1, h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      ring
    have hL := (hasSum_integral_coeffTheta_mul_exp a ha hu).tsum_eq
    have hD := (hasSum_integral_rescaled_dual_coeffTheta_mul_exp b hb hQ hu).tsum_eq
    rw [hsplit, ← hD, hI0, hIh] at hL
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hham : hamburgerSeries a u = (u : ℂ) * ∑' n : ℕ,
        a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + u ^ 2) : ℝ) : ℂ) := by
      rw [hamburgerSeries, ← tsum_mul_left]
      exact tsum_congr fun n => by push_cast; ring
    have hdual : ∑' n : ℕ, b (n + 1) *
        ((1 / u * Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) / Q) * u)) : ℝ) : ℂ) =
        (1 / (u : ℂ)) * ∑' n : ℕ,
          b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * ((u : ℂ) / (Q : ℂ)))) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      push_cast
      have hexp_arg : ((-(2 * (Real.pi : ℂ) * (((n : ℂ) + 1) / (Q : ℂ)) * (u : ℂ)))) =
          -(2 * Real.pi * ((n : ℂ) + 1) * ((u : ℂ) / (Q : ℂ))) := by ring
      rw [hexp_arg]; ring
    rw [hham, hL, hdual]
    push_cast; field_simp [hu0, hπ]
  -- Step 2: Analytic continuation to `U = {z : ℂ | 0 < z.re}`.
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa using summable_sq_of_forall_rpow ha
  have hf_an : AnalyticOnNhd ℂ (hamburgerSeries a) U :=
    (differentiableOn_hamburgerSeries ha2).analyticOnNhd hUo
  set R_rhs : ℂ → ℂ := fun z =>
    ε * (∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (z / (Q : ℂ))))) +
      α / (Real.pi * z) + β
  have hg_an : AnalyticOnNhd ℂ R_rhs U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    have hcomp_exp : DifferentiableOn ℂ
        (fun z : ℂ => ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (z / (Q : ℂ))))) U :=
      (differentiableOn_expDualSeries (summable_sq_of_forall_rpow hb)).comp
        (differentiableOn_id.div_const (Q : ℂ))
        (fun z (hz : 0 < z.re) => by
          show 0 < (z / (Q : ℂ)).re
          rw [Complex.div_ofReal_re]
          exact div_pos hz hQ)
    refine ((hcomp_exp.const_mul ε).add ?_).add (differentiableOn_const β)
    refine (differentiableOn_const α).div (by fun_prop) fun z (hz : 0 < z.re) =>
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) fun h0 => by
        rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have h1U : (1 : ℂ) ∈ U := by show 0 < (1 : ℂ).re; simp
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), hamburgerSeries a z = R_rhs z := by
    set u_seq : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hlim : Tendsto u_seq atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
        rw [add_zero] at h1
        exact ((Complex.continuous_ofReal.tendsto 1).comp h1).congr fun _ => by simp [u_seq]
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u_seq]
        intro heq
        have h' : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast heq
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    exact hlim.frequently (Frequently.of_forall fun k => hreal _ (by positivity))
  have heq_U : ∀ z : ℂ, 0 < z.re → hamburgerSeries a z = R_rhs z :=
    fun z hz => hf_an.eqOn_of_preconnected_of_frequently_eq hg_an
      (convex_halfSpace_re_gt 0).isPreconnected h1U hfreq hz
  -- Step 3: Subtract at `t + (Q : ℂ) * I` and `t`.
  have ht' : 0 < (t + (Q : ℂ) * I).re := by simpa using ht
  rw [heq_U _ ht', heq_U _ ht]
  dsimp only [R_rhs]
  have hper : (∑' n : ℕ, b (n + 1) *
        cexp (-(2 * Real.pi * ((n : ℂ) + 1) * ((t + (Q : ℂ) * I) / (Q : ℂ))))) =
      ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (t / (Q : ℂ)))) := by
    refine tsum_congr fun n => ?_
    have hdiv : (t + (Q : ℂ) * I) / (Q : ℂ) = t / (Q : ℂ) + I := by
      field_simp [hQ0c]
    rw [hdiv, show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (t / (Q : ℂ) + I)) =
      -(2 * Real.pi * ((n : ℂ) + 1) * (t / (Q : ℂ))) +
        ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, div_div, div_div]
  ring

/-- `hamburgerSeries a` is continuous at `(y : ℂ) * I` whenever `|y|` is not a positive integer. -/
theorem continuousAt_hamburgerSeries_of_not_nat_im {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {y : ℝ} (hy : ∀ n : ℕ, 1 ≤ n → |y| ≠ (n : ℝ)) :
    ContinuousAt (hamburgerSeries a) ((y : ℂ) * I) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set N₀ : ℕ := 2 * Nat.ceil |y| + 4
  set S : Finset ℕ := Finset.Icc 1 N₀
  have h1S : 1 ∈ S := Finset.mem_Icc.mpr ⟨le_rfl, by dsimp only [N₀]; omega⟩
  set d₀ : ℝ := S.inf' ⟨1, h1S⟩ (fun m => |(m : ℝ) - (|y|)|)
  have hd₀_pos : 0 < d₀ := by
    rw [Finset.lt_inf'_iff]
    intro m hm
    exact abs_pos.mpr (sub_ne_zero.mpr (hy m (Finset.mem_Icc.mp hm).1).symm)
  set r : ℝ := min (1 / 4) (d₀ / 2)
  have hr_pos : 0 < r := lt_min (by norm_num) (half_pos hd₀_pos)
  set c_den : ℝ := min (3 / 4) (r ^ 2 / (N₀ : ℝ) ^ 2)
  have hc_pos : 0 < c_den := by
    have hN₀_pos : (0 : ℝ) < (N₀ : ℝ) := by dsimp only [N₀]; positivity
    exact lt_min (by norm_num) (by positivity)
  have hden_lb : ∀ n : ℕ, ∀ t ∈ Metric.closedBall ((y : ℂ) * I) r,
      c_den * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ := by
    intro n t ht
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    set η : ℂ := t - (y : ℂ) * I
    have ht_eq : t = (y : ℂ) * I + η := by dsimp only [η]; ring
    have hη_le : ‖η‖ ≤ r := ht
    have hr_q : r ≤ 1 / 4 := min_le_left _ _
    have hr_d : r ≤ d₀ / 2 := min_le_right _ _
    by_cases hle : n + 1 ≤ N₀
    · -- Small `n + 1 ≤ N₀`: factor `((n + 1) - t * I) * ((n + 1) + t * I)`.
      have hm_mem : n + 1 ∈ S := Finset.mem_Icc.mpr ⟨Nat.succ_pos n, hle⟩
      have hd_le : d₀ ≤ |((n + 1 : ℕ) : ℝ) - (|y|)| :=
        Finset.inf'_le (f := fun m : ℕ => |(m : ℝ) - (|y|)|) hm_mem
      have hfac : ((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2 =
          (((n + 1 : ℕ) : ℂ) - t * I) * (((n + 1 : ℕ) : ℂ) + t * I) := by
        linear_combination t ^ 2 * Complex.I_sq
      have habs_tri : ∀ {u : ℝ}, 0 ≤ u → ∀ v : ℝ, |u - (|v|)| ≤ |u - v| := fun {u} hu v => by
        have h1 := abs_sub_abs_le_abs_sub u v
        have h2 := abs_sub_abs_le_abs_sub v u
        rw [abs_of_nonneg hu] at h1 h2
        rw [abs_sub_comm v u] at h2
        exact abs_le.mpr ⟨by linarith, h1⟩
      have hf1 : r ≤ ‖((n + 1 : ℕ) : ℂ) - t * I‖ := by
        rw [ht_eq]
        have he1 : ((n + 1 : ℕ) : ℂ) - ((y : ℂ) * I + η) * I =
            ((((n + 1 : ℕ) : ℝ) + y : ℝ) : ℂ) - η * I := by
          push_cast; linear_combination -(y : ℂ) * Complex.I_sq
        rw [he1]
        have htri := norm_sub_norm_le ((((n + 1 : ℕ) : ℝ) + y : ℝ) : ℂ) (η * I)
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one] at htri
        have habs_ge : |((n + 1 : ℕ) : ℝ) - (|y|)| ≤ |((n + 1 : ℕ) : ℝ) + y| := by
          have h := habs_tri (Nat.cast_nonneg (n + 1)) (-y)
          rwa [abs_neg, sub_neg_eq_add] at h
        linarith
      have hf2 : r ≤ ‖((n + 1 : ℕ) : ℂ) + t * I‖ := by
        rw [ht_eq]
        have he2 : ((n + 1 : ℕ) : ℂ) + ((y : ℂ) * I + η) * I =
            ((((n + 1 : ℕ) : ℝ) - y : ℝ) : ℂ) + η * I := by
          push_cast; linear_combination (y : ℂ) * Complex.I_sq
        rw [he2, show ((((n + 1 : ℕ) : ℝ) - y : ℝ) : ℂ) + η * I =
          ((((n + 1 : ℕ) : ℝ) - y : ℝ) : ℂ) - (-(η * I)) by ring]
        have htri := norm_sub_norm_le ((((n + 1 : ℕ) : ℝ) - y : ℝ) : ℂ) (-(η * I))
        rw [Complex.norm_real, Real.norm_eq_abs, norm_neg, norm_mul, norm_I, mul_one] at htri
        have habs_ge : |((n + 1 : ℕ) : ℝ) - (|y|)| ≤ |((n + 1 : ℕ) : ℝ) - y| :=
          habs_tri (Nat.cast_nonneg (n + 1)) y
        linarith
      have hr2 : r ^ 2 ≤ ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ := by
        rw [hfac, norm_mul, pow_two]
        exact mul_le_mul hf1 hf2 hr_pos.le (norm_nonneg _)
      have hn_le_N : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle) 2
      have hN₀_pos : (0 : ℝ) < (N₀ : ℝ) ^ 2 := by dsimp only [N₀]; positivity
      calc c_den * ((n + 1 : ℕ) : ℝ) ^ 2
          ≤ (r ^ 2 / (N₀ : ℝ) ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ (r ^ 2 / (N₀ : ℝ) ^ 2) * (N₀ : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hn_le_N (by positivity)
        _ = r ^ 2 := div_mul_cancel₀ _ hN₀_pos.ne'
        _ ≤ ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ := hr2
    · -- Large `n + 1 > N₀ = 2 * ⌈|y|⌉₊ + 4`: `‖t‖ ≤ (n + 1) / 2`.
      have hgt : N₀ < n + 1 := Nat.lt_of_not_ge hle
      have hy_ceil : |y| ≤ (Nat.ceil |y| : ℝ) := Nat.le_ceil |y|
      have hn_R : (2 : ℝ) * |y| + 4 ≤ ((n + 1 : ℕ) : ℝ) := by
        have hNR : (N₀ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hgt.le
        dsimp only [N₀] at hNR
        push_cast at hNR ⊢
        linarith
      have ht_norm : ‖t‖ ≤ ((n + 1 : ℕ) : ℝ) / 2 := by
        rw [ht_eq]
        have htri := norm_add_le ((y : ℂ) * I) η
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at htri
        linarith
      have ht_sq : ‖t ^ 2‖ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 / 4 := by
        rw [norm_pow]
        nlinarith [norm_nonneg t]
      have h1 : ‖((n + 1 : ℕ) : ℂ) ^ 2‖ = ((n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [norm_pow, Complex.norm_natCast]
      have hsub := norm_sub_le (((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2) (t ^ 2)
      rw [add_sub_cancel_right, h1] at hsub
      calc c_den * ((n + 1 : ℕ) : ℝ) ^ 2
          ≤ (3 / 4 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ := by linarith
  set R_ball : ℝ := |y| + r
  set K_maj : ℝ := R_ball / (Real.pi * c_den)
  have hcont : ContinuousOn (hamburgerSeries a) (Metric.closedBall ((y : ℂ) * I) r) := by
    refine continuousOn_tsum (fun n => ?_) (ha.mul_left K_maj) (fun n t ht => ?_)
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => mul_ne_zero hπ ?_
      have hpos : 0 < ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ :=
        lt_of_lt_of_le (by positivity) (hden_lb n t ht)
      exact norm_pos_iff.mp hpos
    · have hden_pos : 0 < ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ :=
        lt_of_lt_of_le (by positivity) (hden_lb n t ht)
      have ht_R : ‖t‖ ≤ R_ball := by
        rw [Metric.mem_closedBall, dist_eq_norm] at ht
        have htri := norm_le_norm_add_norm_sub' t ((y : ℂ) * I)
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at htri
        dsimp only [R_ball]; linarith
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, div_le_iff₀ (mul_pos Real.pi_pos hden_pos)]
      calc ‖a (n + 1)‖ * ‖t‖
          ≤ ‖a (n + 1)‖ * R_ball := mul_le_mul_of_nonneg_left ht_R (norm_nonneg _)
        _ = K_maj * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Real.pi * (c_den * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
            dsimp only [K_maj]; field_simp [Real.pi_ne_zero, hc_pos.ne']
        _ ≤ K_maj * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Real.pi * ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖) := by
            gcongr; exact hden_lb n t ht
  exact hcont.continuousAt (Metric.closedBall_mem_nhds _ hr_pos)

/-- Residue of `hamburgerSeries a` at `-(k : ℂ) * I` (`k ≥ 1`) equals `a k / (2π)`. -/
theorem tendsto_add_mul_hamburgerSeries {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun t => (t + (k : ℂ) * I) * hamburgerSeries a t) (𝓝[≠] (-((k : ℂ) * I)))
      (𝓝 (a k / (2 * Real.pi))) := by
  have hodd : ∀ t : ℂ, hamburgerSeries a (-t) = -hamburgerSeries a t := by
    intro t
    unfold hamburgerSeries
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    rw [neg_sq]; ring
  have hneg_map : Tendsto (fun t : ℂ => -t) (𝓝[≠] (-((k : ℂ) * I))) (𝓝[≠] ((k : ℂ) * I)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc := continuous_neg.tendsto (-((k : ℂ) * I))
      rw [neg_neg] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro h
      exact ht (by linear_combination -h)
  refine ((tendsto_sub_mul_hamburgerSeries ha hk).comp hneg_map).congr fun t => ?_
  dsimp only [Function.comp_def]
  rw [hodd t]
  ring

/-- Helper extracting conductor annihilation and `q`-periodic evenness from the rescaled theta law. -/
private theorem coeff_laws_of_rescaled_theta_relation {a b : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {Q : ℝ} (hQ : 0 < Q) {ε α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹)) +
        α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    ((∀ q : ℕ, 1 ≤ q → Q ≠ (q : ℝ)) → ∀ n : ℕ, 1 ≤ n → a n = 0) ∧
    (∀ q : ℕ, 1 ≤ q → Q = (q : ℝ) →
      a q = -2 * α ∧
      (∀ n : ℕ, 1 ≤ n → a (n + q) = a n) ∧
      (∀ k : ℕ, 1 ≤ k → k < q → a (q - k) = a k)) := by
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa using summable_sq_of_forall_rpow ha
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  set c : ℂ := α / Real.pi
  have hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + (Q : ℂ) * I) - hamburgerSeries a t =
        c / (t + (Q : ℂ) * I) - c / t :=
    fun _ ht => hamburgerSeries_periodic_conductor a b ha hb hQ htheta ht
  have hQ_ne0 : (Q : ℂ) * I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hQ.ne') Complex.I_ne_zero
  -- Common limit of `t * (c / (t + Q * I) - c / t)` at `0` on `Re t > 0`.
  have hrhs_zero : Tendsto (fun t : ℂ => t * (c / (t + (Q : ℂ) * I) - c / t))
      (𝓝[{t : ℂ | 0 < t.re}] 0) (𝓝 (-c)) := by
    have hc_at0 : Tendsto (fun t : ℂ => t * (c / (t + (Q : ℂ) * I)) - c) (𝓝 (0 : ℂ))
        (𝓝 (0 * (c / (0 + (Q : ℂ) * I)) - c)) :=
      ((continuous_id.tendsto 0).mul ((continuous_const.tendsto 0).div
        ((continuous_id.add continuous_const).tendsto 0) (by simpa using hQ_ne0))).sub
        tendsto_const_nhds
    simp only [zero_mul, zero_sub] at hc_at0
    refine (hc_at0.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t.re)
    have ht0 : t ≠ 0 := fun h => by rw [h, Complex.zero_re] at ht; exact lt_irrefl 0 ht
    field_simp [ht0]
  have hlhs_zero_2 : Tendsto (fun t : ℂ => t * hamburgerSeries a t)
      (𝓝[{t : ℂ | 0 < t.re}] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).mul
      ((tendsto_hamburgerSeries_zero ha2).mono_left nhdsWithin_le_nhds)
  constructor
  · -- Case 1: `Q` is not a positive integer.
    intro hQ_not_nat
    haveI hne0 := nhdsWithin_re_pos_neBot 0
    simp only [Complex.ofReal_zero, zero_mul] at hne0
    -- First deduce `c = 0` from `t → 0`.
    have hcont_Q : ContinuousAt (hamburgerSeries a) ((Q : ℂ) * I) := by
      refine continuousAt_hamburgerSeries_of_not_nat_im ha2 fun m hm => ?_
      rw [abs_of_pos hQ]
      exact hQ_not_nat m hm
    have hlhs_zero_1 : Tendsto (fun t : ℂ => t * hamburgerSeries a (t + (Q : ℂ) * I))
        (𝓝[{t : ℂ | 0 < t.re}] 0) (𝓝 0) := by
      have hadd0 : Tendsto (fun t : ℂ => t + (Q : ℂ) * I) (𝓝 0) (𝓝 ((Q : ℂ) * I)) := by
        simpa only [zero_add] using
          (by fun_prop : Continuous fun t : ℂ => t + (Q : ℂ) * I).tendsto (0 : ℂ)
      have hsh : Tendsto (fun t : ℂ => hamburgerSeries a (t + (Q : ℂ) * I)) (𝓝 0)
          (𝓝 (hamburgerSeries a ((Q : ℂ) * I))) :=
        hcont_Q.tendsto.comp hadd0
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).mul
        (hsh.mono_left nhdsWithin_le_nhds)
    have hc_eq0 : c = 0 := by
      have hdiff1 := hlhs_zero_1.sub hlhs_zero_2
      rw [sub_zero] at hdiff1
      have hdiff2 : Tendsto
          (fun t : ℂ => t * hamburgerSeries a (t + (Q : ℂ) * I) - t * hamburgerSeries a t)
          (𝓝[{t : ℂ | 0 < t.re}] 0) (𝓝 (-c)) := by
        refine hrhs_zero.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [← mul_sub, hper t ht]
      exact neg_eq_zero.mp (tendsto_nhds_unique hdiff2 hdiff1)
    -- Now for every `n ≥ 1`, `n + Q` is not a positive integer, so residue at `i n` vanishes.
    intro n hn
    haveI hnen := nhdsWithin_re_pos_neBot (n : ℝ)
    have hlen := nhdsWithin_re_pos_le_punctured (n : ℝ)
    simp only [Complex.ofReal_natCast] at hnen hlen
    have hcont_nQ : ContinuousAt (hamburgerSeries a) ((((n : ℝ) + Q : ℝ) : ℂ) * I) := by
      refine continuousAt_hamburgerSeries_of_not_nat_im ha2 fun m _ => ?_
      have hnQ_pos : 0 < (n : ℝ) + Q := by positivity
      rw [abs_of_pos hnQ_pos]
      intro heq
      rcases le_or_gt m n with hmn | hnm
      · have hm_le : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
        linarith
      · have hdiff_nat : m - n ≥ 1 := by omega
        apply hQ_not_nat (m - n) hdiff_nat
        rw [Nat.cast_sub hnm.le]
        linarith
    have hlim_shift0 : Tendsto
        (fun t : ℂ => (t - (n : ℂ) * I) * hamburgerSeries a (t + (Q : ℂ) * I))
        (𝓝[{t : ℂ | 0 < t.re}] ((n : ℂ) * I)) (𝓝 0) := by
      have hpt_eq : (n : ℂ) * I + (Q : ℂ) * I = (((n : ℝ) + Q : ℝ) : ℂ) * I := by
        push_cast; ring
      have hadd_n : Tendsto (fun t : ℂ => t + (Q : ℂ) * I)
          (𝓝 ((n : ℂ) * I)) (𝓝 ((((n : ℝ) + Q : ℝ) : ℂ) * I)) := by
        rw [← hpt_eq]
        exact (by fun_prop : Continuous fun t : ℂ => t + (Q : ℂ) * I).tendsto ((n : ℂ) * I)
      have hsh : Tendsto (fun t : ℂ => hamburgerSeries a (t + (Q : ℂ) * I))
          (𝓝 ((n : ℂ) * I)) (𝓝 (hamburgerSeries a ((((n : ℝ) + Q : ℝ) : ℂ) * I))) :=
        hcont_nQ.tendsto.comp hadd_n
      have hlin0 : Tendsto (fun t : ℂ => t - (n : ℂ) * I) (𝓝 ((n : ℂ) * I)) (𝓝 0) := by
        simpa only [sub_self] using
          (by fun_prop : Continuous fun t : ℂ => t - (n : ℂ) * I).tendsto ((n : ℂ) * I)
      simpa using (hlin0.mono_left nhdsWithin_le_nhds).mul (hsh.mono_left nhdsWithin_le_nhds)
    have hlim_self := (tendsto_sub_mul_hamburgerSeries ha2 hn).mono_left hlen
    have heq_zero : ∀ᶠ t in 𝓝[{t : ℂ | 0 < t.re}] ((n : ℂ) * I),
        (t - (n : ℂ) * I) * hamburgerSeries a (t + (Q : ℂ) * I) =
          (t - (n : ℂ) * I) * hamburgerSeries a t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hp := hper t ht
      rw [hc_eq0, zero_div, zero_div, sub_self, sub_eq_zero] at hp
      rw [hp]
    have hres0 := tendsto_nhds_unique (hlim_self.congr' (EventuallyEq.symm heq_zero)) hlim_shift0
    exact (div_eq_zero_iff.mp hres0).resolve_right h2π
  · -- Case 2: `Q = (q : ℝ)` for `q ≥ 1`.
    intro q hq1 hQ_eq
    have hQc : (Q : ℂ) = (q : ℂ) := by rw [hQ_eq]; simp
    -- 2a. `a q = -2 * α` from `t → 0`.
    have ha_q : a q = -2 * α := by
      haveI hne0 := nhdsWithin_re_pos_neBot 0
      have hle0 := nhdsWithin_re_pos_le_punctured 0
      simp only [Complex.ofReal_zero, zero_mul] at hne0 hle0
      have hsh_0 : Tendsto (fun t : ℂ => t + (Q : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] ((q : ℂ) * I)) := by
        rw [hQc]
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc_0 : Tendsto (fun t : ℂ => t + (q : ℂ) * I) (𝓝 0) (𝓝 ((q : ℂ) * I)) := by
            simpa only [zero_add] using
              (by fun_prop : Continuous fun t : ℂ => t + (q : ℂ) * I).tendsto (0 : ℂ)
          exact hc_0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
          exact fun h => ht (by linear_combination h)
      have hlhs_1 : Tendsto (fun t : ℂ => t * hamburgerSeries a (t + (Q : ℂ) * I))
          (𝓝[{t : ℂ | 0 < t.re}] 0) (𝓝 (a q / (2 * Real.pi))) := by
        refine (((tendsto_sub_mul_hamburgerSeries ha2 hq1).comp hsh_0).mono_left hle0).congr
          fun t => ?_
        dsimp only [Function.comp_def]
        rw [hQc]; ring_nf
      have hdiff1 := hlhs_1.sub hlhs_zero_2
      rw [sub_zero] at hdiff1
      have hdiff2 : Tendsto
          (fun t : ℂ => t * hamburgerSeries a (t + (Q : ℂ) * I) - t * hamburgerSeries a t)
          (𝓝[{t : ℂ | 0 < t.re}] 0) (𝓝 (-c)) := by
        refine hrhs_zero.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [← mul_sub, hper t ht]
      have huniq := tendsto_nhds_unique hdiff1 hdiff2
      have hc_mul : c * (2 * (Real.pi : ℂ)) = 2 * α := by
        dsimp only [c]
        field_simp [hπ]
      rw [div_eq_iff h2π, neg_mul, hc_mul] at huniq
      linear_combination huniq
    -- 2b. `a (n + q) = a n` for `n ≥ 1` from `t → i n`.
    have ha_per : ∀ n : ℕ, 1 ≤ n → a (n + q) = a n := by
      intro n hn
      haveI hnen := nhdsWithin_re_pos_neBot (n : ℝ)
      have hlen := nhdsWithin_re_pos_le_punctured (n : ℝ)
      simp only [Complex.ofReal_natCast] at hnen hlen
      have hsh_n : Tendsto (fun t : ℂ => t + (Q : ℂ) * I)
          (𝓝[≠] ((n : ℂ) * I)) (𝓝[≠] (((n + q : ℕ) : ℂ) * I)) := by
        rw [hQc]
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc_n :=
            (by fun_prop : Continuous fun t : ℂ => t + (q : ℂ) * I).tendsto ((n : ℂ) * I)
          have hpt : (n : ℂ) * I + (q : ℂ) * I = ((n + q : ℕ) : ℂ) * I := by push_cast; ring
          rw [hpt] at hc_n
          exact hc_n.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
          intro h; apply ht; push_cast at h; linear_combination h
      have hB : Tendsto
          (fun t : ℂ => (t - (n : ℂ) * I) * hamburgerSeries a (t + (Q : ℂ) * I))
          (𝓝[{t : ℂ | 0 < t.re}] ((n : ℂ) * I)) (𝓝 (a (n + q) / (2 * Real.pi))) := by
        refine (((tendsto_sub_mul_hamburgerSeries ha2 (n₀ := n + q) (by omega)).comp hsh_n).mono_left
          hlen).congr fun t => ?_
        dsimp only [Function.comp_def]
        rw [hQc]; push_cast; ring_nf
      have hA := (tendsto_sub_mul_hamburgerSeries ha2 hn).mono_left hlen
      have hrhs_n : Tendsto
          (fun t : ℂ => (t - (n : ℂ) * I) * (c / (t + (Q : ℂ) * I) - c / t))
          (𝓝[{t : ℂ | 0 < t.re}] ((n : ℂ) * I)) (𝓝 0) := by
        have hnI_ne : (n : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) I_ne_zero
        have hnqI_ne : (n : ℂ) * I + (Q : ℂ) * I ≠ 0 := by
          rw [hQc, show (n : ℂ) * I + (q : ℂ) * I = ((n + q : ℕ) : ℂ) * I by push_cast; ring]
          exact mul_ne_zero (by exact_mod_cast (by omega : n + q ≠ 0)) I_ne_zero
        have hc_cont : ContinuousAt
            (fun t : ℂ => (t - (n : ℂ) * I) * (c / (t + (Q : ℂ) * I) - c / t)) ((n : ℂ) * I) :=
          (continuousAt_id.sub continuousAt_const).mul
            ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hnqI_ne).sub
              (continuousAt_const.div continuousAt_id hnI_ne))
        simpa using hc_cont.tendsto.mono_left nhdsWithin_le_nhds
      have hdiff0 : Tendsto
          (fun t : ℂ => (t - (n : ℂ) * I) * hamburgerSeries a (t + (Q : ℂ) * I) -
            (t - (n : ℂ) * I) * hamburgerSeries a t)
          (𝓝[{t : ℂ | 0 < t.re}] ((n : ℂ) * I)) (𝓝 0) := by
        refine hrhs_n.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [← mul_sub, hper t ht]
      have huniq := tendsto_nhds_unique (hB.sub hA) hdiff0
      rw [← sub_div] at huniq
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp huniq).resolve_right h2π)
    -- 2c. `a (q - k) = a k` for `1 ≤ k < q` from `t → -i k`.
    have ha_even : ∀ k : ℕ, 1 ≤ k → k < q → a (q - k) = a k := by
      intro k hk hkq
      have hqk1 : 1 ≤ q - k := by omega
      haveI hnek := nhdsWithin_re_pos_neBot (-(k : ℝ))
      have hlek := nhdsWithin_re_pos_le_punctured (-(k : ℝ))
      simp only [Complex.ofReal_neg, Complex.ofReal_natCast, neg_mul] at hnek hlek
      have hsh_k : Tendsto (fun t : ℂ => t + (Q : ℂ) * I)
          (𝓝[≠] (-((k : ℂ) * I))) (𝓝[≠] (((q - k : ℕ) : ℂ) * I)) := by
        rw [hQc]
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc_k :=
            (by fun_prop : Continuous fun t : ℂ => t + (q : ℂ) * I).tendsto (-((k : ℂ) * I))
          have hpt : -((k : ℂ) * I) + (q : ℂ) * I = ((q - k : ℕ) : ℂ) * I := by
            rw [Nat.cast_sub hkq.le]; ring
          rw [hpt] at hc_k
          exact hc_k.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
          intro h; apply ht; rw [Nat.cast_sub hkq.le] at h; linear_combination h
      have hB : Tendsto
          (fun t : ℂ => (t + (k : ℂ) * I) * hamburgerSeries a (t + (Q : ℂ) * I))
          (𝓝[{t : ℂ | 0 < t.re}] (-((k : ℂ) * I))) (𝓝 (a (q - k) / (2 * Real.pi))) := by
        refine (((tendsto_sub_mul_hamburgerSeries ha2 hqk1).comp hsh_k).mono_left hlek).congr
          fun t => ?_
        dsimp only [Function.comp_def]
        rw [hQc, Nat.cast_sub hkq.le]; ring_nf
      have hA := (tendsto_add_mul_hamburgerSeries ha2 hk).mono_left hlek
      have hrhs_k : Tendsto
          (fun t : ℂ => (t + (k : ℂ) * I) * (c / (t + (Q : ℂ) * I) - c / t))
          (𝓝[{t : ℂ | 0 < t.re}] (-((k : ℂ) * I))) (𝓝 0) := by
        have hkI_ne : -((k : ℂ) * I) ≠ 0 :=
          neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast (by omega : k ≠ 0)) I_ne_zero)
        have hqkI_ne : -((k : ℂ) * I) + (Q : ℂ) * I ≠ 0 := by
          rw [hQc, show -((k : ℂ) * I) + (q : ℂ) * I = ((q - k : ℕ) : ℂ) * I by
            rw [Nat.cast_sub hkq.le]; ring]
          exact mul_ne_zero (by exact_mod_cast (by omega : q - k ≠ 0)) I_ne_zero
        have hc_cont : ContinuousAt
            (fun t : ℂ => (t + (k : ℂ) * I) * (c / (t + (Q : ℂ) * I) - c / t)) (-((k : ℂ) * I)) :=
          (continuousAt_id.add continuousAt_const).mul
            ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hqkI_ne).sub
              (continuousAt_const.div continuousAt_id hkI_ne))
        simpa using hc_cont.tendsto.mono_left nhdsWithin_le_nhds
      have hdiff0 : Tendsto
          (fun t : ℂ => (t + (k : ℂ) * I) * hamburgerSeries a (t + (Q : ℂ) * I) -
            (t + (k : ℂ) * I) * hamburgerSeries a t)
          (𝓝[{t : ℂ | 0 < t.re}] (-((k : ℂ) * I))) (𝓝 0) := by
        refine hrhs_k.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [← mul_sub, hper t ht]
      have huniq := tendsto_nhds_unique (hB.sub hA) hdiff0
      rw [← sub_div] at huniq
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp huniq).resolve_right h2π)
    exact ⟨ha_q, ha_per, ha_even⟩

/-- **Conductor integrality and universal `q`-periodic evenness for arbitrary
`UnitPoleFreeCrossHeightDatum` (without multiplicativity):**
1. if `Q` is not a positive integer, then `a(n) = b(n) = 0` (`n ≥ 1`), `R = 0`, and `F(z) = 0` (`z ≠ 1`);
2. if `Q = q ∈ ℕ_{≥ 1}`, then both `a` and `b` are `q`-periodic and reflection-even on `[1, q - 1]`,
   with `a(q) = -2 F(0)` and `R = ω q^{-1/2} b(q)`. -/
theorem conductor_nat_and_periodic_even_of_unitPoleFreeCrossHeightDatum
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) :
    ((∀ q : ℕ, 1 ≤ q → Q ≠ (q : ℝ)) →
      (∀ n : ℕ, 1 ≤ n → a n = 0 ∧ b n = 0) ∧ R = 0 ∧ ∀ z : ℂ, z ≠ 1 → F z = 0) ∧
    (∀ q : ℕ, 1 ≤ q → Q = (q : ℝ) →
      a q = -2 * F 0 ∧
      R = ω * (((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * b q ∧
      (∀ n : ℕ, 1 ≤ n → a (n + q) = a n ∧ b (n + q) = b n) ∧
      (∀ k : ℕ, 1 ≤ k → k < q → a (q - k) = a k ∧ b (q - k) = b k)) := by
  have hQ : 0 < Q := hD.Q_pos
  have hω0 : ω ≠ 0 := fun h => by have := hD.norm_ω; rw [h, norm_zero] at this; norm_num at this
  have ha_sum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun _ hσ => summable_unit_div_rpow hD.unit_a hσ
  have hb_sum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun _ hσ => summable_unit_div_rpow hD.unit_b hσ
  have htheta_a : ∀ x : ℝ, 0 < x → coeffTheta a x =
      (ω * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
        ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b ((1 / Q ^ 2) * x⁻¹)) +
        F 0 + (R / 2) * (x : ℂ) ^ (-(1 / 2 : ℂ)) :=
    fun _ hx => coeffTheta_relation_of_unitPoleFreeCrossHeightDatum hD hx
  -- Invert `x ↦ 1 / (Q ^ 2 * y)` to obtain the dual theta relation for `b`.
  have htheta_b : ∀ y : ℝ, 0 < y → coeffTheta b y =
      (ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
        ((y : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a ((1 / Q ^ 2) * y⁻¹)) +
        (-(ω⁻¹ * (((Q ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (R / 2))) +
        (-(ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F 0))) * (y : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro y hy
    set x : ℝ := (1 / Q ^ 2) * y⁻¹
    have hx_pos : 0 < x := by dsimp only [x]; positivity
    have hx_inv : (1 / Q ^ 2) * x⁻¹ = y := by
      dsimp only [x]; field_simp [hQ.ne', hy.ne']
    have hx_rpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) =
        (Q : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ) := by
      have hx_eq_r : x ^ (-(1 / 2 : ℝ)) = Q * y ^ (1 / 2 : ℝ) := by
        dsimp only [x]
        rw [Real.mul_rpow (by positivity) (inv_pos.mpr hy).le,
          show (1 / Q ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = Q by
            rw [one_div, Real.inv_rpow (sq_nonneg Q), ← Real.rpow_neg (sq_nonneg Q),
              ← Real.rpow_natCast Q 2, ← Real.rpow_mul hQ.le]
            norm_num [Real.rpow_one],
          Real.inv_rpow hy.le, ← Real.rpow_neg hy.le, neg_neg]
      rw [show (-(1 / 2 : ℂ)) = Complex.ofReal (-(1 / 2 : ℝ)) by push_cast; ring,
        show (1 / 2 : ℂ) = Complex.ofReal (1 / 2 : ℝ) by push_cast; ring,
        ← Complex.ofReal_cpow hx_pos.le, ← Complex.ofReal_cpow hy.le, hx_eq_r, Complex.ofReal_mul]
    have hy_cancel : (y : ℂ) ^ (-(1 / 2 : ℂ)) * (y : ℂ) ^ (1 / 2 : ℂ) = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'), neg_add_cancel,
        Complex.cpow_zero]
    have hQ_half_mul : (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (Q : ℂ) =
        (((Q ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
      have hr : Q ^ (-(1 / 2 : ℝ)) * Q = Q ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add_one hQ.ne']; norm_num
      exact_mod_cast hr
    have hQ_half_inv : (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (((Q ^ (1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      have hr : Q ^ (-(1 / 2 : ℝ)) * Q ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hQ, neg_add_cancel, Real.rpow_zero]
      exact_mod_cast hr
    have hrel := htheta_a x hx_pos
    rw [hx_inv, hx_rpow] at hrel
    -- Multiply `hrel` by `ω⁻¹ * Q^{-1/2} * y^{-1/2}` and solve for `coeffTheta b y`.
    have hmul := congrArg
      (fun z => ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (y : ℂ) ^ (-(1 / 2 : ℂ)) * z) hrel
    have hrhs_simp :
        ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (y : ℂ) ^ (-(1 / 2 : ℂ)) *
          ((ω * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
            (((Q : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ)) * coeffTheta b y) +
            F 0 + (R / 2) * ((Q : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ))) =
        coeffTheta b y +
          (ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F 0)) * (y : ℂ) ^ (-(1 / 2 : ℂ)) +
          (ω⁻¹ * (((Q ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (R / 2)) := by
      have h1 : (ω⁻¹ * ω) *
          ((((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ((((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (Q : ℂ))) *
          ((y : ℂ) ^ (-(1 / 2 : ℂ)) * (y : ℂ) ^ (1 / 2 : ℂ)) = 1 := by
        rw [inv_mul_cancel₀ hω0, hQ_half_mul, hQ_half_inv, hy_cancel]; ring
      calc ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (y : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((ω * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
              (((Q : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ)) * coeffTheta b y) +
              F 0 + (R / 2) * ((Q : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ)))
          = ((ω⁻¹ * ω) *
              ((((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ((((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (Q : ℂ))) *
              ((y : ℂ) ^ (-(1 / 2 : ℂ)) * (y : ℂ) ^ (1 / 2 : ℂ))) * coeffTheta b y +
            (ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F 0)) * (y : ℂ) ^ (-(1 / 2 : ℂ)) +
            ω⁻¹ * ((((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (Q : ℂ)) *
              ((y : ℂ) ^ (-(1 / 2 : ℂ)) * (y : ℂ) ^ (1 / 2 : ℂ)) * (R / 2) := by ring
        _ = coeffTheta b y +
            (ω⁻¹ * (((Q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F 0)) * (y : ℂ) ^ (-(1 / 2 : ℂ)) +
            (ω⁻¹ * (((Q ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (R / 2)) := by
              rw [h1, hQ_half_mul, hy_cancel]; ring
    rw [hrhs_simp] at hmul
    linear_combination -hmul
  obtain ⟨ha_nonnat, ha_nat⟩ := coeff_laws_of_rescaled_theta_relation ha_sum hb_sum hQ htheta_a
  obtain ⟨hb_nonnat, hb_nat⟩ := coeff_laws_of_rescaled_theta_relation hb_sum ha_sum hQ htheta_b
  constructor
  · intro hQ_not_nat
    have ha0 := ha_nonnat hQ_not_nat
    have hb0 := hb_nonnat hQ_not_nat
    -- Deduce `F z = 0` on `z ≠ 1` and `R = 0` from `regF = 0` on `Re z > 1`.
    set regF : ℂ → ℂ := Function.update (fun z => (z - 1) * F z) 1 R
    have hreg_an : AnalyticOnNhd ℂ regF Set.univ :=
      (differentiable_regularized_datum hD).differentiableOn.analyticOnNhd isOpen_univ
    have hzero_an : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
      (differentiableOn_const 0).analyticOnNhd isOpen_univ
    have hfreq0 : ∃ᶠ z in 𝓝[≠] (2 : ℂ), regF z = 0 := by
      set u_seq : ℕ → ℂ := fun k => ((2 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)
      have hlim : Tendsto u_seq atTop (𝓝[≠] (2 : ℂ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
        · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (2 : ℝ)
          rw [add_zero] at h1
          exact ((Complex.continuous_ofReal.tendsto 2).comp h1).congr fun _ => by simp [u_seq]
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u_seq]
          intro heq
          have h' : (2 + 1 / ((k : ℝ) + 1) : ℝ) = 2 := by exact_mod_cast heq
          have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith
      refine hlim.frequently (Frequently.of_forall fun k => ?_)
      have hre2 : 1 < (u_seq k).re := by
        dsimp only [u_seq]
        rw [Complex.ofReal_re]
        have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have hne1 : u_seq k ≠ 1 := fun h => by rw [h] at hre2; norm_num at hre2
      dsimp only [regF]
      rw [Function.update_of_ne hne1, hD.dirichlet_eq _ hre2]
      have hts0 : (∑' n : ℕ, a (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-u_seq k)) = 0 := by
        convert tsum_zero with n
        rw [ha0 (n + 1) (Nat.succ_pos n), zero_mul]
      rw [hts0, mul_zero]
    have hreg_eq0 : ∀ z : ℂ, regF z = 0 := fun z =>
      hreg_an.eqOn_of_preconnected_of_frequently_eq hzero_an convex_univ.isPreconnected
        (Set.mem_univ 2) hfreq0 (Set.mem_univ z)
    have hR0 : R = 0 := by simpa [regF] using hreg_eq0 1
    refine ⟨fun n hn => ⟨ha0 n hn, hb0 n hn⟩, hR0, fun z hz1 => ?_⟩
    have hz := hreg_eq0 z
    dsimp only [regF] at hz
    rw [Function.update_of_ne hz1] at hz
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hz1)
  · intro q hq1 hQ_eq
    obtain ⟨ha_q, ha_per, ha_even⟩ := ha_nat q hq1 hQ_eq
    obtain ⟨hb_q, hb_per, hb_even⟩ := hb_nat q hq1 hQ_eq
    have hR_eq : R = ω * (((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * b q := by
      rw [hb_q, hQ_eq]
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
      have hq_inv : (((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((q : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
        have hr : (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ) = 1 := by
          rw [← Real.rpow_add hq_pos, neg_add_cancel, Real.rpow_zero]
        exact_mod_cast hr
      calc R = (ω * ω⁻¹) * ((((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                (((q : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * R := by
            rw [mul_inv_cancel₀ hω0, hq_inv]; ring
        _ = ω * (((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (-2 * -(ω⁻¹ * (((q : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (R / 2))) := by ring
    exact ⟨ha_q, hR_eq,
      fun n hn => ⟨ha_per n hn, hb_per n hn⟩,
      fun k hk hkq => ⟨ha_even k hk hkq, hb_even k hk hkq⟩⟩

/-- Helper extending `F z = riemannZeta z * D z` from `Re z > 1` to all `z ≠ 1` via entire `regF`. -/
private theorem eq_zeta_mul_of_dirichlet_eq
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    {D : ℂ → ℂ} (hD_diff : Differentiable ℂ D)
    (h_right : ∀ z : ℂ, 1 < z.re → F z = riemannZeta z * D z) :
    R = D 1 ∧ ∀ z : ℂ, z ≠ 1 → F z = riemannZeta z * D z := by
  set regF : ℂ → ℂ := Function.update (fun z => (z - 1) * F z) 1 R
  set regZeta : ℂ → ℂ := Function.update (fun z => (z - 1) * riemannZeta z) 1 1
  have hregF_an : AnalyticOnNhd ℂ regF Set.univ :=
    (differentiable_regularized_datum hD).differentiableOn.analyticOnNhd isOpen_univ
  have hregZ_diff : Differentiable ℂ regZeta :=
    differentiable_regularized_datum unitPoleFreeCrossHeightDatum_riemannZeta
  have hprod_an : AnalyticOnNhd ℂ (fun z => regZeta z * D z) Set.univ :=
    (hregZ_diff.mul hD_diff).differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), regF z = regZeta z * D z := by
    set u_seq : ℕ → ℂ := fun k => ((2 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hlim : Tendsto u_seq atTop (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (2 : ℝ)
        rw [add_zero] at h1
        exact ((Complex.continuous_ofReal.tendsto 2).comp h1).congr fun _ => by simp [u_seq]
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u_seq]
        intro heq
        have h' : (2 + 1 / ((k : ℝ) + 1) : ℝ) = 2 := by exact_mod_cast heq
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hre2 : 1 < (u_seq k).re := by
      dsimp only [u_seq]
      rw [Complex.ofReal_re]
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hne1 : u_seq k ≠ 1 := fun h => by rw [h] at hre2; norm_num at hre2
    dsimp only [regF, regZeta]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne1, h_right _ hre2]
    ring
  have heq_all : ∀ z : ℂ, regF z = regZeta z * D z := fun z =>
    hregF_an.eqOn_of_preconnected_of_frequently_eq hprod_an convex_univ.isPreconnected
      (Set.mem_univ 2) hfreq (Set.mem_univ z)
  refine ⟨by simpa [regF, regZeta] using heq_all 1, fun z hz1 => ?_⟩
  have hz := heq_all z
  dsimp only [regF, regZeta] at hz
  rw [Function.update_of_ne hz1, Function.update_of_ne hz1] at hz
  exact mul_left_cancel₀ (sub_ne_zero.mpr hz1) (by linear_combination hz)

/-- **Conductor `0 < Q < 2` uniqueness of `ζ` (without multiplicativity or self-duality):**
every `UnitPoleFreeCrossHeightDatum F a b R Q ω` with `0 < Q < 2` either vanishes identically
(`Q ≠ 1`) or has `Q = 1`, constant coefficients `a(n) = R` and `b(n) = ω⁻¹ R`, and
`F(z) = R · riemannZeta z` for all `z ≠ 1`. -/
theorem eq_const_mul_riemannZeta_of_conductor_lt_two
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) (hQ2 : Q < 2) :
    (Q ≠ 1 → (∀ n : ℕ, 1 ≤ n → a n = 0 ∧ b n = 0) ∧ R = 0 ∧ ∀ z : ℂ, z ≠ 1 → F z = 0) ∧
    (Q = 1 → (∀ n : ℕ, 1 ≤ n → a n = R ∧ b n = ω⁻¹ * R) ∧
      ∀ z : ℂ, z ≠ 1 → F z = R * riemannZeta z) := by
  obtain ⟨hnonnat, hnat⟩ := conductor_nat_and_periodic_even_of_unitPoleFreeCrossHeightDatum hD
  have hω0 : ω ≠ 0 := fun h => by have := hD.norm_ω; rw [h, norm_zero] at this; norm_num at this
  constructor
  · intro hQ_ne1
    refine hnonnat fun q hq1 hQq => ?_
    rcases eq_or_ne q 1 with rfl | hq_ne1
    · exact hQ_ne1 (by simpa using hQq)
    · have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ q)
      linarith
  · intro hQ1
    obtain ⟨_, hR_b1, hper, _⟩ := hnat 1 le_rfl (by simpa using hQ1)
    have ha_const : ∀ n : ℕ, 1 ≤ n → a n = a 1 := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [← ih]; exact (hper k hk).1
    have hb_const : ∀ n : ℕ, 1 ≤ n → b n = b 1 := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [← ih]; exact (hper k hk).2
    have hF_right : ∀ z : ℂ, 1 < z.re → F z = riemannZeta z * (a 1) := by
      intro z hz
      rw [hD.dirichlet_eq z hz, zeta_eq_tsum_one_div_nat_add_one_cpow hz, mul_comm, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [ha_const (n + 1) (Nat.succ_pos n), one_div, ← Complex.cpow_neg]
      push_cast; ring
    obtain ⟨hR_eq_a1, hF_all⟩ := eq_zeta_mul_of_dirichlet_eq hD (differentiable_const (a 1)) hF_right
    have hb1_eq : b 1 = ω⁻¹ * R := by
      rw [hR_b1]
      simp [inv_mul_cancel_left₀ hω0]
    refine ⟨fun n hn => ⟨by rw [ha_const n hn, hR_eq_a1], by rw [hb_const n hn, hb1_eq]⟩,
      fun z hz1 => ?_⟩
    rw [hF_all z hz1, hR_eq_a1, mul_comm]

private lemma dirichlet_factor_functional_on_neg_one_line
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    {Da Db : ℂ → ℂ}
    (hFa : ∀ z : ℂ, z ≠ 1 → F z = riemannZeta z * Da z)
    (hGb : ∀ w : ℂ, 1 < w.re →
      (∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-w)) = riemannZeta w * Db w)
    (t : ℝ) :
    Da ((-1 : ℂ) + (t : ℂ) * I) =
      ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - ((-1 : ℂ) + (t : ℂ) * I)) *
        Db (1 - ((-1 : ℂ) + (t : ℂ) * I)) := by
  set z : ℂ := (-1 : ℂ) + (t : ℂ) * I
  have hz_neg : z.re < 0 := by simp [z]
  have hz0 : z ≠ 0 := fun h => by have := congrArg Complex.re h; simp [z] at this
  have hz1 : z ≠ 1 := fun h => by have := congrArg Complex.re h; simp [z] at this; norm_num at this
  have h1z : 1 < (1 - z).re := by simp [z]
  have hG_ne : Complex.Gammaℝ (1 - z) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ_1z_ne : riemannZeta (1 - z) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1z
  have hχ_ne : zetaChi z ≠ 0 := by
    have hΓz_ne : Complex.Gammaℝ z ≠ 0 := by
      rw [show z = (((-1 : ℝ) : ℂ) + (t : ℂ) * I) by simp [z]]
      exact Gammaℝ_vertical_ne_zero (by norm_num) (by norm_num)
    exact div_ne_zero hG_ne hΓz_ne
  have hζ_z_eq : riemannZeta z = zetaChi z * riemannZeta (1 - z) :=
    zeta_eq_zetaChi_mul hz0 hz1 hG_ne
  have hζ_z_ne : riemannZeta z ≠ 0 := by rw [hζ_z_eq]; exact mul_ne_zero hχ_ne hζ_1z_ne
  have hrefl := hD.crossHeight_refl z hz_neg
  rw [hFa z hz1, hGb (1 - z) h1z] at hrefl
  exact mul_left_cancel₀ hζ_z_ne
    (by linear_combination hrefl - ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - z) * Db (1 - z) * hζ_z_eq)

private lemma selfDual_conductor_two_criticalLine
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    (hQ_eq : Q = (2 : ℝ)) (ha1 : ‖a 1‖ = 1) (hb1 : ‖b 1‖ = 1)
    (hper : ∀ n : ℕ, 1 ≤ n → a (n + 2) = a n ∧ b (n + 2) = b n) :
    ∀ z : ℂ, z ≠ 1 → z.re ≠ 1 / 2 → (F z = 0 ↔ riemannZeta z = 0) := by
  have ha1_ne : a 1 ≠ 0 := fun h => by rw [h, norm_zero] at ha1; norm_num at ha1
  have ha_seq : ∀ n : ℕ, 1 ≤ n → a n = fourPeriodicEvenSeq (a 1) (a 2) (a 2) n := by
    intro n hn
    have h2per : ∀ k : ℕ, 1 ≤ k → a (k + 2) = a k := fun k hk => (hper k hk).1
    have hmod : ∀ m : ℕ, (m % 2 = 1 → a (m + 2) = a 1) ∧ (m % 2 = 0 → 1 ≤ m → a m = a 2) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        constructor
        · intro hm1
          rcases eq_or_ne m 1 with rfl | hm_ne1
          · exact h2per 1 le_rfl
          · rw [show m + 2 = (m - 2 + 2) + 2 by omega, h2per (m - 2 + 2) (by omega)]
            exact (ih (m - 2) (by omega)).1 (by omega)
        · intro hm0 hm_ge1
          rcases eq_or_ne m 2 with rfl | hm_ne2
          · rfl
          · rw [show m = (m - 2) + 2 by omega, h2per (m - 2) (by omega)]
            exact (ih (m - 2) (by omega)).2 (by omega) (by omega)
    unfold fourPeriodicEvenSeq
    rw [if_neg (by omega)]
    by_cases h_odd : n % 2 = 1
    · rw [if_pos h_odd]
      rcases eq_or_ne n 1 with rfl | hn_ne1
      · rfl
      · rw [show n = (n - 2) + 2 by omega]
        exact (hmod (n - 2)).1 (by omega)
    · rw [if_neg h_odd, ite_self]
      exact (hmod n).2 (by omega) hn
  have hb_seq : ∀ m : ℕ, 1 ≤ m → b m = fourPeriodicEvenSeq (b 1) (b 2) (b 2) m := by
    intro m hm
    have h2per : ∀ k : ℕ, 1 ≤ k → b (k + 2) = b k := fun k hk => (hper k hk).2
    have hmod : ∀ n : ℕ, (n % 2 = 1 → b (n + 2) = b 1) ∧ (n % 2 = 0 → 1 ≤ n → b n = b 2) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        constructor
        · intro hn1
          rcases eq_or_ne n 1 with rfl | hn_ne1
          · exact h2per 1 le_rfl
          · rw [show n + 2 = (n - 2 + 2) + 2 by omega, h2per (n - 2 + 2) (by omega)]
            exact (ih (n - 2) (by omega)).1 (by omega)
        · intro hn0 hn_ge1
          rcases eq_or_ne n 2 with rfl | hn_ne2
          · rfl
          · rw [show n = (n - 2) + 2 by omega, h2per (n - 2) (by omega)]
            exact (ih (n - 2) (by omega)).2 (by omega) (by omega)
    unfold fourPeriodicEvenSeq
    rw [if_neg (by omega)]
    by_cases h_odd : m % 2 = 1
    · rw [if_pos h_odd]
      rcases eq_or_ne m 1 with rfl | hm_ne1
      · rfl
      · rw [show m = (m - 2) + 2 by omega]
        exact (hmod (m - 2)).1 (by omega)
    · rw [if_neg h_odd, ite_self]
      exact (hmod m).2 (by omega) hm
  set Da : ℂ → ℂ := fun z => a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z)
  set Db : ℂ → ℂ := fun z => b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-z)
  have hDa_diff : Differentiable ℂ Da := by
    haveI : NeZero (2 : ℂ) := ⟨by norm_num⟩
    exact (differentiable_const (a 1)).add
      (((differentiable_const_cpow_of_neZero (2 : ℂ)).comp differentiable_id.neg).const_mul _)
  have hFa : ∀ z : ℂ, z ≠ 1 → F z = riemannZeta z * Da z := by
    refine (eq_zeta_mul_of_dirichlet_eq hD hDa_diff fun z hz => ?_).2
    rw [hD.dirichlet_eq z hz]
    have hts := fourPeriodicEvenSeq_tsum_eq (a 1) (a 2) (a 2) hz
    rw [sub_self, zero_mul, add_zero] at hts
    rw [← hts]
    exact tsum_congr fun n => by rw [ha_seq (n + 1) (Nat.succ_pos n)]
  have hGb : ∀ w : ℂ, 1 < w.re →
      (∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-w)) = riemannZeta w * Db w := by
    intro w hw
    have hts := fourPeriodicEvenSeq_tsum_eq (b 1) (b 2) (b 2) hw
    rw [sub_self, zero_mul, add_zero] at hts
    rw [← hts]
    exact tsum_congr fun m => by rw [hb_seq (m + 1) (Nat.succ_pos m)]
  -- Evaluate `2^z Da(z) = ω √2 Db(1 - z)` at `t = 0` and `t = π / log 2` to isolate `a 2 - a 1`.
  have hpt_id : ∀ t : ℝ,
      (a 2 - a 1) + ((1 / 2 : ℂ) * a 1 - ω * ((Real.sqrt 2 : ℝ) : ℂ) * (b 2 - b 1) * (1 / 4 : ℂ)) *
        (2 : ℂ) ^ ((t : ℂ) * I) = ω * ((Real.sqrt 2 : ℝ) : ℂ) * b 1 := by
    intro t
    set z : ℂ := (-1 : ℂ) + (t : ℂ) * I
    have hfe_t : a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z) =
        ω * ((2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) * (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z))) := by
      have h0 := dirichlet_factor_functional_on_neg_one_line hD hFa hGb t
      rw [hQ_eq] at h0
      exact h0
    have heq :
        (2 : ℂ) ^ z * (a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z)) =
          (2 : ℂ) ^ z *
            (ω * ((2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) *
              (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)))) :=
      congrArg ((2 : ℂ) ^ z * ·) hfe_t
    have h20 : (2 : ℂ) ≠ 0 := by norm_num
    have h2z_cancel : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
      rw [← Complex.cpow_add _ _ h20, add_neg_cancel, Complex.cpow_zero]
    have h2_sqrt : (2 : ℂ) ^ z * (((2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) = ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_ofNat, ← Complex.cpow_add _ _ h20,
        show z + ((1 / 2 : ℂ) - z) = Complex.ofReal (1 / 2 : ℝ) by push_cast; ring,
        show (2 : ℂ) = Complex.ofReal 2 by norm_num, ← Complex.ofReal_cpow two_pos.le,
        ← Real.sqrt_eq_rpow]
    have h2z_split : (2 : ℂ) ^ z = (1 / 2 : ℂ) * (2 : ℂ) ^ ((t : ℂ) * I) := by
      dsimp only [z]
      rw [Complex.cpow_add _ _ h20, Complex.cpow_neg_one]; norm_num
    have h2_1z : (2 : ℂ) ^ (-(1 - z)) = (1 / 4 : ℂ) * (2 : ℂ) ^ ((t : ℂ) * I) := by
      dsimp only [z]
      rw [show -(1 - ((-1 : ℂ) + (t : ℂ) * I)) = (-2 : ℂ) + (t : ℂ) * I by ring,
        Complex.cpow_add _ _ h20, show (-2 : ℂ) = -(2 : ℕ) by norm_num,
        Complex.cpow_neg, Complex.cpow_natCast]
      norm_num
    have hlhs : (2 : ℂ) ^ z * (a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z)) =
        (1 / 2 : ℂ) * a 1 * (2 : ℂ) ^ ((t : ℂ) * I) + (a 2 - a 1) := by
      calc (2 : ℂ) ^ z * (a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z))
          = (2 : ℂ) ^ z * a 1 + (a 2 - a 1) * ((2 : ℂ) ^ z * (2 : ℂ) ^ (-z)) := by ring
        _ = (1 / 2 : ℂ) * a 1 * (2 : ℂ) ^ ((t : ℂ) * I) + (a 2 - a 1) := by
            rw [h2z_cancel, mul_one, h2z_split]; ring
    have hrhs : (2 : ℂ) ^ z *
        (ω * (((2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) * (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)))) =
        ω * ((Real.sqrt 2 : ℝ) : ℂ) * b 1 +
          ω * ((Real.sqrt 2 : ℝ) : ℂ) * (b 2 - b 1) * (1 / 4 : ℂ) * (2 : ℂ) ^ ((t : ℂ) * I) := by
      calc (2 : ℂ) ^ z *
            (ω * (((2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) * (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z))))
          = ω * ((2 : ℂ) ^ z * (((2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z))) *
              (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z))) := by ring
        _ = ω * ((Real.sqrt 2 : ℝ) : ℂ) * b 1 +
              ω * ((Real.sqrt 2 : ℝ) : ℂ) * (b 2 - b 1) * (1 / 4 : ℂ) * (2 : ℂ) ^ ((t : ℂ) * I) := by
            rw [h2_sqrt, h2_1z]; ring
    rw [hlhs, hrhs] at heq
    linear_combination heq
  have he0 := hpt_id 0
  have he_pi := hpt_id (Real.pi / Real.log 2)
  have h2_pi : (2 : ℂ) ^ (((Real.pi / Real.log 2 : ℝ) : ℂ) * I) = -1 := by
    have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.ofReal_log two_pos.le]
    have harg : ((Real.log 2 : ℝ) : ℂ) * (((Real.pi / Real.log 2 : ℝ) : ℂ) * I) =
        Real.pi * I := by
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_comm (Real.log 2),
        div_mul_cancel₀ _ hlog2_ne]
    rw [harg, Complex.exp_pi_mul_I]
  rw [Complex.ofReal_zero, zero_mul, Complex.cpow_zero] at he0
  rw [h2_pi] at he_pi
  have hc2_eq : a 2 - a 1 = ω * ((Real.sqrt 2 : ℝ) : ℂ) * b 1 := by
    linear_combination (he0 + he_pi) / 2
  have hnorm_c2 : ‖(a 2 - a 1) / a 1‖ ^ 2 = (2 : ℝ) := by
    rw [hc2_eq, norm_div, norm_mul, norm_mul, hD.norm_ω, hb1, ha1,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr two_pos)]
    nlinarith [Real.sq_sqrt two_pos.le]
  intro z hz1 hz_half
  rw [hFa z hz1, mul_eq_zero]
  have hDa_ne : Da z ≠ 0 := by
    intro h0_Da
    apply hz_half
    have hdiv0 : 1 + ((a 2 - a 1) / a 1) * (2 : ℂ) ^ (-z) = 0 := by
      have h := congrArg (fun w => w / a 1) h0_Da
      dsimp only [Da] at h
      rw [zero_div] at h
      field_simp [ha1_ne] at h ⊢
      linear_combination h
    have heq_neg := eq_neg_of_add_eq_zero_right hdiv0
    have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) heq_neg
    simp only [norm_mul, mul_pow, norm_neg, norm_one, one_pow] at hn
    rw [hnorm_c2, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re,
      ← Real.rpow_natCast ((2 : ℝ) ^ (-z.re)) 2, ← Real.rpow_mul two_pos.le] at hn
    have h1 : (2 : ℝ) ^ ((1 : ℝ) + (-z.re * (2 : ℕ))) = (2 : ℝ) ^ (0 : ℝ) := by
      rw [Real.rpow_add two_pos, Real.rpow_one, Real.rpow_zero]
      exact hn
    have hexp := Real.rpow_right_inj two_pos (by norm_num) |>.mp h1
    push_cast at hexp; linarith
  exact ⟨fun h => h.resolve_right hDa_ne, fun h => Or.inl h⟩

private lemma selfDual_conductor_three_criticalLine
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    (hQ_eq : Q = (3 : ℝ)) (ha1 : ‖a 1‖ = 1) (hb1 : ‖b 1‖ = 1)
    (hper : ∀ n : ℕ, 1 ≤ n → a (n + 3) = a n ∧ b (n + 3) = b n)
    (heven : ∀ k : ℕ, 1 ≤ k → k < 3 → a (3 - k) = a k ∧ b (3 - k) = b k) :
    ∀ z : ℂ, z ≠ 1 → z.re ≠ 1 / 2 → (F z = 0 ↔ riemannZeta z = 0) := by
  have ha1_ne : a 1 ≠ 0 := fun h => by rw [h, norm_zero] at ha1; norm_num at ha1
  have ha21 : a 2 = a 1 := (heven 1 le_rfl (by omega)).1
  have hb21 : b 2 = b 1 := (heven 1 le_rfl (by omega)).2
  have ha_seq : ∀ n : ℕ, 1 ≤ n → a n = threePeriodicEvenSeq (a 1) (a 3) n := by
    intro n hn
    have h3per : ∀ k : ℕ, 1 ≤ k → a (k + 3) = a k := fun k hk => (hper k hk).1
    have hmod : ∀ m : ℕ, 1 ≤ m → a m = if m % 3 = 0 then a 3 else a 1 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hm1
        rcases le_or_gt m 3 with hm_le3 | hm_gt3
        · have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
          rcases hm_cases with rfl | rfl | rfl
          · simp
          · simp [ha21]
          · simp
        · rw [show m = (m - 3) + 3 by omega, h3per (m - 3) (by omega),
            ih (m - 3) (by omega) (by omega)]
          rw [Nat.add_mod_right (m - 3) 3]
    unfold threePeriodicEvenSeq
    rw [if_neg (by omega), hmod n hn]
  have hb_seq : ∀ m : ℕ, 1 ≤ m → b m = threePeriodicEvenSeq (b 1) (b 3) m := by
    intro m hm
    have h3per : ∀ k : ℕ, 1 ≤ k → b (k + 3) = b k := fun k hk => (hper k hk).2
    have hmod : ∀ n : ℕ, 1 ≤ n → b n = if n % 3 = 0 then b 3 else b 1 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn1
        rcases le_or_gt n 3 with hn_le3 | hn_gt3
        · have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
          rcases hn_cases with rfl | rfl | rfl
          · simp
          · simp [hb21]
          · simp
        · rw [show n = (n - 3) + 3 by omega, h3per (n - 3) (by omega),
            ih (n - 3) (by omega) (by omega)]
          rw [Nat.add_mod_right (n - 3) 3]
    unfold threePeriodicEvenSeq
    rw [if_neg (by omega), hmod m hm]
  set Da : ℂ → ℂ := fun z => a 1 + (a 3 - a 1) * (3 : ℂ) ^ (-z)
  set Db : ℂ → ℂ := fun z => b 1 + (b 3 - b 1) * (3 : ℂ) ^ (-z)
  have hDa_diff : Differentiable ℂ Da := by
    haveI : NeZero (3 : ℂ) := ⟨by norm_num⟩
    exact (differentiable_const (a 1)).add
      (((differentiable_const_cpow_of_neZero (3 : ℂ)).comp differentiable_id.neg).const_mul _)
  have hFa : ∀ z : ℂ, z ≠ 1 → F z = riemannZeta z * Da z := by
    refine (eq_zeta_mul_of_dirichlet_eq hD hDa_diff fun z hz => ?_).2
    rw [hD.dirichlet_eq z hz, ← threePeriodicEvenSeq_tsum_eq (a 1) (a 3) hz]
    exact tsum_congr fun n => by rw [ha_seq (n + 1) (Nat.succ_pos n)]
  have hGb : ∀ w : ℂ, 1 < w.re →
      (∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-w)) = riemannZeta w * Db w := by
    intro w hw
    rw [← threePeriodicEvenSeq_tsum_eq (b 1) (b 3) hw]
    exact tsum_congr fun m => by rw [hb_seq (m + 1) (Nat.succ_pos m)]
  have hpt_id : ∀ t : ℝ,
      (a 3 - a 1) + ((1 / 3 : ℂ) * a 1 - ω * ((Real.sqrt 3 : ℝ) : ℂ) * (b 3 - b 1) * (1 / 9 : ℂ)) *
        (3 : ℂ) ^ ((t : ℂ) * I) = ω * ((Real.sqrt 3 : ℝ) : ℂ) * b 1 := by
    intro t
    set z : ℂ := (-1 : ℂ) + (t : ℂ) * I
    have hfe_t : a 1 + (a 3 - a 1) * (3 : ℂ) ^ (-z) =
        ω * ((3 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) * (b 1 + (b 3 - b 1) * (3 : ℂ) ^ (-(1 - z))) := by
      have h0 := dirichlet_factor_functional_on_neg_one_line hD hFa hGb t
      rw [hQ_eq] at h0
      exact h0
    have heq :
        (3 : ℂ) ^ z * (a 1 + (a 3 - a 1) * (3 : ℂ) ^ (-z)) =
          (3 : ℂ) ^ z *
            (ω * ((3 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) *
              (b 1 + (b 3 - b 1) * (3 : ℂ) ^ (-(1 - z)))) :=
      congrArg ((3 : ℂ) ^ z * ·) hfe_t
    have h30 : (3 : ℂ) ≠ 0 := by norm_num
    have h3z_cancel : (3 : ℂ) ^ z * (3 : ℂ) ^ (-z) = 1 := by
      rw [← Complex.cpow_add _ _ h30, add_neg_cancel, Complex.cpow_zero]
    have h3_sqrt : (3 : ℂ) ^ z * (((3 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) = ((Real.sqrt 3 : ℝ) : ℂ) := by
      rw [Complex.ofReal_ofNat, ← Complex.cpow_add _ _ h30,
        show z + ((1 / 2 : ℂ) - z) = Complex.ofReal (1 / 2 : ℝ) by push_cast; ring,
        show (3 : ℂ) = Complex.ofReal 3 by norm_num, ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.sqrt_eq_rpow]
    have h3z_split : (3 : ℂ) ^ z = (1 / 3 : ℂ) * (3 : ℂ) ^ ((t : ℂ) * I) := by
      dsimp only [z]
      rw [Complex.cpow_add _ _ h30, Complex.cpow_neg_one]; norm_num
    have h3_1z : (3 : ℂ) ^ (-(1 - z)) = (1 / 9 : ℂ) * (3 : ℂ) ^ ((t : ℂ) * I) := by
      dsimp only [z]
      rw [show -(1 - ((-1 : ℂ) + (t : ℂ) * I)) = (-2 : ℂ) + (t : ℂ) * I by ring,
        Complex.cpow_add _ _ h30, show (-2 : ℂ) = -(2 : ℕ) by norm_num,
        Complex.cpow_neg, Complex.cpow_natCast]
      norm_num
    have hlhs : (3 : ℂ) ^ z * (a 1 + (a 3 - a 1) * (3 : ℂ) ^ (-z)) =
        (1 / 3 : ℂ) * a 1 * (3 : ℂ) ^ ((t : ℂ) * I) + (a 3 - a 1) := by
      calc (3 : ℂ) ^ z * (a 1 + (a 3 - a 1) * (3 : ℂ) ^ (-z))
          = (3 : ℂ) ^ z * a 1 + (a 3 - a 1) * ((3 : ℂ) ^ z * (3 : ℂ) ^ (-z)) := by ring
        _ = (1 / 3 : ℂ) * a 1 * (3 : ℂ) ^ ((t : ℂ) * I) + (a 3 - a 1) := by
            rw [h3z_cancel, mul_one, h3z_split]; ring
    have hrhs : (3 : ℂ) ^ z *
        (ω * (((3 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) * (b 1 + (b 3 - b 1) * (3 : ℂ) ^ (-(1 - z)))) =
        ω * ((Real.sqrt 3 : ℝ) : ℂ) * b 1 +
          ω * ((Real.sqrt 3 : ℝ) : ℂ) * (b 3 - b 1) * (1 / 9 : ℂ) * (3 : ℂ) ^ ((t : ℂ) * I) := by
      calc (3 : ℂ) ^ z *
            (ω * (((3 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) * (b 1 + (b 3 - b 1) * (3 : ℂ) ^ (-(1 - z))))
          = ω * ((3 : ℂ) ^ z * (((3 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z))) *
              (b 1 + (b 3 - b 1) * (3 : ℂ) ^ (-(1 - z))) := by ring
        _ = ω * ((Real.sqrt 3 : ℝ) : ℂ) * b 1 +
              ω * ((Real.sqrt 3 : ℝ) : ℂ) * (b 3 - b 1) * (1 / 9 : ℂ) * (3 : ℂ) ^ ((t : ℂ) * I) := by
            rw [h3_sqrt, h3_1z]; ring
    rw [hlhs, hrhs] at heq
    linear_combination heq
  have he0 := hpt_id 0
  have he_pi := hpt_id (Real.pi / Real.log 3)
  have h3_pi : (3 : ℂ) ^ (((Real.pi / Real.log 3 : ℝ) : ℂ) * I) = -1 := by
    have h3_gt1 : (1 : ℝ) < 3 := by norm_num
    have hlog3_ne : Real.log 3 ≠ 0 := (Real.log_pos h3_gt1).ne'
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]
    have harg : ((Real.log 3 : ℝ) : ℂ) * (((Real.pi / Real.log 3 : ℝ) : ℂ) * I) =
        Real.pi * I := by
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_comm (Real.log 3),
        div_mul_cancel₀ _ hlog3_ne]
    rw [harg, Complex.exp_pi_mul_I]
  rw [Complex.ofReal_zero, zero_mul, Complex.cpow_zero] at he0
  rw [h3_pi] at he_pi
  have hc3_eq : a 3 - a 1 = ω * ((Real.sqrt 3 : ℝ) : ℂ) * b 1 := by
    linear_combination (he0 + he_pi) / 2
  have hnorm_c3 : ‖(a 3 - a 1) / a 1‖ ^ 2 = (3 : ℝ) := by
    have h3_pos : (0 : ℝ) < 3 := by norm_num
    rw [hc3_eq, norm_div, norm_mul, norm_mul, hD.norm_ω, hb1, ha1,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr h3_pos)]
    nlinarith [Real.sq_sqrt h3_pos.le]
  intro z hz1 hz_half
  rw [hFa z hz1, mul_eq_zero]
  have hDa_ne : Da z ≠ 0 := by
    intro h0_Da
    apply hz_half
    have hdiv0 : 1 + ((a 3 - a 1) / a 1) * (3 : ℂ) ^ (-z) = 0 := by
      have h := congrArg (fun w => w / a 1) h0_Da
      dsimp only [Da] at h
      rw [zero_div] at h
      field_simp [ha1_ne] at h ⊢
      linear_combination h
    have heq_neg := eq_neg_of_add_eq_zero_right hdiv0
    have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) heq_neg
    have h3_pos : (0 : ℝ) < 3 := by norm_num
    simp only [norm_mul, mul_pow, norm_neg, norm_one, one_pow] at hn
    rw [hnorm_c3, show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos h3_pos, Complex.neg_re,
      ← Real.rpow_natCast ((3 : ℝ) ^ (-z.re)) 2, ← Real.rpow_mul h3_pos.le] at hn
    have h1 : (3 : ℝ) ^ ((1 : ℝ) + (-z.re * (2 : ℕ))) = (3 : ℝ) ^ (0 : ℝ) := by
      rw [Real.rpow_add h3_pos, Real.rpow_one, Real.rpow_zero]
      exact hn
    have hexp := Real.rpow_right_inj h3_pos (by norm_num) |>.mp h1
    push_cast at hexp; linarith
  exact ⟨fun h => h.resolve_right hDa_ne, fun h => Or.inl h⟩

private lemma selfDual_conductor_four_criticalLine
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    (hQ_eq : Q = (4 : ℝ)) (ha1 : ‖a 1‖ = 1) (hb1 : ‖b 1‖ = 1)
    (hper : ∀ n : ℕ, 1 ≤ n → a (n + 4) = a n ∧ b (n + 4) = b n)
    (heven : ∀ k : ℕ, 1 ≤ k → k < 4 → a (4 - k) = a k ∧ b (4 - k) = b k) :
    ∀ z : ℂ, z ≠ 1 → z.re ≠ 1 / 2 → (F z = 0 ↔ riemannZeta z = 0) := by
  have ha1_ne : a 1 ≠ 0 := fun h => by rw [h, norm_zero] at ha1; norm_num at ha1
  have ha31 : a 3 = a 1 := (heven 1 le_rfl (by omega)).1
  have hb31 : b 3 = b 1 := (heven 1 le_rfl (by omega)).2
  have ha_seq : ∀ n : ℕ, 1 ≤ n → a n = fourPeriodicEvenSeq (a 1) (a 2) (a 4) n := by
    intro n hn
    have h4per : ∀ k : ℕ, 1 ≤ k → a (k + 4) = a k := fun k hk => (hper k hk).1
    have hmod : ∀ m : ℕ, 1 ≤ m →
        a m = if m % 2 = 1 then a 1 else if m % 4 = 2 then a 2 else a 4 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hm1
        rcases le_or_gt m 4 with hm_le4 | hm_gt4
        · have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
          rcases hm_cases with rfl | rfl | rfl | rfl
          · simp
          · simp
          · simp [ha31]
          · simp
        · rw [show m = (m - 4) + 4 by omega, h4per (m - 4) (by omega),
            ih (m - 4) (by omega) (by omega)]
          have hm2 : ((m - 4) + 4) % 2 = (m - 4) % 2 := by omega
          have hm4 : ((m - 4) + 4) % 4 = (m - 4) % 4 := Nat.add_mod_right (m - 4) 4
          rw [hm2, hm4]
    unfold fourPeriodicEvenSeq
    rw [if_neg (by omega), hmod n hn]
  have hb_seq : ∀ m : ℕ, 1 ≤ m → b m = fourPeriodicEvenSeq (b 1) (b 2) (b 4) m := by
    intro m hm
    have h4per : ∀ k : ℕ, 1 ≤ k → b (k + 4) = b k := fun k hk => (hper k hk).2
    have hmod : ∀ n : ℕ, 1 ≤ n →
        b n = if n % 2 = 1 then b 1 else if n % 4 = 2 then b 2 else b 4 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn1
        rcases le_or_gt n 4 with hn_le4 | hn_gt4
        · have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
          rcases hn_cases with rfl | rfl | rfl | rfl
          · simp
          · simp
          · simp [hb31]
          · simp
        · rw [show n = (n - 4) + 4 by omega, h4per (n - 4) (by omega),
            ih (n - 4) (by omega) (by omega)]
          have hn2 : ((n - 4) + 4) % 2 = (n - 4) % 2 := by omega
          have hn4 : ((n - 4) + 4) % 4 = (n - 4) % 4 := Nat.add_mod_right (n - 4) 4
          rw [hn2, hn4]
    unfold fourPeriodicEvenSeq
    rw [if_neg (by omega), hmod m hm]
  set Da : ℂ → ℂ := fun z => a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z) + (a 4 - a 2) * (4 : ℂ) ^ (-z)
  set Db : ℂ → ℂ := fun z => b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-z) + (b 4 - b 2) * (4 : ℂ) ^ (-z)
  have hDa_diff : Differentiable ℂ Da := by
    haveI : NeZero (2 : ℂ) := ⟨by norm_num⟩
    haveI : NeZero (4 : ℂ) := ⟨by norm_num⟩
    exact ((differentiable_const (a 1)).add
      (((differentiable_const_cpow_of_neZero (2 : ℂ)).comp differentiable_id.neg).const_mul _)).add
      (((differentiable_const_cpow_of_neZero (4 : ℂ)).comp differentiable_id.neg).const_mul _)
  have hFa : ∀ z : ℂ, z ≠ 1 → F z = riemannZeta z * Da z := by
    refine (eq_zeta_mul_of_dirichlet_eq hD hDa_diff fun z hz => ?_).2
    rw [hD.dirichlet_eq z hz, ← fourPeriodicEvenSeq_tsum_eq (a 1) (a 2) (a 4) hz]
    exact tsum_congr fun n => by rw [ha_seq (n + 1) (Nat.succ_pos n)]
  have hGb : ∀ w : ℂ, 1 < w.re →
      (∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-w)) = riemannZeta w * Db w := by
    intro w hw
    rw [← fourPeriodicEvenSeq_tsum_eq (b 1) (b 2) (b 4) hw]
    exact tsum_congr fun m => by rw [hb_seq (m + 1) (Nat.succ_pos m)]
  -- Isolate `a 4 - a 2 = 2 ω b 1` by 4-point Fourier averaging on `2^{i t} ∈ {1, -1, I, -I}`.
  have hpt_id : ∀ t : ℝ,
      (a 4 - a 2) +
        ((1 / 2 : ℂ) * (a 2 - a 1) - 2 * ω * (b 2 - b 1) * (1 / 4 : ℂ)) *
          ((2 : ℂ) ^ ((t : ℂ) * I)) +
        ((1 / 4 : ℂ) * a 1 - 2 * ω * (b 4 - b 2) * (1 / 16 : ℂ)) *
          ((2 : ℂ) ^ ((t : ℂ) * I)) ^ 2 =
        2 * ω * b 1 := by
    intro t
    set z : ℂ := (-1 : ℂ) + (t : ℂ) * I
    set U_t : ℂ := (2 : ℂ) ^ ((t : ℂ) * I)
    have hfe_t :
        a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z) + (a 4 - a 2) * (4 : ℂ) ^ (-z) =
          ω * ((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) *
            (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)) + (b 4 - b 2) * (4 : ℂ) ^ (-(1 - z))) := by
      have h0 := dirichlet_factor_functional_on_neg_one_line hD hFa hGb t
      rw [hQ_eq] at h0
      exact h0
    have heq :
        (4 : ℂ) ^ z * (a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z) + (a 4 - a 2) * (4 : ℂ) ^ (-z)) =
          (4 : ℂ) ^ z *
            (ω * ((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) *
              (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)) + (b 4 - b 2) * (4 : ℂ) ^ (-(1 - z)))) :=
      congrArg ((4 : ℂ) ^ z * ·) hfe_t
    have h20 : (2 : ℂ) ≠ 0 := by norm_num
    have h40 : (4 : ℂ) ≠ 0 := by norm_num
    have h4z_cancel : (4 : ℂ) ^ z * (4 : ℂ) ^ (-z) = 1 := by
      rw [← Complex.cpow_add _ _ h40, add_neg_cancel, Complex.cpow_zero]
    have h4_sqrt : (4 : ℂ) ^ z * (((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) = 2 := by
      rw [Complex.ofReal_ofNat, ← Complex.cpow_add _ _ h40,
        show z + ((1 / 2 : ℂ) - z) = Complex.ofReal (1 / 2 : ℝ) by push_cast; ring,
        show (4 : ℂ) = Complex.ofReal 4 by norm_num, ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4),
        ← Real.sqrt_eq_rpow]
      norm_num
    have h4_eq_22 : ∀ w : ℂ, (4 : ℂ) ^ w = ((2 : ℂ) ^ w) ^ 2 := by
      intro w
      rw [pow_two, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le w]
      norm_num
    have h2z_split : (2 : ℂ) ^ z = (1 / 2 : ℂ) * U_t := by
      dsimp only [z, U_t]
      rw [Complex.cpow_add _ _ h20, Complex.cpow_neg_one]; norm_num
    have h4z_split : (4 : ℂ) ^ z = (1 / 4 : ℂ) * U_t ^ 2 := by
      rw [h4_eq_22 z, h2z_split]; ring
    have h42_prod : (4 : ℂ) ^ z * (2 : ℂ) ^ (-z) = (1 / 2 : ℂ) * U_t := by
      have h2_cancel : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
        rw [← Complex.cpow_add _ _ h20, add_neg_cancel, Complex.cpow_zero]
      calc (4 : ℂ) ^ z * (2 : ℂ) ^ (-z)
          = (2 : ℂ) ^ z * ((2 : ℂ) ^ z * (2 : ℂ) ^ (-z)) := by rw [h4_eq_22 z]; ring
        _ = (1 / 2 : ℂ) * U_t := by rw [h2_cancel, mul_one, h2z_split]
    have h2_1z : (2 : ℂ) ^ (-(1 - z)) = (1 / 4 : ℂ) * U_t := by
      dsimp only [z, U_t]
      rw [show -(1 - ((-1 : ℂ) + (t : ℂ) * I)) = (-2 : ℂ) + (t : ℂ) * I by ring,
        Complex.cpow_add _ _ h20, show (-2 : ℂ) = -(2 : ℕ) by norm_num,
        Complex.cpow_neg, Complex.cpow_natCast]
      norm_num
    have h4_1z : (4 : ℂ) ^ (-(1 - z)) = (1 / 16 : ℂ) * U_t ^ 2 := by
      rw [h4_eq_22 (-(1 - z)), h2_1z]; ring
    have hlhs : (4 : ℂ) ^ z * (a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z) + (a 4 - a 2) * (4 : ℂ) ^ (-z)) =
        (1 / 4 : ℂ) * a 1 * U_t ^ 2 + (1 / 2 : ℂ) * (a 2 - a 1) * U_t + (a 4 - a 2) := by
      calc (4 : ℂ) ^ z * (a 1 + (a 2 - a 1) * (2 : ℂ) ^ (-z) + (a 4 - a 2) * (4 : ℂ) ^ (-z))
          = (4 : ℂ) ^ z * a 1 + (a 2 - a 1) * ((4 : ℂ) ^ z * (2 : ℂ) ^ (-z)) +
              (a 4 - a 2) * ((4 : ℂ) ^ z * (4 : ℂ) ^ (-z)) := by ring
        _ = (1 / 4 : ℂ) * a 1 * U_t ^ 2 + (1 / 2 : ℂ) * (a 2 - a 1) * U_t + (a 4 - a 2) := by
            rw [h42_prod, h4z_cancel, h4z_split]; ring
    have hrhs : (4 : ℂ) ^ z *
        (ω * (((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) *
          (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)) + (b 4 - b 2) * (4 : ℂ) ^ (-(1 - z)))) =
        2 * ω * b 1 + 2 * ω * (b 2 - b 1) * (1 / 4 : ℂ) * U_t +
          2 * ω * (b 4 - b 2) * (1 / 16 : ℂ) * U_t ^ 2 := by
      calc (4 : ℂ) ^ z *
            (ω * (((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) *
              (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)) + (b 4 - b 2) * (4 : ℂ) ^ (-(1 - z))))
          = ω * ((4 : ℂ) ^ z * (((4 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z))) *
              (b 1 + (b 2 - b 1) * (2 : ℂ) ^ (-(1 - z)) + (b 4 - b 2) * (4 : ℂ) ^ (-(1 - z))) := by ring
        _ = 2 * ω * b 1 + 2 * ω * (b 2 - b 1) * (1 / 4 : ℂ) * U_t +
              2 * ω * (b 4 - b 2) * (1 / 16 : ℂ) * U_t ^ 2 := by
            rw [h4_sqrt, h2_1z, h4_1z]; ring
    rw [hlhs, hrhs] at heq
    linear_combination heq
  have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hU_val : ∀ c_ang : ℝ,
      (2 : ℂ) ^ (((c_ang * Real.pi / Real.log 2 : ℝ) : ℂ) * I) =
        Complex.exp (((c_ang * Real.pi : ℝ) : ℂ) * I) := by
    intro c_ang
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.ofReal_log two_pos.le]
    congr 1
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_comm (Real.log 2),
      div_mul_cancel₀ _ hlog2_ne]
  have he0 := hpt_id 0
  have he1 := hpt_id (1 * Real.pi / Real.log 2)
  have he_half := hpt_id ((1 / 2) * Real.pi / Real.log 2)
  have he_nhalf := hpt_id (-(1 / 2) * Real.pi / Real.log 2)
  rw [Complex.ofReal_zero, zero_mul, Complex.cpow_zero] at he0
  rw [hU_val 1, one_mul, Complex.exp_pi_mul_I] at he1
  have hexp_half : Complex.exp ((((1 / 2 : ℝ) * Real.pi : ℝ) : ℂ) * I) = I := by
    rw [show (((1 / 2 : ℝ) * Real.pi : ℝ) : ℂ) * I = ((Real.pi / 2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    simp
  have hexp_nhalf : Complex.exp (((-(1 / 2 : ℝ) * Real.pi : ℝ) : ℂ) * I) = -I := by
    rw [show ((-(1 / 2 : ℝ) * Real.pi : ℝ) : ℂ) * I = -(((1 / 2 : ℝ) * Real.pi : ℝ) : ℂ) * I by
      push_cast; ring, neg_mul, Complex.exp_neg, hexp_half, inv_I]
  rw [hU_val (1 / 2), hexp_half] at he_half
  rw [hU_val (-(1 / 2)), hexp_nhalf] at he_nhalf
  have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hnI2 : (-I : ℂ) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
  rw [hI2] at he_half
  rw [hnI2] at he_nhalf
  have hc4_eq : a 4 - a 2 = 2 * ω * b 1 := by
    linear_combination (he0 + he1 + he_half + he_nhalf) / 4
  -- Deduce critical-line purity of `Da` via normalized `u₂ = a 2 / a 1`, `u₄ = a 4 / a 1`.
  set u₂ : ℂ := a 2 / a 1
  set u₄ : ℂ := a 4 / a 1
  have hu₂_le : ‖u₂‖ ≤ 1 := by
    dsimp only [u₂]; rw [norm_div, ha1, div_one]; exact hD.unit_a 2 (by omega)
  have hu₄_le : ‖u₄‖ ≤ 1 := by
    dsimp only [u₄]; rw [norm_div, ha1, div_one]; exact hD.unit_a 4 (by omega)
  have hdiff_u : ‖u₄ - u₂‖ ^ 2 = 4 := by
    have hsub_u : u₄ - u₂ = (a 4 - a 2) / a 1 := by dsimp only [u₂, u₄]; ring
    rw [hsub_u, hc4_eq, norm_div, norm_mul, norm_mul, hD.norm_ω, hb1, ha1]
    norm_num
  -- Parallelogram law forces `u₄ = -u₂` and `Complex.normSq u₂ = 1`.
  have hnsq2 : u₂.re ^ 2 + u₂.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq u₂
    rw [Complex.normSq_apply] at h; nlinarith [norm_nonneg u₂]
  have hnsq4 : u₄.re ^ 2 + u₄.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq u₄
    rw [Complex.normSq_apply] at h; nlinarith [norm_nonneg u₄]
  have hnsq_d : (u₄.re - u₂.re) ^ 2 + (u₄.im - u₂.im) ^ 2 = 4 := by
    have h := Complex.normSq_eq_norm_sq (u₄ - u₂)
    rw [hdiff_u, Complex.normSq_apply] at h
    simpa [pow_two] using h
  have hu₄_neg : u₄ = -u₂ := by
    apply Complex.ext
    · simp; nlinarith [sq_nonneg (u₄.re + u₂.re), sq_nonneg (u₄.im + u₂.im)]
    · simp; nlinarith [sq_nonneg (u₄.re + u₂.re), sq_nonneg (u₄.im + u₂.im)]
  have hu₂_nsq : Complex.normSq u₂ = 1 := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (u₄.re + u₂.re), sq_nonneg (u₄.im + u₂.im)]
  intro z hz1 hz_half
  rw [hFa z hz1, mul_eq_zero]
  have hDa_ne : Da z ≠ 0 := by
    intro h0_Da
    apply hz_half
    set X : ℂ := (2 : ℂ) ^ (-z)
    have h4X : (4 : ℂ) ^ (-z) = X ^ 2 := by
      dsimp only [X]
      rw [pow_two, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le (-z)]
      norm_num
    have hdiv0 : 1 + (u₂ - 1) * X + (u₄ - u₂) * X ^ 2 = 0 := by
      have h := congrArg (fun w => w / a 1) h0_Da
      dsimp only [Da] at h
      rw [h4X, zero_div] at h
      dsimp only [u₂, u₄]
      field_simp [ha1_ne] at h ⊢
      linear_combination h
    rw [hu₄_neg] at hdiv0
    have hrel : 1 - X = u₂ * X * (2 * X - 1) := by linear_combination hdiv0
    have hnsq_rel := congrArg Complex.normSq hrel
    rw [map_mul, map_mul, hu₂_nsq, one_mul,
      Complex.normSq_apply (1 - X), Complex.normSq_apply X, Complex.normSq_apply (2 * X - 1)]
      at hnsq_rel
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im] at hnsq_rel
    have hcoord : (1 - X.re) ^ 2 + (-X.im) ^ 2 =
        (X.re ^ 2 + X.im ^ 2) * ((2 * X.re - 1) ^ 2 + (2 * X.im) ^ 2) := by
      simpa [pow_two] using hnsq_rel
    have hfac : (2 * (X.re ^ 2 + X.im ^ 2) - 1) *
        (2 * (X.re - 1 / 2) ^ 2 + 2 * X.im ^ 2 + 1 / 2) = 0 := by linear_combination -hcoord
    have hpos_fac : 0 < 2 * (X.re - 1 / 2) ^ 2 + 2 * X.im ^ 2 + 1 / 2 := by positivity
    have hr_half : Complex.normSq X = 1 / 2 := by
      rw [Complex.normSq_apply]
      linarith [(mul_eq_zero.mp hfac).resolve_right hpos_fac.ne']
    rw [Complex.normSq_eq_norm_sq, show X = ((2 : ℝ) : ℂ) ^ (-z) by dsimp only [X]; norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re,
      ← Real.rpow_natCast ((2 : ℝ) ^ (-z.re)) 2, ← Real.rpow_mul two_pos.le] at hr_half
    have h1 : (2 : ℝ) ^ (-z.re * (2 : ℕ)) = (2 : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]; norm_num at hr_half ⊢; exact hr_half
    have hexp := Real.rpow_right_inj two_pos (by norm_num) |>.mp h1
    push_cast at hexp; linarith
  exact ⟨fun h => h.resolve_right hDa_ne, fun h => Or.inl h⟩

/-- **Sharp sub-conductor-`5` critical-line rigidity without multiplicativity (`0 < Q < 5`):**
for **every** `UnitPoleFreeCrossHeightDatum F a b R Q ω` with `0 < Q < 5`, `‖a(1)‖ = 1`, and
`‖b(1)‖ = 1` (in particular every normalized self-dual datum `b = star ∘ a`, with **zero**
multiplicativity hypothesis):
1. `Q ∈ {1, 2, 3, 4}` (`∃ q ∈ {1, 2, 3, 4}, Q = q`);
2. for every `z ∈ ℂ \ {1}` with `Re z ≠ 1 / 2`, `F(z) = 0 ↔ riemannZeta z = 0`. -/
theorem selfDual_conductor_lt_five_classification
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) (hQ5 : Q < 5)
    (ha1 : ‖a 1‖ = 1) (hb1 : ‖b 1‖ = 1) :
    (∃ q : ℕ, q ∈ ({1, 2, 3, 4} : Finset ℕ) ∧ Q = (q : ℝ)) ∧
      ∀ z : ℂ, z ≠ 1 → z.re ≠ 1 / 2 → (F z = 0 ↔ riemannZeta z = 0) := by
  obtain ⟨hnonnat, hnat⟩ := conductor_nat_and_periodic_even_of_unitPoleFreeCrossHeightDatum hD
  have ha1_ne : a 1 ≠ 0 := fun h => by rw [h, norm_zero] at ha1; norm_num at ha1
  have hex_q : ∃ q : ℕ, 1 ≤ q ∧ Q = (q : ℝ) := by
    by_contra hno
    push Not at hno
    exact ha1_ne ((hnonnat hno).1 1 le_rfl).1
  obtain ⟨q, hq1, hQ_eq⟩ := hex_q
  have hq4 : q ≤ 4 := by
    have hqR : (q : ℝ) < 5 := hQ_eq ▸ hQ5
    have hlt5 : q < 5 := by exact_mod_cast hqR
    omega
  have hq_mem : q ∈ ({1, 2, 3, 4} : Finset ℕ) := by
    have : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp
  refine ⟨⟨q, hq_mem, hQ_eq⟩, ?_⟩
  obtain ⟨_, _, hper, heven⟩ := hnat q hq1 hQ_eq
  have hq_cases : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by omega
  rcases hq_cases with rfl | rfl | rfl | rfl
  · have hlt2 : Q < 2 := by rw [hQ_eq]; norm_num
    obtain ⟨_, h1_eq⟩ := eq_const_mul_riemannZeta_of_conductor_lt_two hD hlt2
    obtain ⟨hab, hFz⟩ := h1_eq (by simpa using hQ_eq)
    have hR_ne : R ≠ 0 := by
      have ha1_R := (hab 1 le_rfl).1
      exact fun h0 => ha1_ne (by rw [ha1_R, h0])
    intro z hz1 _
    rw [hFz z hz1, mul_eq_zero]
    exact ⟨fun h => h.resolve_left hR_ne, fun h => Or.inr h⟩
  · exact selfDual_conductor_two_criticalLine hD (by simpa using hQ_eq) ha1 hb1 hper
  · exact selfDual_conductor_three_criticalLine hD (by simpa using hQ_eq) ha1 hb1 hper heven
  · exact selfDual_conductor_four_criticalLine hD (by simpa using hQ_eq) ha1 hb1 hper heven

end Part2HamburgerConductorRigidity


/-! ### Part 3: Over-Horizon Pure-Direct Gaussian Witnesses and Uniform Dual-Vacuum Extraction -/

section Part3PureDirectAndDualVacuum

/-- Finite pure-direct Gaussian Dirichlet polynomial of length `L` at scale `x`
(zero dual terms and zero pole term). -/
def pureDirectGaussianWitness (a : ℕ → ℂ) (s : ℂ) (x : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.range L,
    a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))

/-- Pole-cleared pure-direct Gaussian witness for `(1 - 2^{-(1 - s)}) ζ(s)` at scale `x` and
length `L` (canceling `smoothAFEZetaShiftedPoleResidue` identically while keeping zero dual terms). -/
def poleClearedPureDirectZetaWitness (s : ℂ) (x : ℝ) (L : ℕ) : ℂ :=
  pureDirectGaussianWitness (fun _ => 1) s x L -
    (2 : ℂ) ^ (-(1 - s)) * pureDirectGaussianWitness (fun _ => 1) s (2 * x) L

/-- Exact scale covariance of `smoothAFEZetaShiftedPoleResidue`: multiplying `x` by `d ≥ 1` and
weighting by `d^{-(1 - s)}` leaves `smoothAFEZetaShiftedPoleResidue s x` invariant. -/
theorem smoothAFEZetaShiftedPoleResidue_mul_scale
    {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (d : ℂ) ^ (-(1 - s)) * smoothAFEZetaShiftedPoleResidue s ((d : ℝ) * x) =
      smoothAFEZetaShiftedPoleResidue s x := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_ne0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  unfold smoothAFEZetaShiftedPoleResidue
  have hmul_pow : (((d : ℝ) * x : ℝ) : ℂ) ^ (1 - s) =
      (d : ℂ) ^ (1 - s) * (x : ℂ) ^ (1 - s) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hd_pos.le hx.le (1 - s),
      Complex.ofReal_natCast]
  have hcancel : (d : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ (1 - s) = 1 := by
    rw [← Complex.cpow_add _ _ hd_ne0, neg_add_cancel, Complex.cpow_zero]
  rw [hmul_pow]
  calc (d : ℂ) ^ (-(1 - s)) *
        (((d : ℂ) ^ (1 - s) * (x : ℂ) ^ (1 - s)) * Complex.exp ((1 - s) ^ 2) / (1 - s))
      = ((d : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ (1 - s)) *
          ((x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ 2) / (1 - s)) := by ring
    _ = (x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ 2) / (1 - s) := by rw [hcancel, one_mul]

/-- Across `0 < Re s < 1 / 2`, the pole-clearing prefactor `1 - 2^{-(1 - s)}` satisfies
`1 / 4 < ‖1 - 2^{-(1 - s)}‖` (hence never vanishes). -/
theorem one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub
    {s : ℂ} (h_half : s.re < 1 / 2) :
    (1 / 4 : ℝ) < ‖(1 : ℂ) - (2 : ℂ) ^ (-(1 - s))‖ := by
  have hnorm_two : ‖(2 : ℂ) ^ (-(1 - s))‖ < 3 / 4 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
      show (-(1 - s)).re = -(1 - s.re) by simp]
    have hsq : ((2 : ℝ) ^ (-(1 - s.re))) ^ (2 : ℕ) < (3 / 4 : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 - s.re))) 2, ← Real.rpow_mul two_pos.le]
      have h1 : (2 : ℝ) ^ (-(1 - s.re) * (2 : ℕ)) < (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by push_cast; linarith)
      have h2 : (2 : ℝ) ^ (-1 : ℝ) < (3 / 4 : ℝ) ^ (2 : ℕ) := by norm_num
      exact h1.trans h2
    by_contra hge; push Not at hge
    have hsq_ge : (3 / 4 : ℝ) ^ (2 : ℕ) ≤ ((2 : ℝ) ^ (-(1 - s.re))) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hge 2
    linarith
  have htri := norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (-(1 - s)))
  rw [norm_one] at htri
  linarith

/-- **Over-horizon pure-direct Gaussian witness theorem across ALL of `Ω_open`:**
for every `UnitPoleFreeCrossHeightDatum F a b R Q ω`, every over-horizon exponent `δ > 0`, and
every target decay power `B : ℝ`, setting `x = |Im s|^{1 + δ}` annihilates the **entire** infinite
reflected dual series (`m ≥ 0`) and the shifted pole residue below `|Im s|^{-B}`, reducing `F(s)`
to `pureDirectGaussianWitness a s (|Im s|^{1 + δ}) (max 2 ⌈|Im s|^{1 + 2δ}⌉₊)` within `E |Im s|^{-B}`
across every point of `Ω_open`. -/
theorem exists_pure_direct_gaussian_witness_on_remaining_strip
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ E : ℝ, 0 < E ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ‖F s - pureDirectGaussianWitness a s (|s.im| ^ (1 + δ))
            (max 2 (Nat.ceil (|s.im| ^ (1 + 2 * δ))))‖ ≤
          E * |s.im| ^ (-B) := by
  set B₀ : ℝ := max 0 B
  have hB_le : B ≤ B₀ := le_max_right 0 B
  have hB₀_nn : 0 ≤ B₀ := le_max_left 0 B
  -- 1. Select `r ≥ 1` so `B₀ + 1 ≤ 2 * r * δ`, `A ≥ 2` so `B₀ + 2 + 2 * δ ≤ A * δ`, and `M_p` for the pole.
  obtain ⟨r, hr1, hr_δ⟩ : ∃ r : ℕ, 1 ≤ r ∧ B₀ + 1 ≤ 2 * (r : ℝ) * δ := by
    refine ⟨max 1 (Nat.ceil ((B₀ + 1) / (2 * δ))), le_max_left _ _, ?_⟩
    have hc : (B₀ + 1) / (2 * δ) ≤ (Nat.ceil ((B₀ + 1) / (2 * δ)) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((B₀ + 1) / (2 * δ)) : ℝ) ≤
        ((max 1 (Nat.ceil ((B₀ + 1) / (2 * δ))) : ℕ) : ℝ) := by exact_mod_cast le_max_right 1 _
    have h := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp (hc.trans hm)
    linarith
  obtain ⟨A, hA2, hA_δ⟩ : ∃ A : ℕ, 2 ≤ A ∧ B₀ + 2 + 2 * δ ≤ (A : ℝ) * δ := by
    refine ⟨max 2 (Nat.ceil ((B₀ + 2 + 2 * δ) / δ)), le_max_left _ _, ?_⟩
    have hc : (B₀ + 2 + 2 * δ) / δ ≤ (Nat.ceil ((B₀ + 2 + 2 * δ) / δ) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((B₀ + 2 + 2 * δ) / δ) : ℝ) ≤
        ((max 2 (Nat.ceil ((B₀ + 2 + 2 * δ) / δ)) : ℕ) : ℝ) := by exact_mod_cast le_max_right 2 _
    have h := (div_le_iff₀ hδ).mp (hc.trans hm)
    linarith
  set M_p : ℕ := Nat.ceil (B₀ + 2 + δ)
  have hMp_ge : B₀ + 2 + δ ≤ (M_p : ℝ) := Nat.le_ceil _
  have hA_pos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hA2R : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  obtain ⟨C_dir, hC_dir0, hC_dir⟩ := exists_smoothAFE_direct_tail_le hA_pos
  obtain ⟨K_dual, hK_dual_pos, hK_dual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) hr1
  have hsum_p2 : Summable (fun m : ℕ => (m + 1 : ℝ) ^ (-2 : ℝ)) := by
    have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  set S_p2 : ℝ := ∑' m : ℕ, (m + 1 : ℝ) ^ (-2 : ℝ)
  have hSp2_nn : 0 ≤ S_p2 := tsum_nonneg fun _ => by positivity
  have hQ_pos : 0 < Q := hD.Q_pos
  set Q_fac : ℝ := max 1 (Q ^ (1 / 2 : ℝ)) * Q ^ (2 * (r : ℝ))
  have hQ_fac_pos : 0 < Q_fac := by dsimp only [Q_fac]; positivity
  refine ⟨C_dir + Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_p2 +
      ‖R‖ * Real.exp 1 * (M_p.factorial : ℝ) + 1, by positivity, fun s hlo hhi him => ?_⟩
  set τ : ℝ := |s.im|
  have hτ1 : 1 < τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := zero_lt_one.trans hτ1
  set x : ℝ := τ ^ (1 + δ)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hxQ_pos : 0 < x / Q := div_pos hx_pos hQ_pos
  set L : ℕ := max 2 (Nat.ceil (τ ^ (1 + 2 * δ)))
  have hL1 : 1 ≤ L := le_trans (by omega : 1 ≤ 2) (le_max_left _ _)
  have hL_ge : τ ^ (1 + 2 * δ) ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 2 _))
  have hs0 : 0 < s.re := by linarith
  have hsA : 1 < s.re + (A : ℝ) := by linarith
  rw [crossHeight_gaussian_two_tsum_eq hD hx_pos hs0 hhi]
  have hbase_dir := summable_smoothAFE_direct hA_pos hx_pos hsA
  have hsum_dir : Summable (fun n : ℕ =>
      a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) := by
    refine Summable.of_norm_bounded hbase_dir.norm fun n => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_a (n + 1) (Nat.succ_pos n))
  unfold crossHeightGaussianTwoSeries pureDirectGaussianWitness
  rw [← hsum_dir.sum_add_tsum_nat_add L]
  have halg :
      ((∑ n ∈ Finset.range L,
            a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) +
          ∑' j : ℕ, a (j + L + 1) *
            (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          (∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m) -
        R * smoothAFEZetaShiftedPoleResidue s x) -
      (∑ n ∈ Finset.range L,
        a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) =
      ((∑' j : ℕ, a (j + L + 1) *
            (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          (∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)) -
        R * smoothAFEZetaShiftedPoleResidue s x := by ring
  rw [halg]
  -- Bound 1: Direct tail `n ≥ L`.
  have hshift_z : Summable (fun j : ℕ =>
      ‖(((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => ‖(((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))‖) L).mpr
      hbase_dir.norm
  have hpt_j : ∀ j : ℕ,
      ‖a (j + L + 1) * (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ ≤
        ‖(((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ := fun j => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_a _ (by omega))
  have hsum_td := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_j hshift_z
  have hbd_dir : ‖∑' j : ℕ, a (j + L + 1) *
      (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ ≤
      C_dir * τ ^ (-B) := by
    have hden1 : 1 ≤ s.re + (A : ℝ) - 1 := by linarith
    have h0 := (norm_tsum_le_tsum_norm hsum_td).trans ((hsum_td.tsum_le_tsum hpt_j hshift_z).trans
      ((hC_dir s x hx_pos hsA L hL1).trans (mul_le_mul_of_nonneg_left
        (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hden1) (by positivity))))
    have hxA : x ^ (A : ℝ) = τ ^ ((1 + δ) * (A : ℝ)) :=
      (Real.rpow_mul hτ_pos.le (1 + δ) (A : ℝ)).symm
    have hexp_neg : 1 - (s.re + (A : ℝ)) ≤ 0 := by linarith
    have hL_pow : (L : ℝ) ^ (1 - (s.re + (A : ℝ))) ≤
        τ ^ ((1 + 2 * δ) * (1 - (s.re + (A : ℝ)))) := by
      calc (L : ℝ) ^ (1 - (s.re + (A : ℝ)))
          ≤ (τ ^ (1 + 2 * δ)) ^ (1 - (s.re + (A : ℝ))) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτ_pos _) hL_ge hexp_neg
        _ = τ ^ ((1 + 2 * δ) * (1 - (s.re + (A : ℝ)))) := (Real.rpow_mul hτ_pos.le _ _).symm
    have hexp_le : (1 + δ) * (A : ℝ) + (1 + 2 * δ) * (1 - (s.re + (A : ℝ))) ≤ -B := by
      have hid : (1 + δ) * (A : ℝ) + (1 + 2 * δ) * (1 - (s.re + (A : ℝ))) =
          -((A : ℝ) * δ) + (1 + 2 * δ) * (1 - s.re) := by ring
      have h1s_le1 : (1 + 2 * δ) * (1 - s.re) ≤ 1 + 2 * δ :=
        mul_le_of_le_one_right (by positivity) (by linarith)
      linarith
    calc ‖∑' j : ℕ, a (j + L + 1) *
            (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖
        ≤ C_dir * x ^ (A : ℝ) * (L : ℝ) ^ (1 - (s.re + (A : ℝ))) := h0
      _ ≤ C_dir * τ ^ ((1 + δ) * (A : ℝ)) * τ ^ ((1 + 2 * δ) * (1 - (s.re + (A : ℝ)))) := by
          rw [hxA]
          exact mul_le_mul_of_nonneg_left hL_pow (by positivity)
      _ = C_dir * τ ^ ((1 + δ) * (A : ℝ) + (1 + 2 * δ) * (1 - (s.re + (A : ℝ)))) := by
          rw [mul_assoc, ← Real.rpow_add hτ_pos]
      _ ≤ C_dir * τ ^ (-B) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hτ1.le hexp_le) hC_dir0
  -- Bound 2: Full reflected dual series (`m ≥ 0`).
  have hbd_dual : ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
      (∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)‖ ≤
      (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_p2) * τ ^ (-B) := by
    set K_loc : ℝ := K_dual * (x / Q) ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
    have hpt_du : ∀ m : ℕ,
        ‖b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖ ≤
          K_loc * (m + 1 : ℝ) ^ (-2 : ℝ) := fun m => by
      rw [norm_mul]
      have h1 := mul_le_of_le_one_left
        (norm_nonneg (smoothAFEZetaDualCoefficientGeneral s (x / Q) m))
        (hD.unit_b (m + 1) (Nat.succ_pos m))
      have h2 := (hK_dual s (x / Q) hlo hhi hxQ_pos).1 m
      have hm_pow : (m + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) ≤ (m + 1 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos m) (by linarith)
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hm_pow (by positivity)))
    have hmaj_u := hsum_p2.mul_left K_loc
    have hs_u := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_du hmaj_u
    have hts_u : ‖∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖ ≤
        K_loc * S_p2 :=
      (norm_tsum_le_tsum_norm hs_u).trans ((hs_u.tsum_le_tsum hpt_du hmaj_u).trans_eq tsum_mul_left)
    have hQ_pref : ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ * (x / Q) ^ (-2 * (r : ℝ)) ≤
        Q_fac * τ ^ ((1 + δ) * (-2 * (r : ℝ))) := by
      rw [norm_mul, hD.norm_ω, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ_pos,
        show ((1 / 2 : ℂ) - s).re = 1 / 2 - s.re by simp]
      have hQ_half : Q ^ (1 / 2 - s.re) ≤ max 1 (Q ^ (1 / 2 : ℝ)) := by
        rcases le_total 1 Q with h1Q | hQ1
        · exact (Real.rpow_le_rpow_of_exponent_le h1Q (by linarith)).trans (le_max_right _ _)
        · exact (Real.rpow_le_one hQ_pos.le hQ1 (by linarith)).trans (le_max_left _ _)
      have hxQ_pow : (x / Q) ^ (-2 * (r : ℝ)) =
          Q ^ (2 * (r : ℝ)) * τ ^ ((1 + δ) * (-2 * (r : ℝ))) := by
        rw [Real.div_rpow hx_pos.le hQ_pos.le, show -2 * (r : ℝ) = -(2 * (r : ℝ)) by ring,
          Real.rpow_neg hQ_pos.le, div_inv_eq_mul, mul_comm]
        congr 1
        dsimp only [x]
        rw [← Real.rpow_mul hτ_pos.le]
      rw [hxQ_pow]
      calc Q ^ (1 / 2 - s.re) * (Q ^ (2 * (r : ℝ)) * τ ^ ((1 + δ) * (-2 * (r : ℝ))))
          ≤ max 1 (Q ^ (1 / 2 : ℝ)) * (Q ^ (2 * (r : ℝ)) * τ ^ ((1 + δ) * (-2 * (r : ℝ)))) :=
            mul_le_mul_of_nonneg_right hQ_half (by positivity)
        _ = Q_fac * τ ^ ((1 + δ) * (-2 * (r : ℝ))) := by dsimp only [Q_fac]; ring
    have h1τ_le : (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) ≤
        (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by
      have hexp_nn : 0 ≤ (2 * r : ℝ) + 1 / 2 - s.re := by linarith
      have hexp_le : (2 * r : ℝ) + 1 / 2 - s.re ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
      calc (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
          ≤ (2 * τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
            Real.rpow_le_rpow (by positivity) (by linarith) hexp_nn
        _ = (2 : ℝ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
            Real.mul_rpow two_pos.le hτ_pos.le
        _ ≤ (2 : ℝ) ^ (((2 * r + 1 : ℕ) : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
              (by positivity)
        _ = (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by rw [Real.rpow_natCast]
    have hexp_du_le : (1 + δ) * (-2 * (r : ℝ)) + ((2 * r : ℝ) + 1 / 2 - s.re) ≤ -B := by
      have hid : (1 + δ) * (-2 * (r : ℝ)) + ((2 * r : ℝ) + 1 / 2 - s.re) =
          -(2 * (r : ℝ) * δ) + (1 / 2 - s.re) := by ring
      linarith
    rw [norm_mul]
    calc ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ *
            ‖∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖
        ≤ ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ * (K_loc * S_p2) :=
          mul_le_mul_of_nonneg_left hts_u (norm_nonneg _)
      _ = K_dual * (‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ * (x / Q) ^ (-2 * (r : ℝ))) *
            (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * S_p2 := by dsimp only [K_loc]; ring
      _ ≤ K_dual * (Q_fac * τ ^ ((1 + δ) * (-2 * (r : ℝ)))) *
            ((2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re)) * S_p2 := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left hQ_pref hK_dual_pos.le)
              h1τ_le (by positivity) (by positivity)) hSp2_nn
      _ = (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_p2) *
            (τ ^ ((1 + δ) * (-2 * (r : ℝ))) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re)) := by ring
      _ = (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_p2) *
            τ ^ ((1 + δ) * (-2 * (r : ℝ)) + ((2 * r : ℝ) + 1 / 2 - s.re)) := by
          rw [← Real.rpow_add hτ_pos]
      _ ≤ (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_p2) * τ ^ (-B) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hτ1.le hexp_du_le)
            (by positivity)
  -- Bound 3: Shifted pole residue.
  have hbd_pole : ‖R * smoothAFEZetaShiftedPoleResidue s x‖ ≤
      (‖R‖ * Real.exp 1 * (M_p.factorial : ℝ)) * τ ^ (-B) := by
    rw [norm_mul, smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, Complex.norm_exp]
    have h1s_norm : 1 ≤ ‖(1 : ℂ) - s‖ := by
      calc (1 : ℝ) ≤ τ := hτ1.le
        _ = |((1 : ℂ) - s).im| := by dsimp only [τ]; simp
        _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
    have hx_1s : x ^ ((1 - s).re) ≤ τ ^ (1 + δ) := by
      dsimp only [x]
      rw [← Real.rpow_mul hτ_pos.le, show (1 - s).re = 1 - s.re by simp]
      exact Real.rpow_le_rpow_of_exponent_le hτ1.le
        (mul_le_of_le_one_right (by positivity) (by linarith))
    have hre_sq : (((1 - s) ^ (2 : ℕ)).re) ≤ 1 - τ ^ 2 := by
      have h1 : (((1 - s) ^ (2 : ℕ)).re) = (1 - s.re) ^ 2 - s.im ^ 2 := by
        simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im]
        ring
      have h1s_sq : (1 - s.re) ^ 2 ≤ 1 := by
        rw [pow_two]
        exact (mul_self_le_mul_self (by linarith) (by linarith)).trans_eq (one_mul 1)
      dsimp only [τ]; rw [h1, ← sq_abs s.im]; linarith
    have hexp_tau : Real.exp (-(τ ^ 2)) ≤ (M_p.factorial : ℝ) * τ ^ (-(M_p : ℝ)) := by
      have hsq_ge : τ ≤ τ ^ 2 := by rw [pow_two]; exact le_mul_of_one_le_left hτ_pos.le hτ1.le
      have hpow_fac : τ ^ M_p / (M_p.factorial : ℝ) ≤ Real.exp (τ ^ 2) :=
        (Real.pow_div_factorial_le_exp τ hτ_pos.le M_p).trans (Real.exp_le_exp.mpr hsq_ge)
      have hfac_pos : (0 : ℝ) < (M_p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos M_p
      rw [Real.rpow_neg hτ_pos.le, Real.rpow_natCast, Real.exp_neg,
        inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have h1 : τ ^ M_p ≤ Real.exp (τ ^ 2) * (M_p.factorial : ℝ) :=
        (div_le_iff₀ hfac_pos).mp hpow_fac
      have hpow_pos : 0 < τ ^ M_p := pow_pos hτ_pos M_p
      calc (1 : ℝ) = (τ ^ M_p)⁻¹ * τ ^ M_p := (inv_mul_cancel₀ hpow_pos.ne').symm
        _ ≤ (τ ^ M_p)⁻¹ * (Real.exp (τ ^ 2) * (M_p.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpow_pos.le)
        _ = (M_p.factorial : ℝ) * (τ ^ M_p)⁻¹ * Real.exp (τ ^ 2) := by ring
    have htau_Mp : τ ^ (1 + δ) * τ ^ (-(M_p : ℝ)) ≤ τ ^ (-B) := by
      rw [← Real.rpow_add hτ_pos]
      exact Real.rpow_le_rpow_of_exponent_le hτ1.le (by linarith)
    have hdiv_le : x ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) / ‖(1 : ℂ) - s‖ ≤
        Real.exp 1 * (M_p.factorial : ℝ) * τ ^ (-B) := by
      calc x ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) / ‖(1 : ℂ) - s‖
          ≤ x ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) :=
            div_le_self (by positivity) h1s_norm
        _ ≤ τ ^ (1 + δ) * Real.exp (1 - τ ^ 2) :=
            mul_le_mul hx_1s (Real.exp_le_exp.mpr hre_sq) (Real.exp_nonneg _) (by positivity)
        _ = Real.exp 1 * (τ ^ (1 + δ) * Real.exp (-(τ ^ 2))) := by
            rw [show 1 - τ ^ 2 = 1 + -(τ ^ 2) by ring, Real.exp_add]; ring
        _ ≤ Real.exp 1 * (τ ^ (1 + δ) * ((M_p.factorial : ℝ) * τ ^ (-(M_p : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_tau (by positivity))
              (Real.exp_nonneg _)
        _ = Real.exp 1 * (M_p.factorial : ℝ) * (τ ^ (1 + δ) * τ ^ (-(M_p : ℝ))) := by ring
        _ ≤ Real.exp 1 * (M_p.factorial : ℝ) * τ ^ (-B) :=
            mul_le_mul_of_nonneg_left htau_Mp (by positivity)
    exact (mul_le_mul_of_nonneg_left hdiv_le (norm_nonneg _)).trans_eq (by ring)
  have ht1 := norm_sub_le
    ((∑' j : ℕ, a (j + L + 1) *
        (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
      ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)
    (R * smoothAFEZetaShiftedPoleResidue s x)
  have ht2 := norm_sub_le
    (∑' j : ℕ, a (j + L + 1) *
      (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x)))
    (ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
      ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)
  have hsum3 : ‖((∑' j : ℕ, a (j + L + 1) *
        (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
      ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m) -
      R * smoothAFEZetaShiftedPoleResidue s x‖ ≤
      (C_dir + Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_p2 +
        ‖R‖ * Real.exp 1 * (M_p.factorial : ℝ)) * τ ^ (-B) := by
    linarith [ht1, ht2, hbd_dir, hbd_dual, hbd_pole]
  exact hsum3.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hτ_pos.le _))

/-- **Unconditional `RiemannHypothesis` equivalence with pole-cleared pure-direct Gaussian
witnesses across ALL of `Ω_open`:**
there exist explicit `s`-independent constants `C_dir, K_dual > 0` such that:
1. at every `s ∈ Ω_open`, `x > 0`, and `L ≥ 1`, `poleClearedPureDirectZetaWitness s x L`
   (containing zero dual terms and zero pole term) approximates `(1 - 2^{-(1 - s)}) ζ(s)` within
   `C_dir x^2 L^{-(1 + Re s)} + K_dual x^{-2} (1 + |Im s|)^{5/2 - Re s}`;
2. `RiemannHypothesis` holds if and only if at **every** point of `Ω_open`, some scale `x ≥ |Im s|`
   gives strict certified excess at `L = max 2 ⌈x^2⌉₊`. -/
theorem rh_iff_pure_direct_gaussian_witness_on_remaining_strip :
    ∃ C_dir K_dual : ℝ, 0 < C_dir ∧ 0 < K_dual ∧
      (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∀ {x : ℝ}, 0 < x → ∀ L : ℕ, 1 ≤ L →
          ‖(1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s -
              poleClearedPureDirectZetaWitness s x L‖ ≤
            C_dir * x ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) +
              K_dual * x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)) ∧
      (RiemannHypothesis ↔
        ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
          ∃ x : ℝ, |s.im| ≤ x ∧
            C_dir * x ^ (2 : ℝ) *
                ((max 2 (Nat.ceil (x ^ (2 : ℝ))) : ℕ) : ℝ) ^ (-(1 + s.re)) +
              K_dual * x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) <
              ‖poleClearedPureDirectZetaWitness s x (max 2 (Nat.ceil (x ^ (2 : ℝ))))‖) := by
  obtain ⟨C₀, hC₀, hC_dir⟩ := exists_smoothAFE_direct_tail_le (A := 2) (by norm_num)
  obtain ⟨Kd₀, hKd₀, hK_dual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := 1) le_rfl
  have hsum_p2 : Summable (fun m : ℕ => (m + 1 : ℝ) ^ (-2 : ℝ)) := by
    have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  set S_p2 : ℝ := ∑' m : ℕ, (m + 1 : ℝ) ^ (-2 : ℝ)
  have hSp2_nn : 0 ≤ S_p2 := tsum_nonneg fun _ => by positivity
  set C_dir : ℝ := 5 * C₀ + 1
  set K_dual : ℝ := 2 * Kd₀ * S_p2 + 1
  have hC_pos : 0 < C_dir := by dsimp only [C_dir]; positivity
  have hK_pos : 0 < K_dual := by dsimp only [K_dual]; positivity
  -- Helper: single-scale bound on `(Dir_tail(y, L) - Dual(y))` for `y > 0`.
  have hsingle : ∀ (s : ℂ), 3001 / 24000 ≤ s.re → s.re < 1 / 2 → ∀ {y : ℝ}, 0 < y →
      ∀ L : ℕ, 1 ≤ L →
        ‖(riemannZeta s + smoothAFEZetaShiftedPoleResidue s y) -
            pureDirectGaussianWitness (fun _ => 1) s y L‖ ≤
          C₀ * y ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) +
            (Kd₀ * S_p2) * y ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by
    intro s hlo hhi y hy L hL1
    have hs0 : 0 < s.re := by linarith
    have hsA : 1 < s.re + 2 := by linarith
    have hfe := crossHeight_gaussian_two_tsum_eq unitPoleFreeCrossHeightDatum_riemannZeta hy hs0 hhi
    unfold crossHeightGaussianTwoSeries at hfe
    simp only [one_mul, Complex.ofReal_one, Complex.one_cpow, div_one] at hfe
    have hsum_d := summable_smoothAFE_direct (A := 2) (by norm_num) hy hsA
    unfold pureDirectGaussianWitness
    simp only [one_mul]
    rw [hfe, ← hsum_d.sum_add_tsum_nat_add L]
    have halg :
        (((∑ n ∈ Finset.range L,
              (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)) +
            ∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / y))) -
          (∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s y m) -
          smoothAFEZetaShiftedPoleResidue s y) +
          smoothAFEZetaShiftedPoleResidue s y) -
        (∑ n ∈ Finset.range L,
          (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y))) =
        (∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / y))) -
          ∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s y m := by
      simp only [Nat.add_assoc, Nat.add_comm L 1]
      ring
    rw [halg]
    have hsh_d : Summable (fun j : ℕ =>
        ‖(((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / y))‖) :=
      (summable_nat_add_iff
        (f := fun n : ℕ => ‖(((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y))‖) L).mpr
        hsum_d.norm
    have hden1 : 1 ≤ s.re + 2 - 1 := by linarith
    have hb1 : ‖∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / y))‖ ≤
        C₀ * y ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) := by
      have h0 := (norm_tsum_le_tsum_norm hsh_d).trans (hC_dir s y hy hsA L hL1)
      rw [show 1 - (s.re + 2) = -(1 + s.re) by ring] at h0
      exact h0.trans (mul_le_mul_of_nonneg_left
        (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hden1) (by positivity))
    set K_y : ℝ := Kd₀ * y ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)
    have hpt_u : ∀ m : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s y m‖ ≤
        K_y * (m + 1 : ℝ) ^ (-2 : ℝ) := fun m => by
      have h0 : ‖smoothAFEZetaDualCoefficientGeneral s y m‖ ≤
          K_y * (m + 1 : ℝ) ^ (-(3 - s.re)) := by
        dsimp only [K_y]
        simpa only [Nat.cast_one, show -2 * (1 : ℝ) = (-2 : ℝ) by ring,
          show (2 * (1 : ℝ)) + 1 / 2 - s.re = (5 / 2 : ℝ) - s.re by ring,
          show 2 * (1 : ℝ) + 1 - s.re = 3 - s.re by ring] using (hK_dual s y hlo hhi hy).1 m
      exact h0.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos m) (by linarith))
        (by dsimp only [K_y]; positivity))
    have hmaj_u := hsum_p2.mul_left K_y
    have hs_u := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_u hmaj_u
    have hb2 : ‖∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s y m‖ ≤
        (Kd₀ * S_p2) * y ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by
      have h0 := (norm_tsum_le_tsum_norm hs_u).trans
        ((hs_u.tsum_le_tsum hpt_u hmaj_u).trans_eq tsum_mul_left)
      exact h0.trans_eq (by dsimp only [K_y]; ring)
    exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
  have hmain_bd : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      ∀ {x : ℝ}, 0 < x → ∀ L : ℕ, 1 ≤ L →
        ‖(1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s -
            poleClearedPureDirectZetaWitness s x L‖ ≤
          C_dir * x ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) +
            K_dual * x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by
    intro s hlo hhi _ x hx L hL1
    have h2x : 0 < (2 : ℝ) * x := by positivity
    have hpole_eq := smoothAFEZetaShiftedPoleResidue_mul_scale (d := 2) (by omega) hx s
    simp only [Nat.cast_ofNat] at hpole_eq
    have hident :
        (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s - poleClearedPureDirectZetaWitness s x L =
          ((riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) -
              pureDirectGaussianWitness (fun _ => 1) s x L) -
            (2 : ℂ) ^ (-(1 - s)) *
              ((riemannZeta s + smoothAFEZetaShiftedPoleResidue s ((2 : ℝ) * x)) -
                pureDirectGaussianWitness (fun _ => 1) s (2 * x) L) := by
      unfold poleClearedPureDirectZetaWitness
      linear_combination hpole_eq
    rw [hident]
    have hb_x := hsingle s hlo hhi hx L hL1
    have hb_2x := hsingle s hlo hhi h2x L hL1
    have h2_le1 : ‖(2 : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
        show (-(1 - s)).re = -(1 - s.re) by simp]
      exact Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by linarith)
    have h2x_sq : ((2 : ℝ) * x) ^ (2 : ℝ) = 4 * x ^ (2 : ℝ) := by
      rw [Real.mul_rpow two_pos.le hx.le]; norm_num
    have h2x_m2 : ((2 : ℝ) * x) ^ (-2 : ℝ) ≤ x ^ (-2 : ℝ) := by
      rw [Real.mul_rpow two_pos.le hx.le]
      exact mul_le_of_le_one_left (by positivity) (by norm_num)
    have hmul_2x : ‖(2 : ℂ) ^ (-(1 - s)) *
        ((riemannZeta s + smoothAFEZetaShiftedPoleResidue s ((2 : ℝ) * x)) -
          pureDirectGaussianWitness (fun _ => 1) s (2 * x) L)‖ ≤
        4 * C₀ * x ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) +
          (Kd₀ * S_p2) * x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by
      rw [norm_mul]
      calc ‖(2 : ℂ) ^ (-(1 - s))‖ *
            ‖(riemannZeta s + smoothAFEZetaShiftedPoleResidue s ((2 : ℝ) * x)) -
              pureDirectGaussianWitness (fun _ => 1) s (2 * x) L‖
          ≤ 1 * (C₀ * ((2 : ℝ) * x) ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) +
              (Kd₀ * S_p2) * ((2 : ℝ) * x) ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)) :=
            mul_le_mul h2_le1 hb_2x (norm_nonneg _) zero_le_one
        _ ≤ 4 * C₀ * x ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) +
              (Kd₀ * S_p2) * x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by
            rw [one_mul, h2x_sq]
            have h1 : (Kd₀ * S_p2) * ((2 : ℝ) * x) ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) ≤
                (Kd₀ * S_p2) * x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h2x_m2 (by positivity)) (by positivity)
            linarith
    have htri := norm_sub_le
      ((riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) -
        pureDirectGaussianWitness (fun _ => 1) s x L)
      ((2 : ℂ) ^ (-(1 - s)) *
        ((riemannZeta s + smoothAFEZetaShiftedPoleResidue s ((2 : ℝ) * x)) -
          pureDirectGaussianWitness (fun _ => 1) s (2 * x) L))
    have h1nn : 0 ≤ x ^ (2 : ℝ) * (L : ℝ) ^ (-(1 + s.re)) := by positivity
    have h2nn : 0 ≤ x ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by positivity
    dsimp only [C_dir, K_dual]
    nlinarith
  refine ⟨C_dir, K_dual, hC_pos, hK_pos, hmain_bd, ?_⟩
  have hrh_zeta : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| → riemannZeta s ≠ 0 := by
    rw [rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour.2]
    refine forall₄_congr fun s hlo hhi him => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hceil185 : 185 ≤ Nat.ceil |s.im| := by
      have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
      omega
    have hmax1 : max 1 (Nat.ceil |s.im|) = Nat.ceil |s.im| := max_eq_right (by omega)
    rw [← (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).2, hmax1]
  rw [hrh_zeta]
  refine forall₄_congr fun s hlo hhi him => ?_
  constructor
  · intro hζ_ne
    have hpref_pos : 0 < ‖(1 : ℂ) - (2 : ℂ) ^ (-(1 - s))‖ :=
      lt_trans (by norm_num) (one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi)
    set η₀ : ℝ := ‖(1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s‖
    have hη₀_pos : 0 < η₀ := by
      dsimp only [η₀]; rw [norm_mul]
      exact mul_pos hpref_pos (norm_pos_iff.mpr hζ_ne)
    set A_tot : ℝ := C_dir + K_dual * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)
    have hA_pos : 0 < A_tot := by dsimp only [A_tot]; positivity
    set Y₀ : ℝ := 2 * A_tot / η₀ + 1
    have hY₀_gt : 2 * A_tot / η₀ < Y₀ := by dsimp only [Y₀]; linarith
    have hY₀_pos : 0 < Y₀ := by dsimp only [Y₀]; positivity
    set x₀ : ℝ := max |s.im| (Y₀ ^ (4 : ℕ))
    have hx₀_ge_im : |s.im| ≤ x₀ := le_max_left _ _
    have hx₀_ge_Y : Y₀ ^ (4 : ℕ) ≤ x₀ := le_max_right _ _
    have hx₀_1 : 1 ≤ x₀ := (by linarith : 1 ≤ |s.im|).trans hx₀_ge_im
    have hx₀_pos : 0 < x₀ := zero_lt_one.trans_le hx₀_1
    set L₀ : ℕ := max 2 (Nat.ceil (x₀ ^ (2 : ℝ)))
    have hL₀_1 : 1 ≤ L₀ := le_trans (by omega : 1 ≤ 2) (le_max_left _ _)
    have hL₀_ge : x₀ ^ (2 : ℝ) ≤ (L₀ : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 2 _))
    have herr_lt :
        C_dir * x₀ ^ (2 : ℝ) * (L₀ : ℝ) ^ (-(1 + s.re)) +
          K_dual * x₀ ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) < η₀ / 2 := by
      have hp1 : x₀ ^ (2 : ℝ) * (L₀ : ℝ) ^ (-(1 + s.re)) ≤ x₀ ^ (-1 / 4 : ℝ) := by
        have hL_le : (L₀ : ℝ) ^ (-(1 + s.re)) ≤ (x₀ ^ (2 : ℝ)) ^ (-(1 + s.re)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx₀_pos _) hL₀_ge (by linarith)
        calc x₀ ^ (2 : ℝ) * (L₀ : ℝ) ^ (-(1 + s.re))
            ≤ x₀ ^ (2 : ℝ) * (x₀ ^ (2 : ℝ)) ^ (-(1 + s.re)) :=
              mul_le_mul_of_nonneg_left hL_le (by positivity)
          _ = x₀ ^ (2 : ℝ) * x₀ ^ (2 * -(1 + s.re)) := by rw [← Real.rpow_mul hx₀_pos.le]
          _ = x₀ ^ (-2 * s.re) := by rw [← Real.rpow_add hx₀_pos]; congr 1; ring
          _ ≤ x₀ ^ (-1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx₀_1 (by linarith)
      have hp2 : x₀ ^ (-2 : ℝ) ≤ x₀ ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx₀_1 (by norm_num)
      have hx_inv_lt : x₀ ^ (-1 / 4 : ℝ) < η₀ / (2 * A_tot) := by
        have h1 : x₀ ^ (-1 / 4 : ℝ) ≤ (Y₀ ^ (4 : ℕ)) ^ (-1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (pow_pos hY₀_pos 4) hx₀_ge_Y (by norm_num)
        have h2 : (Y₀ ^ (4 : ℕ)) ^ (-1 / 4 : ℝ) = Y₀⁻¹ := by
          rw [← Real.rpow_natCast Y₀ 4, ← Real.rpow_mul hY₀_pos.le]
          norm_num [Real.rpow_neg_one]
        have h3 : Y₀⁻¹ < η₀ / (2 * A_tot) := by
          rw [inv_lt_comm₀ hY₀_pos (by positivity), inv_div]
          exact hY₀_gt
        exact (h1.trans_eq h2).trans_lt h3
      calc C_dir * x₀ ^ (2 : ℝ) * (L₀ : ℝ) ^ (-(1 + s.re)) +
            K_dual * x₀ ^ (-2 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)
          ≤ C_dir * x₀ ^ (-1 / 4 : ℝ) +
              K_dual * x₀ ^ (-1 / 4 : ℝ) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) := by
            have hd1 := mul_le_mul_of_nonneg_left hp1 hC_pos.le
            have hd2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hK_pos.le)
              (by positivity : 0 ≤ (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re))
            linarith
        _ = A_tot * x₀ ^ (-1 / 4 : ℝ) := by dsimp only [A_tot]; ring
        _ < A_tot * (η₀ / (2 * A_tot)) := mul_lt_mul_of_pos_left hx_inv_lt hA_pos
        _ = η₀ / 2 := by field_simp [hA_pos.ne']
    have htb := hmain_bd s hlo hhi him hx₀_pos L₀ hL₀_1
    have htri := norm_sub_norm_le ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)
      (poleClearedPureDirectZetaWitness s x₀ L₀)
    refine ⟨x₀, hx₀_ge_im, ?_⟩
    dsimp only [η₀] at herr_lt
    linarith
  · rintro ⟨x, hx_ge, hbeat⟩ hζ0
    have hx_pos : 0 < x := (by linarith : 0 < |s.im|).trans_le hx_ge
    set L : ℕ := max 2 (Nat.ceil (x ^ (2 : ℝ)))
    have hL1 : 1 ≤ L := le_trans (by omega : 1 ≤ 2) (le_max_left _ _)
    have htb := hmain_bd s hlo hhi him hx_pos L hL1
    have heq : ‖(1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s -
        poleClearedPureDirectZetaWitness s x L‖ = ‖poleClearedPureDirectZetaWitness s x L‖ := by
      rw [hζ0, mul_zero, zero_sub, norm_neg]
    dsimp only [L] at htb heq
    linarith

/-- Uniform vertical bound on `‖zetaChi ((3 / 4 : ℂ) + (u : ℂ) * I)‖` across all `u : ℝ`. -/
private lemma exists_norm_zetaChi_threeQuarters_le :
    ∃ M₃₄ : ℝ, 0 < M₃₄ ∧ ∀ u : ℝ, ‖zetaChi ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ M₃₄ := by
  have hcont : Continuous (fun u : ℝ => zetaChi ((3 / 4 : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    refine (zetaChi_analyticAt ?_).continuousAt.comp (by fun_prop)
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp; norm_num
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-200 : ℝ) 200) hcont.continuousOn
  refine ⟨max 1 M₀, lt_of_lt_of_le zero_lt_one (le_max_left 1 M₀), fun u => ?_⟩
  by_cases hu : |u| ≤ 200
  · exact (hM₀ u (abs_le.mp hu)).trans (le_max_right 1 M₀)
  · push Not at hu
    set s' : ℂ := (1 / 4 : ℂ) - (u : ℂ) * I
    have hs'_0 : 0 < s'.re := by simp [s']
    have hs'_half : s'.re < 1 / 2 := by simp [s']; norm_num
    have hs'_im : 184 < |s'.im| := by
      have him_eq : |s'.im| = |u| := by simp [s']
      linarith
    obtain ⟨h1, h2, h3, h4⟩ :=
      norm_zetaChi_reflected_le_rpow_above_oneHundredEightyFour hs'_0 hs'_half hs'_im
    have h1s' : 1 - s' = (3 / 4 : ℂ) + (u : ℂ) * I := by
      dsimp only [s']; ring
    rw [← h1s', h1]
    exact (h2.trans (h3.trans h4).le).trans (le_max_left 1 M₀)

/-- **Uniform dual-vacuum extraction across the entire open left strip `0 < Re s < 1 / 2`:**
shifting the `m = 0` dual mode `smoothAFEZetaDualCoefficientGeneral s x 0` from `Re w = -1`
rightward across the simple pole `w = 0` to `Re w = 3 / 4 - Re s ∈ (1 / 4, 3 / 4)` (`Re(s + w) = 3 / 4`,
avoiding both `w = 0` and `s + w = 1` by `> 1 / 4`) extracts `-zetaChi s` with an `s`-independent
and `x`-uniform remainder `C_vac * x^{3 / 4 - Re s}`. -/
theorem exists_norm_smoothAFEZetaDualCoefficientGeneral_zero_add_zetaChi_le :
    ∃ C_vac : ℝ, 0 < C_vac ∧
      ∀ (s : ℂ) (x : ℝ), 0 < s.re → s.re < 1 / 2 → 0 < x →
        ‖smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s‖ ≤
          C_vac * x ^ (3 / 4 - s.re) := by
  obtain ⟨M₃₄, hM₃₄_pos, hM₃₄⟩ := exists_norm_zetaChi_threeQuarters_le
  have hgauss_int : Integrable (fun v : ℝ => Real.exp (-(v ^ 2))) := by
    simpa only [pow_zero, one_mul] using integrable_shifted_pow_mul_exp_neg_sq 1 0
  set G₀_int : ℝ := ∫ v : ℝ, Real.exp (-(v ^ 2))
  have hG₀_nn : 0 ≤ G₀_int := integral_nonneg fun _ => by positivity
  set C_vac : ℝ := (1 / (2 * Real.pi)) * M₃₄ * (4 * Real.exp 1) * G₀_int + 1
  refine ⟨C_vac, by dsimp only [C_vac]; positivity, fun s x hs0 hhi hx => ?_⟩
  have hs1 : s.re < 1 := by linarith
  set c_p : ℝ := 3 / 4 - s.re
  have hcp_lo : 1 / 4 < c_p := by dsimp only [c_p]; linarith
  have hcp_hi : c_p < 3 / 4 := by dsimp only [c_p]; linarith
  have hcp_pos : 0 < c_p := lt_trans (by norm_num) hcp_lo
  have hcp_ne : c_p ≠ 0 := hcp_pos.ne'
  -- Step 1: Identify `smoothAFEZetaReflectedTerm s x 0 w = g w * (w - 0)⁻¹` with `g` analytic on `{Re(s + w) < 7 / 8}`.
  set U : Set ℂ := {w : ℂ | (s + w).re < 7 / 8}
  have hU_open : IsOpen U :=
    isOpen_lt (Complex.continuous_re.comp (continuous_const.add continuous_id)) continuous_const
  set g : ℂ → ℂ := fun w => zetaChi (s + w) * (x : ℂ) ^ w * Complex.exp (w ^ (2 : ℕ))
  have hg_diff : DifferentiableOn ℂ g U := by
    intro w hw
    have hre_pos : 0 < (1 - (s + w)).re := by
      have hw' : (s + w).re < 7 / 8 := hw
      simp only [Complex.sub_re, Complex.one_re]; linarith
    haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hd1 : DifferentiableAt ℂ (fun u => zetaChi (s + u)) w :=
      (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hre_pos)).differentiableAt.comp w
        (differentiableAt_const s |>.add differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun u => (x : ℂ) ^ u) w :=
      (differentiable_const_cpow_of_neZero (x : ℂ)).differentiableAt
    have hd3 : DifferentiableAt ℂ (fun u => Complex.exp (u ^ (2 : ℕ))) w :=
      (differentiable_exp.comp (differentiable_pow 2)).differentiableAt
    exact ((hd1.mul hd2).mul hd3).differentiableWithinAt
  have hg_an : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hU_open
  have hg_zero : g 0 = zetaChi s := by
    dsimp only [g]
    simp
  have hH_eq : smoothAFEZetaReflectedTerm s x 0 = fun w => g w * (w - 0)⁻¹ := by
    funext w
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    dsimp only [g, smoothAFEGaussianKernel]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one, sub_zero, div_eq_mul_inv]
    ring
  -- Step 2: Cauchy integral formula on `[-1, c_p] × [-T, T]` for all `T > 0`.
  have hrect : ∀ T : ℝ, 0 < T →
      ((∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * zetaChi s := by
    intro T hT
    set z₁ : ℂ := (-1 : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (c_p : ℂ) + (T : ℂ) * I
    have hz₁_re : z₁.re = -1 := by simp [z₁]
    have hz₁_im : z₁.im = -T := by simp [z₁]
    have hz₂_re : z₂.re = c_p := by simp [z₂]
    have hz₂_im : z₂.im = T := by simp [z₂]
    have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
      intro w hw
      rw [Complex.mem_reProdIm, hz₁_re, hz₂_re, uIcc_of_le (by linarith)] at hw
      show (s + w).re < 7 / 8
      rw [Complex.add_re]
      have hw_hi : w.re ≤ 3 / 4 - s.re := hw.1.2
      linarith
    have hbox := rectIntegral_cauchyFormula_analyticOnNhd hsub hg_an
      (p := 0) (by rw [hz₁_re]; norm_num) (by rw [hz₂_re]; simpa using hcp_pos)
      (by rw [hz₁_im]; simp; linarith) (by rw [hz₂_im]; simp; linarith)
    rw [← hH_eq, hg_zero] at hbox
    simpa [rectIntegral, z₁, z₂, sub_eq_add_neg] using hbox
  -- Step 3: Horizontal edges `(-1)..c_p` at `± i T` vanish via `hasStripPolyGrowthOffReal_zetaChi`.
  obtain ⟨T₀_s, N_s, C_s, hCs_pos, hchi_strip⟩ :=
    hasStripPolyGrowthOffReal_zetaChi (s.re - 1) (3 / 4)
  have hhoriz : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ =>
        ∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set X_bd : ℝ := max (x ^ (-1 : ℝ)) (x ^ c_p)
    set K_sh : ℝ := C_s * X_bd * Real.exp 1
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq (1 + |s.im|) N_s).const_mul K_sh)
    filter_upwards [eventually_ge_atTop (max 1 (|T₀_s| + |s.im| + 2))] with T hT u hu
    rw [Set.uIoc_of_le (by linarith : (-1 : ℝ) ≤ c_p)] at hu
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hT_big : |T₀_s| + |s.im| + 2 ≤ T := (le_max_right _ _).trans hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos (zero_lt_one.trans_le hT1)]
    set w : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hsw_re1 : s.re - 1 ≤ (s + w).re := by simp [w]; linarith [hu.1.le]
    have hsw_re2 : (s + w).re ≤ 3 / 4 := by
      simp [w]; have : u ≤ 3 / 4 - s.re := hu.2; linarith
    have hsw_im_ge : T₀_s ≤ |(s + w).im| := by
      rw [Complex.add_im, show w.im = ε * T by simp [w]]
      have htri : |ε * T| - |s.im| ≤ |s.im + ε * T| := by
        have h := abs_sub_abs_le_abs_sub (ε * T) (-s.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      linarith [le_abs_self T₀_s]
    have hsw_im_le : 1 + |(s + w).im| ≤ (1 + |s.im|) + T := by
      calc 1 + |(s + w).im|
          = 1 + |s.im + ε * T| := by rw [Complex.add_im, show w.im = ε * T by simp [w]]
        _ ≤ 1 + (|s.im| + |ε * T|) := by linarith [abs_add_le s.im (ε * T)]
        _ = (1 + |s.im|) + T := by rw [habsv]; ring
    have hchi_bd : ‖zetaChi (s + w)‖ ≤ C_s * ((1 + |s.im|) + T) ^ N_s :=
      (hchi_strip (s + w) hsw_re1 hsw_re2 hsw_im_ge).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsw_im_le N_s) hCs_pos)
    have hx_le : ‖(x : ℂ) ^ w‖ ≤ X_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, show w.re = u by simp [w]]
      rcases le_total 1 x with h1x | h1x
      · exact (Real.rpow_le_rpow_of_exponent_le h1x hu.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx h1x hu.1.le).trans (le_max_left _ _)
    have hker_le : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 1 * Real.exp (-(T ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hw_re_sq : (w ^ 2).re = u ^ 2 - T ^ (2 : ℕ) := by
        dsimp only [w]
        simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
        nlinarith
      have hu2 : u ^ 2 ≤ 1 := by
        have h1 : -1 ≤ u := hu.1.le
        have h2 : u ≤ 1 := hu.2.trans (by linarith)
        nlinarith
      have hwnorm1 : 1 ≤ ‖w‖ := by
        calc (1 : ℝ) ≤ T := hT1
          _ = |w.im| := by simp [w, habsv]
          _ ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [hw_re_sq]
      exact (div_le_self (Real.exp_nonneg _) hwnorm1).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one]
    rw [norm_mul, norm_mul]
    calc ‖zetaChi (s + w)‖ * ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
        ≤ (C_s * ((1 + |s.im|) + T) ^ N_s) * X_bd * (Real.exp 1 * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul hchi_bd hx_le (norm_nonneg _) (by positivity))
            hker_le (norm_nonneg _) ?_
          exact mul_nonneg (by positivity) ((Real.rpow_nonneg hx.le (-1)).trans (le_max_left _ _))
      _ = K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))) := by
          dsimp only [K_sh]; ring
  -- Step 4: Right vertical edge `Re w = c_p` integrability and pointwise Gaussian majorant.
  have hpt_right : ∀ v : ℝ,
      ‖smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I)‖ ≤
        (M₃₄ * (4 * Real.exp 1) * x ^ c_p) * Real.exp (-(v ^ 2)) := by
    intro v
    have hsw_eq : s + ((c_p : ℂ) + (v : ℂ) * I) =
        (3 / 4 : ℂ) + ((s.im + v : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [c_p]
      · simp [c_p]
    have hchi_v : ‖zetaChi (s + ((c_p : ℂ) + (v : ℂ) * I))‖ ≤ M₃₄ := by
      rw [hsw_eq]; exact hM₃₄ (s.im + v)
    have hker_v := norm_smoothAFEGaussianKernel_vertical_le_of_ne (σ := c_p) hcp_ne v
    have hcp_ker : Real.exp (c_p ^ 2) / |c_p| ≤ 4 * Real.exp 1 := by
      rw [abs_of_pos hcp_pos, div_le_iff₀ hcp_pos]
      have hsq1 : c_p ^ 2 ≤ 1 := by nlinarith
      have hexp1 : Real.exp (c_p ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr hsq1
      have h4 : Real.exp 1 ≤ 4 * Real.exp 1 * c_p := by nlinarith [Real.exp_pos 1]
      exact hexp1.trans h4
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      show (((c_p : ℂ) + (v : ℂ) * I).re) = c_p by simp]
    calc ‖zetaChi (s + ((c_p : ℂ) + (v : ℂ) * I))‖ * x ^ c_p *
          ‖smoothAFEGaussianKernel ((c_p : ℂ) + (v : ℂ) * I)‖
        ≤ M₃₄ * x ^ c_p * ((4 * Real.exp 1) * Real.exp (-(v ^ 2))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hchi_v (by positivity))
            (hker_v.trans (mul_le_mul_of_nonneg_right hcp_ker (Real.exp_nonneg _)))
            (norm_nonneg _) (by positivity)
      _ = (M₃₄ * (4 * Real.exp 1) * x ^ c_p) * Real.exp (-(v ^ 2)) := by ring
  have hright_int : Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I)) := by
    refine Integrable.mono' (hgauss_int.const_mul (M₃₄ * (4 * Real.exp 1) * x ^ c_p)) ?_
      (Filter.Eventually.of_forall hpt_right)
    have hcont : Continuous (fun v : ℝ =>
        smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I)) := by
      rw [hH_eq]
      have hpath : Continuous (fun v : ℝ => (c_p : ℂ) + (v : ℂ) * I) := by fun_prop
      have hg_v : Continuous (fun v : ℝ => g ((c_p : ℂ) + (v : ℂ) * I)) := by
        refine hg_an.continuousOn.comp_continuous hpath fun v => ?_
        show (s + ((c_p : ℂ) + (v : ℂ) * I)).re < 7 / 8
        simp [c_p]; norm_num
      have hinv_v : Continuous (fun v : ℝ => (((c_p : ℂ) + (v : ℂ) * I) - 0)⁻¹) :=
        (hpath.sub continuous_const).inv₀ fun v h0 => by
          have := congrArg Complex.re h0; simp at this; exact hcp_ne this
      exact hg_v.mul hinv_v
    exact hcont.aestronglyMeasurable
  have hleft_int : Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I)) := by
    simpa using smoothAFEZetaReflectedTerm_general_left_one_integrable hx hs0 hs1 0
  -- Step 5: Pass `T → +∞` to extract `smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s`.
  have hlim_r : Tendsto (fun T : ℝ =>
      ∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hright_int tendsto_neg_atTop_atBot tendsto_id
  have hlim_l : Tendsto (fun T : ℝ =>
      ∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hleft_int tendsto_neg_atTop_atBot tendsto_id
  have htop : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz 1 (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz (-1) (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hlim_r.const_smul I)).sub (hlim_l.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 : ℝ)..c_p, smoothAFEZetaReflectedTerm s x 0 ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * zetaChi s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hrect T hT
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  have hcancel :
      (∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I)) -
        (∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I)) =
        (2 * Real.pi : ℂ) * zetaChi s := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hm1_eq : smoothAFEZetaDualCoefficientGeneral s x 0 =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [Complex.real_smul, show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
    calc (zetaChi s * (((0 : ℕ) : ℂ) + 1) ^ (s - 1)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand s (1 / ((((0 : ℕ) : ℝ) + 1) * x))
              ((-1 : ℂ) + (v : ℂ) * I))
        = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ((zetaChi s * (((0 : ℕ) : ℂ) + 1) ^ (s - 1)) *
              ∫ v : ℝ, smoothAFEDualRatioIntegrand s (1 / ((((0 : ℕ) : ℝ) + 1) * x))
                ((-1 : ℂ) + (v : ℂ) * I)) := by ring
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((-1 : ℂ) + (v : ℂ) * I) := by
          rw [integral_smoothAFEZetaReflectedTerm_general_left_one_eq hx hs0 hs1]
  have hsum_eq : smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I) := by
    have hinv : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (2 * Real.pi : ℂ) = 1 := by
      push_cast; field_simp [Real.pi_ne_zero]
    have hmul := congrArg (fun z : ℂ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) * z) hcancel
    rw [mul_sub, ← mul_assoc, hinv, one_mul, ← hm1_eq] at hmul
    linear_combination -hmul
  rw [hsum_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have hint_bd : ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I)‖ ≤
      (M₃₄ * (4 * Real.exp 1) * x ^ c_p) * G₀_int := by
    have h0 := norm_integral_le_of_norm_le
      (hgauss_int.const_mul (M₃₄ * (4 * Real.exp 1) * x ^ c_p))
      (Filter.Eventually.of_forall hpt_right)
    rwa [MeasureTheory.integral_const_mul] at h0
  calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x 0 ((c_p : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * ((M₃₄ * (4 * Real.exp 1) * x ^ c_p) * G₀_int) :=
        mul_le_mul_of_nonneg_left hint_bd (by positivity)
    _ = ((1 / (2 * Real.pi)) * M₃₄ * (4 * Real.exp 1) * G₀_int) * x ^ (3 / 4 - s.re) := by
        dsimp only [c_p]; ring
    _ ≤ C_vac * x ^ (3 / 4 - s.re) := by
        dsimp only [C_vac]
        have : 0 ≤ x ^ (3 / 4 - s.re) := Real.rpow_nonneg hx.le _
        linarith

end Part3PureDirectAndDualVacuum


/-! ### Part 4: Pole-Cleared Reflected-Möbius Cross-Height Sieve, Strictly Sub-Diagonal Annihilation, and Vaughan Forcing Across `Ω_open` -/

section Part4ReflectedMobiusSubdiagonalDuality

/-- Pole-cleared reflected Möbius Dirichlet polynomial `(1 - 2^{-z}) ∑_{d=1}^D μ(d) d^{-z}`. -/
def poleClearedMoebiusPoly (D : ℕ) (z : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-z)) *
    ∑ d ∈ Finset.Icc 1 D, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z)

/-- Sieve coefficient of `(1 - 2^{-z}) (∑_{d=1}^D μ(d) d^{-z}) ζ(z)` at `k ≥ 1`:
`∑_{d ∣ k, d ≤ D} μ(d) - ∑_{2 d ∣ k, d ≤ D} μ(d)`. -/
def poleClearedSieveCoeff (D k : ℕ) : ℂ :=
  (∑ d ∈ k.divisors.filter (· ≤ D), (ArithmeticFunction.moebius d : ℂ)) -
    (if 2 ∣ k then
      ∑ d ∈ (k / 2).divisors.filter (· ≤ D), (ArithmeticFunction.moebius d : ℂ)
    else 0)

/-- Strictly sub-diagonal inner cutoff `⌊(1 / 2) d (|Im s| / 184)^{-δ / 2}⌋₊` (`≤ d / 2`). -/
def subdiagCutoff (δ : ℝ) (s : ℂ) (d : ℕ) : ℕ :=
  Nat.floor ((1 / 2 : ℝ) * (d : ℝ) * (|s.im| / 184) ^ (-δ / 2))

/-- Pole-cleared strictly sub-diagonal reflected-Möbius Gaussian double sum:
only pairs `(d, n)` with `1 ≤ n ≤ subdiagCutoff δ s d` (`2 n ≤ d`, strictly `n < d`) survive. -/
def subdiagMoebiusGaussian (δ : ℝ) (s : ℂ) (x : ℝ) (D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D,
    (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
      ∑ n ∈ Finset.Icc 1 (subdiagCutoff δ s d),
        (n : ℂ) ^ (-s) *
          (smoothAFECutoff ((n : ℝ) / ((d : ℝ) * x)) -
            (2 : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((n : ℝ) / (2 * (d : ℝ) * x)))

/-- Strictly sub-diagonal Vaughan Type-I bilinear Gaussian sum (`2 n ≤ d`, cutoffs `U, V`). -/
def subdiagVaughanTypeI (δ : ℝ) (U V : ℕ) (s : ℂ) (x : ℝ) (D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D,
    -((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) d : ℝ) : ℂ) *
      (d : ℂ) ^ (-(1 - s)) *
      ∑ n ∈ Finset.Icc 1 (subdiagCutoff δ s d),
        (n : ℂ) ^ (-s) *
          (smoothAFECutoff ((n : ℝ) / ((d : ℝ) * x)) -
            (2 : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((n : ℝ) / (2 * (d : ℝ) * x)))

/-- Strictly sub-diagonal Vaughan Type-II bilinear Gaussian sum (`2 n ≤ d`, cutoffs `U, V`). -/
def subdiagVaughanTypeII (δ : ℝ) (U V : ℕ) (s : ℂ) (x : ℝ) (D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D,
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) d : ℝ) : ℂ) *
      (d : ℂ) ^ (-(1 - s)) *
      ∑ n ∈ Finset.Icc 1 (subdiagCutoff δ s d),
        (n : ℂ) ^ (-s) *
          (smoothAFECutoff ((n : ℝ) / ((d : ℝ) * x)) -
            (2 : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((n : ℝ) / (2 * (d : ℝ) * x)))

private lemma norm_moebius_intCast_le_one (d : ℕ) :
    ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp

private lemma sum_divisors_moebius_complex_eq_ite (k : ℕ) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℂ)) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have hc := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at hc
  split_ifs at hc with hk1
  · simpa [if_pos hk1] using hc
  · simpa [if_neg hk1] using hc

private lemma sum_range_add_one_eq_sum_Icc (f : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range M, f (n + 1)) = ∑ m ∈ Finset.Icc 1 M, f m := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (Nat.succ_pos M)]

/-- Exact scale covariance of `smoothAFEZetaDualCoefficientGeneral`: multiplying `x` by `d ≥ 1`
and weighting by `d^{-(1 - s)}` shifts index `m` (`m + 1`) to `d * (m + 1) - 1`. -/
theorem smoothAFEZetaDualCoefficientGeneral_mul_scale
    {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (m : ℕ) :
    (d : ℂ) ^ (-(1 - s)) * smoothAFEZetaDualCoefficientGeneral s ((d : ℝ) * x) m =
      smoothAFEZetaDualCoefficientGeneral s x (d * (m + 1) - 1) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdx_pos : 0 < (d : ℝ) * x := mul_pos hd_pos hx
  have hd_ne0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [smoothAFEZetaDualCoefficientGeneral_eq_deep_even (r := 1) le_rfl hdx_pos hs0 hhi m,
    smoothAFEZetaDualCoefficientGeneral_eq_deep_even (r := 1) le_rfl hx hs0 hhi (d * (m + 1) - 1),
    ← mul_assoc, mul_comm ((d : ℂ) ^ (-(1 - s))) (((1 / (2 * Real.pi) : ℝ) : ℂ)), mul_assoc,
    ← MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  set w : ℂ := ((-2 * ((1 : ℕ) : ℝ) : ℝ) : ℂ) + (v : ℂ) * I
  rw [smoothAFEZetaReflectedTerm_eq_cpow, smoothAFEZetaReflectedTerm_eq_cpow]
  have hdm_pos : 1 ≤ d * (m + 1) := Nat.mul_pos hd (Nat.succ_pos m)
  have hdm_cast : ((d * (m + 1) - 1 : ℕ) : ℂ) + 1 = (d : ℂ) * ((m : ℂ) + 1) := by
    have hnat : (d * (m + 1) - 1) + 1 = d * (m + 1) := Nat.sub_add_cancel hdm_pos
    have hc : (((d * (m + 1) - 1 + 1 : ℕ) : ℂ)) = ((d * (m + 1) : ℕ) : ℂ) := by rw [hnat]
    push_cast at hc ⊢
    exact hc
  have hdx_pow : (((d : ℝ) * x : ℝ) : ℂ) ^ w = (d : ℂ) ^ w * (x : ℂ) ^ w := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hd_pos.le hx.le w,
      Complex.ofReal_natCast]
  have hdm_pow : ((d : ℂ) * ((m : ℂ) + 1)) ^ (s + w - 1) =
      (d : ℂ) ^ (s + w - 1) * ((m : ℂ) + 1) ^ (s + w - 1) := by
    have hm_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
    rw [show (d : ℂ) = ((d : ℝ) : ℂ) by simp,
      show (m : ℂ) + 1 = (((m + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg hd_pos.le hm_nn (s + w - 1)]
  have hd_comb : (d : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ w = (d : ℂ) ^ (s + w - 1) := by
    rw [← Complex.cpow_add _ _ hd_ne0]
    congr 1; ring
  rw [hdm_cast, hdx_pow, hdm_pow]
  calc (d : ℂ) ^ (-(1 - s)) *
        (zetaChi (s + w) * ((m : ℂ) + 1) ^ (s + w - 1) *
          ((d : ℂ) ^ w * (x : ℂ) ^ w) * smoothAFEGaussianKernel w)
      = zetaChi (s + w) * (((d : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ w) * ((m : ℂ) + 1) ^ (s + w - 1)) *
          (x : ℂ) ^ w * smoothAFEGaussianKernel w := by ring
    _ = zetaChi (s + w) * ((d : ℂ) ^ (s + w - 1) * ((m : ℂ) + 1) ^ (s + w - 1)) *
          (x : ℂ) ^ w * smoothAFEGaussianKernel w := by rw [hd_comb]

private lemma tsum_smoothAFEZetaDualCoefficientGeneral_mul_eq_ite_dvd
    {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (_hx : 0 < x) :
    (∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s x (q * (m + 1) - 1)) =
      ∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0 := by
  set g : ℕ → ℂ := fun k =>
    if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0
  set ι : ℕ → ℕ := fun m => q * (m + 1) - 1
  have hι_add1 : ∀ m : ℕ, ι m + 1 = q * (m + 1) := fun m => by
    dsimp only [ι]
    exact Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos m))
  have hι_inj : Function.Injective ι := by
    intro m₁ m₂ heq
    have h1 : ι m₁ + 1 = ι m₂ + 1 := congrArg (· + 1) heq
    rw [hι_add1, hι_add1] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hq h1
    omega
  have hcomp : (fun m : ℕ => smoothAFEZetaDualCoefficientGeneral s x (q * (m + 1) - 1)) =
      fun m : ℕ => g (ι m) := by
    funext m
    dsimp only [g]
    rw [hι_add1 m, if_pos (dvd_mul_right q (m + 1))]
  rw [hcomp]
  refine Function.Injective.tsum_eq hι_inj fun k hk => ?_
  rw [Function.mem_support] at hk
  have hdvd : q ∣ (k + 1) := by
    by_contra hnd
    exact hk (by dsimp only [g]; exact if_neg hnd)
  obtain ⟨c, hc⟩ := hdvd
  have hc_pos : 1 ≤ c := by
    by_contra hc0
    have h0 : c = 0 := by omega
    rw [h0, mul_zero] at hc; omega
  refine ⟨c - 1, ?_⟩
  dsimp only [ι]
  rw [Nat.sub_add_cancel hc_pos, ← hc]
  omega

private lemma poleClearedSieveCoeff_one {D : ℕ} (hD : 1 ≤ D) :
    poleClearedSieveCoeff D 1 = 1 := by
  unfold poleClearedSieveCoeff
  have hflt : (1 : ℕ).divisors.filter (· ≤ D) = {1} := by
    rw [Nat.divisors_one]
    ext d; simp; omega
  have hndvd : ¬ (2 ∣ (1 : ℕ)) := by omega
  rw [hflt, if_neg hndvd, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
  norm_num

private lemma poleClearedSieveCoeff_two {D : ℕ} (hD2 : 2 ≤ D) :
    poleClearedSieveCoeff D 2 = -1 := by
  unfold poleClearedSieveCoeff
  have hflt2 : (2 : ℕ).divisors.filter (· ≤ D) = (2 : ℕ).divisors :=
    Finset.filter_true_of_mem fun d hd =>
      (Nat.le_of_dvd two_pos (Nat.dvd_of_mem_divisors hd)).trans hD2
  have hflt1 : (1 : ℕ).divisors.filter (· ≤ D) = {1} := by
    rw [Nat.divisors_one]
    ext d; simp; omega
  rw [hflt2, sum_divisors_moebius_complex_eq_ite 2, if_neg (by omega : (2 : ℕ) ≠ 1),
    if_pos (dvd_refl 2), Nat.div_self two_pos, hflt1, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one]
  norm_num

private lemma poleClearedSieveCoeff_eq_zero_of_three_le {D k : ℕ}
    (hk3 : 3 ≤ k) (hkD : k ≤ D) :
    poleClearedSieveCoeff D k = 0 := by
  unfold poleClearedSieveCoeff
  have hk_pos : 0 < k := by omega
  have hflt1 : k.divisors.filter (· ≤ D) = k.divisors :=
    Finset.filter_true_of_mem fun d hd =>
      (Nat.le_of_dvd hk_pos (Nat.dvd_of_mem_divisors hd)).trans hkD
  rw [hflt1, sum_divisors_moebius_complex_eq_ite k, if_neg (by omega : k ≠ 1)]
  split_ifs with h2k
  · have hk2_ge2 : 2 ≤ k / 2 := by omega
    have hk2_leD : k / 2 ≤ D := (Nat.div_le_self k 2).trans hkD
    have hflt2 : (k / 2).divisors.filter (· ≤ D) = (k / 2).divisors :=
      Finset.filter_true_of_mem fun d hd =>
        (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hk2_leD
    rw [hflt2, sum_divisors_moebius_complex_eq_ite (k / 2), if_neg (by omega : k / 2 ≠ 1), sub_self]
  · simp

private lemma norm_poleClearedSieveCoeff_le (D k : ℕ) :
    ‖poleClearedSieveCoeff D k‖ ≤ 2 * (k : ℝ) := by
  rcases eq_or_ne k 0 with rfl | hk0
  · unfold poleClearedSieveCoeff; simp
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
  have hsum_le : ∀ m : ℕ, 0 < m →
      ‖∑ d ∈ m.divisors.filter (· ≤ D), (ArithmeticFunction.moebius d : ℂ)‖ ≤ (m : ℝ) := by
    intro m hm
    have hsub : m.divisors.filter (· ≤ D) ⊆ Finset.Icc 1 m := by
      intro d hd
      have hdv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdv hm, Nat.le_of_dvd hm hdv⟩
    calc ‖∑ d ∈ m.divisors.filter (· ≤ D), (ArithmeticFunction.moebius d : ℂ)‖
        ≤ ∑ d ∈ m.divisors.filter (· ≤ D), ‖(ArithmeticFunction.moebius d : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ m.divisors.filter (· ≤ D), (1 : ℝ) :=
          Finset.sum_le_sum fun d _ => norm_moebius_intCast_le_one d
      _ = ((m.divisors.filter (· ≤ D)).card : ℝ) := by simp
      _ ≤ ((Finset.Icc 1 m).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (m : ℝ) := by simp
  unfold poleClearedSieveCoeff
  refine (norm_sub_le _ _).trans ?_
  have h1 := hsum_le k hk_pos
  have h2 : ‖if 2 ∣ k then
      ∑ d ∈ (k / 2).divisors.filter (· ≤ D), (ArithmeticFunction.moebius d : ℂ) else 0‖ ≤ (k : ℝ) := by
    split_ifs with h2k
    · obtain ⟨q, hq⟩ := h2k
      have hq_pos : 0 < k / 2 := by omega
      exact (hsum_le (k / 2) hq_pos).trans (by exact_mod_cast Nat.div_le_self k 2)
    · rw [norm_zero]; positivity
  linarith

/-- **Exact pole-cleared reflected-Möbius cross-height Gaussian sieve identity (`D ≥ 2`):**
combining `crossHeight_gaussian_two_tsum_eq` at scales `d x` and `2 d x` (`1 ≤ d ≤ D`) weighted by
`μ(d) d^{-(1 - s)}` cancels `smoothAFEZetaShiftedPoleResidue` identically to `0`, annihilates every
dual integer `3 ≤ k ≤ D` by Möbius inversion, and isolates `-(I(s, x, 0) - I(s, x, 1))`. -/
theorem poleCleared_reflected_moebius_crossHeight_eq
    {D : ℕ} (hD2 : 2 ≤ D) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    riemannZeta s * poleClearedMoebiusPoly D (1 - s) =
      (∑ d ∈ Finset.Icc 1 D,
          (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
            ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
              (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
                (2 : ℂ) ^ (-(1 - s)) *
                  smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) -
        (smoothAFEZetaDualCoefficientGeneral s x 0 -
          smoothAFEZetaDualCoefficientGeneral s x 1) -
        ∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
          smoothAFEZetaDualCoefficientGeneral s x (j + D) := by
  have hs1 : s.re < 1 := by linarith
  have hsA : 1 < s.re + 2 := by linarith
  have hsum_du : Summable (fun k : ℕ => smoothAFEZetaDualCoefficientGeneral s x k) := by
    obtain ⟨Kd0, _, hKd0⟩ := exists_norm_smoothAFEZetaDualCoefficientGeneral_le hx hs0 hs1
    exact Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2 - s.re) (by linarith)).mul_left Kd0) hKd0
  -- Single-scale rescaled cross-height identity for `q ≥ 1`.
  have hscale_q : ∀ {q : ℕ}, 1 ≤ q →
      (q : ℂ) ^ (-(1 - s)) * riemannZeta s =
        (q : ℂ) ^ (-(1 - s)) *
            (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((q : ℝ) * x)))) -
          (∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
          smoothAFEZetaShiftedPoleResidue s x := by
    intro q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hqx : 0 < (q : ℝ) * x := mul_pos hq_pos hx
    have hfe := crossHeight_gaussian_two_tsum_eq unitPoleFreeCrossHeightDatum_riemannZeta hqx hs0 hhi
    unfold crossHeightGaussianTwoSeries at hfe
    simp only [one_mul, Complex.ofReal_one, Complex.one_cpow, div_one] at hfe
    have hmul := congrArg (fun z : ℂ => (q : ℂ) ^ (-(1 - s)) * z) hfe
    rw [mul_sub, mul_sub, smoothAFEZetaShiftedPoleResidue_mul_scale hq hx s] at hmul
    have hdu_congr :
        (q : ℂ) ^ (-(1 - s)) *
            (∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s ((q : ℝ) * x) m) =
          ∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0 := by
      rw [← tsum_mul_left,
        tsum_congr (fun m => smoothAFEZetaDualCoefficientGeneral_mul_scale hq hx hs0 hhi m)]
      exact tsum_smoothAFEZetaDualCoefficientGeneral_mul_eq_ite_dvd hq hx
    rwa [hdu_congr] at hmul
  -- Subtract `q = 2 * d` from `q = d` for each `d ≥ 1` (canceling `smoothAFEZetaShiftedPoleResidue` identically).
  have hpair_d : ∀ d ∈ Finset.Icc 1 D,
      (ArithmeticFunction.moebius d : ℂ) * ((d : ℂ) ^ (-(1 - s)) *
          (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s) =
        ((ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
            ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
              (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
                (2 : ℂ) ^ (-(1 - s)) *
                  smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) -
          ∑' k : ℕ, (ArithmeticFunction.moebius d : ℂ) *
            ((if d ∣ (k + 1) then (1 : ℂ) else 0) - (if 2 * d ∣ (k + 1) then (1 : ℂ) else 0)) *
            smoothAFEZetaDualCoefficientGeneral s x k := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have h2d1 : 1 ≤ 2 * d := by omega
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have h2d_cpow : ((2 * d : ℕ) : ℂ) ^ (-(1 - s)) =
        (2 : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ (-(1 - s)) := by
      rw [show ((2 * d : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * ((d : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg two_pos.le hd_pos.le (-(1 - s))]
      push_cast; rfl
    have h1 := hscale_q hd1
    have h2 := hscale_q h2d1
    rw [h2d_cpow, show ((2 * d : ℕ) : ℝ) * x = 2 * (d : ℝ) * x by push_cast; ring] at h2
    have hsum_d1 := summable_smoothAFE_direct (A := 2) (by norm_num) (mul_pos hd_pos hx) hsA
    have hsum_d2 := (summable_smoothAFE_direct (A := 2) (by norm_num)
      (show 0 < 2 * (d : ℝ) * x by positivity) hsA).mul_left ((2 : ℂ) ^ (-(1 - s)))
    have hdir_sub :
        (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))) -
          (2 : ℂ) ^ (-(1 - s)) *
            (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
              smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) =
          ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) := by
      rw [← tsum_mul_left, ← hsum_d1.tsum_sub hsum_d2]
      refine tsum_congr fun n => by ring
    have hdu1 : Summable (fun k : ℕ =>
        if d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) := by
      refine Summable.of_norm_bounded hsum_du.norm fun k => ?_
      split_ifs <;> simp
    have hdu2 : Summable (fun k : ℕ =>
        if 2 * d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) := by
      refine Summable.of_norm_bounded hsum_du.norm fun k => ?_
      split_ifs <;> simp
    have hdu_sub :
        (ArithmeticFunction.moebius d : ℂ) *
          ((∑' k : ℕ, if d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
            (∑' k : ℕ, if 2 * d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0)) =
          ∑' k : ℕ, (ArithmeticFunction.moebius d : ℂ) *
            ((if d ∣ (k + 1) then (1 : ℂ) else 0) - (if 2 * d ∣ (k + 1) then (1 : ℂ) else 0)) *
            smoothAFEZetaDualCoefficientGeneral s x k := by
      rw [← hdu1.tsum_sub hdu2, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      split_ifs <;> ring
    have hdiff : (d : ℂ) ^ (-(1 - s)) * (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s =
        (d : ℂ) ^ (-(1 - s)) * riemannZeta s -
          (2 : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ (-(1 - s)) * riemannZeta s := by ring
    rw [hdiff, h1, h2]
    calc (ArithmeticFunction.moebius d : ℂ) *
          (((d : ℂ) ^ (-(1 - s)) *
                (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))) -
              (∑' k : ℕ, if d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
              smoothAFEZetaShiftedPoleResidue s x) -
            ((2 : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ (-(1 - s)) *
                (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
                  smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) -
              (∑' k : ℕ, if 2 * d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
              smoothAFEZetaShiftedPoleResidue s x))
        = (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
            ((∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))) -
              (2 : ℂ) ^ (-(1 - s)) *
                (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
                  smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) -
          (ArithmeticFunction.moebius d : ℂ) *
            ((∑' k : ℕ, if d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
              (∑' k : ℕ, if 2 * d ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0)) := by ring
      _ = _ := by rw [hdir_sub, hdu_sub]
  -- Sum `hpair_d` over `d ∈ Finset.Icc 1 D` and interchange the finite sum with `tsum` on the dual side.
  have hlhs_expand : riemannZeta s * poleClearedMoebiusPoly D (1 - s) =
      ∑ d ∈ Finset.Icc 1 D,
        (ArithmeticFunction.moebius d : ℂ) * ((d : ℂ) ^ (-(1 - s)) *
          (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s) := by
    unfold poleClearedMoebiusPoly
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  rw [hlhs_expand, Finset.sum_congr rfl hpair_d, Finset.sum_sub_distrib]
  -- Identify the finite-sieved dual series with `∑' k, poleClearedSieveCoeff D (k + 1) * I(s, x, k)`.
  have hdu_term_sum : ∀ d ∈ Finset.Icc 1 D, Summable (fun k : ℕ =>
      (ArithmeticFunction.moebius d : ℂ) *
        ((if d ∣ (k + 1) then (1 : ℂ) else 0) - (if 2 * d ∣ (k + 1) then (1 : ℂ) else 0)) *
        smoothAFEZetaDualCoefficientGeneral s x k) := by
    intro d _
    refine Summable.of_norm_bounded (hsum_du.norm.mul_left 2) fun k => ?_
    rw [norm_mul, norm_mul]
    have hm1 := norm_moebius_intCast_le_one d
    have hif : ‖(if d ∣ (k + 1) then (1 : ℂ) else 0) - (if 2 * d ∣ (k + 1) then (1 : ℂ) else 0)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖if d ∣ (k + 1) then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
      have h2 : ‖if 2 * d ∣ (k + 1) then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
      linarith
    calc ‖(ArithmeticFunction.moebius d : ℂ)‖ *
          ‖(if d ∣ (k + 1) then (1 : ℂ) else 0) - (if 2 * d ∣ (k + 1) then (1 : ℂ) else 0)‖ *
          ‖smoothAFEZetaDualCoefficientGeneral s x k‖
        ≤ 1 * 2 * ‖smoothAFEZetaDualCoefficientGeneral s x k‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul hm1 hif (norm_nonneg _) zero_le_one) (norm_nonneg _)
      _ = 2 * ‖smoothAFEZetaDualCoefficientGeneral s x k‖ := by ring
  rw [← Summable.tsum_finsetSum hdu_term_sum]
  have hcoeff_k : ∀ k : ℕ,
      (∑ d ∈ Finset.Icc 1 D,
          (ArithmeticFunction.moebius d : ℂ) *
            ((if d ∣ (k + 1) then (1 : ℂ) else 0) - (if 2 * d ∣ (k + 1) then (1 : ℂ) else 0)) *
            smoothAFEZetaDualCoefficientGeneral s x k) =
        poleClearedSieveCoeff D (k + 1) * smoothAFEZetaDualCoefficientGeneral s x k := by
    intro k
    rw [← Finset.sum_mul]
    congr 1
    set m : ℕ := k + 1
    have hm_pos : 0 < m := Nat.succ_pos k
    have hsplit : (∑ d ∈ Finset.Icc 1 D,
          (ArithmeticFunction.moebius d : ℂ) *
            ((if d ∣ m then (1 : ℂ) else 0) - (if 2 * d ∣ m then (1 : ℂ) else 0))) =
        (∑ d ∈ Finset.Icc 1 D, if d ∣ m then (ArithmeticFunction.moebius d : ℂ) else 0) -
          (∑ d ∈ Finset.Icc 1 D, if 2 * d ∣ m then (ArithmeticFunction.moebius d : ℂ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
    rw [hsplit]
    unfold poleClearedSieveCoeff
    congr 1
    · rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨fun ⟨⟨_, hdD⟩, hdm⟩ => ⟨⟨hdm, hm_pos.ne'⟩, hdD⟩,
        fun ⟨⟨hdm, _⟩, hdD⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hdm hm_pos, hdD⟩, hdm⟩⟩
    · by_cases h2m : 2 ∣ m
      · rw [if_pos h2m, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        obtain ⟨q, hq_eq⟩ := h2m
        have hq_pos : 0 < q := by omega
        have hm_div : m / 2 = q := by rw [hq_eq, Nat.mul_div_right q two_pos]
        rw [hm_div]
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨_, hdD⟩, h2dm⟩
          rw [hq_eq, mul_dvd_mul_iff_left (by omega : 2 ≠ 0)] at h2dm
          exact ⟨⟨h2dm, hq_pos.ne'⟩, hdD⟩
        · rintro ⟨⟨hdq, _⟩, hdD⟩
          have h2dm : 2 * d ∣ m := by rw [hq_eq]; exact mul_dvd_mul_left 2 hdq
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdq hq_pos, hdD⟩, h2dm⟩
      · rw [if_neg h2m]
        refine Finset.sum_eq_zero fun d _ => if_neg fun h2dm => h2m (dvd_trans (dvd_mul_right 2 d) h2dm)
  have hsum_sieved : Summable (fun k : ℕ =>
      poleClearedSieveCoeff D (k + 1) * smoothAFEZetaDualCoefficientGeneral s x k) :=
    (summable_sum hdu_term_sum).congr hcoeff_k
  rw [tsum_congr hcoeff_k, ← hsum_sieved.sum_add_tsum_nat_add D]
  -- Evaluate `∑ k ∈ Finset.range D, poleClearedSieveCoeff D (k + 1) * I(s, x, k) = I(s, x, 0) - I(s, x, 1)`.
  have hhead_eq : (∑ k ∈ Finset.range D,
        poleClearedSieveCoeff D (k + 1) * smoothAFEZetaDualCoefficientGeneral s x k) =
      smoothAFEZetaDualCoefficientGeneral s x 0 - smoothAFEZetaDualCoefficientGeneral s x 1 := by
    have hsplit_range : Finset.range D = Finset.range (2 + (D - 2)) :=
      congrArg Finset.range (by omega)
    rw [hsplit_range, Finset.sum_range_add]
    have hr2 : (∑ k ∈ Finset.range 2,
          poleClearedSieveCoeff D (k + 1) * smoothAFEZetaDualCoefficientGeneral s x k) =
        smoothAFEZetaDualCoefficientGeneral s x 0 - smoothAFEZetaDualCoefficientGeneral s x 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [zero_add, poleClearedSieveCoeff_one (by omega : 1 ≤ D),
        poleClearedSieveCoeff_two hD2, one_mul, neg_one_mul]
      ring
    have hmid0 : (∑ j ∈ Finset.range (D - 2),
          poleClearedSieveCoeff D (2 + j + 1) * smoothAFEZetaDualCoefficientGeneral s x (2 + j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt : j < D - 2 := Finset.mem_range.mp hj
      rw [poleClearedSieveCoeff_eq_zero_of_three_le (by omega) (by omega), zero_mul]
    rw [hr2, hmid0, add_zero]
  rw [hhead_eq]
  simp only [Nat.add_assoc, Nat.add_comm D 1]
  ring

/-- **Strict sub-diagonality and low-divisor annihilation of `subdiagCutoff`:**
for every `δ > 0`, `184 < |Im s|`, and `d : ℕ`:
1. every `n ∈ Finset.Icc 1 (subdiagCutoff δ s d)` satisfies `2 * n ≤ d` (hence `n < d`, excluding
   the diagonal `n = d` and all super-diagonal pairs `n > d`);
2. for every `d < ⌈2 (|Im s| / 184)^{δ / 2}⌉₊` (in particular `d = 1` and `d = 2`),
   `subdiagCutoff δ s d = 0`. -/
theorem subdiagCutoff_two_mul_le_and_eq_zero_of_lt
    {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (him : 184 < |s.im|) :
    (∀ (d n : ℕ), n ∈ Finset.Icc 1 (subdiagCutoff δ s d) → 2 * n ≤ d ∧ n < d) ∧
      3 ≤ Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2)) ∧
      (∀ d : ℕ, d < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2)) → subdiagCutoff δ s d = 0) := by
  have hrat_gt1 : 1 < |s.im| / 184 := by linarith
  have hrat_pos : 0 < |s.im| / 184 := zero_lt_one.trans hrat_gt1
  have hrpow_lt1 : (|s.im| / 184) ^ (-δ / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hrat_gt1 (by linarith)
  have hrpow_gt1 : 1 < (|s.im| / 184) ^ (δ / 2) :=
    Real.one_lt_rpow hrat_gt1 (by positivity)
  refine ⟨fun d n hn => ?_, ?_, fun d hd => ?_⟩
  · obtain ⟨hn1, hn_hi⟩ := Finset.mem_Icc.mp hn
    have hnR : (n : ℝ) ≤ (subdiagCutoff δ s d : ℝ) := by exact_mod_cast hn_hi
    unfold subdiagCutoff at hnR
    have hfl : (Nat.floor ((1 / 2 : ℝ) * (d : ℝ) * (|s.im| / 184) ^ (-δ / 2)) : ℝ) ≤
        (1 / 2 : ℝ) * (d : ℝ) * (|s.im| / 184) ^ (-δ / 2) :=
      Nat.floor_le (by positivity)
    have hle_half : (1 / 2 : ℝ) * (d : ℝ) * (|s.im| / 184) ^ (-δ / 2) ≤ (1 / 2 : ℝ) * (d : ℝ) :=
      mul_le_of_le_one_right (by positivity) hrpow_lt1.le
    have h2nR : (2 * n : ℝ) ≤ (d : ℝ) := by linarith
    have h2n : 2 * n ≤ d := by exact_mod_cast h2nR
    exact ⟨h2n, by omega⟩
  · have hgt2 : (2 : ℝ) < 2 * (|s.im| / 184) ^ (δ / 2) := by linarith
    have hlt_ceil : 2 < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2)) :=
      (Nat.lt_ceil).mpr (by exact_mod_cast hgt2)
    omega
  · unfold subdiagCutoff
    refine Nat.floor_eq_zero.mpr ?_
    have hd_lt : (d : ℝ) < 2 * (|s.im| / 184) ^ (δ / 2) := (Nat.lt_ceil).mp hd
    have hprod1 : (|s.im| / 184) ^ (δ / 2) * (|s.im| / 184) ^ (-δ / 2) = 1 := by
      rw [← Real.rpow_add hrat_pos, show δ / 2 + -δ / 2 = 0 by ring, Real.rpow_zero]
    calc (1 / 2 : ℝ) * (d : ℝ) * (|s.im| / 184) ^ (-δ / 2)
        < (1 / 2 : ℝ) * (2 * (|s.im| / 184) ^ (δ / 2)) * (|s.im| / 184) ^ (-δ / 2) :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hd_lt (by norm_num)) (by positivity)
      _ = (|s.im| / 184) ^ (δ / 2) * (|s.im| / 184) ^ (-δ / 2) := by ring
      _ = 1 := hprod1

/-- Reusable single-scale super-cutoff Gaussian tail bound above `B_sub ≤ M + 1`. -/
private lemma subdiag_direct_single_tail_le
    {A : ℕ} {K_cut : ℝ} (hA_le : (2 : ℝ) ≤ (A : ℝ)) (hK_cut0 : 0 ≤ K_cut)
    (hK_cut : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ K_cut * u ^ (-(A : ℝ)))
    {S_p2 : ℝ} (hsum_p2 : Summable (fun j : ℕ => (j + 1 : ℝ) ^ (-2 : ℝ)))
    (hSp2_eq : ∑' j : ℕ, (j + 1 : ℝ) ^ (-2 : ℝ) = S_p2)
    {s : ℂ} (hs0 : 0 < s.re)
    {y B_sub : ℝ} (M : ℕ) (hy : 0 < y) (hB_pos : 0 < B_sub) (hB_le : B_sub ≤ (M : ℝ) + 1) :
    ‖∑' j : ℕ, (((j + M + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + M + 1 : ℕ) : ℝ) / y))‖ ≤
      ((K_cut + 1) * S_p2) * y ^ (A : ℝ) * B_sub ^ (2 - (A : ℝ)) := by
  set C_y : ℝ := (K_cut + 1) * y ^ (A : ℝ) * B_sub ^ (2 - (A : ℝ))
  have hpt : ∀ j : ℕ,
      ‖(((j + M + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + M + 1 : ℕ) : ℝ) / y))‖ ≤
        C_y * (j + 1 : ℝ) ^ (-2 : ℝ) := by
    intro j
    have hk_pos_n : 0 < j + M + 1 := by omega
    have hk_pos : (0 : ℝ) < ((j + M + 1 : ℕ) : ℝ) := by exact_mod_cast hk_pos_n
    have hB_le_k : B_sub ≤ ((j + M + 1 : ℕ) : ℝ) :=
      hB_le.trans (by push_cast; linarith : (M : ℝ) + 1 ≤ ((j + M + 1 : ℕ) : ℝ))
    have hj_le_k : (j + 1 : ℝ) ≤ ((j + M + 1 : ℕ) : ℝ) := by push_cast; linarith
    have ht0 := norm_smoothAFE_term_le hK_cut hy s (j + M + 1) hk_pos_n
    have hsplit_p : (((j + M + 1 : ℕ) : ℝ) ^ (-(s.re + (A : ℝ)))) =
        (((j + M + 1 : ℕ) : ℝ) ^ (2 - (A : ℝ))) * (((j + M + 1 : ℕ) : ℝ) ^ (-(2 + s.re))) := by
      rw [← Real.rpow_add hk_pos]; congr 1; ring
    have hp1 : (((j + M + 1 : ℕ) : ℝ) ^ (2 - (A : ℝ))) ≤ B_sub ^ (2 - (A : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hB_pos hB_le_k (by linarith)
    have hp2 : (((j + M + 1 : ℕ) : ℝ) ^ (-(2 + s.re))) ≤ (j + 1 : ℝ) ^ (-2 : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk_pos_n) (by linarith)).trans
        (Real.rpow_le_rpow_of_nonpos (by positivity) hj_le_k (by norm_num))
    calc ‖(((j + M + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + M + 1 : ℕ) : ℝ) / y))‖
        ≤ K_cut * y ^ (A : ℝ) * (((j + M + 1 : ℕ) : ℝ) ^ (-(s.re + (A : ℝ)))) := ht0
      _ ≤ (K_cut + 1) * y ^ (A : ℝ) *
            ((((j + M + 1 : ℕ) : ℝ) ^ (2 - (A : ℝ))) * (((j + M + 1 : ℕ) : ℝ) ^ (-(2 + s.re)))) := by
          rw [← hsplit_p]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
      _ ≤ (K_cut + 1) * y ^ (A : ℝ) * (B_sub ^ (2 - (A : ℝ)) * (j + 1 : ℝ) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hp1 hp2 (by positivity) (by positivity))
            (by positivity)
      _ = C_y * (j + 1 : ℝ) ^ (-2 : ℝ) := by dsimp only [C_y]; ring
  have hmaj := hsum_p2.mul_left C_y
  have hs_j := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hmaj
  exact (norm_tsum_le_tsum_norm hs_j).trans
    ((hs_j.tsum_le_tsum hpt hmaj).trans_eq (by rw [tsum_mul_left, hSp2_eq]; dsimp only [C_y]; ring))

/-- Splits the reflected-Möbius direct Gaussian double sum at `subdiagCutoff δ s d`. -/
private lemma subdiag_split_direct_sum_eq
    {δ : ℝ} {A : ℕ} (hA_pos : 0 < (A : ℝ)) {x : ℝ} (hx_pos : 0 < x)
    {s : ℂ} (hsA : 1 < s.re + (A : ℝ)) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
          ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) =
      subdiagMoebiusGaussian δ s x D +
        ∑ d ∈ Finset.Icc 1 D,
          (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
            ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
              (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
                (2 : ℂ) ^ (-(1 - s)) *
                  smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) := by
  have hsplit_dir : ∀ d ∈ Finset.Icc 1 D,
      (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
          (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
            (2 : ℂ) ^ (-(1 - s)) *
              smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) =
        (∑ n ∈ Finset.Icc 1 (subdiagCutoff δ s d),
            (n : ℂ) ^ (-s) *
              (smoothAFECutoff ((n : ℝ) / ((d : ℝ) * x)) -
                (2 : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((n : ℝ) / (2 * (d : ℝ) * x)))) +
          ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) := by
    intro d hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have h2dx_pos : 0 < 2 * (d : ℝ) * x := by
      rw [mul_assoc]; exact mul_pos two_pos (mul_pos hd_pos hx_pos)
    have hs1_d := summable_smoothAFE_direct hA_pos (mul_pos hd_pos hx_pos) hsA
    have hs2_d := (summable_smoothAFE_direct hA_pos h2dx_pos hsA).mul_left ((2 : ℂ) ^ (-(1 - s)))
    have hs_comb : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (-s) *
        (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
          (2 : ℂ) ^ (-(1 - s)) *
            smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) :=
      (hs1_d.sub hs2_d).congr fun n => by ring
    rw [← hs_comb.sum_add_tsum_nat_add (subdiagCutoff δ s d),
      sum_range_add_one_eq_sum_Icc
        (fun m : ℕ => (m : ℂ) ^ (-s) *
          (smoothAFECutoff ((m : ℝ) / ((d : ℝ) * x)) -
            (2 : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((m : ℝ) / (2 * (d : ℝ) * x))))
        (subdiagCutoff δ s d)]
  unfold subdiagMoebiusGaussian
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d hd => by rw [hsplit_dir d hd, mul_add]

/-- Reusable bound on the sieved dual tail `k ≥ D + 1` at `x = c * |Im s|^{-δ}`. -/
private lemma subdiag_sieved_dual_tail_le
    {δ : ℝ} {r : ℕ} (hr2R : (2 : ℝ) ≤ (r : ℝ)) {K_dual : ℝ} (hK_dual_pos : 0 < K_dual)
    (hK_dual : ∀ (s : ℂ) (y : ℝ), 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 0 < y →
      ∀ n : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s y n‖ ≤
        K_dual * y ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
          (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {c : ℝ} (hc_pos : 0 < c) {D : ℕ} (hD1 : 1 ≤ D)
    (hD_ge : c ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ) ≤ (D : ℝ)) :
    ‖∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
        smoothAFEZetaDualCoefficientGeneral s (c * |s.im| ^ (-δ)) (j + D)‖ ≤
      (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
        (c ^ (-2 * (r : ℝ)) * c ^ (4 * (r : ℝ) - 3)) *
        |s.im| ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) := by
  set τ : ℝ := |s.im|
  have hτ1 : 1 < τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := zero_lt_one.trans hτ1
  have hτ_negδ_pos : 0 < τ ^ (-δ) := Real.rpow_pos_of_pos hτ_pos _
  set x : ℝ := c * τ ^ (-δ)
  have hx_pos : 0 < x := mul_pos hc_pos hτ_negδ_pos
  set P_du : ℝ := 2 * (r : ℝ) - s.re
  have hP_gt1 : 1 < P_du := by dsimp only [P_du]; linarith
  have hP_sub1 : 1 ≤ P_du - 1 := by dsimp only [P_du]; linarith
  set A_du : ℝ := 2 * K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
  have hA_du_nn : 0 ≤ A_du := by dsimp only [A_du]; positivity
  have hmaj_du : Summable (fun j : ℕ => A_du * (((j + D + 1 : ℕ) : ℝ) ^ (-P_du))) := by
    refine Summable.mul_left _ ?_
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-P_du)) := by
      rw [Real.summable_nat_rpow]; linarith
    exact ((summable_nat_add_iff (D + 1)).mpr hbase).congr fun j => by
      push_cast; congr 1; ring
  have hpt_du : ∀ j : ℕ,
      ‖poleClearedSieveCoeff D (j + D + 1) * smoothAFEZetaDualCoefficientGeneral s x (j + D)‖ ≤
        A_du * (((j + D + 1 : ℕ) : ℝ) ^ (-P_du)) := by
    intro j
    rw [norm_mul]
    have h1 := norm_poleClearedSieveCoeff_le D (j + D + 1)
    have h2 := hK_dual s x hlo hhi hx_pos (j + D)
    have hk_pos : (0 : ℝ) < ((j + D + 1 : ℕ) : ℝ) := by positivity
    have hk_eq : ((j + D : ℕ) + 1 : ℝ) = ((j + D + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hk_eq] at h2
    have hpow_comb : ((j + D + 1 : ℕ) : ℝ) *
        (((j + D + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) =
        ((j + D + 1 : ℕ) : ℝ) ^ (-P_du) := by
      calc ((j + D + 1 : ℕ) : ℝ) * (((j + D + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)))
          = (((j + D + 1 : ℕ) : ℝ) ^ (1 : ℝ)) *
              (((j + D + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) := by rw [Real.rpow_one]
        _ = ((j + D + 1 : ℕ) : ℝ) ^ (-P_du) := by
            rw [← Real.rpow_add hk_pos]; dsimp only [P_du]; congr 1; ring
    calc ‖poleClearedSieveCoeff D (j + D + 1)‖ *
          ‖smoothAFEZetaDualCoefficientGeneral s x (j + D)‖
        ≤ (2 * ((j + D + 1 : ℕ) : ℝ)) *
            (K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              (((j + D + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = A_du * (((j + D + 1 : ℕ) : ℝ) *
            (((j + D + 1 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)))) := by dsimp only [A_du]; ring
      _ = A_du * (((j + D + 1 : ℕ) : ℝ) ^ (-P_du)) := by rw [hpow_comb]
  have hsum_j := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_du hmaj_du
  have hts_le : ‖∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
      smoothAFEZetaDualCoefficientGeneral s x (j + D)‖ ≤ A_du * (D : ℝ) ^ (1 - P_du) := by
    calc ‖∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
            smoothAFEZetaDualCoefficientGeneral s x (j + D)‖
        ≤ ∑' j : ℕ, A_du * (((j + D + 1 : ℕ) : ℝ) ^ (-P_du)) :=
          (norm_tsum_le_tsum_norm hsum_j).trans (hsum_j.tsum_le_tsum hpt_du hmaj_du)
      _ = A_du * ∑' j : ℕ, (((j + D + 1 : ℕ) : ℝ) ^ (-P_du)) := tsum_mul_left
      _ ≤ A_du * ((D : ℝ) ^ (1 - P_du) / (P_du - 1)) :=
          mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hP_gt1 hD1) hA_du_nn
      _ ≤ A_du * (D : ℝ) ^ (1 - P_du) :=
          mul_le_mul_of_nonneg_left
            (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg D) _) hP_sub1) hA_du_nn
  have hD_ge1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hD_pow : (D : ℝ) ^ (1 - P_du) ≤
      c ^ (4 * (r : ℝ) - 3) * τ ^ ((1 + 3 * δ) * (3 / 2 - 2 * (r : ℝ))) := by
    have h1 : (D : ℝ) ^ (1 - P_du) ≤ (D : ℝ) ^ (3 / 2 - 2 * (r : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hD_ge1 (by dsimp only [P_du]; linarith)
    have h2 : (D : ℝ) ^ (3 / 2 - 2 * (r : ℝ)) ≤
        (c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)) ^ (3 / 2 - 2 * (r : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos
        (mul_pos (Real.rpow_pos_of_pos hc_pos _) (Real.rpow_pos_of_pos hτ_pos _))
        hD_ge (by linarith)
    have h3 : (c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)) ^ (3 / 2 - 2 * (r : ℝ)) =
        c ^ (4 * (r : ℝ) - 3) * τ ^ ((1 + 3 * δ) * (3 / 2 - 2 * (r : ℝ))) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ_pos.le _),
        ← Real.rpow_mul hc_pos.le, ← Real.rpow_mul hτ_pos.le]
      congr 2; ring
    exact (h1.trans h2).trans_eq h3
  have hx_pow_du : x ^ (-2 * (r : ℝ)) = c ^ (-2 * (r : ℝ)) * τ ^ (2 * (r : ℝ) * δ) := by
    dsimp only [x]
    rw [Real.mul_rpow hc_pos.le hτ_negδ_pos.le, ← Real.rpow_mul hτ_pos.le]
    congr 2; ring
  have h1τ_le : (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) ≤
      (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by
    have hexp_nn : 0 ≤ (2 * r : ℝ) + 1 / 2 - s.re := by linarith
    have hexp_le : (2 * r : ℝ) + 1 / 2 - s.re ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
        ≤ (2 * τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.rpow_le_rpow (by positivity) (by linarith) hexp_nn
      _ = (2 : ℝ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.mul_rpow two_pos.le hτ_pos.le
      _ ≤ (2 : ℝ) ^ (((2 * r + 1 : ℕ) : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
            (Real.rpow_nonneg hτ_pos.le _)
      _ = (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by rw [Real.rpow_natCast]
  have hτ_comb_eq :
      τ ^ (2 * (r : ℝ) * δ) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
        τ ^ ((1 + 3 * δ) * (3 / 2 - 2 * (r : ℝ))) =
      τ ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) := by
    rw [← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
    congr 1; ring
  calc ‖∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
          smoothAFEZetaDualCoefficientGeneral s x (j + D)‖
      ≤ A_du * (D : ℝ) ^ (1 - P_du) := hts_le
    _ ≤ (2 * K_dual * (c ^ (-2 * (r : ℝ)) * τ ^ (2 * (r : ℝ) * δ)) *
          ((2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re))) *
          (c ^ (4 * (r : ℝ) - 3) * τ ^ ((1 + 3 * δ) * (3 / 2 - 2 * (r : ℝ)))) := by
        dsimp only [A_du]; rw [hx_pow_du]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1τ_le
          (mul_nonneg (mul_nonneg zero_le_two hK_dual_pos.le)
            (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ_pos.le _))))
          hD_pow (Real.rpow_nonneg (Nat.cast_nonneg D) _)
          (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hK_dual_pos.le)
            (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ_pos.le _)))
            (mul_nonneg (pow_nonneg zero_le_two _) (Real.rpow_nonneg hτ_pos.le _)))
    _ = (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
          (c ^ (-2 * (r : ℝ)) * c ^ (4 * (r : ℝ) - 3)) *
          (τ ^ (2 * (r : ℝ) * δ) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
            τ ^ ((1 + 3 * δ) * (3 / 2 - 2 * (r : ℝ)))) := by ring
    _ = (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
          (c ^ (-2 * (r : ℝ)) * c ^ (4 * (r : ℝ) - 3)) *
          τ ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) := by rw [hτ_comb_eq]

/-- Reusable bound on the super-cutoff direct Gaussian sum `j + subdiagCutoff δ s d + 1` across `1 ≤ d ≤ D`. -/
private lemma subdiag_supercutoff_direct_sum_le
    {δ : ℝ} (hδ0 : 0 < δ) {A : ℕ} (hA6 : 6 ≤ A) {K_cut : ℝ} (hK_cut0 : 0 ≤ K_cut)
    (hK_cut : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ K_cut * u ^ (-(A : ℝ)))
    {S_p2 : ℝ} (hSp2_pos : 0 < S_p2)
    (hsum_p2 : Summable (fun j : ℕ => (j + 1 : ℝ) ^ (-2 : ℝ)))
    (hSp2_eq : ∑' j : ℕ, (j + 1 : ℝ) ^ (-2 : ℝ) = S_p2)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {c : ℝ} (hc_pos : 0 < c) {D : ℕ} (hD1 : 1 ≤ D) :
    let x : ℝ := c * |s.im| ^ (-δ)
    ‖∑ d ∈ Finset.Icc 1 D,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
          ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))‖ ≤
      ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
        (D : ℝ) ^ (5 / 2 : ℝ) * c ^ (A : ℝ) *
        |s.im| ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) := by
  dsimp only
  have hA6R : (6 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA6
  have hA_pos : (0 : ℝ) < (A : ℝ) := by linarith
  have hsA : 1 < s.re + (A : ℝ) := by linarith
  set τ : ℝ := |s.im|
  have hτ1 : 1 < τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := zero_lt_one.trans hτ1
  have hτ_negδ_pos : 0 < τ ^ (-δ) := Real.rpow_pos_of_pos hτ_pos _
  set x : ℝ := c * τ ^ (-δ)
  have hx_pos : 0 < x := mul_pos hc_pos hτ_negδ_pos
  have hrat_pos : 0 < τ / 184 := div_pos hτ_pos (by norm_num)
  have hrat_half_pos : 0 < (τ / 184) ^ (-δ / 2) := Real.rpow_pos_of_pos hrat_pos _
  have h2_le1 : ‖(2 : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
      show (-(1 - s)).re = -(1 - s.re) by simp]
    exact Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by linarith)
  have hC0_nn : 0 ≤ (1 + (2 : ℝ) ^ A) * (K_cut + 1) * S_p2 :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hSp2_pos.le
  have hC1_nn : 0 ≤ (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith)) hSp2_pos.le
  have hpt_d : ∀ d ∈ Finset.Icc 1 D,
      ‖(ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
          ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))‖ ≤
        ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
          (D : ℝ) ^ (3 / 2 : ℝ) * c ^ (A : ℝ) *
          τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hdx_pos : 0 < (d : ℝ) * x := mul_pos hd_pos hx_pos
    have h2dx_pos : 0 < 2 * (d : ℝ) * x := by rw [mul_assoc]; exact mul_pos two_pos hdx_pos
    set B_d : ℝ := (1 / 2 : ℝ) * (d : ℝ) * (τ / 184) ^ (-δ / 2)
    have hBd_pos : 0 < B_d := mul_pos (mul_pos (by norm_num) hd_pos) hrat_half_pos
    have hBd_le : B_d ≤ (subdiagCutoff δ s d : ℝ) + 1 := (Nat.lt_floor_add_one B_d).le
    have hs1_j : Summable (fun j : ℕ => (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
        smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))) :=
      (summable_nat_add_iff
        (f := fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (-s) *
          smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))) (subdiagCutoff δ s d)).mpr
        (summable_smoothAFE_direct hA_pos hdx_pos hsA)
    have hs2_j : Summable (fun j : ℕ => (2 : ℂ) ^ (-(1 - s)) *
        (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
          smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) :=
      ((summable_nat_add_iff
        (f := fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (-s) *
          smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) (subdiagCutoff δ s d)).mpr
        (summable_smoothAFE_direct hA_pos h2dx_pos hsA)).mul_left ((2 : ℂ) ^ (-(1 - s)))
    have hts_split :
        (∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))) =
          (∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))) -
          (2 : ℂ) ^ (-(1 - s)) *
            (∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
              smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))) := by
      rw [← tsum_mul_left, ← hs1_j.tsum_sub hs2_j]
      exact tsum_congr fun j => by ring
    have hb1 := subdiag_direct_single_tail_le (by linarith : (2 : ℝ) ≤ (A : ℝ)) hK_cut0 hK_cut
      hsum_p2 hSp2_eq hs0 (subdiagCutoff δ s d) hdx_pos hBd_pos hBd_le
    have hb2 := subdiag_direct_single_tail_le (by linarith : (2 : ℝ) ≤ (A : ℝ)) hK_cut0 hK_cut
      hsum_p2 hSp2_eq hs0 (subdiagCutoff δ s d) h2dx_pos hBd_pos hBd_le
    have h2dx_A : (2 * (d : ℝ) * x) ^ (A : ℝ) = (2 : ℝ) ^ A * ((d : ℝ) * x) ^ (A : ℝ) := by
      rw [mul_assoc, Real.mul_rpow two_pos.le hdx_pos.le, Real.rpow_natCast, ← mul_assoc]
    rw [h2dx_A] at hb2
    have hcomb_j :
        ‖∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))‖ ≤
          ((1 + (2 : ℝ) ^ A) * (K_cut + 1) * S_p2) * ((d : ℝ) * x) ^ (A : ℝ) * B_d ^ (2 - (A : ℝ)) := by
      rw [hts_split]
      have ht := norm_sub_le
        (∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
          smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x))))
        ((2 : ℂ) ^ (-(1 - s)) *
          ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))
      rw [norm_mul] at ht
      have hm2 := (mul_le_of_le_one_left (norm_nonneg _) h2_le1).trans hb2
      linarith
    have hd_pref : ‖(ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s))‖ ≤
        (d : ℝ) ^ (s.re - 1) := by
      rw [norm_mul, show (d : ℂ) = ((d : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos, show (-(1 - s)).re = s.re - 1 by simp]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hd_pos.le _) (norm_moebius_intCast_le_one d)
    have hdx_pow : ((d : ℝ) * x) ^ (A : ℝ) =
        (d : ℝ) ^ (A : ℝ) * c ^ (A : ℝ) * τ ^ (-(A : ℝ) * δ) := by
      dsimp only [x]
      rw [Real.mul_rpow hd_pos.le hx_pos.le, Real.mul_rpow hc_pos.le hτ_negδ_pos.le,
        ← Real.rpow_mul hτ_pos.le]
      ring_nf
    have hBd_pow : B_d ^ (2 - (A : ℝ)) ≤
        (2 : ℝ) ^ (A - 2) * (d : ℝ) ^ (2 - (A : ℝ)) * τ ^ (((A : ℝ) - 2) * (δ / 2)) := by
      dsimp only [B_d]
      rw [Real.mul_rpow (mul_pos (by norm_num) hd_pos).le hrat_half_pos.le,
        Real.mul_rpow (by norm_num) hd_pos.le, ← Real.rpow_mul hrat_pos.le]
      have hhalf_p : (1 / 2 : ℝ) ^ (2 - (A : ℝ)) = (2 : ℝ) ^ (A - 2) := by
        have hsub : ((A - 2 : ℕ) : ℝ) = (A : ℝ) - 2 := Nat.cast_sub (by omega)
        rw [one_div, Real.inv_rpow two_pos.le, ← Real.rpow_neg two_pos.le,
          show -(2 - (A : ℝ)) = ((A - 2 : ℕ) : ℝ) by linarith, Real.rpow_natCast]
      have hrat_le : (τ / 184) ^ (-δ / 2 * (2 - (A : ℝ))) ≤
          τ ^ (((A : ℝ) - 2) * (δ / 2)) := by
        rw [show -δ / 2 * (2 - (A : ℝ)) = ((A : ℝ) - 2) * (δ / 2) by ring]
        exact Real.rpow_le_rpow hrat_pos.le (by linarith) (by nlinarith)
      rw [hhalf_p]
      exact mul_le_mul_of_nonneg_left hrat_le
        (mul_nonneg (pow_nonneg zero_le_two _) (Real.rpow_nonneg hd_pos.le _))
    have hd_comb : (d : ℝ) ^ (s.re - 1) * (d : ℝ) ^ (A : ℝ) * (d : ℝ) ^ (2 - (A : ℝ)) ≤
        (D : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hd_pos, ← Real.rpow_add hd_pos,
        show s.re - 1 + (A : ℝ) + (2 - (A : ℝ)) = 1 + s.re by ring]
      exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) (by linarith)).trans
        (Real.rpow_le_rpow hd_pos.le (by exact_mod_cast hdD) (by norm_num))
    rw [norm_mul]
    calc ‖(ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s))‖ *
          ‖∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
            (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
              (2 : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))‖
        ≤ (d : ℝ) ^ (s.re - 1) *
            (((1 + (2 : ℝ) ^ A) * (K_cut + 1) * S_p2) * ((d : ℝ) * x) ^ (A : ℝ) * B_d ^ (2 - (A : ℝ))) :=
          mul_le_mul hd_pref hcomb_j (norm_nonneg _) (Real.rpow_nonneg hd_pos.le _)
      _ ≤ (d : ℝ) ^ (s.re - 1) *
            (((1 + (2 : ℝ) ^ A) * (K_cut + 1) * S_p2) *
              ((d : ℝ) ^ (A : ℝ) * c ^ (A : ℝ) * τ ^ (-(A : ℝ) * δ)) *
              ((2 : ℝ) ^ (A - 2) * (d : ℝ) ^ (2 - (A : ℝ)) * τ ^ (((A : ℝ) - 2) * (δ / 2)))) := by
          rw [hdx_pow]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hBd_pow
              (mul_nonneg hC0_nn (mul_nonneg (mul_nonneg (Real.rpow_nonneg hd_pos.le _)
                (Real.rpow_nonneg hc_pos.le _)) (Real.rpow_nonneg hτ_pos.le _))))
            (Real.rpow_nonneg hd_pos.le _)
      _ = ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
            ((d : ℝ) ^ (s.re - 1) * (d : ℝ) ^ (A : ℝ) * (d : ℝ) ^ (2 - (A : ℝ))) *
            c ^ (A : ℝ) *
            (τ ^ (-(A : ℝ) * δ) * τ ^ (((A : ℝ) - 2) * (δ / 2))) := by ring
      _ ≤ ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
            (D : ℝ) ^ (3 / 2 : ℝ) * c ^ (A : ℝ) *
            τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) := by
          rw [← Real.rpow_add hτ_pos]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hd_comb hC1_nn) (Real.rpow_nonneg hc_pos.le _))
            (Real.rpow_nonneg hτ_pos.le _)
  have h0 := (norm_sum_le _ _).trans (Finset.sum_le_sum hpt_d)
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul] at h0
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hD_comb : (D : ℝ) * (D : ℝ) ^ (3 / 2 : ℝ) = (D : ℝ) ^ (5 / 2 : ℝ) := by
    calc (D : ℝ) * (D : ℝ) ^ (3 / 2 : ℝ)
        = (D : ℝ) ^ (1 : ℝ) * (D : ℝ) ^ (3 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (D : ℝ) ^ (5 / 2 : ℝ) := by rw [← Real.rpow_add hD_pos]; norm_num
  calc ‖∑ d ∈ Finset.Icc 1 D,
          (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
            ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
              (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
                (2 : ℂ) ^ (-(1 - s)) *
                  smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))‖
      ≤ (D : ℝ) * (((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
          (D : ℝ) ^ (3 / 2 : ℝ) * c ^ (A : ℝ) *
          τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2))) := h0
    _ = ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
          ((D : ℝ) * (D : ℝ) ^ (3 / 2 : ℝ)) * c ^ (A : ℝ) *
          τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) := by ring
    _ = ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
          (D : ℝ) ^ (5 / 2 : ℝ) * c ^ (A : ℝ) *
          τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) := by rw [hD_comb]

/-- **Strictly sub-diagonal reflected-Möbius cross-height duality across ALL of `Ω_open`:**
for every `δ ∈ (0, 1 / 4)`, there exists an `s`-independent scale constant `c_scale ∈ (0, 1 / 4]`
such that setting `x(s) = c_scale |Im s|^{-δ}` and `D(s) = max 4 ⌈c_scale^{-2} |Im s|^{1 + 3δ}⌉₊`
approximates `ζ(s) * poleClearedMoebiusPoly (D(s)) (1 - s)` by
`(1 - 2^{-(1 - s)}) zetaChi(s) + subdiagMoebiusGaussian δ s (x(s)) (D(s))` within
`< (1 / 16) * (|Im s| / 184)^{-δ / 4}` at **every** point `s ∈ Ω_open`. -/
theorem exists_subdiagonal_moebius_gaussian_duality_on_remaining_strip
    {δ : ℝ} (hδ0 : 0 < δ) (hδ_qtr : δ < 1 / 4) :
    ∃ c_scale : ℝ, 0 < c_scale ∧ c_scale ≤ 1 / 4 ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        let x : ℝ := c_scale * |s.im| ^ (-δ)
        let D : ℕ := max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
        ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s) -
            ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + subdiagMoebiusGaussian δ s x D)‖ <
          (1 / 16 : ℝ) * (|s.im| / 184) ^ (-δ / 4) := by
  -- 1. Fix `r ≥ 2` (`3 + 6δ ≤ 4 r δ`) and `A ≥ 6` (`8 + 20δ ≤ A δ`) depending only on `δ`.
  obtain ⟨r, hr2, hr_δ⟩ : ∃ r : ℕ, 2 ≤ r ∧ 3 + 6 * δ ≤ 4 * (r : ℝ) * δ := by
    refine ⟨max 2 (Nat.ceil ((3 + 6 * δ) / (4 * δ))), le_max_left _ _, ?_⟩
    have hc : (3 + 6 * δ) / (4 * δ) ≤ (Nat.ceil ((3 + 6 * δ) / (4 * δ)) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((3 + 6 * δ) / (4 * δ)) : ℝ) ≤
        ((max 2 (Nat.ceil ((3 + 6 * δ) / (4 * δ))) : ℕ) : ℝ) := by exact_mod_cast le_max_right 2 _
    have h := (div_le_iff₀ (by positivity : 0 < 4 * δ)).mp (hc.trans hm)
    linarith
  obtain ⟨A, hA6, hA_δ⟩ : ∃ A : ℕ, 6 ≤ A ∧ 8 + 20 * δ ≤ (A : ℝ) * δ := by
    refine ⟨max 6 (Nat.ceil ((8 + 20 * δ) / δ)), le_max_left _ _, ?_⟩
    have hc : (8 + 20 * δ) / δ ≤ (Nat.ceil ((8 + 20 * δ) / δ) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((8 + 20 * δ) / δ) : ℝ) ≤
        ((max 6 (Nat.ceil ((8 + 20 * δ) / δ)) : ℕ) : ℝ) := by exact_mod_cast le_max_right 6 _
    have h := (div_le_iff₀ hδ0).mp (hc.trans hm)
    linarith
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hA6R : (6 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA6
  have hA_pos : (0 : ℝ) < (A : ℝ) := by linarith
  obtain ⟨C_vac, hC_vac_pos, hC_vac⟩ := exists_norm_smoothAFEZetaDualCoefficientGeneral_zero_add_zetaChi_le
  obtain ⟨K_dual, hK_dual_pos, hK_dual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := r) (by omega)
  obtain ⟨K_cut, hK_cut0, hK_cut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA_pos
  have hsum_p2 : Summable (fun j : ℕ => (j + 1 : ℝ) ^ (-2 : ℝ)) := by
    have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  set S_p2 : ℝ := ∑' j : ℕ, (j + 1 : ℝ) ^ (-2 : ℝ)
  have hSp2_pos : 0 < S_p2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) ^ (-2 : ℝ))
      (hsum_p2.le_tsum 0 fun _ _ => by positivity)
  -- 2. Define explicit positive constants `K_vac`, `K_du`, `K_dir` and choose `c_scale` small enough.
  set K_vac : ℝ := 3 * C_vac + 1
  set K_du : ℝ := 2 * K_dual * (2 : ℝ) ^ (2 * r + 1) + 1
  set K_dir : ℝ := 8 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2 + 1
  have hK_vac_pos : 0 < K_vac := by dsimp only [K_vac]; positivity
  have hK_du_pos : 0 < K_du := by dsimp only [K_du]; positivity
  have hK_dir_pos : 0 < K_dir := by dsimp only [K_dir]; positivity
  set c_scale : ℝ := min (1 / 4)
    (min ((1 / (50 * K_vac)) ^ (4 : ℕ)) (min (1 / (50 * K_du)) (1 / (50 * K_dir))))
  have hc_pos : 0 < c_scale := by
    dsimp only [c_scale]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hc_qtr : c_scale ≤ 1 / 4 := min_le_left _ _
  have hc_le1 : c_scale ≤ 1 := hc_qtr.trans (by norm_num)
  have hc_vac : K_vac * c_scale ^ (1 / 4 : ℝ) < 1 / 48 := by
    have hle : c_scale ≤ (1 / (50 * K_vac)) ^ (4 : ℕ) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hrp : c_scale ^ (1 / 4 : ℝ) ≤ ((1 / (50 * K_vac)) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hc_pos.le hle (by norm_num)
    have hid : ((1 / (50 * K_vac)) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = 1 / (50 * K_vac) := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hid] at hrp
    calc K_vac * c_scale ^ (1 / 4 : ℝ)
        ≤ K_vac * (1 / (50 * K_vac)) := mul_le_mul_of_nonneg_left hrp hK_vac_pos.le
      _ = 1 / 50 := by field_simp [hK_vac_pos.ne']
      _ < 1 / 48 := by norm_num
  have hc_du : K_du * c_scale < 1 / 48 := by
    have hle : c_scale ≤ 1 / (50 * K_du) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    calc K_du * c_scale ≤ K_du * (1 / (50 * K_du)) := mul_le_mul_of_nonneg_left hle hK_du_pos.le
      _ = 1 / 50 := by field_simp [hK_du_pos.ne']
      _ < 1 / 48 := by norm_num
  have hc_dir : K_dir * c_scale < 1 / 48 := by
    have hle : c_scale ≤ 1 / (50 * K_dir) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    calc K_dir * c_scale ≤ K_dir * (1 / (50 * K_dir)) := mul_le_mul_of_nonneg_left hle hK_dir_pos.le
      _ = 1 / 50 := by field_simp [hK_dir_pos.ne']
      _ < 1 / 48 := by norm_num
  refine ⟨c_scale, hc_pos, hc_qtr, fun s hlo hhi him => ?_⟩
  dsimp only
  set τ : ℝ := |s.im|
  have hτ_184 : 184 < τ := him
  have hτ1 : 1 < τ := by linarith
  have hτ_pos : 0 < τ := zero_lt_one.trans hτ1
  set x : ℝ := c_scale * τ ^ (-δ)
  have hx_pos : 0 < x := by dsimp only [x]; positivity
  set D : ℕ := max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)))
  have hD4 : 4 ≤ D := le_max_left _ _
  have hD2 : 2 ≤ D := by omega
  have hD1 : 1 ≤ D := by omega
  have hs0 : 0 < s.re := by linarith
  have hsA : 1 < s.re + (A : ℝ) := by linarith
  -- Common comparison `τ ^ (-δ / 4) ≤ (τ / 184) ^ (-δ / 4)`.
  have hτ_to_rat : τ ^ (-δ / 4) ≤ (τ / 184) ^ (-δ / 4) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hrat_pos : 0 < (τ / 184) ^ (-δ / 4) := Real.rpow_pos_of_pos (by positivity) _
  have h2_le1 : ‖(2 : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
      show (-(1 - s)).re = -(1 - s.re) by simp]
    exact Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by linarith)
  -- Apply the exact reflected-Möbius cross-height identity and split each direct series at `subdiagCutoff δ s d`.
  rw [poleCleared_reflected_moebius_crossHeight_eq hD2 hx_pos hs0 hhi,
    subdiag_split_direct_sum_eq hA_pos hx_pos hsA D]
  -- Algebraic regrouping into Piece A (vacuum) + Piece B (sieved dual tail) + Piece C (direct tail).
  have hI1_eq :
      (2 : ℂ) ^ (-(1 - s)) * smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 =
        smoothAFEZetaDualCoefficientGeneral s x 1 := by
    simpa only [Nat.cast_ofNat] using
      smoothAFEZetaDualCoefficientGeneral_mul_scale (d := 2) (by omega) hx_pos hs0 hhi 0
  set E_vac : ℂ := -(smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s) +
    (2 : ℂ) ^ (-(1 - s)) * (smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s)
  set E_du : ℂ := ∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
    smoothAFEZetaDualCoefficientGeneral s x (j + D)
  set E_dir : ℂ := ∑ d ∈ Finset.Icc 1 D,
    (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
      ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
        (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
          (2 : ℂ) ^ (-(1 - s)) *
            smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))
  have halg_err :
      (subdiagMoebiusGaussian δ s x D + E_dir -
          (smoothAFEZetaDualCoefficientGeneral s x 0 - smoothAFEZetaDualCoefficientGeneral s x 1) -
          E_du) -
        ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + subdiagMoebiusGaussian δ s x D) =
      E_vac - E_du + E_dir := by
    dsimp only [E_vac]
    linear_combination -hI1_eq
  rw [halg_err]
  -- Bound Piece A (`E_vac`): `< (1 / 48) * (τ / 184) ^ (-δ / 4)`.
  have hbd_vac : ‖E_vac‖ < (1 / 48 : ℝ) * (τ / 184) ^ (-δ / 4) := by
    have hx_le1 : x ≤ 1 := by
      dsimp only [x]
      have hτ_le1 : τ ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1.le (by linarith)
      exact (mul_le_of_le_one_right hc_pos.le hτ_le1).trans hc_le1
    have h2x_le1 : 2 * x ≤ 1 := by
      dsimp only [x]
      have hτ_le1 : τ ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1.le (by linarith)
      have h1 : 2 * (c_scale * τ ^ (-δ)) ≤ 2 * c_scale :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hc_pos.le hτ_le1) zero_le_two
      linarith
    have hx_pow : x ^ (3 / 4 - s.re) ≤ c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := by
      have h1 : x ^ (3 / 4 - s.re) ≤ x ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le1 (by linarith)
      have h2 : x ^ (1 / 4 : ℝ) = c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := by
        dsimp only [x]
        rw [Real.mul_rpow hc_pos.le (by positivity), ← Real.rpow_mul hτ_pos.le]
        congr 2; ring
      exact h1.trans_eq h2
    have h2x_pow : (2 * x) ^ (3 / 4 - s.re) ≤ 2 * c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := by
      have h1 : (2 * x) ^ (3 / 4 - s.re) ≤ (2 * x) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity) h2x_le1 (by linarith)
      have h2_rpow : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_lt_two.le (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h2 : (2 * x) ^ (1 / 4 : ℝ) ≤ 2 * (x ^ (1 / 4 : ℝ)) := by
        rw [Real.mul_rpow two_pos.le hx_pos.le]
        exact mul_le_mul_of_nonneg_right h2_rpow (by positivity)
      have h3 : x ^ (1 / 4 : ℝ) = c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := by
        dsimp only [x]
        rw [Real.mul_rpow hc_pos.le (by positivity), ← Real.rpow_mul hτ_pos.le]
        congr 2; ring
      calc (2 * x) ^ (3 / 4 - s.re) ≤ 2 * (x ^ (1 / 4 : ℝ)) := h1.trans h2
        _ = 2 * c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := by rw [h3]; ring
    have hv1 := (hC_vac s x hs0 hhi hx_pos).trans (mul_le_mul_of_nonneg_left hx_pow hC_vac_pos.le)
    have hv2 := (hC_vac s (2 * x) hs0 hhi (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2x_pow hC_vac_pos.le)
    have htri : ‖E_vac‖ ≤ 3 * C_vac * c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := by
      dsimp only [E_vac]
      have ht := norm_add_le (-(smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s))
        ((2 : ℂ) ^ (-(1 - s)) * (smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s))
      rw [norm_neg, norm_mul] at ht
      have hm2 : ‖(2 : ℂ) ^ (-(1 - s))‖ *
          ‖smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s‖ ≤
          C_vac * (2 * c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4)) :=
        (mul_le_of_le_one_left (norm_nonneg _) h2_le1).trans hv2
      linarith
    calc ‖E_vac‖
        ≤ (3 * C_vac) * c_scale ^ (1 / 4 : ℝ) * τ ^ (-δ / 4) := htri
      _ ≤ K_vac * c_scale ^ (1 / 4 : ℝ) * (τ / 184) ^ (-δ / 4) := by
          have hk : 3 * C_vac ≤ K_vac := by dsimp only [K_vac]; linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_right hk (by positivity))
            hτ_to_rat (by positivity) (by positivity)
      _ < (1 / 48 : ℝ) * (τ / 184) ^ (-δ / 4) :=
          mul_lt_mul_of_pos_right hc_vac hrat_pos
  -- Bound Piece B (`E_du`): `< (1 / 48) * (τ / 184) ^ (-δ / 4)`.
  have hbd_du : ‖E_du‖ < (1 / 48 : ℝ) * (τ / 184) ^ (-δ / 4) := by
    have hD_ge : c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ) ≤ (D : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 4 _))
    have h0 := subdiag_sieved_dual_tail_le hr2R hK_dual_pos
      (fun s y hlo hhi hy n => (hK_dual s y hlo hhi hy).1 n)
      hlo hhi him hc_pos hD1 hD_ge
    have hc_comb : c_scale ^ (-2 * (r : ℝ)) * c_scale ^ (4 * (r : ℝ) - 3) ≤ c_scale := by
      rw [← Real.rpow_add hc_pos, show -2 * (r : ℝ) + (4 * (r : ℝ) - 3) = 2 * (r : ℝ) - 3 by ring]
      exact (Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le1 (by linarith)).trans_eq
        (Real.rpow_one c_scale)
    have hτ_comb : τ ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) ≤ τ ^ (-δ / 4) :=
      Real.rpow_le_rpow_of_exponent_le hτ1.le (by linarith)
    have hk : 2 * K_dual * (2 : ℝ) ^ (2 * r + 1) ≤ K_du := by dsimp only [K_du]; linarith
    calc ‖E_du‖
        ≤ (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
            (c_scale ^ (-2 * (r : ℝ)) * c_scale ^ (4 * (r : ℝ) - 3)) *
            τ ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) := h0
      _ ≤ K_du * c_scale * (τ / 184) ^ (-δ / 4) :=
          mul_le_mul (mul_le_mul hk hc_comb
            (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hc_pos.le _)) hK_du_pos.le)
            (hτ_comb.trans hτ_to_rat) (Real.rpow_nonneg hτ_pos.le _)
            (mul_nonneg hK_du_pos.le hc_pos.le)
      _ < (1 / 48 : ℝ) * (τ / 184) ^ (-δ / 4) :=
          mul_lt_mul_of_pos_right hc_du hrat_pos
  -- Bound Piece C (`E_dir`): `< (1 / 48) * (τ / 184) ^ (-δ / 4)`.
  have hbd_dir : ‖E_dir‖ < (1 / 48 : ℝ) * (τ / 184) ^ (-δ / 4) := by
    have hsum_D := subdiag_supercutoff_direct_sum_le hδ0 hA6 hK_cut0 hK_cut
      hSp2_pos hsum_p2 rfl hs0 hhi him hc_pos hD1
    have hD_hi : (D : ℝ) ≤ 2 * c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ) := by
      set u : ℝ := c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)
      have hc_m2 : 16 ≤ c_scale ^ (-2 : ℝ) := by
        have h1 : (1 / 4 : ℝ) ^ (-2 : ℝ) ≤ c_scale ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hc_pos hc_qtr (by norm_num)
        have h2 : (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 := by norm_num
        linarith
      have hτ_13 : 1 ≤ τ ^ (1 + 3 * δ) := Real.one_le_rpow hτ1.le (by positivity)
      have hu4 : 4 ≤ u := by
        dsimp only [u]
        calc (4 : ℝ) ≤ 16 * 1 := by norm_num
          _ ≤ c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ) :=
            mul_le_mul hc_m2 hτ_13 zero_le_one (Real.rpow_nonneg hc_pos.le _)
      have hceil_ge4 : 4 ≤ Nat.ceil u := by
        have hR : (4 : ℝ) ≤ (Nat.ceil u : ℝ) := hu4.trans (Nat.le_ceil u)
        exact_mod_cast hR
      have hD_eq : D = Nat.ceil u := max_eq_right hceil_ge4
      rw [hD_eq]
      have hlt : (Nat.ceil u : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      dsimp only [u] at hlt hu4
      linarith
    have hD52 : (D : ℝ) ^ (5 / 2 : ℝ) ≤
        8 * c_scale ^ (-5 : ℝ) * τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) := by
      have h1 : (D : ℝ) ^ (5 / 2 : ℝ) ≤ (2 * c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg D) hD_hi (by norm_num)
      have h2_52 : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 := by
        calc (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_lt_two.le (by norm_num)
          _ = 8 := by norm_num
      have h2 : (2 * c_scale ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)) ^ (5 / 2 : ℝ) ≤
          8 * c_scale ^ (-5 : ℝ) * τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) := by
        rw [Real.mul_rpow (mul_nonneg zero_le_two (Real.rpow_nonneg hc_pos.le _))
            (Real.rpow_nonneg hτ_pos.le _),
          Real.mul_rpow two_pos.le (Real.rpow_nonneg hc_pos.le _),
          ← Real.rpow_mul hc_pos.le, ← Real.rpow_mul hτ_pos.le,
          show (-2 : ℝ) * (5 / 2 : ℝ) = (-5 : ℝ) by norm_num,
          show (1 + 3 * δ) * (5 / 2 : ℝ) = (5 / 2 : ℝ) * (1 + 3 * δ) by ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2_52 (Real.rpow_nonneg hc_pos.le _))
          (Real.rpow_nonneg hτ_pos.le _)
      exact h1.trans h2
    have hc_dir_comb : c_scale ^ (-5 : ℝ) * c_scale ^ (A : ℝ) ≤ c_scale := by
      rw [← Real.rpow_add hc_pos]
      exact (Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le1 (by linarith)).trans_eq
        (Real.rpow_one c_scale)
    have hτ_dir_comb :
        τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) * τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) ≤
          τ ^ (-δ / 4) := by
      rw [← Real.rpow_add hτ_pos]
      refine Real.rpow_le_rpow_of_exponent_le hτ1.le ?_
      have hid : (5 / 2 : ℝ) * (1 + 3 * δ) + (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) =
          5 / 2 + (13 / 2) * δ - ((A : ℝ) * δ) / 2 := by ring
      linarith
    have hC1_nn : 0 ≤ (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith)) hSp2_pos.le
    calc ‖E_dir‖
        ≤ ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
            (8 * c_scale ^ (-5 : ℝ) * τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ))) * c_scale ^ (A : ℝ) *
            τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) :=
          hsum_D.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hD52 hC1_nn) (Real.rpow_nonneg hc_pos.le _))
            (Real.rpow_nonneg hτ_pos.le _))
      _ = (8 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2) *
            (c_scale ^ (-5 : ℝ) * c_scale ^ (A : ℝ)) *
            (τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) *
              τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2))) := by ring
      _ ≤ K_dir * c_scale * (τ / 184) ^ (-δ / 4) := by
          have hk : 8 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * (K_cut + 1) * S_p2 ≤ K_dir := by
            dsimp only [K_dir]; linarith
          exact mul_le_mul (mul_le_mul hk hc_dir_comb
            (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hc_pos.le _)) hK_dir_pos.le)
            (hτ_dir_comb.trans hτ_to_rat)
            (mul_nonneg (Real.rpow_nonneg hτ_pos.le _) (Real.rpow_nonneg hτ_pos.le _))
            (mul_nonneg hK_dir_pos.le hc_pos.le)
      _ < (1 / 48 : ℝ) * (τ / 184) ^ (-δ / 4) :=
          mul_lt_mul_of_pos_right hc_dir hrat_pos
  have ht1 := norm_add_le (E_vac - E_du) E_dir
  have ht2 := norm_sub_le E_vac E_du
  linarith

/-- **Pointwise `HasStrictPrimeGasWitness` production from sub-diagonal domination on `Ω_open`:**
whenever `subdiagMoebiusGaussian δ s x D` falls strictly below the amplified Spira vacuum margin
`(1 / 4) (|Im s| / 7)^{1/2 - Re s} - (1 / 16) (|Im s| / 184)^{-δ / 4}` (`> 3 / 16`), `ζ(s) ≠ 0`,
producing an explicit `HasStrictPrimeGasWitness` at `s`. -/
theorem strict_primeGas_witness_of_subdiagonal_domination_on_remaining_strip
    {δ c_scale : ℝ} (_hδ0 : 0 < δ)
    (hduality : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      let x : ℝ := c_scale * |s.im| ^ (-δ)
      let D : ℕ := max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
      ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s) -
          ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + subdiagMoebiusGaussian δ s x D)‖ <
        (1 / 16 : ℝ) * (|s.im| / 184) ^ (-δ / 4))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {L_hor : ℝ} (hL_hor : 0 < L_hor)
    (hdom :
      ‖subdiagMoebiusGaussian δ s (c_scale * |s.im| ^ (-δ))
          (max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ))))‖ ≤
        (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) -
          (1 / 16 : ℝ) * (|s.im| / 184) ^ (-δ / 4)) :
    HasStrictPrimeGasWitness s (by linarith) L_hor := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  refine (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hL_hor).mpr ?_
  intro hζ0
  have herr := hduality s hlo hhi him
  dsimp only at herr
  rw [hζ0, zero_mul, zero_sub, norm_neg] at herr
  have hpref := one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi
  obtain ⟨_, _, hchi_ge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour hs0 hhi him
  have hchi_pos : 0 < ‖zetaChi s‖ := lt_of_lt_of_le (by positivity) hchi_ge
  have hvac_gt : (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) <
      ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ := by
    rw [norm_mul]
    calc (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re)
        ≤ (1 / 4 : ℝ) * ‖zetaChi s‖ := mul_le_mul_of_nonneg_left hchi_ge (by norm_num)
      _ < ‖1 - (2 : ℂ) ^ (-(1 - s))‖ * ‖zetaChi s‖ := mul_lt_mul_of_pos_right hpref hchi_pos
  set V : ℂ := (1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s
  set S_sub : ℂ := subdiagMoebiusGaussian δ s (c_scale * |s.im| ^ (-δ))
    (max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ))))
  have htri : ‖V‖ - ‖S_sub‖ ≤ ‖V + S_sub‖ := by
    have h := norm_sub_norm_le V (-S_sub)
    rwa [sub_neg_eq_add, norm_neg] at h
  linarith

/-- Exact two-mode dual vacuum + strictly sub-diagonal reflected-Möbius witness:
`subdiagMoebiusGaussian δ s x D - (I(s, x, 0) - I(s, x, 1))`, eliminating all dual modes `3 ≤ k ≤ D`,
all diagonal/super-diagonal direct terms `2 n > d`, and the entire `s = 1` pole residue. -/
def subdiagMoebiusVacuumWitness (δ : ℝ) (s : ℂ) (x : ℝ) (D : ℕ) : ℂ :=
  subdiagMoebiusGaussian δ s x D -
    (smoothAFEZetaDualCoefficientGeneral s x 0 - smoothAFEZetaDualCoefficientGeneral s x 1)

/-- **Unconditional `RiemannHypothesis` equivalence with strictly sub-diagonal reflected-Möbius
witnesses across ALL of `Ω_open`:**
for every `δ ∈ (0, 1 / 4)`, there exists an `s`-independent constant `C_cubic > 0` such that:
1. at every `s ∈ Ω_open`, every `c ∈ (0, 1 / 4]`, and every `D ∈ [D₀(c), 2 D₀(c)]` with
   `D₀(c) = max 4 ⌈c^{-2} |Im s|^{1 + 3δ}⌉₊`, `subdiagMoebiusVacuumWitness δ s (c |Im s|^{-δ}) D`
   approximates `ζ(s) * poleClearedMoebiusPoly D (1 - s)` within `C_cubic * c^3`;
2. `RiemannHypothesis` holds if and only if at **every** point of `Ω_open`, some `(c, D)` in that
   dyadic Bertrand window beats the certified `C_cubic * c^3` bound (proved unconditionally in the
   forward direction via Bertrand's postulate `p ∈ (D₀(c), 2 D₀(c)]` with `μ(p) = -1`). -/
theorem rh_iff_subdiagonal_moebius_gaussian_separation_on_remaining_strip
    {δ : ℝ} (hδ0 : 0 < δ) (hδ_qtr : δ < 1 / 4) :
    ∃ C_cubic : ℝ, 0 < C_cubic ∧
      (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∀ {c : ℝ}, 0 < c → c ≤ 1 / 4 →
          let D₀ : ℕ := max 4 (Nat.ceil (c ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
          ∀ D ∈ Finset.Icc D₀ (2 * D₀),
            ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s) -
                subdiagMoebiusVacuumWitness δ s (c * |s.im| ^ (-δ)) D‖ ≤
              C_cubic * c ^ (3 : ℕ)) ∧
      (RiemannHypothesis ↔
        ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
          ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧
            let D₀ : ℕ := max 4 (Nat.ceil (c ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
            ∃ D ∈ Finset.Icc D₀ (2 * D₀),
              C_cubic * c ^ (3 : ℕ) <
                ‖subdiagMoebiusVacuumWitness δ s (c * |s.im| ^ (-δ)) D‖) := by
  -- 1. Select `r ≥ 3` (`3 + 6δ ≤ 4 r δ`) and `A ≥ 8` (`8 + 20δ ≤ A δ`) so both tails are `O(c^3)`.
  obtain ⟨r, hr3, hr_δ⟩ : ∃ r : ℕ, 3 ≤ r ∧ 3 + 6 * δ ≤ 4 * (r : ℝ) * δ := by
    refine ⟨max 3 (Nat.ceil ((3 + 6 * δ) / (4 * δ))), le_max_left _ _, ?_⟩
    have hc : (3 + 6 * δ) / (4 * δ) ≤ (Nat.ceil ((3 + 6 * δ) / (4 * δ)) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((3 + 6 * δ) / (4 * δ)) : ℝ) ≤
        ((max 3 (Nat.ceil ((3 + 6 * δ) / (4 * δ))) : ℕ) : ℝ) := by exact_mod_cast le_max_right 3 _
    have h := (div_le_iff₀ (by positivity : 0 < 4 * δ)).mp (hc.trans hm)
    linarith
  obtain ⟨A, hA8, hA_δ⟩ : ∃ A : ℕ, 8 ≤ A ∧ 8 + 20 * δ ≤ (A : ℝ) * δ := by
    refine ⟨max 8 (Nat.ceil ((8 + 20 * δ) / δ)), le_max_left _ _, ?_⟩
    have hc : (8 + 20 * δ) / δ ≤ (Nat.ceil ((8 + 20 * δ) / δ) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((8 + 20 * δ) / δ) : ℝ) ≤
        ((max 8 (Nat.ceil ((8 + 20 * δ) / δ)) : ℕ) : ℝ) := by exact_mod_cast le_max_right 8 _
    have h := (div_le_iff₀ hδ0).mp (hc.trans hm)
    linarith
  have hr3R : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
  have hA8R : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA8
  have hA_pos : (0 : ℝ) < (A : ℝ) := by linarith
  obtain ⟨K_dual, hK_dual_pos, hK_dual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := r) (by omega)
  obtain ⟨K_cut, hK_cut0, hK_cut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA_pos
  have hsum_p2 : Summable (fun j : ℕ => (j + 1 : ℝ) ^ (-2 : ℝ)) := by
    have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  set S_p2 : ℝ := ∑' j : ℕ, (j + 1 : ℝ) ^ (-2 : ℝ)
  have hSp2_pos : 0 < S_p2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) ^ (-2 : ℝ))
      (hsum_p2.le_tsum 0 fun _ _ => by positivity)
  set K_c1 : ℝ := K_cut + 1
  set C_cubic : ℝ := 2 * K_dual * (2 : ℝ) ^ (2 * r + 1) +
    32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2 + 1
  have hC_pos : 0 < C_cubic := by dsimp only [C_cubic, K_c1]; positivity
  -- Prove the uniform `C_cubic * c ^ 3` bound across `D ∈ [D₀(c), 2 D₀(c)]`.
  have hcubic_bd : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      ∀ {c : ℝ}, 0 < c → c ≤ 1 / 4 →
        let D₀ : ℕ := max 4 (Nat.ceil (c ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
        ∀ D ∈ Finset.Icc D₀ (2 * D₀),
          ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s) -
              subdiagMoebiusVacuumWitness δ s (c * |s.im| ^ (-δ)) D‖ ≤
            C_cubic * c ^ (3 : ℕ) := by
    intro s hlo hhi him c hc_pos hc_qtr D₀ D hD_mem
    obtain ⟨hD_lo, hD_hi_2⟩ := Finset.mem_Icc.mp hD_mem
    have hc_le1 : c ≤ 1 := hc_qtr.trans (by norm_num)
    set τ : ℝ := |s.im|
    have hτ1 : 1 < τ := by dsimp only [τ]; linarith
    have hτ_pos : 0 < τ := zero_lt_one.trans hτ1
    set x : ℝ := c * τ ^ (-δ)
    have hx_pos : 0 < x := by dsimp only [x]; positivity
    have hD₀_4 : 4 ≤ D₀ := le_max_left _ _
    have hD2 : 2 ≤ D := by omega
    have hD1 : 1 ≤ D := by omega
    have hs0 : 0 < s.re := by linarith
    have hsA : 1 < s.re + (A : ℝ) := by linarith
    rw [poleCleared_reflected_moebius_crossHeight_eq hD2 hx_pos hs0 hhi,
      subdiag_split_direct_sum_eq hA_pos hx_pos hsA D]
    unfold subdiagMoebiusVacuumWitness
    set E_du : ℂ := ∑' j : ℕ, poleClearedSieveCoeff D (j + D + 1) *
      smoothAFEZetaDualCoefficientGeneral s x (j + D)
    set E_dir : ℂ := ∑ d ∈ Finset.Icc 1 D,
      (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s)) *
        ∑' j : ℕ, (((j + subdiagCutoff δ s d + 1 : ℕ) : ℂ) ^ (-s) *
          (smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
            (2 : ℂ) ^ (-(1 - s)) *
              smoothAFECutoff (((j + subdiagCutoff δ s d + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))
    have halg :
        (subdiagMoebiusGaussian δ s x D + E_dir -
            (smoothAFEZetaDualCoefficientGeneral s x 0 - smoothAFEZetaDualCoefficientGeneral s x 1) -
            E_du) -
          (subdiagMoebiusGaussian δ s x D -
            (smoothAFEZetaDualCoefficientGeneral s x 0 - smoothAFEZetaDualCoefficientGeneral s x 1)) =
        E_dir - E_du := by ring
    rw [halg]
    -- Bound `E_du ≤ (2 * K_dual * 2^{2r + 1}) * c^3`.
    have hbd_du : ‖E_du‖ ≤ (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) * c ^ (3 : ℕ) := by
      have hD_ge : c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ) ≤ (D : ℝ) :=
        ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 4 _))).trans (Nat.cast_le.mpr hD_lo)
      have h0 := subdiag_sieved_dual_tail_le (by linarith : (2 : ℝ) ≤ (r : ℝ)) hK_dual_pos
        (fun s y hlo hhi hy n => (hK_dual s y hlo hhi hy).1 n)
        hlo hhi him hc_pos hD1 hD_ge
      have hc_comb : c ^ (-2 * (r : ℝ)) * c ^ (4 * (r : ℝ) - 3) ≤ c ^ (3 : ℕ) := by
        rw [← Real.rpow_add hc_pos, show -2 * (r : ℝ) + (4 * (r : ℝ) - 3) = 2 * (r : ℝ) - 3 by ring,
          ← Real.rpow_natCast c 3]
        exact Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le1 (by push_cast; linarith)
      have hτ_le1 : τ ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hτ1.le (by linarith)
      calc ‖E_du‖
          ≤ (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
              (c ^ (-2 * (r : ℝ)) * c ^ (4 * (r : ℝ) - 3)) *
              τ ^ (2 - s.re + (9 / 2) * δ - 4 * (r : ℝ) * δ) := h0
        _ ≤ (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) * c ^ (3 : ℕ) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc_comb
              (mul_nonneg (mul_nonneg zero_le_two hK_dual_pos.le) (pow_nonneg zero_le_two _)))
              hτ_le1 (Real.rpow_nonneg hτ_pos.le _)
              (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hK_dual_pos.le)
                (pow_nonneg zero_le_two _)) (pow_nonneg hc_pos.le 3))
        _ = (2 * K_dual * (2 : ℝ) ^ (2 * r + 1)) * c ^ (3 : ℕ) := mul_one _
    -- Bound `E_dir ≤ (32 * (1 + 2^A) * 2^{A - 2} * K_c1 * S_p2) * c^3`.
    have hbd_dir : ‖E_dir‖ ≤
        (32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2) * c ^ (3 : ℕ) := by
      have hsum_D := subdiag_supercutoff_direct_sum_le hδ0 (by omega : 6 ≤ A) hK_cut0 hK_cut
        hSp2_pos hsum_p2 rfl hs0 hhi him hc_pos hD1
      have hD_hi_4 : (D : ℝ) ≤ 4 * c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ) := by
        set u : ℝ := c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)
        have hc_m2 : 16 ≤ c ^ (-2 : ℝ) := by
          have h1 : (1 / 4 : ℝ) ^ (-2 : ℝ) ≤ c ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos hc_pos hc_qtr (by norm_num)
          have h2 : (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 := by norm_num
          linarith
        have hτ_13 : 1 ≤ τ ^ (1 + 3 * δ) := Real.one_le_rpow hτ1.le (by positivity)
        have hu4 : 4 ≤ u := by
          dsimp only [u]
          calc (4 : ℝ) ≤ 16 * 1 := by norm_num
            _ ≤ c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ) :=
              mul_le_mul hc_m2 hτ_13 zero_le_one (Real.rpow_nonneg hc_pos.le _)
        have hceil_ge4 : 4 ≤ Nat.ceil u := by
          have hR : (4 : ℝ) ≤ (Nat.ceil u : ℝ) := hu4.trans (Nat.le_ceil u)
          exact_mod_cast hR
        have hD₀_eq : D₀ = Nat.ceil u := max_eq_right hceil_ge4
        have hD_le_2D₀ : (D : ℝ) ≤ 2 * (D₀ : ℝ) := by
          have hcast : (D : ℝ) ≤ ((2 * D₀ : ℕ) : ℝ) := Nat.cast_le.mpr hD_hi_2
          push_cast at hcast; exact hcast
        rw [hD₀_eq] at hD_le_2D₀
        have hlt : (Nat.ceil u : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one (by linarith)).le
        dsimp only [u] at hlt hu4
        linarith
      have hD52 : (D : ℝ) ^ (5 / 2 : ℝ) ≤
          32 * c ^ (-5 : ℝ) * τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) := by
        have h1 : (D : ℝ) ^ (5 / 2 : ℝ) ≤ (4 * c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg D) hD_hi_4 (by norm_num)
        have h4_52 : (4 : ℝ) ^ (5 / 2 : ℝ) = 32 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast 2 2,
            ← Real.rpow_mul two_pos.le]
          norm_num
        have h2 : (4 * c ^ (-2 : ℝ) * τ ^ (1 + 3 * δ)) ^ (5 / 2 : ℝ) =
            32 * c ^ (-5 : ℝ) * τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) := by
          rw [Real.mul_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hc_pos.le _))
              (Real.rpow_nonneg hτ_pos.le _),
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc_pos.le _),
            ← Real.rpow_mul hc_pos.le, ← Real.rpow_mul hτ_pos.le, h4_52,
            show (-2 : ℝ) * (5 / 2 : ℝ) = (-5 : ℝ) by norm_num,
            show (1 + 3 * δ) * (5 / 2 : ℝ) = (5 / 2 : ℝ) * (1 + 3 * δ) by ring]
        exact h1.trans_eq h2
      have hc_dir_comb : c ^ (-5 : ℝ) * c ^ (A : ℝ) ≤ c ^ (3 : ℕ) := by
        rw [← Real.rpow_add hc_pos, ← Real.rpow_natCast c 3]
        exact Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le1 (by push_cast; linarith)
      have hτ_le1 :
          τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) * τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) ≤ 1 := by
        rw [← Real.rpow_add hτ_pos]
        refine Real.rpow_le_one_of_one_le_of_nonpos hτ1.le ?_
        have hid : (5 / 2 : ℝ) * (1 + 3 * δ) + (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) =
            5 / 2 + (13 / 2) * δ - ((A : ℝ) * δ) / 2 := by ring
        linarith
      have hC1_nn : 0 ≤ (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (by dsimp only [K_c1]; linarith)) hSp2_pos.le
      have hC32_nn : 0 ≤ 32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2 := by
        have h32_eq : 32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2 =
            32 * ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2) := by ring
        rw [h32_eq]
        exact mul_nonneg (by norm_num) hC1_nn
      calc ‖E_dir‖
          ≤ ((1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2) *
              (32 * c ^ (-5 : ℝ) * τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ))) * c ^ (A : ℝ) *
              τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2)) :=
            hsum_D.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hD52 hC1_nn) (Real.rpow_nonneg hc_pos.le _))
              (Real.rpow_nonneg hτ_pos.le _))
        _ = (32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2) *
              (c ^ (-5 : ℝ) * c ^ (A : ℝ)) *
              (τ ^ ((5 / 2 : ℝ) * (1 + 3 * δ)) *
                τ ^ (-(A : ℝ) * δ + ((A : ℝ) - 2) * (δ / 2))) := by ring
        _ ≤ (32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2) * c ^ (3 : ℕ) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc_dir_comb hC32_nn) hτ_le1
              (mul_nonneg (Real.rpow_nonneg hτ_pos.le _) (Real.rpow_nonneg hτ_pos.le _))
              (mul_nonneg hC32_nn (pow_nonneg hc_pos.le 3))
        _ = (32 * (1 + (2 : ℝ) ^ A) * (2 : ℝ) ^ (A - 2) * K_c1 * S_p2) * c ^ (3 : ℕ) := mul_one _
    have ht := norm_sub_le E_dir E_du
    have hc3_nn : 0 ≤ c ^ (3 : ℕ) := by positivity
    dsimp only [C_cubic]
    nlinarith
  refine ⟨C_cubic, hC_pos, hcubic_bd, ?_⟩
  have hrh_zeta : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| → riemannZeta s ≠ 0 := by
    rw [rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour.2]
    refine forall₄_congr fun s hlo hhi him => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hceil185 : 185 ≤ Nat.ceil |s.im| := by
      have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
      omega
    have hmax1 : max 1 (Nat.ceil |s.im|) = Nat.ceil |s.im| := max_eq_right (by omega)
    rw [← (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).2, hmax1]
  rw [hrh_zeta]
  refine forall₄_congr fun s hlo hhi him => ?_
  constructor
  · -- `→`: Use Bertrand's postulate `p ∈ (D₀, 2 D₀]` (`μ(p) = -1`) to force `‖ζ(s) * poleClearedMoebiusPoly D (1 - s)‖ ≥ γ_s * c₀^2`.
    intro hζ_ne
    have hτ1 : 1 < |s.im| := by linarith
    have hτ_pos : 0 < |s.im| := zero_lt_one.trans hτ1
    have hζ_pos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζ_ne
    set γ_s : ℝ := (‖riemannZeta s‖ / 32) * |s.im| ^ (-(1 + 3 * δ))
    have hγ_pos : 0 < γ_s := by dsimp only [γ_s]; positivity
    set c₀ : ℝ := min (1 / 4) (γ_s / (2 * C_cubic + 1))
    have hc₀_pos : 0 < c₀ := lt_min (by norm_num) (by positivity)
    have hc₀_qtr : c₀ ≤ 1 / 4 := min_le_left _ _
    have hc₀_small : C_cubic * c₀ < γ_s / 2 := by
      have hle : c₀ ≤ γ_s / (2 * C_cubic + 1) := min_le_right _ _
      calc C_cubic * c₀ ≤ C_cubic * (γ_s / (2 * C_cubic + 1)) :=
            mul_le_mul_of_nonneg_left hle hC_pos.le
        _ < (C_cubic + 1 / 2) * (γ_s / (2 * C_cubic + 1)) :=
            mul_lt_mul_of_pos_right (by linarith) (by positivity)
        _ = γ_s / 2 := by field_simp [show (2 * C_cubic + 1 : ℝ) ≠ 0 by positivity]
    set D₀ : ℕ := max 4 (Nat.ceil (c₀ ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
    have hD₀_4 : 4 ≤ D₀ := le_max_left _ _
    obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul D₀ (by omega)
    have hp_mem : p ∈ Finset.Icc D₀ (2 * D₀) := Finset.mem_Icc.mpr ⟨hp_gt.le, hp_le⟩
    have hpm1_mem : p - 1 ∈ Finset.Icc D₀ (2 * D₀) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    -- Jump identity between `p` and `p - 1` from `μ(p) = -1`.
    have hjump : riemannZeta s * poleClearedMoebiusPoly p (1 - s) -
        riemannZeta s * poleClearedMoebiusPoly (p - 1) (1 - s) =
        -(riemannZeta s * (1 - (2 : ℂ) ^ (-(1 - s))) * (p : ℂ) ^ (-(1 - s))) := by
      unfold poleClearedMoebiusPoly
      have hIcc : Finset.Icc 1 p = Finset.Icc 1 ((p - 1) + 1) :=
        congrArg (Finset.Icc 1) (by omega)
      have hsum_split :
          (∑ d ∈ Finset.Icc 1 p, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s))) =
            (∑ d ∈ Finset.Icc 1 (p - 1), (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-(1 - s))) +
              (ArithmeticFunction.moebius p : ℂ) * (p : ℂ) ^ (-(1 - s)) := by
        rw [hIcc, Finset.sum_Icc_succ_top (by omega : 1 ≤ (p - 1) + 1),
          show (p - 1) + 1 = p by omega]
      rw [hsum_split, ArithmeticFunction.moebius_apply_prime hp_prime]
      push_cast; ring
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hp_hi : (p : ℝ) ≤ 4 * c₀ ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ) := by
      set u : ℝ := c₀ ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)
      have hc_m2 : 16 ≤ c₀ ^ (-2 : ℝ) := by
        have h1 : (1 / 4 : ℝ) ^ (-2 : ℝ) ≤ c₀ ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hc₀_pos hc₀_qtr (by norm_num)
        have h2 : (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 := by norm_num
        linarith
      have hτ_13 : 1 ≤ |s.im| ^ (1 + 3 * δ) := Real.one_le_rpow hτ1.le (by positivity)
      have hu4 : 4 ≤ u := by
        dsimp only [u]
        calc (4 : ℝ) ≤ 16 * 1 := by norm_num
          _ ≤ c₀ ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ) :=
            mul_le_mul hc_m2 hτ_13 zero_le_one (by positivity)
      have hceil_ge4 : 4 ≤ Nat.ceil u := by
        have hR : (4 : ℝ) ≤ (Nat.ceil u : ℝ) := hu4.trans (Nat.le_ceil u)
        exact_mod_cast hR
      have hD₀_eq : D₀ = Nat.ceil u := max_eq_right hceil_ge4
      have hp_le_2D₀ : (p : ℝ) ≤ 2 * (D₀ : ℝ) := by
        have hcast : (p : ℝ) ≤ ((2 * D₀ : ℕ) : ℝ) := Nat.cast_le.mpr hp_le
        push_cast at hcast; exact hcast
      rw [hD₀_eq] at hp_le_2D₀
      have hlt : (Nat.ceil u : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      dsimp only [u] at hlt hu4
      linarith
    have hp_inv_ge : (1 / 4 : ℝ) * |s.im| ^ (-(1 + 3 * δ)) * c₀ ^ (2 : ℕ) ≤
        ‖(p : ℂ) ^ (-(1 - s))‖ := by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,
        show (-(1 - s)).re = -(1 - s.re) by simp]
      have h1 : (p : ℝ)⁻¹ ≤ (p : ℝ) ^ (-(1 - s.re)) := by
        rw [← Real.rpow_neg_one (p : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
      have h2 : (4 * c₀ ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ))⁻¹ ≤ (p : ℝ)⁻¹ :=
        inv_anti₀ hp_pos hp_hi
      have h3 : (4 * c₀ ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ))⁻¹ =
          (1 / 4 : ℝ) * |s.im| ^ (-(1 + 3 * δ)) * c₀ ^ (2 : ℕ) := by
        rw [mul_inv, mul_inv, ← Real.rpow_neg hc₀_pos.le, ← Real.rpow_neg hτ_pos.le,
          show -(-2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      exact (h3.symm.trans_le h2).trans h1
    have hjump_ge : 2 * γ_s * c₀ ^ (2 : ℕ) ≤
        ‖riemannZeta s * poleClearedMoebiusPoly p (1 - s) -
            riemannZeta s * poleClearedMoebiusPoly (p - 1) (1 - s)‖ := by
      rw [hjump, norm_neg, norm_mul, norm_mul]
      have hpref := (one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi).le
      calc 2 * γ_s * c₀ ^ (2 : ℕ)
          = ‖riemannZeta s‖ * (1 / 4 : ℝ) *
              ((1 / 4 : ℝ) * |s.im| ^ (-(1 + 3 * δ)) * c₀ ^ (2 : ℕ)) := by
            dsimp only [γ_s]; ring
        _ ≤ ‖riemannZeta s‖ * ‖1 - (2 : ℂ) ^ (-(1 - s))‖ * ‖(p : ℂ) ^ (-(1 - s))‖ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpref hζ_pos.le) hp_inv_ge
              (by positivity) (by positivity)
    have htri_p := norm_sub_le
      (riemannZeta s * poleClearedMoebiusPoly p (1 - s))
      (riemannZeta s * poleClearedMoebiusPoly (p - 1) (1 - s))
    have hex_D : ∃ D ∈ Finset.Icc D₀ (2 * D₀),
        γ_s * c₀ ^ (2 : ℕ) ≤ ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s)‖ := by
      by_cases hp_big : γ_s * c₀ ^ (2 : ℕ) ≤ ‖riemannZeta s * poleClearedMoebiusPoly p (1 - s)‖
      · exact ⟨p, hp_mem, hp_big⟩
      · exact ⟨p - 1, hpm1_mem, by linarith⟩
    obtain ⟨D, hD_in, hD_lb⟩ := hex_D
    have herr_D := hcubic_bd s hlo hhi him hc₀_pos hc₀_qtr D hD_in
    have herr_strict : C_cubic * c₀ ^ (3 : ℕ) <
        ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s)‖ / 2 := by
      have hc2_pos : 0 < c₀ ^ (2 : ℕ) := pow_pos hc₀_pos 2
      calc C_cubic * c₀ ^ (3 : ℕ)
          = (C_cubic * c₀) * c₀ ^ (2 : ℕ) := by ring
        _ < (γ_s / 2) * c₀ ^ (2 : ℕ) := mul_lt_mul_of_pos_right hc₀_small hc2_pos
        _ = (γ_s * c₀ ^ (2 : ℕ)) / 2 := by ring
        _ ≤ ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s)‖ / 2 := by linarith
    have htri_w := norm_sub_norm_le
      (riemannZeta s * poleClearedMoebiusPoly D (1 - s))
      (subdiagMoebiusVacuumWitness δ s (c₀ * |s.im| ^ (-δ)) D)
    exact ⟨c₀, hc₀_pos, hc₀_qtr, D, hD_in, by linarith⟩
  · -- `←`: If `ζ(s) = 0`, `ζ(s) * poleClearedMoebiusPoly D (1 - s) = 0`, contradicting strict excess.
    rintro ⟨c, hc_pos, hc_qtr, D, hD_in, hbeat⟩ hζ0
    have herr := hcubic_bd s hlo hhi him hc_pos hc_qtr D hD_in
    rw [hζ0, zero_mul, zero_sub, norm_neg] at herr
    linarith

/-- **Exact trans-horizon Vaughan Type-I + Type-II decomposition of `subdiagMoebiusGaussian`:**
because `subdiagCutoff δ s d = 0` for all `d < ⌈2 (|Im s| / 184)^{δ / 2}⌉₊`, for **every** pair
of Vaughan cutoffs `U, V < ⌈2 (|Im s| / 184)^{δ / 2}⌉₊`, `subdiagMoebiusGaussian` splits
identically (with zero short Type-0 head) into `subdiagVaughanTypeI + subdiagVaughanTypeII`. -/
theorem subdiagMoebiusGaussian_eq_vaughanTypeI_add_typeII
    {δ : ℝ} (hδ0 : 0 < δ) {s : ℂ} (him : 184 < |s.im|)
    {U V : ℕ} (hU : U < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2)))
    (hV : V < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2))) (x : ℝ) (D : ℕ) :
    subdiagMoebiusGaussian δ s x D =
      subdiagVaughanTypeI δ U V s x D + subdiagVaughanTypeII δ U V s x D := by
  obtain ⟨_, _, hlow0⟩ := subdiagCutoff_two_mul_le_and_eq_zero_of_lt hδ0 him
  unfold subdiagMoebiusGaussian subdiagVaughanTypeI subdiagVaughanTypeII
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd_lt : d < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2))
  · rw [hlow0 d hd_lt]
    simp
  · have hd_ge : Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2)) ≤ d := Nat.le_of_not_lt hd_lt
    have hv := GaloisForLFunctions.BezoutValuationIncidence.moebius_vaughan_apply_of_gt
      (U := U) (V := V) (n := d) (lt_of_lt_of_le hU hd_ge) (lt_of_lt_of_le hV hd_ge)
    have hm_cast : (ArithmeticFunction.moebius d : ℂ) =
        (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d : ℝ) : ℂ) := by
      rw [ArithmeticFunction.intCoe_apply]
      exact (Complex.ofReal_intCast (ArithmeticFunction.moebius d)).symm
    rw [hm_cast, hv]
    push_cast
    ring

/-- **Forced strictly sub-diagonal Vaughan Type-I or Type-II bilinear floor at any `ζ(s) = 0` in
`Ω_open`:**
at any zero `riemannZeta s = 0` in `Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`), for
every `U, V < ⌈2 (|Im s| / 184)^{δ / 2}⌉₊` (in particular at the growing cutoff
`U = V = ⌈2 (|Im s| / 184)^{δ / 2}⌉₊ - 1`), at least one of the strictly sub-diagonal (`2 n ≤ d`)
Vaughan sums `subdiagVaughanTypeI` or `subdiagVaughanTypeII` is forced strictly above
`((1 / 4) * (|Im s| / 7)^{1/2 - Re s} - 1 / 16) / 2 > 3 / 32`. -/
theorem subdiagonal_vaughan_typeI_or_typeII_forced_above_spira_floor_of_zeta_eq_zero
    {δ c_scale : ℝ} (hδ0 : 0 < δ)
    (hduality : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      let x : ℝ := c_scale * |s.im| ^ (-δ)
      let D : ℕ := max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
      ‖riemannZeta s * poleClearedMoebiusPoly D (1 - s) -
          ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + subdiagMoebiusGaussian δ s x D)‖ <
        (1 / 16 : ℝ) * (|s.im| / 184) ^ (-δ / 4))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    (hζ0 : riemannZeta s = 0)
    {U V : ℕ} (hU : U < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2)))
    (hV : V < Nat.ceil (2 * (|s.im| / 184) ^ (δ / 2))) :
    let x : ℝ := c_scale * |s.im| ^ (-δ)
    let D : ℕ := max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
    (3 / 32 : ℝ) < ((1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - 1 / 16) / 2 ∧
      ((1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - 1 / 16) / 2 <
        max ‖subdiagVaughanTypeI δ U V s x D‖ ‖subdiagVaughanTypeII δ U V s x D‖ := by
  dsimp only
  have hs0 : 0 < s.re := by linarith
  set x : ℝ := c_scale * |s.im| ^ (-δ)
  set D : ℕ := max 4 (Nat.ceil (c_scale ^ (-2 : ℝ) * |s.im| ^ (1 + 3 * δ)))
  obtain ⟨h1_lt, h2_lt, hchi_ge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour hs0 hhi him
  have hrpow_gt1 : 1 < (|s.im| / 7) ^ (1 / 2 - s.re) := h1_lt.trans h2_lt
  have hfloor_gt : (3 / 32 : ℝ) < ((1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - 1 / 16) / 2 := by
    linarith
  refine ⟨hfloor_gt, ?_⟩
  have herr := hduality s hlo hhi him
  dsimp only at herr
  rw [hζ0, zero_mul, zero_sub, norm_neg] at herr
  have herr_lt_16 : ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + subdiagMoebiusGaussian δ s x D‖ <
      1 / 16 := by
    have hrpow_lt1 : (|s.im| / 184) ^ (-δ / 4) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    exact herr.trans (by linarith)
  have hpref := one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi
  have hchi_pos : 0 < ‖zetaChi s‖ := lt_of_lt_of_le (by positivity) hchi_ge
  have hvac_gt : (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) <
      ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ := by
    rw [norm_mul]
    calc (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re)
        ≤ (1 / 4 : ℝ) * ‖zetaChi s‖ := mul_le_mul_of_nonneg_left hchi_ge (by norm_num)
      _ < ‖1 - (2 : ℂ) ^ (-(1 - s))‖ * ‖zetaChi s‖ := mul_lt_mul_of_pos_right hpref hchi_pos
  have htri1 : ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ - ‖subdiagMoebiusGaussian δ s x D‖ ≤
      ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + subdiagMoebiusGaussian δ s x D‖ := by
    have h := norm_sub_norm_le ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s) (-subdiagMoebiusGaussian δ s x D)
    rwa [sub_neg_eq_add, norm_neg] at h
  have hsub_gt : (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - 1 / 16 <
      ‖subdiagMoebiusGaussian δ s x D‖ := by linarith
  rw [subdiagMoebiusGaussian_eq_vaughanTypeI_add_typeII hδ0 him hU hV x D] at hsub_gt
  have htri2 := norm_add_le (subdiagVaughanTypeI δ U V s x D) (subdiagVaughanTypeII δ U V s x D)
  have hm1 := le_max_left ‖subdiagVaughanTypeI δ U V s x D‖ ‖subdiagVaughanTypeII δ U V s x D‖
  have hm2 := le_max_right ‖subdiagVaughanTypeI δ U V s x D‖ ‖subdiagVaughanTypeII δ U V s x D‖
  linarith

end Part4ReflectedMobiusSubdiagonalDuality

#print axioms norm_asymTwinParam_pos_and_lt_one
#print axioms exists_asymmetric_conductor_four_crossHeight_countermodel_at_every_leftStrip_point
#print axioms coeffTheta_relation_of_unitPoleFreeCrossHeightDatum
#print axioms hamburgerSeries_periodic_conductor
#print axioms conductor_nat_and_periodic_even_of_unitPoleFreeCrossHeightDatum
#print axioms eq_const_mul_riemannZeta_of_conductor_lt_two
#print axioms selfDual_conductor_lt_five_classification
#print axioms smoothAFEZetaShiftedPoleResidue_mul_scale
#print axioms one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub
#print axioms exists_pure_direct_gaussian_witness_on_remaining_strip
#print axioms rh_iff_pure_direct_gaussian_witness_on_remaining_strip
#print axioms exists_norm_smoothAFEZetaDualCoefficientGeneral_zero_add_zetaChi_le
#print axioms smoothAFEZetaDualCoefficientGeneral_mul_scale
#print axioms poleCleared_reflected_moebius_crossHeight_eq
#print axioms subdiagCutoff_two_mul_le_and_eq_zero_of_lt
#print axioms exists_subdiagonal_moebius_gaussian_duality_on_remaining_strip
#print axioms strict_primeGas_witness_of_subdiagonal_domination_on_remaining_strip
#print axioms rh_iff_subdiagonal_moebius_gaussian_separation_on_remaining_strip
#print axioms subdiagMoebiusGaussian_eq_vaughanTypeI_add_typeII
#print axioms subdiagonal_vaughan_typeI_or_typeII_forced_above_spira_floor_of_zeta_eq_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
