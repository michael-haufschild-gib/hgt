import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectiveIndexOfTheAtomicKernelIsOneSquare
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.AMarginNeedsHarmonicCorrelation
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.FullCorrelationKeepsTheMargin
import GaloisForLFunctions.ArithmeticCountingPositivity.SmallPrimeFlipsLieBelowTheMaximalGap
import GaloisForLFunctions.ArithmeticCountingPositivity.PositiveDensityTransfersTheExactCutoffGap
import GaloisForLFunctions.ArithmeticCountingPositivity.CofinitePrimeFlipsHaveZeroGap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRenormalizedHodgeIndex

/-!
# The atomic Hodge index separates exactly the submaximal margins

At atomic resolution a sign gauge `ω` (`ω² = 1`) is the matrix `D·1 − P_N(ω ·)` on the horizon
`{1, …, N}` (`HeckeKreinToeplitz.gaugeAtomMatrix`), and its **atomic Hodge defect** at the
counterterm `D` is its index on the pole hyperplane `Σ x_n/√n = 0`
(`HeckeKreinToeplitz.poleNegIndex`). The **margin** of `ω` is measured by its hyperplane gaps
(`SelectiveMultiscaleArithmeticPositivity.HasHyperplaneGap`): `g` is a gap if, eventually,
`P_N(ωx) ≤ (log N − γ − g + ε)|x|²` on the pole hyperplane. `ζ` has the maximal margin `2 log 2`.

* **Gap ⇒ Hodge index** (`eventually_poleNegIndex_gauge_eq_zero_of_hasHyperplaneGap`): a gap `g`
  makes the Hodge defect vanish for every counterterm `D ≥ log N − γ − g + ε`.
* **No gap ⇒ Hodge defect** (`frequently_one_le_poleNegIndex_gauge_of_not_hasHyperplaneGap`): if
  `g` is not a gap, then for some `ε > 0` the Hodge defect is at least one at every counterterm
  `D < log N − γ − g + ε`, for infinitely many `N`.
* **Exact separation** (`hodgeSeparates_iff_not_hasHyperplaneGap`): just above `ζ`'s ceiling
  `log N − γ − 2 log 2` the atomic Hodge index holds for `ζ` and fails for `ω`, infinitely often,
  iff `2 log 2` is not a gap of `ω`.
* **The twins** (corollaries, from the margin classifications of SMAP and ArithmeticCountingPositivity):
  separated are the Liouville twin (`hodgeSeparates_liouville`), every gauge with
  `S_N(ω)² = o(log N)` (`hodgeSeparates_of_harmonicSum_small`), every cofinite flip
  (`hodgeSeparates_cofiniteFlip`) and the prime flips `p < 11` (`hodgeSeparates_primeFlip_iff`); not
  separated are the prime flips `p ≥ 11` and every gauge with harmonic correlation `S_N(ω)/H_N → 1`
  (`not_hodgeSeparates_of_correlation`).
* **Every prime-set twin** (`hodgeSeparates_primeSetFlip_iff`): flipping an arbitrary set `P` of
  primes, finite or infinite, is separated iff its greatest gap is below `2 log 2`
  (ArithmeticCountingPositivity).

So the atomic Hodge index is a selection mechanism with a sharp domain: the twins it misses are those
whose top is the pole up to the conductor-`2` excitation. Finite flips among them are separated by
the glued test index (`TheGluedIndexSelectsZeta`).
-/

open Finset Filter
open scoped Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticElectrostatics (atomicWeilForm)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex liouvilleSign
  liouvilleSign_mul_self finiteFlip)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- The atomic matrix of a gauge at the counterterm `D`, as a complex Hermitian matrix. -/
abbrev gaugeAtom (N : ℕ) (D : ℝ) (ω : ℕ → ℝ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℂ :=
  (gaugeAtomMatrix N D ω).map (↑)

/-- The real form of a gauge on a horizon vector. -/
theorem gaugeAtom_real (N : ℕ) (D : ℝ) {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (y : PrimeHorizonIndex N → ℝ) :
    y ⬝ᵥ (gaugeAtomMatrix N D ω *ᵥ y) =
      D * ∑ n ∈ Icc 1 N, horizonExtend y n ^ 2 -
        atomicWeilForm N (fun n => ω n * horizonExtend y n) := by
  rw [← hermQuad_map_ofReal_real, ← hermQuad_gaugeAtom_restrict N D hω (horizonExtend y)]
  simp only [horizonExtend_coe]

/-- **A real bound on the pole hyperplane kills the Hodge defect.** -/
theorem poleNegIndex_gauge_eq_zero_of_le {N : ℕ} {D : ℝ} {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (h : ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
      atomicWeilForm N (fun n => ω n * x n) ≤ D * ∑ n ∈ Icc 1 N, x n ^ 2) :
    poleNegIndex N (gaugeAtom N D ω) = 0 := by
  rw [poleNegIndex, negIndexOn_eq_zero_iff]
  intro c hc
  have hc0 : poleFunctional N c = 0 := LinearMap.mem_ker.mp hc
  have key : ∀ y : PrimeHorizonIndex N → ℝ, ∑ n, y n * (Real.sqrt (n : ℕ))⁻¹ = 0 →
      0 ≤ y ⬝ᵥ (gaugeAtomMatrix N D ω *ᵥ y) := fun y hy => by
    rw [gaugeAtom_real N D hω]
    have := h (horizonExtend y) (by rw [sum_horizonExtend_div_sqrt]; exact hy)
    linarith
  rw [gaugeAtom, hermQuad_map_ofReal]
  refine add_nonneg (key _ ?_) (key _ ?_)
  · rw [← re_poleFunctional, hc0, Complex.zero_re]
  · rw [← im_poleFunctional, hc0, Complex.zero_im]

/-- **Gap ⇒ Hodge index.** -/
theorem eventually_poleNegIndex_gauge_eq_zero_of_hasHyperplaneGap {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {g : ℝ} (hg : HasHyperplaneGap ω g) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ - g + ε ≤ D →
      poleNegIndex N (gaugeAtom N D ω) = 0 := by
  obtain ⟨N₀, h⟩ := hg ε hε
  filter_upwards [eventually_ge_atTop N₀] with N hN D hD
  refine poleNegIndex_gauge_eq_zero_of_le hω fun x hx => ?_
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  exact (h N hN x hx).trans (mul_le_mul_of_nonneg_right hD hS)

/-- **No gap ⇒ Hodge defect, infinitely often.** -/
theorem frequently_one_le_poleNegIndex_gauge_of_not_hasHyperplaneGap {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {g : ℝ} (h : ¬ HasHyperplaneGap ω g) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ N : ℕ in atTop, ∀ D : ℝ, D < Real.log N - γ - g + ε →
      1 ≤ poleNegIndex N (gaugeAtom N D ω) := by
  obtain ⟨ε, hε, hN₀⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ x : ℕ → ℝ,
      ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧
        (Real.log N - γ - g + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 <
          atomicWeilForm N (fun n => ω n * x n) := by
    by_contra hc
    refine h fun ε hε => ?_
    by_contra hc'
    refine hc ⟨ε, hε, fun N₀ => ?_⟩
    by_contra hc''
    refine hc' ⟨N₀, fun N hN x hx => ?_⟩
    by_contra hlt
    exact hc'' ⟨N, hN, x, hx, lt_of_not_ge hlt⟩
  refine ⟨ε, hε, frequently_atTop.mpr fun N₀ => ?_⟩
  obtain ⟨N, hN₀, x, hx, hlt⟩ := hN₀ N₀
  refine ⟨N, hN₀, fun D hD => ?_⟩
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  refine one_le_negIndexOn (c := fun n : PrimeHorizonIndex N => (x n : ℂ))
    (LinearMap.mem_ker.mpr ?_) ?_
  · rw [poleFunctional_restrict, hx, Complex.ofReal_zero]
  · rw [gaugeAtom, hermQuad_gaugeAtom_restrict N D hω]
    nlinarith [mul_le_mul_of_nonneg_right hD.le hS]

/-- `ζ`'s atomic matrix is the trivial gauge. -/
theorem gaugeAtom_one (N : ℕ) (D : ℝ) :
    gaugeAtom N D (fun _ => 1) = gram (atomKernel D) (horizonPoint N) :=
  gaugeAtomMatrix_one N D

/-- The **atomic Hodge index separates `ζ` from `ω`** just above `ζ`'s ceiling: for some `δ > 0`
and infinitely many `N`, at `D = log N − γ − 2 log 2 + δ` the pole index of `ζ` is `0` and that of
`ω` is positive. -/
def HodgeSeparates (ω : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N : ℕ in atTop,
    poleNegIndex N (gram (atomKernel (Real.log N - γ - 2 * Real.log 2 + δ)) (horizonPoint N)) = 0 ∧
      1 ≤ poleNegIndex N (gaugeAtom N (Real.log N - γ - 2 * Real.log 2 + δ) ω)

/-- **Exact separation**: the atomic Hodge index separates `ζ` from a sign gauge iff the gauge does
not attain the maximal margin `2 log 2`. -/
theorem hodgeSeparates_iff_not_hasHyperplaneGap {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) :
    HodgeSeparates ω ↔ ¬ HasHyperplaneGap ω (2 * Real.log 2) := by
  have h1 : ∀ n : ℕ, (fun _ : ℕ => (1 : ℝ)) n * (fun _ : ℕ => (1 : ℝ)) n = 1 := fun _ => by norm_num
  constructor
  · rintro ⟨δ, hδ, hfreq⟩ hgap
    obtain ⟨N, ⟨-, h1'⟩, hpos⟩ := (hfreq.and_eventually
      (eventually_poleNegIndex_gauge_eq_zero_of_hasHyperplaneGap hω hgap hδ)).exists
    have h0 := hpos _ le_rfl
    omega
  · intro h
    obtain ⟨ε, hε, hfreq⟩ := frequently_one_le_poleNegIndex_gauge_of_not_hasHyperplaneGap hω h
    refine ⟨ε / 2, by positivity, (hfreq.and_eventually
      (eventually_poleNegIndex_gauge_eq_zero_of_hasHyperplaneGap h1
        zeta_hasHyperplaneGap_two_mul_log_two (half_pos hε))).mono fun N hN => ?_⟩
    refine ⟨?_, hN.1 _ (by linarith)⟩
    rw [← gaugeAtom_one]
    exact hN.2 _ le_rfl

/-- **The Liouville twin is separated.** -/
theorem hodgeSeparates_liouville : HodgeSeparates liouvilleSign :=
  (hodgeSeparates_iff_not_hasHyperplaneGap liouvilleSign_mul_self).mpr
    (not_liouville_hasHyperplaneGap' (by positivity))

/-- **Every gauge with `S_N(ω)² = o(log N)` is separated.** -/
theorem hodgeSeparates_of_harmonicSum_small {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => gaugeHarmonicSum ω N ^ 2 / Real.log N) atTop (nhds 0)) :
    HodgeSeparates ω :=
  (hodgeSeparates_iff_not_hasHyperplaneGap hω).mpr
    (not_hasHyperplaneGap_of_harmonicSum_small hω hS (by positivity))

/-- **Full harmonic correlation is not separated.** -/
theorem not_hodgeSeparates_of_correlation {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => gaugeHarmonicSum ω N / gaugeHarmonicSum (fun _ => 1) N) atTop
      (nhds 1)) :
    ¬ HodgeSeparates ω := fun h =>
  (hodgeSeparates_iff_not_hasHyperplaneGap hω).mp h
    (hasHyperplaneGap_two_mul_log_two_of_correlation hω hS)

theorem finiteFlip_mul_self (F : Finset ℕ) (n : ℕ) : finiteFlip F n * finiteFlip F n = 1 := by
  rw [finiteFlip, ← prod_mul_distrib]
  refine prod_eq_one fun p _ => ?_
  rw [← mul_pow]
  norm_num

/-! ### Sign gauges defined up to the value at `0` -/

/-- The gauge with its value at `0` set to `1`; the atomic forms read only `n ≥ 1`. -/
def gaugeFix (ω : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else ω n

theorem gaugeFix_mul_self {ω : ℕ → ℝ} (hω : ∀ n, n ≠ 0 → ω n * ω n = 1) (n : ℕ) :
    gaugeFix ω n * gaugeFix ω n = 1 := by
  unfold gaugeFix
  split_ifs with h
  · norm_num
  · exact hω n h

theorem gaugeAtom_gaugeFix (N : ℕ) (D : ℝ) (ω : ℕ → ℝ) :
    gaugeAtom N D (gaugeFix ω) = gaugeAtom N D ω := by
  have h : ∀ n : PrimeHorizonIndex N, gaugeFix ω n = ω n := fun n =>
    if_neg (by have := (mem_Icc.mp n.2).1; omega)
  ext m n
  simp only [gaugeAtom, Matrix.map_apply, gaugeAtomMatrix, h]

theorem hasHyperplaneGap_gaugeFix_iff {ω : ℕ → ℝ} {g : ℝ} :
    HasHyperplaneGap (gaugeFix ω) g ↔ HasHyperplaneGap ω g := by
  have h : ∀ (N : ℕ) (x : ℕ → ℝ), atomicWeilForm N (fun n => gaugeFix ω n * x n) =
      atomicWeilForm N (fun n => ω n * x n) := fun N x =>
    RenormalizedArithmeticPotentialTheory.atomicWeilForm_congr fun n hn => by
      rw [gaugeFix, if_neg (by have := (mem_Icc.mp hn).1; omega)]
  simp only [HasHyperplaneGap, h]

/-- **Exact separation for gauges with `ω(n)² = 1` for `n ≥ 1`.** -/
theorem hodgeSeparates_iff_of_ne_zero {ω : ℕ → ℝ} (hω : ∀ n, n ≠ 0 → ω n * ω n = 1) :
    HodgeSeparates ω ↔ ¬ HasHyperplaneGap ω (2 * Real.log 2) := by
  have h : HodgeSeparates (gaugeFix ω) ↔ HodgeSeparates ω := by
    simp only [HodgeSeparates, gaugeAtom_gaugeFix]
  rw [← h, hodgeSeparates_iff_not_hasHyperplaneGap (gaugeFix_mul_self hω),
    hasHyperplaneGap_gaugeFix_iff]

/-- **Every cofinite flip is separated**: it has no positive margin. -/
theorem hodgeSeparates_cofiniteFlip {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    HodgeSeparates (ArithmeticCountingPositivity.cofiniteFlip F) := by
  rw [hodgeSeparates_iff_of_ne_zero fun n hn =>
    (ArithmeticCountingPositivity.cofiniteFlip_isSignGauge F).mul_self hn]
  intro h
  have := (ArithmeticCountingPositivity.isGreatest_cofiniteFlip_hyperplaneGap hF).2 h
  linarith [Real.log_pos one_lt_two]

/-- **Every prime-set twin is separated iff its greatest gap is below `2 log 2`.** -/
theorem hodgeSeparates_primeSetFlip_iff (P : Set ℕ) :
    HodgeSeparates (ArithmeticCountingPositivity.primeSetFlip P) ↔
      ArithmeticCountingPositivity.primeSetGreatestGap P < 2 * Real.log 2 := by
  have hω : ∀ n, n ≠ 0 → ArithmeticCountingPositivity.primeSetFlip P n *
      ArithmeticCountingPositivity.primeSetFlip P n = 1 := fun n _ => by
    rw [ArithmeticCountingPositivity.primeSetFlip_eq_finiteFlip_of_le P le_rfl]
    exact finiteFlip_mul_self _ n
  rw [hodgeSeparates_iff_of_ne_zero hω,
    ArithmeticCountingPositivity.primeSetFlip_hasHyperplaneGap_iff_le_greatestGap, not_le]

/-- **A prime flip is separated iff `p < 11`.** -/
theorem hodgeSeparates_primeFlip_iff {p : ℕ} (hp : p.Prime) :
    HodgeSeparates (finiteFlip {p}) ↔ p < 11 := by
  rw [hodgeSeparates_iff_not_hasHyperplaneGap (finiteFlip_mul_self {p}),
    ArithmeticCountingPositivity.primeFlip_hasHyperplaneGap_two_mul_log_two_iff hp, not_le]

end GaloisForLFunctions.RenormalizedIntersectionTheory
