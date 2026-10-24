import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalCollaredFirstVariation
import GaloisForLFunctions.«arithmetic-positivity-theory».FromTheCriticalFamilyToTheReceiver

/-!
# Complete First Variation Sign Equivalence and Moving-Aperture Grid-Tent Transfer on RH-Complete Families

Every finite translated factorial-tent pattern `factorialTentPattern S n b t` (and in particular
every single-scale grid tent pattern `gridTentPattern G n a M`) is compactly supported and
Lipschitz, so its extended Weil energy `suzukiCriticalExtendedWeilEnergy` coincides in `EReal` with
the finite complete Weil energy `compactFullWeilEnergy` (and `fullZeroForm`). Embedding `ℝ ↪ EReal`
therefore upgrades the `L²` Suzuki first-variation limit to exact real-valued convergence
`(autocorr P 0 - suzukiCriticalSourcePairing P ω) / ω → compactFullWeilEnergy P` as `ω → 0⁺` across
the entire RH-complete `factorialTentPattern` and `gridTentPattern` families, retaining all
archimedean Lévy, Gamma, prime-power, and polar terms.

Combined with the joint compact-window `Γ`-lower semicontinuity and deficit inheritance of
`SuzukiCriticalMovingWindowDeficit` and the moving-aperture critical-family positivity of
`SuzukiCriticalCollaredFirstVariation`, this module establishes three unconditional results:

1. **Exact Real-Valued Complete First Variation and Two-Way RH Sign Equivalence on
   `factorialTentPattern` and `gridTentPattern`:**
   - Every Lipschitz `f ∈ C_c(ℝ, ℝ)`, and hence every `factorialTentPattern` and `gridTentPattern`,
     has real-valued positive-shift Suzuki first variation equal to `compactFullWeilEnergy f`.
   - Strict complete Weil positivity of `P` yields an explicit linear finite-shift literal Suzuki
     deficit `ω * (W / 2) < autocorr P 0 - suzukiCriticalSourcePairing P ω`; conversely, any
     negative complete Weil value `W < 0` (such as an off-line zero witness) forces a strict linear
     finite-shift overshoot `autocorr P 0 + ω * (-W / 2) < suzukiCriticalSourcePairing P ω`.
   - Consequently, `RiemannHypothesis` is equivalent both to nonnegativity of the complete Suzuki
     first variation across `factorialTentPattern` and to the absence of linear small-shift
     overshoot above `autocorr P 0` across `factorialTentPattern`.

2. **Quantitative `L²` Grid-Tent Approximation and Grid-Scale-Uniform (`n`-Independent) Finite-Shift
   Suzuki Deficits:**
   - Every Lipschitz compact source `g ∈ C_c(ℝ, ℝ)` automatically has Lipschitz exponentially
     weighted profile `x ↦ e^{-3x/2} g(x)`, and its single-scale grid tent patterns `P_n` converge
     strongly to `g` in `L²(ℝ)` at explicit rate `O(√(d_{n+1}))` inside `[-(R + 2), R + 2]`.
   - Whenever `2 * μ ≤ compactFullWeilEnergy g` with `μ > 0`, combining finite-scale pigeonhole
     extraction with joint compact-window `L²` deficit inheritance (`SuzukiCriticalMovingWindowDeficit`)
     produces an explicit scale threshold `n₀` and a **single positive shift threshold `ω₀ > 0`
     independent of the grid scale `n`** such that
     `ω * (μ / 2) < autocorr (P_n) 0 - suzukiCriticalSourcePairing (P_n) ω` holds simultaneously for
     all `n ≥ n₀` and all `ω ∈ (0, ω₀)`.

3. **Unconditional Finite-Shift Suzuki Deficits on `gridTentPattern` Across All Positivity Regimes:**
   - Small-aperture all-profile receiver regime: every nonzero `F ∈ C_c²([-3/10, 3/10], ℝ)`.
   - Small-aperture odd receiver regime past `(log 2) / 2`: every nonzero odd
     `F ∈ C_c²([-181/500, 181/500], ℝ)` where the prime `2` actively enters the correlation support.
   - Unbounded-aperture high dyadic blocks, polynomial scale windows `[M, L M]` (`L ≤ M^δ`), and
     arbitrary-depth lacunary block unions at every truncation height `V ≥ criticalTruncationThreshold`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ENNReal CompactlySupported RealInnerProductSpace
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.CHMDDoobGraph

namespace RHTower
noncomputable section

/-! ## Section 1: Exact Real-Valued Complete First Variation and RH Sign Equivalence on `factorialTentPattern` -/

/-- On any Lipschitz compactly supported source `f ∈ C_c(ℝ, ℝ)`, the extended Weil energy
`suzukiCriticalExtendedWeilEnergy f` coincides with `(compactFullWeilEnergy f : EReal)`. -/
theorem suzukiCriticalExtendedWeilEnergy_eq_compactFullWeilEnergy_of_lipschitz
    (f : C_c(ℝ, ℝ)) {K : ℝ} (hK : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    suzukiCriticalExtendedWeilEnergy f = (compactFullWeilEnergy f : EReal) := by
  have hf : MemLp (f : ℝ → ℝ) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hJ := integrableOn_levy_of_lipschitz f (K := K) hK
  have hW := re_weilFullFunctional_eq_of_compact_finite_jump f hJ
  have hac (x : ℝ) : sourceAutocorrelation f x = autocorr f x := by
    rw [← autocorr_neg]
    unfold sourceAutocorrelation autocorr
    simp only [sub_eq_add_neg]
  have hnn : ∀ x ∈ Ioi (0 : ℝ),
      0 ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    intro x hx
    exact mul_nonneg (AutocorrelationKrein.deficit_nonneg hf x) (archLevySinhWeight_pos hx).le
  have hlev : (sourceLevyEnergy f : EReal) = (biScaleLevyEnergy f : ℝ) := by
    unfold sourceLevyEnergy biScaleLevyEnergy
    simp only [hac]
    rw [← ofReal_integral_eq_lintegral_ofReal hJ
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn)),
      EReal.coe_ennreal_ofReal, max_eq_left (setIntegral_nonneg measurableSet_Ioi hnn)]
  unfold suzukiCriticalExtendedWeilEnergy compactFullWeilEnergy
  rw [hlev, ← EReal.coe_add, hW]
  congr 1
  ring

/-- Every Lipschitz compactly supported source `f ∈ C_c(ℝ, ℝ)` has finite real-valued positive-shift
Suzuki first variation equal to `compactFullWeilEnergy f`. -/
theorem tendsto_suzukiCriticalSourcePairing_firstVariation_of_lipschitz
    (f : C_c(ℝ, ℝ)) {K : ℝ} (hK : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    Tendsto (fun omega : ℝ => (autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega)
      (𝓝[>] 0) (𝓝 (compactFullWeilEnergy f)) := by
  have hf : MemLp (f : ℝ → ℝ) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have h := tendsto_suzukiCriticalSourcePairing_extended_firstVariation hf f.hasCompactSupport
  change Tendsto (fun omega : ℝ =>
    (((autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega : ℝ) : EReal))
    (𝓝[>] 0) (𝓝 (suzukiCriticalExtendedWeilEnergy f)) at h
  rw [suzukiCriticalExtendedWeilEnergy_eq_compactFullWeilEnergy_of_lipschitz f hK] at h
  exact EReal.tendsto_coe.mp h

/-- Identification of `suzukiCriticalExtendedWeilEnergy` with `compactFullWeilEnergy` and
`fullZeroForm` across the entire `factorialTentPattern` family. -/
theorem suzukiCriticalExtendedWeilEnergy_factorialTentPattern
    (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ) :
    suzukiCriticalExtendedWeilEnergy (factorialTentPattern S n b t) =
      (compactFullWeilEnergy (factorialTentPattern S n b t) : EReal) ∧
    suzukiCriticalExtendedWeilEnergy (factorialTentPattern S n b t) =
      (fullZeroForm (factorialTentPattern S n b t) : EReal) := by
  have h1 := suzukiCriticalExtendedWeilEnergy_eq_compactFullWeilEnergy_of_lipschitz
    (factorialTentPattern S n b t) (factorialTentPattern_lipschitz_bound S n b t)
  exact ⟨h1, h1.trans (congrArg (fun x : ℝ => (x : EReal))
    (fullZeroForm_eq_compactFullWeilEnergy (factorialTentPattern S n b t)).symm)⟩

/-- **Exact Complete First Variation on `factorialTentPattern`.**
For every finite translated factorial-tent pattern `P = factorialTentPattern S n b t`, the real
difference quotient `(autocorr P 0 - suzukiCriticalSourcePairing P ω) / ω` converges in `ℝ` to
`compactFullWeilEnergy P` as `ω → 0⁺`. -/
theorem tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation
    (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ) :
    Tendsto (fun omega : ℝ =>
        (autocorr (factorialTentPattern S n b t) 0 -
          suzukiCriticalSourcePairing (factorialTentPattern S n b t) omega) / omega)
      (𝓝[>] 0) (𝓝 (compactFullWeilEnergy (factorialTentPattern S n b t))) :=
  tendsto_suzukiCriticalSourcePairing_firstVariation_of_lipschitz
    (factorialTentPattern S n b t) (factorialTentPattern_lipschitz_bound S n b t)

/-- **Exact Complete First Variation on `gridTentPattern`.** -/
theorem tendsto_suzukiCriticalSourcePairing_gridTentPattern_firstVariation
    (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M : ℕ) :
    Tendsto (fun omega : ℝ =>
        (autocorr (gridTentPattern G n a M) 0 -
          suzukiCriticalSourcePairing (gridTentPattern G n a M) omega) / omega)
      (𝓝[>] 0) (𝓝 (compactFullWeilEnergy (gridTentPattern G n a M))) := by
  unfold gridTentPattern
  exact tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation _ _ _ _

/-- Positive complete Weil energy on a `factorialTentPattern` forces a strict linear finite-shift
Suzuki deficit on an explicit interval `(0, ω₀)`. -/
theorem exists_suzukiCriticalDeficit_factorialTentPattern_of_pos
    {S : Finset ℕ} {n : ℕ → ℕ} {b t : ℕ → ℝ}
    (hpos : 0 < compactFullWeilEnergy (factorialTentPattern S n b t)) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      ω * (compactFullWeilEnergy (factorialTentPattern S n b t) / 2) <
        autocorr (factorialTentPattern S n b t) 0 -
          suzukiCriticalSourcePairing (factorialTentPattern S n b t) ω ∧
      suzukiCriticalSourcePairing (factorialTentPattern S n b t) ω <
        autocorr (factorialTentPattern S n b t) 0 := by
  set P := factorialTentPattern S n b t
  set W := compactFullWeilEnergy P
  have hlim := tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation S n b t
  have hev := hlim.eventually (Ioi_mem_nhds (show W / 2 < W by linarith))
  obtain ⟨ω₀, hω₀, hball⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨ω₀, hω₀, fun ω hω0 hω_lt => ?_⟩
  have hmem : ω ∈ Metric.ball (0 : ℝ) ω₀ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hω0]
    exact hω_lt
  have hq : W / 2 < (autocorr P 0 - suzukiCriticalSourcePairing P ω) / ω := hball hmem hω0
  have hd : ω * (W / 2) < autocorr P 0 - suzukiCriticalSourcePairing P ω := by
    simpa only [mul_comm] using (lt_div_iff₀ hω0).mp hq
  exact ⟨hd, by linarith [mul_pos hω0 (half_pos hpos)]⟩

/-- Negative complete Weil energy on a `factorialTentPattern` (such as an off-line zero witness)
forces a strict linear finite-shift overshoot above `autocorr P 0` on an explicit interval `(0, ω₀)`. -/
theorem exists_suzukiCriticalOvershoot_factorialTentPattern_of_neg
    {S : Finset ℕ} {n : ℕ → ℕ} {b t : ℕ → ℝ}
    (hneg : compactFullWeilEnergy (factorialTentPattern S n b t) < 0) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      autocorr (factorialTentPattern S n b t) 0 +
        ω * (-compactFullWeilEnergy (factorialTentPattern S n b t) / 2) <
          suzukiCriticalSourcePairing (factorialTentPattern S n b t) ω ∧
      autocorr (factorialTentPattern S n b t) 0 <
        suzukiCriticalSourcePairing (factorialTentPattern S n b t) ω := by
  set P := factorialTentPattern S n b t
  set W := compactFullWeilEnergy P
  have hlim := tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation S n b t
  have hev := hlim.eventually (Iio_mem_nhds (show W < W / 2 by linarith))
  obtain ⟨ω₀, hω₀, hball⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨ω₀, hω₀, fun ω hω0 hω_lt => ?_⟩
  have hmem : ω ∈ Metric.ball (0 : ℝ) ω₀ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hω0]
    exact hω_lt
  have hq : (autocorr P 0 - suzukiCriticalSourcePairing P ω) / ω < W / 2 := hball hmem hω0
  have hd : autocorr P 0 - suzukiCriticalSourcePairing P ω < (W / 2) * ω :=
    (div_lt_iff₀ hω0).mp hq
  have hov : autocorr P 0 + ω * (-W / 2) < suzukiCriticalSourcePairing P ω := by linarith
  exact ⟨hov, by linarith [mul_pos hω0 (show 0 < -W / 2 by linarith)]⟩

/-- **Sign Equivalence for the Complete Suzuki First Variation on the RH-Complete Family
`factorialTentPattern`.**
The Riemann Hypothesis holds if and only if every `factorialTentPattern` has nonnegative real-valued
Suzuki complete first-variation limit, and if and only if no `factorialTentPattern` exhibits linear
small-shift overshoot above its `L²` mass `autocorr P 0`. -/
theorem riemannHypothesis_iff_factorialTentPattern_suzukiFirstVariation_nonneg :
    (RiemannHypothesis ↔ ∀ (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ),
      ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun omega : ℝ =>
        (autocorr (factorialTentPattern S n b t) 0 -
          suzukiCriticalSourcePairing (factorialTentPattern S n b t) omega) / omega)
        (𝓝[>] 0) (𝓝 L)) ∧
    (RiemannHypothesis ↔ ∀ (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ omega : ℝ in 𝓝[>] 0,
        suzukiCriticalSourcePairing (factorialTentPattern S n b t) omega ≤
          autocorr (factorialTentPattern S n b t) 0 + ε * omega) := by
  have hiff2 : RiemannHypothesis ↔ ∀ (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ omega : ℝ in 𝓝[>] 0,
        suzukiCriticalSourcePairing (factorialTentPattern S n b t) omega ≤
          autocorr (factorialTentPattern S n b t) 0 + ε * omega := by
    rw [riemannHypothesis_iff_factorialTentPattern_nonneg]
    constructor
    · intro hRH S n b t ε hε
      set P := factorialTentPattern S n b t
      have hW : 0 ≤ compactFullWeilEnergy P := hRH S n b t
      have hlim := tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation S n b t
      have hev := hlim.eventually (Ioi_mem_nhds (show -ε < compactFullWeilEnergy P by linarith))
      filter_upwards [self_mem_nhdsWithin, hev] with omega homega hq
      change 0 < omega at homega
      have hd : -ε * omega < autocorr P 0 - suzukiCriticalSourcePairing P omega :=
        (lt_div_iff₀ homega).mp hq
      linarith
    · intro hno S n b t
      by_contra hlt
      push Not at hlt
      set P := factorialTentPattern S n b t
      set ε := -compactFullWeilEnergy P / 2
      have hε : 0 < ε := by unfold ε; linarith
      obtain ⟨ω₀, hω₀, hov⟩ := exists_suzukiCriticalOvershoot_factorialTentPattern_of_neg hlt
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
        (eventually_nhdsWithin_iff.mp (hno S n b t ε hε))
      set ω := min (ω₀ / 2) (δ / 2)
      have hω0 : 0 < ω := lt_min (half_pos hω₀) (half_pos hδ)
      have hω_lt_ω₀ : ω < ω₀ := (min_le_left _ _).trans_lt (half_lt_self hω₀)
      have hω_lt_δ : ω < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
      have hmem : ω ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hω0]
        exact hω_lt_δ
      have hle : suzukiCriticalSourcePairing P ω ≤ autocorr P 0 + ε * ω := hball hmem hω0
      have hgt := (hov ω hω0 hω_lt_ω₀).1
      change autocorr P 0 + ω * ε < suzukiCriticalSourcePairing P ω at hgt
      linarith
  refine ⟨?_, hiff2⟩
  constructor
  · intro hRH S n b t
    exact ⟨compactFullWeilEnergy (factorialTentPattern S n b t),
      riemannHypothesis_iff_factorialTentPattern_nonneg.mp hRH S n b t,
      tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation S n b t⟩
  · intro hex
    refine hiff2.mpr fun S n b t ε hε => ?_
    obtain ⟨L, hL0, hlim⟩ := hex S n b t
    have hev := hlim.eventually (Ioi_mem_nhds (show -ε < L by linarith))
    filter_upwards [self_mem_nhdsWithin, hev] with omega homega hq
    change 0 < omega at homega
    have hd : -ε * omega < autocorr (factorialTentPattern S n b t) 0 -
        suzukiCriticalSourcePairing (factorialTentPattern S n b t) omega :=
      (lt_div_iff₀ homega).mp hq
    linarith

/-- **Sign Equivalence for the Complete Suzuki First Variation on the Single-Scale RH-Complete
Family `gridTentPattern`.**
The Riemann Hypothesis holds if and only if for every profile `G : ℝ → ℝ` and every radius `R ≥ 0`,
for all sufficiently large arithmetic scales `n`, the single-scale uniform-grid factorial-tent
pattern `gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊` has
nonnegative real-valued Suzuki complete first-variation limit (equivalently, exhibits no linear
small-shift overshoot above its `L²` mass). -/
theorem riemannHypothesis_iff_eventually_gridTentPattern_suzukiFirstVariation_nonneg :
    (RiemannHypothesis ↔ ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R → ∀ᶠ n : ℕ in atTop,
      let P := gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun omega : ℝ =>
        (autocorr P 0 - suzukiCriticalSourcePairing P omega) / omega)
        (𝓝[>] 0) (𝓝 L)) ∧
    (RiemannHypothesis ↔ ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R → ∀ᶠ n : ℕ in atTop,
      let P := gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      ∀ ε : ℝ, 0 < ε → ∀ᶠ omega : ℝ in 𝓝[>] 0,
        suzukiCriticalSourcePairing P omega ≤ autocorr P 0 + ε * omega) := by
  have hiff2 : RiemannHypothesis ↔ ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R → ∀ᶠ n : ℕ in atTop,
      let P := gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      ∀ ε : ℝ, 0 < ε → ∀ᶠ omega : ℝ in 𝓝[>] 0,
        suzukiCriticalSourcePairing P omega ≤ autocorr P 0 + ε * omega := by
    rw [riemannHypothesis_iff_eventually_gridTentPattern_nonneg]
    constructor
    · intro hRH G R hR
      filter_upwards [hRH G R hR] with n hW
      dsimp only
      intro ε hε
      set P := gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      have hlim := tendsto_suzukiCriticalSourcePairing_gridTentPattern_firstVariation G n (-(R + 1))
        ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      have hev := hlim.eventually (Ioi_mem_nhds (show -ε < compactFullWeilEnergy P by linarith))
      filter_upwards [self_mem_nhdsWithin, hev] with omega homega hq
      change 0 < omega at homega
      have hd : -ε * omega < autocorr P 0 - suzukiCriticalSourcePairing P omega :=
        (lt_div_iff₀ homega).mp hq
      linarith
    · intro hno G R hR
      filter_upwards [hno G R hR] with n hn
      dsimp only at hn
      set P := gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      by_contra hlt
      push Not at hlt
      set ε := -compactFullWeilEnergy P / 2
      have hε : 0 < ε := by unfold ε; linarith
      have hlt' : compactFullWeilEnergy (factorialTentPattern
          (Finset.range (⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊ + 1)) (fun _ => n)
          (fun i => G (-(R + 1) + ↑i * sourceFactorialWidth (n + 1)) *
            (Real.exp (sourceFactorialWidth (n + 1)) - 1) ^ 2 *
            Real.exp (-(3 * (sourceFactorialWidth (n + 1) - (-(R + 1) + ↑i * sourceFactorialWidth (n + 1))) / 2)) /
            sourceFactorialWidth (n + 1))
          (fun i => sourceFactorialWidth (n + 1) - (-(R + 1) + ↑i * sourceFactorialWidth (n + 1)))) < 0 := by
        change compactFullWeilEnergy P < 0
        exact hlt
      obtain ⟨ω₀, hω₀, hov⟩ := exists_suzukiCriticalOvershoot_factorialTentPattern_of_neg hlt'
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
        (eventually_nhdsWithin_iff.mp (hn ε hε))
      set ω := min (ω₀ / 2) (δ / 2)
      have hω0 : 0 < ω := lt_min (half_pos hω₀) (half_pos hδ)
      have hω_lt_ω₀ : ω < ω₀ := (min_le_left _ _).trans_lt (half_lt_self hω₀)
      have hω_lt_δ : ω < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
      have hmem : ω ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hω0]
        exact hω_lt_δ
      have hle : suzukiCriticalSourcePairing P ω ≤ autocorr P 0 + ε * ω := hball hmem hω0
      have hgt := (hov ω hω0 hω_lt_ω₀).1
      change autocorr P 0 + ω * ε < suzukiCriticalSourcePairing P ω at hgt
      linarith
  refine ⟨?_, hiff2⟩
  constructor
  · intro hRH G R hR
    filter_upwards [riemannHypothesis_iff_eventually_gridTentPattern_nonneg.mp hRH G R hR] with n hW
    dsimp only
    exact ⟨compactFullWeilEnergy _, hW,
      tendsto_suzukiCriticalSourcePairing_gridTentPattern_firstVariation G n (-(R + 1)) _⟩
  · intro hex
    refine hiff2.mpr fun G R hR => ?_
    filter_upwards [hex G R hR] with n hn
    dsimp only at hn ⊢
    obtain ⟨L, hL0, hlim⟩ := hn
    intro ε hε
    have hev := hlim.eventually (Ioi_mem_nhds (show -ε < L by linarith))
    filter_upwards [self_mem_nhdsWithin, hev] with omega homega hq
    change 0 < omega at homega
    have hd : -ε * omega < autocorr _ 0 - suzukiCriticalSourcePairing _ omega :=
      (lt_div_iff₀ homega).mp hq
    linarith

/-! ## Section 2: Quantitative `L²` Grid-Tent Convergence and Grid-Scale-Uniform Finite-Shift Suzuki Deficits -/

/-- Any bounded Lipschitz profile `g` vanishing outside `[-R, R]` (`0 ≤ R`) automatically has
Lipschitz exponentially weighted seed `x ↦ e^{-3x/2} g(x)`. -/
theorem expNegThreeHalves_mul_lipschitz {g : ℝ → ℝ} {R Mg Kg : ℝ} (hR : 0 ≤ R)
    (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|) (x y : ℝ) :
    |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤
      Real.exp (3 * R / 2) * (Kg + 3 / 2 * Mg) * |x - y| := by
  have hflip : ∀ u v, |g (-u) - g (-v)| ≤ Kg * |u - v| := fun u v => by
    simpa only [show -u - -v = -(u - v) by ring, abs_neg] using hKg (-u) (-v)
  have hMflip : ∀ u, |g (-u)| ≤ Mg := fun u => hMg (-u)
  have hout : ∀ u, R < |u| → g (-u) = 0 := fun u hu => hgR (-u) (by simpa only [abs_neg] using hu)
  have h := expWeight_mul_lipschitz (F := fun u => g (-u)) hR hflip hMflip hout (-x) (-y)
  have h1 : Real.exp (3 * -x / 2) * g (- -x) = Real.exp (-(3 * x / 2)) * g x := by
    rw [neg_neg]; congr 2; ring
  have h2 : Real.exp (3 * -y / 2) * g (- -y) = Real.exp (-(3 * y / 2)) * g y := by
    rw [neg_neg]; congr 2; ring
  have h3 : |-x - -y| = |x - y| := by rw [show -x - -y = -(x - y) by ring, abs_neg]
  rwa [h1, h2, h3] at h

private theorem norm_toLp_sub_eq_sqrt_integral_sq' {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ = Real.sqrt (∫ x, (f x - g x) ^ 2) := by
  have hsq : ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 := by
    rw [← hf.toLp_sub hg, ← autocorr_zero_eq_norm_toLp_sq (hf.sub hg)]
    unfold autocorr
    simp only [Pi.sub_apply, add_zero, sq]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Quantitative `L²` squared-distance bound for `gridTentPattern` on `[-R, R]`. -/
theorem integral_sq_gridTentPattern_sub_le (g : C_c(ℝ, ℝ)) {R Mg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n : ℕ) :
    (∫ x, (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
        n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊ x - g x) ^ 2) ≤
      gridTentMassApproximationConstant R Mg L * sourceFactorialWidth (n + 1) := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  obtain ⟨hfM, -, -, hgap⟩ := compactSourceL1Gap_gridTentPattern_le g hR hgR hMg hGL n
  set P := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
    n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  set B := R + 2
  set MG := Real.exp (3 * B / 2) * Mg
  set Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  have hMM : 0 ≤ Mf + Mg := by positivity
  have hint_sq : Integrable (fun x => (P x - g x) ^ 2) := by
    have h := ((P - g).continuous.mul (P - g).continuous).integrable_of_hasCompactSupport
      (μ := volume) (P - g).hasCompactSupport.mul_right
    exact h.congr (Eventually.of_forall fun x => by
      rw [Pi.mul_apply]; dsimp only; rw [sq]; rfl)
  have hint_abs : Integrable (fun x => (Mf + Mg) * |P x - g x|) :=
    (((P - g).continuous.integrable_of_hasCompactSupport
      (μ := volume) (P - g).hasCompactSupport).abs).const_mul (Mf + Mg)
  have hpt : ∀ x, (P x - g x) ^ 2 ≤ (Mf + Mg) * |P x - g x| := fun x => by
    have htri : |P x - g x| ≤ Mf + Mg :=
      (abs_sub _ _).trans (add_le_add (hfM x) (hMg x))
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_right htri (abs_nonneg _)
  calc (∫ x, (P x - g x) ^ 2)
      ≤ ∫ x, (Mf + Mg) * |P x - g x| := integral_mono hint_sq hint_abs hpt
    _ = (Mf + Mg) * compactSourceL1Gap P g := by
        unfold compactSourceL1Gap; rw [integral_const_mul]
    _ ≤ (Mf + Mg) * (2 * B * (Real.exp (3 * B / 2) * (2 * L)) * sourceFactorialWidth (n + 1)) :=
        mul_le_mul_of_nonneg_left hgap hMM
    _ = gridTentMassApproximationConstant R Mg L * sourceFactorialWidth (n + 1) := by
        unfold gridTentMassApproximationConstant; ring

/-- Strong `L²(ℝ)` convergence of `gridTentPattern` to `g` as `n → ∞`. -/
theorem tendsto_gridTentPattern_toLp (g : C_c(ℝ, ℝ)) {R Mg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (hp : ∀ n : ℕ, MemLp (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
      n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊ : ℝ → ℝ) 2 volume)
    (hg_lp : MemLp (g : ℝ → ℝ) 2 volume) :
    Tendsto (fun n : ℕ => (hp n).toLp (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
      n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊))
      atTop (𝓝 (hg_lp.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hdn : Tendsto (fun n : ℕ => sourceFactorialWidth (n + 1)) atTop (𝓝 0) := by
    have hub : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 12 : ℝ)
      simp only [mul_zero] at this
      exact this.congr fun n => by field_simp
    refine squeeze_zero (fun n => (sourceFactorialWidth_pos (by omega)).le) (fun n => ?_) hub
    have := (sourceFactorialWidth_bounds (N := n + 1) (by omega)).2
    push_cast at this; exact this
  have hprod := hdn.const_mul (gridTentMassApproximationConstant R Mg L)
  rw [mul_zero] at hprod
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hprod
  rw [Real.sqrt_zero] at hsqrt
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hsqrt
  dsimp only [Function.comp_apply]
  rw [norm_toLp_sub_eq_sqrt_integral_sq']
  exact Real.sqrt_le_sqrt (integral_sq_gridTentPattern_sub_le g hR hgR hMg hGL n)

/-- **Grid-Scale-Uniform (`n`-Independent) Finite-Shift Suzuki Deficit Transfer.**
Whenever `g ∈ C_c(ℝ, ℝ)` has complete Weil energy `2 * μ ≤ compactFullWeilEnergy g` (`μ > 0`), at
every scale threshold `n₀` where the grid-tent approximation error is at most `μ`, there exists a
**single positive shift threshold `ω₀ > 0` independent of `n`** such that every grid tent pattern
`P_n` (`n ≥ n₀`) simultaneously satisfies `μ ≤ compactFullWeilEnergy P_n` and the linear finite-shift
literal Suzuki deficit `ω * (μ / 2) < autocorr P_n 0 - suzukiCriticalSourcePairing P_n ω` on `(0, ω₀)`. -/
theorem exists_gridTentPattern_uniform_suzukiDeficit (g : C_c(ℝ, ℝ)) {R Mg Kg L μ : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (hμ : 0 < μ) (hge : 2 * μ ≤ compactFullWeilEnergy g)
    {n₀ : ℕ} (hn₀ : ∀ n ≥ n₀,
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ≤ μ) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
    let P : ℕ → C_c(ℝ, ℝ) := fun n =>
      gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    (∀ n ≥ n₀, μ ≤ compactFullWeilEnergy (P n)) ∧
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      ω * (μ / 2) < autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
      suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  dsimp only
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
  set P : ℕ → C_c(ℝ, ℝ) := fun n =>
    gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  have hP_weil : ∀ n ≥ n₀, μ ≤ compactFullWeilEnergy (P n) := fun n hn => by
    have h1 := (abs_le.mp (abs_compactFullWeilEnergy_gridTentPattern_sub_le g hR hgR hMg hKg hGL n)).1
    have h2 := hn₀ n hn
    linarith
  refine ⟨hP_weil, ?_⟩
  suffices hmain : ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      ω * (μ / 2) < autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω by
    obtain ⟨ω₀, hω₀, hshift⟩ := hmain
    refine ⟨ω₀, hω₀, fun n hn ω hω0 hω_lt => ?_⟩
    have hd := hshift n hn ω hω0 hω_lt
    exact ⟨hd, by linarith [mul_pos hω0 (half_pos hμ)]⟩
  by_contra hbad
  have hseq : ∀ k : ℕ, ∃ ω : ℝ, 0 < ω ∧ ω < 1 / ((k : ℝ) + 1) ∧
      ∃ m : ℕ, n₀ ≤ m ∧
        autocorr (P m) 0 - suzukiCriticalSourcePairing (P m) ω ≤ ω * (μ / 2) := by
    intro k
    by_contra hk
    push Not at hk
    refine hbad ⟨1 / ((k : ℝ) + 1), by positivity, fun n hn ω hω0 hω_lt => ?_⟩
    exact hk ω hω0 hω_lt n hn
  choose w hw_pos hw_lt m hm_ge hle using hseq
  have hw0 : Tendsto w atTop (𝓝 0) :=
    squeeze_zero (fun k => (hw_pos k).le) (fun k => (hw_lt k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto w atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw0, Eventually.of_forall hw_pos⟩
  by_cases hbdd : ∃ N : ℕ, ∀ᶠ k in atTop, m k ≤ N
  · -- Bounded-scale branch: finite pigeonhole extracts a constant scale `m (φ k) = j₀ ≥ n₀`.
    obtain ⟨N, hN⟩ := hbdd
    have hmem_Icc : ∀ᶠ k in atTop, m k ∈ Finset.Icc n₀ N :=
      hN.mono fun k hk => Finset.mem_Icc.mpr ⟨hm_ge k, hk⟩
    have hpig : ∀ s : Finset ℕ, (∀ᶠ k in atTop, m k ∈ s) → ∃ j ∈ s, ∃ᶠ k in atTop, m k = j := by
      intro s hs
      by_contra hall
      push Not at hall
      have hnone : ∀ (t : Finset ℕ), (∀ j ∈ t, ∀ᶠ k in atTop, m k ≠ j) → ∀ᶠ k in atTop, m k ∉ t := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => exact Eventually.of_forall fun _ => Finset.notMem_empty _
        | @insert a u _ ih =>
          have ha : ∀ᶠ k in atTop, m k ≠ a := ht a (Finset.mem_insert_self a u)
          have hu : ∀ᶠ k in atTop, m k ∉ u :=
            ih fun j hj => ht j (Finset.mem_insert_of_mem hj)
          exact (ha.and hu).mono fun k ⟨h1, h2⟩ hm => (Finset.mem_insert.mp hm).elim h1 h2
      obtain ⟨k, hk_in, hk_out⟩ := (hs.and (hnone s hall)).exists
      exact hk_out hk_in
    obtain ⟨j₀, hj₀_mem, hfreq⟩ := hpig (Finset.Icc n₀ N) hmem_Icc
    have hj₀_ge : n₀ ≤ j₀ := (Finset.mem_Icc.mp hj₀_mem).1
    obtain ⟨φ, hφ_mono, hmφ⟩ := Filter.extraction_of_frequently_atTop hfreq
    have hPj₀_ge : μ ≤ compactFullWeilEnergy (P j₀) := hP_weil j₀ hj₀_ge
    have hlim := (tendsto_suzukiCriticalSourcePairing_gridTentPattern_firstVariation G j₀ (-(R + 1))
      ⌈2 * (R + 1) / sourceFactorialWidth (j₀ + 1)⌉₊).comp (hw.comp hφ_mono.tendsto_atTop)
    have hev := hlim.eventually (Ioi_mem_nhds (show μ / 2 < compactFullWeilEnergy (P j₀) by linarith))
    obtain ⟨k, hk⟩ := hev.exists
    dsimp only [Function.comp_apply] at hk
    change μ / 2 < (autocorr (P j₀) 0 - suzukiCriticalSourcePairing (P j₀) (w (φ k))) / w (φ k) at hk
    have hd : w (φ k) * (μ / 2) <
        autocorr (P j₀) 0 - suzukiCriticalSourcePairing (P j₀) (w (φ k)) := by
      simpa only [mul_comm] using (lt_div_iff₀ (hw_pos (φ k))).mp hk
    have hPm : P (m (φ k)) = P j₀ := congrArg P (hmφ k)
    rw [← hPm] at hd
    linarith [hle (φ k)]
  · -- Unbounded-scale branch: diagonal extraction gives `m (φ k) → ∞`, contradicted by joint-window `L²` deficit inheritance.
    have hfreq_gt : ∀ N : ℕ, ∃ᶠ k in atTop, N < m k := fun N => by
      have hnot : ¬∀ᶠ k in atTop, m k ≤ N := fun h => hbdd ⟨N, h⟩
      simpa only [not_le] using Filter.not_eventually.mp hnot
    obtain ⟨φ, hφ_mono, hmφ⟩ := Filter.extraction_forall_of_frequently hfreq_gt
    have hm_top : Tendsto (fun k => m (φ k)) atTop atTop :=
      tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => (Nat.lt_of_le_of_lt hk (hmφ k)).le⟩
    have hp_all : ∀ n : ℕ, MemLp (P n : ℝ → ℝ) 2 volume := fun n =>
      (P n).continuous.memLp_of_hasCompactSupport (P n).hasCompactSupport
    have hg_lp : MemLp (g : ℝ → ℝ) 2 volume :=
      g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
    have htoLp := (tendsto_gridTentPattern_toLp g hR hgR hMg hGL hp_all hg_lp).comp hm_top
    have hs_P : ∀ k : ℕ, ∀ᵐ x ∂volume, x ∉ Icc (-(R + 2)) (R + 2) → P (m (φ k)) x = 0 :=
      fun k => Eventually.of_forall fun x hx => by
        have hf0 := (compactSourceL1Gap_gridTentPattern_le g hR hgR hMg hGL (m (φ k))).2.2.1
        refine hf0 x ?_
        by_contra hle_abs
        exact hx (abs_le.mp (not_lt.mp hle_abs))
    have hs_g : ∀ᵐ x ∂volume, x ∉ Icc (-(R + 2)) (R + 2) → g x = 0 :=
      Eventually.of_forall fun x hx => by
        refine hgR x ?_
        have hB : R + 2 < |x| := by
          by_contra hle_abs
          exact hx (abs_le.mp (not_lt.mp hle_abs))
        linarith
    have hweil_g : ((2 * μ : ℝ) : EReal) ≤ suzukiCriticalExtendedWeilEnergy g := by
      rw [suzukiCriticalExtendedWeilEnergy_eq_compactFullWeilEnergy_of_lipschitz g hKg]
      exact EReal.coe_le_coe_iff.mpr hge
    have hw_sub : Tendsto (w ∘ φ) atTop (𝓝[>] 0) := hw.comp hφ_mono.tendsto_atTop
    have hev := eventually_suzukiCriticalDeficit_of_joint_window_L2
      (f := fun k => (P (m (φ k)) : ℝ → ℝ)) (g := (g : ℝ → ℝ)) (w := w ∘ φ)
      (a := -(R + 2)) (b := R + 2) (c := 2 * μ) (δ := 3 * μ / 2)
      (fun k => hp_all (m (φ k))) hg_lp hs_P hs_g htoLp hw_sub hweil_g (by positivity)
    obtain ⟨k, hk⟩ := hev.exists
    dsimp only [Function.comp_apply] at hk
    have hsub : 2 * μ - 3 * μ / 2 = μ / 2 := by ring
    rw [hsub] at hk
    linarith [hle (φ k)]

/-- Explicit arithmetic-scale specialization `n₀ = ⌈gridTentApproximationConstant R Mg Kg L / (12 * μ)⌉₊`
of `exists_gridTentPattern_uniform_suzukiDeficit`. -/
theorem exists_gridTentPattern_uniform_suzukiDeficit_explicit_scale (g : C_c(ℝ, ℝ)) {R Mg Kg L μ : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (hμ : 0 < μ) (hge : 2 * μ ≤ compactFullWeilEnergy g) :
    let n₀ : ℕ := ⌈gridTentApproximationConstant R Mg Kg L / (12 * μ)⌉₊
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
    let P : ℕ → C_c(ℝ, ℝ) := fun n =>
      gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    (∀ n ≥ n₀, μ ≤ compactFullWeilEnergy (P n)) ∧
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      ω * (μ / 2) < autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
      suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  dsimp only
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hKg0 : 0 ≤ Kg := by have := (abs_nonneg _).trans (hKg 1 0); norm_num at this; exact this
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  have hC := gridTentApproximationConstant_nonneg hR hMg0 hKg0 hL0
  refine exists_gridTentPattern_uniform_suzukiDeficit g hR hgR hMg hKg hGL hμ hge
    (n₀ := ⌈gridTentApproximationConstant R Mg Kg L / (12 * μ)⌉₊) fun n hn => ?_
  have hd : sourceFactorialWidth (n + 1) ≤ 1 / (12 * ((n : ℝ) + 1)) := by
    have := (sourceFactorialWidth_bounds (N := n + 1) (by omega)).2
    push_cast at this; exact this
  have hceil : gridTentApproximationConstant R Mg Kg L / (12 * μ) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h12n : gridTentApproximationConstant R Mg Kg L ≤ 12 * μ * ((n : ℝ) + 1) := by
    have h1 := (div_le_iff₀ (by positivity : 0 < 12 * μ)).mp hceil
    nlinarith
  calc gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1)
      ≤ gridTentApproximationConstant R Mg Kg L * (1 / (12 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hd hC
    _ ≤ μ := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith

/-! ## Section 3: Unconditional `gridTentPattern` Finite-Shift Suzuki Deficits Across All Positivity Regimes -/

private theorem integral_sq_pos_of_continuous_nonzero {F : ℝ → ℝ}
    (hF_cont : Continuous F) (hFc : HasCompactSupport F) (hne : ∃ x, F x ≠ 0) :
    0 < ∫ x, F x ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  set c := |F x₀| / 2
  have hc : 0 < c := half_pos (abs_pos.mpr hx₀)
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp hF_cont.continuousAt) c hc
  set s := Icc (x₀ - δ / 2) (x₀ + δ / 2)
  have hint_sq : Integrable (fun x => F x ^ 2) := by
    have h := (hF_cont.mul hF_cont).integrable_of_hasCompactSupport (μ := volume) hFc.mul_right
    exact h.congr (Eventually.of_forall fun x => by rw [Pi.mul_apply]; dsimp only; rw [sq])
  have hint_ind : Integrable (s.indicator fun _ => c ^ 2) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (measure_Icc_lt_top (a := x₀ - δ / 2) (b := x₀ + δ / 2)).ne)
  have hpt : ∀ x, s.indicator (fun _ => c ^ 2) x ≤ F x ^ 2 := fun x => by
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      have hdist : dist x x₀ < δ := by
        rw [Real.dist_eq]
        exact (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans_lt (half_lt_self hδ)
      have hFx_close : |F x - F x₀| < c := by simpa only [Real.dist_eq] using hclose hdist
      have hFx_ge : c ≤ |F x| := by
        have htri := abs_sub_abs_le_abs_sub (F x₀) (F x)
        rw [abs_sub_comm] at htri
        unfold c at hFx_close ⊢
        linarith
      rw [← sq_abs (F x)]
      exact pow_le_pow_left₀ hc.le hFx_ge 2
    · rw [Set.indicator_of_notMem hx]
      exact sq_nonneg _
  have hpos_ind : 0 < ∫ x, s.indicator (fun _ => c ^ 2) x := by
    rw [integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul,
      show (x₀ + δ / 2) - (x₀ - δ / 2) = δ by ring]
    positivity
  exact hpos_ind.trans_le (integral_mono hint_ind hint_sq hpt)

/-- **Unconditional Small-Aperture All-Profile `gridTentPattern` Suzuki Deficit (`[-3/10, 3/10]`).**
Every nonzero `F ∈ C_c²(ℝ, ℝ)` supported in `[-3/10, 3/10]` induces an explicit grid-scale threshold
`n₀` and an `n`-independent shift threshold `ω₀ > 0` on which every `gridTentPattern` `P_n` (`n ≥ n₀`)
achieves strict linear finite-shift literal Suzuki deficit. -/
theorem exists_gridTentPattern_suzukiDeficit_of_support_le_threeTenths
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, 3 / 10 < |x| → F x = 0) (hne : ∃ x, F x ≠ 0) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
    let P : ℕ → C_c(ℝ, ℝ) := fun n =>
      gridTentPattern G n (-(3 / 10 + 1)) ⌈2 * (3 / 10 + 1) / sourceFactorialWidth (n + 1)⌉₊
    ∃ n₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      (1 / 10000) * (∫ x, F x ^ 2) ≤ compactFullWeilEnergy (P n) ∧
      ω * ((1 / 20000) * ∫ x, F x ^ 2) <
        autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
      suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hsq_pos : 0 < ∫ x, F x ^ 2 :=
    integral_sq_pos_of_continuous_nonzero hF.continuous hFc hne
  set μ : ℝ := (1 / 10000) * ∫ x, F x ^ 2
  have hμ : 0 < μ := by positivity
  have hge : 2 * μ ≤ compactFullWeilEnergy Fc :=
    (compactFullWeilEnergy_and_gridTent_ge_of_support_le_threeTenths hF hFc hsupp).1
  obtain ⟨Mg, hMg_norm⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨Kg, hKg_lip⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
  have hMg : ∀ x, |Fc x| ≤ Mg := fun x => by rw [← Real.norm_eq_abs]; exact hMg_norm x
  have hKg : ∀ x y, |Fc x - Fc y| ≤ (Kg : ℝ) * |x - y| := fun x y => by
    have := hKg_lip.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hGL := expNegThreeHalves_mul_lipschitz (by norm_num : (0 : ℝ) ≤ 3 / 10) hsupp hMg hKg
  obtain ⟨hP_weil, ω₀, hω₀, hshift⟩ :=
    exists_gridTentPattern_uniform_suzukiDeficit_explicit_scale Fc (by norm_num) hsupp
      hMg hKg hGL hμ hge
  refine ⟨_, ω₀, hω₀, fun n hn ω hω0 hω_lt => ⟨hP_weil n hn, ?_⟩⟩
  obtain ⟨hd, hlt⟩ := hshift n hn ω hω0 hω_lt
  have hhalf : μ / 2 = (1 / 20000) * ∫ x, F x ^ 2 := by unfold μ; ring
  rw [hhalf] at hd
  exact ⟨hd, hlt⟩

/-- **Unconditional Odd-Sector `gridTentPattern` Suzuki Deficit Past `(log 2) / 2` (`[-181/500, 181/500]`).**
Because `(Real.log 2) / 2 < 181 / 500`, the prime `2` actively enters the correlation support. Every
nonzero odd `F ∈ C_c²(ℝ, ℝ)` supported in `[-181/500, 181/500]` induces an explicit grid-scale
threshold `n₀` and an `n`-independent shift threshold `ω₀ > 0` on which every `gridTentPattern` `P_n`
(`n ≥ n₀`) achieves strict linear finite-shift literal Suzuki deficit. -/
theorem exists_gridTentPattern_suzukiDeficit_of_odd_support_le_threeHundredSixtyTwoThousandths
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, 181 / 500 < |x| → F x = 0)
    (hne : ∃ x, F x ≠ 0) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
    let P : ℕ → C_c(ℝ, ℝ) := fun n =>
      gridTentPattern G n (-(181 / 500 + 1)) ⌈2 * (181 / 500 + 1) / sourceFactorialWidth (n + 1)⌉₊
    Real.log 2 / 2 < 181 / 500 ∧
    ∃ n₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      (1 / 2000) * (∫ x, F x ^ 2) ≤ compactFullWeilEnergy (P n) ∧
      ω * ((1 / 4000) * ∫ x, F x ^ 2) <
        autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
      suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hsq_pos : 0 < ∫ x, F x ^ 2 :=
    integral_sq_pos_of_continuous_nonzero hF.continuous hFc hne
  set μ : ℝ := (1 / 2000) * ∫ x, F x ^ 2
  have hμ : 0 < μ := by positivity
  obtain ⟨hlog2, hge, -⟩ :=
    compactFullWeilEnergy_and_gridTent_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
      hF hFc hodd hsupp
  obtain ⟨Mg, hMg_norm⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨Kg, hKg_lip⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
  have hMg : ∀ x, |Fc x| ≤ Mg := fun x => by rw [← Real.norm_eq_abs]; exact hMg_norm x
  have hKg : ∀ x y, |Fc x - Fc y| ≤ (Kg : ℝ) * |x - y| := fun x y => by
    have := hKg_lip.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hGL := expNegThreeHalves_mul_lipschitz (by norm_num : (0 : ℝ) ≤ 181 / 500) hsupp hMg hKg
  obtain ⟨hP_weil, ω₀, hω₀, hshift⟩ :=
    exists_gridTentPattern_uniform_suzukiDeficit_explicit_scale Fc (by norm_num) hsupp
      hMg hKg hGL hμ hge
  refine ⟨hlog2, _, ω₀, hω₀, fun n hn ω hω0 hω_lt => ⟨hP_weil n hn, ?_⟩⟩
  obtain ⟨hd, hlt⟩ := hshift n hn ω hω0 hω_lt
  have hhalf : μ / 2 = (1 / 4000) * ∫ x, F x ^ 2 := by unfold μ; ring
  rw [hhalf] at hd
  exact ⟨hd, hlt⟩

private theorem transfer_criticalTruncatedSource_to_gridTentPattern
    {V γ : ℝ} (hV : criticalTruncationThreshold ≤ V) {S : Finset ℕ} {b : ℕ → ℝ}
    (hγ : 0 < γ) (hb : ∃ k ∈ S, b k ≠ 0)
    (htrunc : (((γ * ∑ k ∈ S, b k ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b) :
    let R : ℝ := Real.log (2 * V)
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedSource V S b x
    let P : ℕ → C_c(ℝ, ℝ) := fun n =>
      gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    0 < R ∧
    ∃ n₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
      (γ / 2) * (∑ k ∈ S, b k ^ 2) ≤ compactFullWeilEnergy (P n) ∧
      ω * ((γ / 4) * ∑ k ∈ S, b k ^ 2) <
        autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
      suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  dsimp only
  have hV_gt1 : 1 < V := lt_of_lt_of_le (by
    unfold criticalTruncationThreshold
    exact lt_of_lt_of_le (by linarith [factorialWindowLength_pos]) (le_max_left _ _)) hV
  have hV0 : 0 < V := by linarith
  set R : ℝ := Real.log (2 * V)
  have hR_pos : 0 < R := Real.log_pos (by linarith)
  set g : C_c(ℝ, ℝ) := criticalTruncatedTest hV0 S b
  have hgR : ∀ x, R < |x| → g x = 0 := fun x hx => by
    refine criticalTruncatedSource_eq_zero hV0 S b fun hmem => ?_
    have habs : |x| ≤ R := abs_le.mpr ⟨hmem.1, hmem.2.trans hR_pos.le⟩
    linarith
  obtain ⟨Mg, hMg_norm⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  have hMg : ∀ x, |g x| ≤ Mg := fun x => by rw [← Real.norm_eq_abs]; exact hMg_norm x
  obtain ⟨Kg, hKg⟩ := exists_lipschitz_criticalTruncatedSource hV0 S b
  have hGL := expNegThreeHalves_mul_lipschitz hR_pos.le hgR hMg hKg
  obtain ⟨k₀, hk₀_mem, hk₀_ne⟩ := hb
  have hsum_pos : 0 < ∑ k ∈ S, b k ^ 2 :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hk₀_ne)
      (Finset.single_le_sum (fun k _ => sq_nonneg (b k)) hk₀_mem)
  set μ : ℝ := (γ / 2) * ∑ k ∈ S, b k ^ 2
  have hμ : 0 < μ := by positivity
  have hge : 2 * μ ≤ compactFullWeilEnergy g := by
    rw [← compactFullWeilEnergy_criticalTruncatedTest hV0 S b] at htrunc
    have hreal : γ * ∑ k ∈ S, b k ^ 2 ≤ compactFullWeilEnergy g := EReal.coe_le_coe_iff.mp htrunc
    unfold μ; linarith
  obtain ⟨hP_weil, ω₀, hω₀, hshift⟩ :=
    exists_gridTentPattern_uniform_suzukiDeficit_explicit_scale g hR_pos.le hgR
      hMg hKg hGL hμ hge
  refine ⟨hR_pos, _, ω₀, hω₀, fun n hn ω hω0 hω_lt => ⟨hP_weil n hn, ?_⟩⟩
  obtain ⟨hd, hlt⟩ := hshift n hn ω hω0 hω_lt
  have hhalf : μ / 2 = (γ / 4) * ∑ k ∈ S, b k ^ 2 := by unfold μ; ring
  rw [hhalf] at hd
  exact ⟨hd, hlt⟩

/-- **Unconditional Unbounded-Aperture `gridTentPattern` Suzuki Deficit on High Dyadic Blocks.**
At every arbitrarily large truncation height `V ≥ criticalTruncationThreshold` (`R = log(2V) → ∞`),
every dyadic block `DyadicScaleBlock S M` (`M ≥ M₀`) and nonzero pattern `b` induce an explicit
grid-scale threshold `n₀` and an `n`-independent shift threshold `ω₀ > 0` on which every
`gridTentPattern` `P_n` (`n ≥ n₀`) achieves strict linear finite-shift literal Suzuki deficit. -/
theorem exists_dyadic_gridTentPattern_suzukiDeficit :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ S : Finset ℕ, DyadicScaleBlock S M →
      ∀ b : ℕ → ℝ, (∃ k ∈ S, b k ≠ 0) → ∀ V : ℝ, criticalTruncationThreshold ≤ V →
        let R : ℝ := Real.log (2 * V)
        let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedSource V S b x
        let P : ℕ → C_c(ℝ, ℝ) := fun n =>
          gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
        0 < R ∧
        ∃ n₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
          (criticalTruncatedArchLogSlope / 8 * Real.log M) * (∑ k ∈ S, b k ^ 2) ≤
            compactFullWeilEnergy (P n) ∧
          ω * ((criticalTruncatedArchLogSlope / 16 * Real.log M) * ∑ k ∈ S, b k ^ 2) <
            autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
          suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set Kt := s * criticalTruncatedArchLogOffset + criticalTruncatedChannelConstant
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((hlog.eventually_gt_atTop (4 * Kt / s)).and (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM S hS b hb V hV => ?_⟩
  dsimp only
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  set γ := s / 4 * Real.log M
  have hγ : 0 < γ := by positivity
  have hKt_lt : Kt < s / 4 * Real.log M := by
    have := (div_lt_iff₀ hs).mp hlogM
    linarith
  have hgap : γ ≤ s * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedChannelConstant := by
    unfold γ Kt at *; nlinarith
  have hE : 0 ≤ ∑ k ∈ S, b k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htrunc : (((γ * ∑ k ∈ S, b k ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b :=
    (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
      (criticalTruncatedCompleteEnergy_ge S b hM2 hS hV)
  obtain ⟨hR, n₀, ω₀, hω₀, hres⟩ :=
    transfer_criticalTruncatedSource_to_gridTentPattern hV hγ hb htrunc
  refine ⟨hR, n₀, ω₀, hω₀, fun n hn ω hω0 hω_lt => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hres n hn ω hω0 hω_lt
  have hg2 : γ / 2 = s / 8 * Real.log M := by unfold γ; ring
  have hg4 : γ / 4 = s / 16 * Real.log M := by unfold γ; ring
  rw [hg2] at h1
  rw [hg4] at h2
  exact ⟨h1, h2, h3⟩

/-- **Unconditional Unbounded-Aperture `gridTentPattern` Suzuki Deficit on Polynomial Scale Windows
`[M, L M]`.**
At every arbitrarily large truncation height `V ≥ criticalTruncationThreshold` (`R = log(2V) → ∞`),
every polynomial scale window `ScaleWindow S M L` (`L ≤ M^δ`, `M ≥ M₀`) and nonzero pattern `b`
induce an explicit grid-scale threshold `n₀` and an `n`-independent shift threshold `ω₀ > 0` on which
every `gridTentPattern` `P_n` (`n ≥ n₀`) achieves strict linear finite-shift literal Suzuki deficit. -/
theorem exists_polynomial_window_gridTentPattern_suzukiDeficit :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ k ∈ S, b k ≠ 0) →
        ∀ V : ℝ, criticalTruncationThreshold ≤ V →
          let R : ℝ := Real.log (2 * V)
          let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedSource V S b x
          let P : ℕ → C_c(ℝ, ℝ) := fun n =>
            gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
          0 < R ∧
          ∃ n₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
            (criticalTruncatedArchLogSlope / 8 * Real.log M) * (∑ k ∈ S, b k ^ 2) ≤
              compactFullWeilEnergy (P n) ∧
            ω * ((criticalTruncatedArchLogSlope / 16 * Real.log M) * ∑ k ∈ S, b k ^ 2) <
              autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
            suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set W := criticalTruncatedWindowPrimeSlope
  have hW : 0 ≤ W := criticalTruncatedWindowPrimeSlope_nonneg
  set δ := s / (4 * (W + 1))
  have hδ : 0 < δ := by positivity
  set Kt := s * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant + 6 * W
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((hlog.eventually_gt_atTop (4 * Kt / s)).and (eventually_ge_atTop 2))
  refine ⟨δ, hδ, M₀, fun M hM L hL hLM S hS b hb V hV => ?_⟩
  dsimp only
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ δ * Real.log M := by
    have := Real.log_le_log hL0 hLM
    rwa [Real.log_rpow hMpos] at this
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hWlogL : 2 * W * Real.log L ≤ s / 2 * Real.log M := by
    calc 2 * W * Real.log L ≤ 2 * W * (δ * Real.log M) := by gcongr
      _ = s / 2 * Real.log M * (W / (W + 1)) := by unfold δ; field_simp; ring
      _ ≤ s / 2 * Real.log M * 1 := by gcongr; rw [div_le_one (by linarith)]; linarith
      _ = s / 2 * Real.log M := by ring
  set γ := s / 4 * Real.log M
  have hγ : 0 < γ := by positivity
  have hKt_lt : Kt < s / 4 * Real.log M := by
    have := (div_lt_iff₀ hs).mp hlogM
    linarith
  have hgap : γ ≤ s * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant - 2 * W * (3 + Real.log L) := by
    unfold γ Kt at *; nlinarith
  have hE : 0 ≤ ∑ k ∈ S, b k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htrunc : (((γ * ∑ k ∈ S, b k ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b :=
    (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
      (criticalTruncatedCompleteEnergy_ge_of_window S b hM2 hL hS hV)
  obtain ⟨hR, n₀, ω₀, hω₀, hres⟩ :=
    transfer_criticalTruncatedSource_to_gridTentPattern hV hγ hb htrunc
  refine ⟨hR, n₀, ω₀, hω₀, fun n hn ω hω0 hω_lt => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hres n hn ω hω0 hω_lt
  have hg2 : γ / 2 = s / 8 * Real.log M := by unfold γ; ring
  have hg4 : γ / 4 = s / 16 * Real.log M := by unfold γ; ring
  rw [hg2] at h1
  rw [hg4] at h2
  exact ⟨h1, h2, h3⟩

/-- **Unconditional Unbounded-Aperture `gridTentPattern` Suzuki Deficit Across Arbitrary-Depth
Lacunary Block Unions.**
At every arbitrarily large truncation height `V ≥ criticalTruncationThreshold` (`R = log(2V) → ∞`),
every arbitrary-depth lacunary block family `IsLacunaryBlockFamily J M S` (`M₀ ≤ M 0`) and nonzero
pattern `b` induce an explicit grid-scale threshold `n₀` and an `n`-independent shift threshold
`ω₀ > 0` on which every `gridTentPattern` `P_n` (`n ≥ n₀`) achieves strict linear finite-shift
literal Suzuki deficit. -/
theorem exists_lacunary_gridTentPattern_suzukiDeficit :
    ∃ M₀ : ℕ, ∀ (J : ℕ) (M : ℕ → ℕ) (S : ℕ → Finset ℕ), IsLacunaryBlockFamily J M S →
      M₀ ≤ M 0 → ∀ b : ℕ → ℝ, (∃ k ∈ (Finset.range J).biUnion S, b k ≠ 0) →
        ∀ V : ℝ, criticalTruncationThreshold ≤ V →
          let T := (Finset.range J).biUnion S
          let R : ℝ := Real.log (2 * V)
          let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedSource V T b x
          let P : ℕ → C_c(ℝ, ℝ) := fun n =>
            gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
          0 < R ∧
          ∃ n₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ n ≥ n₀, ∀ ω : ℝ, 0 < ω → ω < ω₀ →
            (criticalTruncatedArchLogSlope / 8 * Real.log (M 0)) * (∑ k ∈ T, b k ^ 2) ≤
              compactFullWeilEnergy (P n) ∧
            ω * ((criticalTruncatedArchLogSlope / 16 * Real.log (M 0)) * ∑ k ∈ T, b k ^ 2) <
              autocorr (P n) 0 - suzukiCriticalSourcePairing (P n) ω ∧
            suzukiCriticalSourcePairing (P n) ω < autocorr (P n) 0 := by
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set Kt := s * criticalTruncatedArchLogOffset + lacunaryChannelConstant
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop (4 * Kt / s))
  refine ⟨M₀, fun J M S h hM b hb V hV => ?_⟩
  dsimp only
  set T := (Finset.range J).biUnion S
  have hlogM := hM₀ (M 0) hM
  have hM3 : 3 ≤ M 0 := h.1
  have hlogM_pos : 0 < Real.log (M 0) := Real.log_pos (by exact_mod_cast (show 1 < M 0 by omega))
  set γ := s / 4 * Real.log (M 0)
  have hγ : 0 < γ := by positivity
  have hKt_lt : Kt < s / 4 * Real.log (M 0) := by
    have := (div_lt_iff₀ hs).mp hlogM
    linarith
  have hgap : γ ≤ s * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
      lacunaryChannelConstant := by
    unfold γ Kt at *; nlinarith
  have hE : 0 ≤ ∑ k ∈ T, b k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htrunc : (((γ * ∑ k ∈ T, b k ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V T b :=
    (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
      (criticalTruncatedCompleteEnergy_ge_of_lacunary h b hV)
  obtain ⟨hR, n₀, ω₀, hω₀, hres⟩ :=
    transfer_criticalTruncatedSource_to_gridTentPattern hV hγ hb htrunc
  refine ⟨hR, n₀, ω₀, hω₀, fun n hn ω hω0 hω_lt => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hres n hn ω hω0 hω_lt
  have hg2 : γ / 2 = s / 8 * Real.log (M 0) := by unfold γ; ring
  have hg4 : γ / 4 = s / 16 * Real.log (M 0) := by unfold γ; ring
  rw [hg2] at h1
  rw [hg4] at h2
  exact ⟨h1, h2, h3⟩

end
end RHTower
