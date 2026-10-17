import GaloisForLFunctions.BiScaleUncertainty.HyperbolicGaugeMeanSquareChebyshevWeilSynthesis
import GaloisForLFunctions.BiScaleUncertainty.ExplicitNyquistPolarAndChebyshevFactorialProducer

/-!
# Pillar XXX: Unconditional Chebyshev Nyquist-Cell, Coprime Stencil & Prime-Free Archimedean Weil Producers

This module develops **Pillar XXX** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**,
completing the transition from **receiver-side** explicit-formula rewritings to **100% explicit,
unconditional producers**:

1. **General Multi-Scale & Coprime `(2, 3)` Chebyshev–Nyman–Beurling Factorial Producers (§1):**
   - For any finite dilation stencil `(s : Finset ℕ, c : ℕ → ℝ)`, we prove the exact algebraic
     decomposition (`generalChebyshevStencilProducer_eq`) of
     $$\mathcal{P}_{s,c}(N) := \sum_{a \in s} c_a\,\operatorname{floorSummatory}\;\operatorname{chebyshevPsi}\;(a N)$$
     into the double-pole moment $\bigl(\sum_{a \in s} c_a a\bigr)(N\log N - N)$, the polar-slope
     moment $\bigl(\sum_{a \in s} c_a a\log a\bigr)N$, and the Stirling residual sum
     $\sum_{a \in s} c_a\,\operatorname{stirlingResidual}(a N)$.
   - For any bi-null stencil, both the $N\log N$ and $N$ main terms cancel identically without
     introducing Dirichlet's divisor summatory $D(N)$, yielding the unconditional $O(\log N)$ bound
     `abs_generalBiNullChebyshevProducer_le`.
   - Instantiating the **Coprime `(2, 3)` Chebyshev–Nyman–Beurling Producer**
     $$\operatorname{coprimeTwoThreeChebyshevProducer}(N) := T(6N) - 2T(3N) - 3T(2N) + 6T(N)$$
     (corresponding to $(1 - 2\cdot 2^{-s})(1 - 3\cdot 3^{-s})$ on the coprime primes $2$ and $3$)
     gives the unconditional $O(\log N)$ bound
     $$\bigl|\operatorname{coprimeTwoThreeChebyshevProducer}(N)\bigr| \;\le\; 12\log(6N + 1) + 2.$$

2. **Unconditional Chebyshev Nyquist-Cell & Hyperbolic-Gauge Producers (§2):**
   - Using `Chebyshev.psi_le_const_mul_self` and `Chebyshev.psi_nonneg`, we define the explicit
     producer constant `chebyshevProducerSlope := Real.log 4 + 3` and prove unconditionally:
     - `|Chebyshev.psi x - x| ≤ chebyshevProducerSlope * x` for all `x ≥ 0`,
     - `|normalizedLogError t| ≤ chebyshevProducerSlope * Real.exp (t / 2)` for all `t : ℝ`,
     - `normalizedLogError (cutoff N) ^ 2 ≤ chebyshevProducerSlope ^ 2 * (N + 2)` for all `N : ℕ`.
   - Combining this with `le_cellCenter` and `cellCenter_le` on each Nyquist cell
     `[log n, log(n+1))` (`n ≥ 1`), we prove the **Universal Single-Cell Chebyshev Producer Bound**:
     $$\bigl|\operatorname{Chebyshev.psi}(n) - \operatorname{cellCenter}(n)\bigr| \;\le\; \operatorname{chebyshevProducerSlope}\cdot n,
       \qquad \frac{(\operatorname{Chebyshev.psi}(n) - \operatorname{cellCenter}(n))^2}{n(n+1)} \;\le\; \operatorname{chebyshevProducerSlope}^2,$$
     and the **Unconditional Discrete & Continuous Chebyshev Mean-Square Producer Bounds**:
     $$\operatorname{discreteChebyshevCellSum}(N) \;\le\; \operatorname{chebyshevProducerSlope}^2 (N + 1),$$
     $$\int_0^{\operatorname{cutoff}(N)} \operatorname{normalizedLogError}(t)^2\,dt \;\le\; \operatorname{chebyshevProducerSlope}^2 (N + 1) + 2.$$

3. **Unconditional Prime-Free Archimedean Packet & Full Weil Functional Producers (§3–§4):**
   - Up through Pillar XXVIII, the full Weil functional bounds still retained `chebyshevWork`,
     `normalizedLogError`, and `discreteChebyshevCellSum` on the bound side.
   - Using `SignedPrimePolar.pairing_sq_le_packetEnergy` (`pairing² ≤ autocorr f 0 * packetEnergy`)
     together with our unconditional Nyquist-cell Chebyshev producer bounds, we eliminate
     `chebyshevWork`, `normalizedLogError`, `discreteChebyshevCellSum`, and `Chebyshev.psi`
     **completely**, defining the purely archimedean functional
     `archimedeanPacketProducerBound f N` and proving 100% unconditional, prime-free archimedean
     bounds on `packetEnergy f N`, `|pairing N (autocorr f)|`, and
     `(weilFullFunctional Λ (weilTest f f)).re` across `RealWeilTestFn`, `RealEvenPolarTestFn`,
     `RealSmoothEvenPolarTestFn`, `RealOddTestFn`, and `RealHyperplaneGenerator`.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. General Multi-Scale & Coprime `(2, 3)` Chebyshev–Nyman–Beurling Factorial Producers -/

/-- **General Multi-Scale Chebyshev–Nyman–Beurling Factorial Producer:**
For a finite dilation support `s : Finset ℕ` and weights `c : ℕ → ℝ`,
`generalChebyshevStencilProducer s c N := ∑ a ∈ s, c a * floorSummatory chebyshevPsi (a * N)`. -/
def generalChebyshevStencilProducer (s : Finset ℕ) (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ s, c a * floorSummatory chebyshevPsi (a * N)

/-- **Single-Dilation Chebyshev Floor Summatory Decomposition:**
For any `a ≥ 1` and `N ≥ 1`,
`floorSummatory chebyshevPsi (a * N) = a * (N * log N - N) + (a * log a) * N + stirlingResidual (a * N)`. -/
theorem floorSummatory_chebyshevPsi_mul_eq {a N : ℕ} (ha : 1 ≤ a) (hN : 1 ≤ N) :
    floorSummatory chebyshevPsi (a * N) =
      (a : ℝ) * ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ)) +
        ((a : ℝ) * Real.log (a : ℝ)) * (N : ℝ) +
        stirlingResidual (a * N) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual (a * N)]
  push_cast
  rw [Real.log_mul ha0.ne' hN0.ne']
  ring

/-- **Exact Pole-Slope-Stirling Decomposition of `generalChebyshevStencilProducer`:**
For any finite dilation set `s : Finset ℕ` with `∀ a ∈ s, 1 ≤ a` and any `N ≥ 1`,
`generalChebyshevStencilProducer s c N = (∑ a ∈ s, c a * a) * (N log N - N) + (∑ a ∈ s, c a * a * log a) * N + ∑ a ∈ s, c a * stirlingResidual (a * N)`. -/
theorem generalChebyshevStencilProducer_eq (s : Finset ℕ) (c : ℕ → ℝ) {N : ℕ}
    (hs : ∀ a ∈ s, 1 ≤ a) (hN : 1 ≤ N) :
    generalChebyshevStencilProducer s c N =
      (∑ a ∈ s, c a * (a : ℝ)) * ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ)) +
        (∑ a ∈ s, c a * (a : ℝ) * Real.log (a : ℝ)) * (N : ℝ) +
        ∑ a ∈ s, c a * stirlingResidual (a * N) := by
  unfold generalChebyshevStencilProducer
  have hterm : ∀ a ∈ s,
      c a * floorSummatory chebyshevPsi (a * N) =
        (c a * (a : ℝ)) * ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ)) +
          (c a * (a : ℝ) * Real.log (a : ℝ)) * (N : ℝ) +
          c a * stirlingResidual (a * N) := by
    intro a ha
    rw [floorSummatory_chebyshevPsi_mul_eq (hs a ha) hN]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul]

/-- **Unconditional `O(log N)` Bound for Any Bi-Null Chebyshev Stencil Producer:**
If `∑ a ∈ s, c a * a = 0` (double-pole cancellation) and `∑ a ∈ s, c a * a * log a = 0`
(simple-pole slope cancellation), then for every `N ≥ 1`,
`|generalChebyshevStencilProducer s c N| ≤ ∑ a ∈ s, |c a| * (log(a * N + 1) + 1)`. -/
theorem abs_generalBiNullChebyshevProducer_le (s : Finset ℕ) (c : ℕ → ℝ) {N : ℕ}
    (hs : ∀ a ∈ s, 1 ≤ a)
    (hpole : ∑ a ∈ s, c a * (a : ℝ) = 0)
    (hslope : ∑ a ∈ s, c a * (a : ℝ) * Real.log (a : ℝ) = 0)
    (hN : 1 ≤ N) :
    |generalChebyshevStencilProducer s c N| ≤
      ∑ a ∈ s, |c a| * (Real.log ((a : ℝ) * (N : ℝ) + 1) + 1) := by
  rw [generalChebyshevStencilProducer_eq s c hs hN, hpole, hslope, zero_mul, zero_mul,
    add_zero, zero_add]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun a ha => ?_
  rw [abs_mul]
  have ha1 : 1 ≤ a := hs a ha
  have haN1 : 1 ≤ a * N := Nat.mul_pos ha1 hN
  obtain ⟨hlo, hup⟩ := stirlingResidual_bounds haN1
  push_cast at hup
  have habs_stirling : |stirlingResidual (a * N)| ≤ Real.log ((a : ℝ) * (N : ℝ) + 1) + 1 := by
    rw [abs_of_pos (by linarith)]
    exact hup
  exact mul_le_mul_of_nonneg_left habs_stirling (abs_nonneg _)

/-- **Coprime `(2, 3)` Chebyshev–Nyman–Beurling Producer:**
`coprimeTwoThreeChebyshevProducer N := T(6N) - 2 T(3N) - 3 T(2N) + 6 T(N)`.
In Mellin space this applies the product `(1 - 2 · 2^{-s})(1 - 3 · 3^{-s})` across the coprime
primes `2` and `3`, annihilating both the double pole `N log N` and the simple pole `N` at `s = 1`. -/
def coprimeTwoThreeChebyshevProducer (N : ℕ) : ℝ :=
  floorSummatory chebyshevPsi (6 * N) - 2 * floorSummatory chebyshevPsi (3 * N) -
    3 * floorSummatory chebyshevPsi (2 * N) + 6 * floorSummatory chebyshevPsi N

/-- **Exact Reduction of `coprimeTwoThreeChebyshevProducer` to `chebyshevAlternatingProducer`:**
`coprimeTwoThreeChebyshevProducer N = chebyshevAlternatingProducer (3 * N) - 3 * chebyshevAlternatingProducer N`. -/
theorem coprimeTwoThreeChebyshevProducer_eq_alternating_diff (N : ℕ) :
    coprimeTwoThreeChebyshevProducer N =
      chebyshevAlternatingProducer (3 * N) - 3 * chebyshevAlternatingProducer N := by
  unfold coprimeTwoThreeChebyshevProducer chebyshevAlternatingProducer
  rw [show 2 * (3 * N) = 6 * N by ring]
  ring

/-- **Exact Cancellation of Both `N log N` and `N` Main Terms in `coprimeTwoThreeChebyshevProducer`:**
For every `N ≥ 1`,
`coprimeTwoThreeChebyshevProducer N = stirlingResidual (6 * N) - 2 * stirlingResidual (3 * N) - 3 * stirlingResidual (2 * N) + 6 * stirlingResidual N`. -/
theorem coprimeTwoThreeChebyshevProducer_eq_stirling_comb {N : ℕ} (hN : 1 ≤ N) :
    coprimeTwoThreeChebyshevProducer N =
      stirlingResidual (6 * N) - 2 * stirlingResidual (3 * N) -
        3 * stirlingResidual (2 * N) + 6 * stirlingResidual N := by
  rw [coprimeTwoThreeChebyshevProducer_eq_alternating_diff,
    chebyshevAlternatingProducer_eq_linear_add_stirling (by omega : 1 ≤ 3 * N),
    chebyshevAlternatingProducer_eq_linear_add_stirling hN]
  rw [show 2 * (3 * N) = 6 * N by ring]
  push_cast
  ring

/-- **Unconditional `O(log N)` Bound for the Coprime `(2, 3)` Chebyshev Producer:**
For every `N ≥ 1`,
`|coprimeTwoThreeChebyshevProducer N| ≤ 12 * log(6N + 1) + 2`. -/
theorem abs_coprimeTwoThreeChebyshevProducer_le {N : ℕ} (hN : 1 ≤ N) :
    |coprimeTwoThreeChebyshevProducer N| ≤ 12 * Real.log (6 * (N : ℝ) + 1) + 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo6, hup6⟩ := stirlingResidual_bounds (by omega : 1 ≤ 6 * N)
  obtain ⟨hlo3, hup3⟩ := stirlingResidual_bounds (by omega : 1 ≤ 3 * N)
  obtain ⟨hlo2, hup2⟩ := stirlingResidual_bounds (by omega : 1 ≤ 2 * N)
  obtain ⟨hlo1, hup1⟩ := stirlingResidual_bounds hN
  push_cast at hlo6 hup6 hlo3 hup3 hlo2 hup2
  have hlog16 : Real.log ((N : ℝ) + 1) ≤ Real.log (6 * (N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog26 : Real.log (2 * (N : ℝ) + 1) ≤ Real.log (6 * (N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog36 : Real.log (3 * (N : ℝ) + 1) ≤ Real.log (6 * (N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog6_nonneg : 0 ≤ Real.log (6 * (N : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  rw [coprimeTwoThreeChebyshevProducer_eq_stirling_comb hN, abs_le]
  constructor <;> linarith

/-! ## §2. Unconditional Chebyshev Nyquist-Cell & Hyperbolic-Gauge Producers -/

/-- **Universal Chebyshev Producer Slope Constant:**
`chebyshevProducerSlope := log 4 + 3`.
Since `0 ≤ ψ(x) ≤ (log 4 + 4) x` (`Chebyshev.psi_le_const_mul_self`), `|ψ(x) - x|` and
`|ψ(n) - cellCenter n|` are unconditionally bounded by `chebyshevProducerSlope * x` and
`chebyshevProducerSlope * n`. -/
def chebyshevProducerSlope : ℝ := Real.log 4 + 3

theorem three_le_chebyshevProducerSlope : 3 ≤ chebyshevProducerSlope := by
  unfold chebyshevProducerSlope
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

theorem chebyshevProducerSlope_pos : 0 < chebyshevProducerSlope :=
  lt_of_lt_of_le (by norm_num) three_le_chebyshevProducerSlope

/-- **Unconditional Pointwise Chebyshev Error Producer Bound:**
For every `x ≥ 0`,
`|Chebyshev.psi x - x| ≤ chebyshevProducerSlope * x`. -/
theorem abs_chebyshev_psi_sub_self_le {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ chebyshevProducerSlope * x := by
  have h0 : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  have hup : Chebyshev.psi x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold chebyshevProducerSlope
  rw [abs_le]
  constructor
  · nlinarith
  · linarith

/-- **Unconditional Pointwise `logError` Producer Bound:**
For every `t : ℝ`,
`|SignedPrimePolar.logError t| ≤ chebyshevProducerSlope * Real.exp t`. -/
theorem abs_logError_le_exp (t : ℝ) :
    |SignedPrimePolar.logError t| ≤ chebyshevProducerSlope * Real.exp t := by
  unfold SignedPrimePolar.logError
  exact abs_chebyshev_psi_sub_self_le (Real.exp_pos t).le

/-- **Unconditional Pointwise `normalizedLogError` Producer Bound:**
For every `t : ℝ`,
`|normalizedLogError t| ≤ chebyshevProducerSlope * Real.exp (t / 2)`. -/
theorem abs_normalizedLogError_le_exp_half (t : ℝ) :
    |ChebyshevGauge.normalizedLogError t| ≤ chebyshevProducerSlope * Real.exp (t / 2) := by
  unfold ChebyshevGauge.normalizedLogError
  rw [abs_mul, abs_of_pos (Real.exp_pos (-t / 2))]
  have h := mul_le_mul_of_nonneg_left (abs_logError_le_exp t) (Real.exp_pos (-t / 2)).le
  have hexp : Real.exp (-t / 2) * (chebyshevProducerSlope * Real.exp t) =
      chebyshevProducerSlope * Real.exp (t / 2) := by
    calc Real.exp (-t / 2) * (chebyshevProducerSlope * Real.exp t)
        = chebyshevProducerSlope * (Real.exp (-t / 2) * Real.exp t) := by ring
      _ = chebyshevProducerSlope * Real.exp (-t / 2 + t) := by rw [← Real.exp_add]
      _ = chebyshevProducerSlope * Real.exp (t / 2) := by congr 2; ring
  linarith

/-- **Unconditional Squared `normalizedLogError` Producer Bound at `cutoff N`:**
For every `N : ℕ`,
`normalizedLogError (cutoff N) ^ 2 ≤ chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)`. -/
theorem normalizedLogError_cutoff_sq_le (N : ℕ) :
    ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2 ≤
      chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2) := by
  have habs := abs_normalizedLogError_le_exp_half (SignedPrimePolar.cutoff N)
  have hnonneg : 0 ≤ chebyshevProducerSlope * Real.exp (SignedPrimePolar.cutoff N / 2) :=
    mul_nonneg chebyshevProducerSlope_pos.le (Real.exp_pos _).le
  have hsq :
      ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2 ≤
        (chebyshevProducerSlope * Real.exp (SignedPrimePolar.cutoff N / 2)) ^ 2 := by
    rw [← sq_abs (ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N))]
    exact sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg hnonneg]; exact habs)
  have hexp_sq :
      Real.exp (SignedPrimePolar.cutoff N / 2) ^ 2 = (N : ℝ) + 2 := by
    calc Real.exp (SignedPrimePolar.cutoff N / 2) ^ 2
        = Real.exp (SignedPrimePolar.cutoff N / 2) *
            Real.exp (SignedPrimePolar.cutoff N / 2) := sq _
      _ = Real.exp (SignedPrimePolar.cutoff N / 2 + SignedPrimePolar.cutoff N / 2) :=
          (Real.exp_add _ _).symm
      _ = Real.exp (SignedPrimePolar.cutoff N) := by rw [add_halves]
      _ = (N : ℝ) + 2 := exp_cutoff_eq N
  calc ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2
      ≤ chebyshevProducerSlope ^ 2 * Real.exp (SignedPrimePolar.cutoff N / 2) ^ 2 := by
          linarith [show (chebyshevProducerSlope * Real.exp (SignedPrimePolar.cutoff N / 2)) ^ 2 =
            chebyshevProducerSlope ^ 2 * Real.exp (SignedPrimePolar.cutoff N / 2) ^ 2 by ring]
    _ = chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2) := by rw [hexp_sq]

/-- **Unconditional Single-Cell Centered Chebyshev Producer Bound:**
For every Nyquist cell `[log n, log(n+1))` (`n ≥ 1`),
`|Chebyshev.psi (n : ℝ) - cellCenter n| ≤ chebyshevProducerSlope * (n : ℝ)`. -/
theorem abs_chebyshev_psi_sub_cellCenter_le {n : ℕ} (hn : 1 ≤ n) :
    |Chebyshev.psi (n : ℝ) - ChebyshevGauge.cellCenter n| ≤
      chebyshevProducerSlope * (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hpsi_nonneg : 0 ≤ Chebyshev.psi (n : ℝ) := Chebyshev.psi_nonneg (n : ℝ)
  have hpsi_le : Chebyshev.psi (n : ℝ) ≤ (Real.log 4 + 4) * (n : ℝ) :=
    Chebyshev.psi_le_const_mul_self hn0
  have hcenter_lo : (n : ℝ) ≤ ChebyshevGauge.cellCenter n :=
    ChebyshevGauge.le_cellCenter hn
  have hcenter_hi : ChebyshevGauge.cellCenter n ≤ (n : ℝ) + 1 :=
    ChebyshevGauge.cellCenter_le hn
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold chebyshevProducerSlope
  rw [abs_le]
  constructor
  · nlinarith
  · linarith

/-- **Universal Single-Cell Normalized Chebyshev Quadratic Producer Bound:**
On every Nyquist cell `n ≥ 1`, the critical-line weighted squared Chebyshev residual is
unconditionally bounded by the universal constant `chebyshevProducerSlope ^ 2`:
`(Chebyshev.psi n - cellCenter n)² / (n * (n + 1)) ≤ chebyshevProducerSlope ^ 2`. -/
theorem nyquist_cell_chebyshev_term_le {n : ℕ} (hn : 1 ≤ n) :
    (Chebyshev.psi (n : ℝ) - ChebyshevGauge.cellCenter n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤
      chebyshevProducerSlope ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have habs := abs_chebyshev_psi_sub_cellCenter_le hn
  have hnonneg : 0 ≤ chebyshevProducerSlope * (n : ℝ) :=
    mul_nonneg chebyshevProducerSlope_pos.le hn0.le
  have hsq :
      (Chebyshev.psi (n : ℝ) - ChebyshevGauge.cellCenter n) ^ 2 ≤
        (chebyshevProducerSlope * (n : ℝ)) ^ 2 := by
    rw [← sq_abs (Chebyshev.psi (n : ℝ) - ChebyshevGauge.cellCenter n)]
    exact sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg hnonneg]; exact habs)
  rw [div_le_iff₀ (by positivity)]
  calc (Chebyshev.psi (n : ℝ) - ChebyshevGauge.cellCenter n) ^ 2
      ≤ chebyshevProducerSlope ^ 2 * (n : ℝ) ^ 2 := by
          linarith [show (chebyshevProducerSlope * (n : ℝ)) ^ 2 =
            chebyshevProducerSlope ^ 2 * (n : ℝ) ^ 2 by ring]
    _ ≤ chebyshevProducerSlope ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          nlinarith

/-- **Unconditional Discrete Chebyshev Cell Sum Producer Bound:**
For every `N : ℕ`,
`discreteChebyshevCellSum N ≤ chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1)`. -/
theorem discreteChebyshevCellSum_le (N : ℕ) :
    discreteChebyshevCellSum N ≤ chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) := by
  unfold discreteChebyshevCellSum
  calc (∑ k ∈ Finset.range (N + 1),
          (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ChebyshevGauge.cellCenter (k + 1)) ^ 2 /
            (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)))
      ≤ ∑ _ ∈ Finset.range (N + 1), chebyshevProducerSlope ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact nyquist_cell_chebyshev_term_le (by omega : 1 ≤ k + 1)
    _ = ((Finset.range (N + 1)).card : ℝ) * chebyshevProducerSlope ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) := by
          rw [Finset.card_range]
          push_cast
          ring

/-- **Unconditional Continuous Mean-Square Chebyshev Producer Bound at `cutoff N`:**
For every `N : ℕ`,
`∫_{t ∈ [0, cutoff N]} normalizedLogError(t)² dt ≤ chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2`. -/
theorem integral_normalizedLogError_sq_cutoff_le (N : ℕ) :
    (∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2) ≤
      chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2 := by
  have h1 := (sum_center_sq_le_integral_cutoff_le N).2
  have h2 := discreteChebyshevCellSum_le N
  linarith

/-! ## §3. Unconditional Prime-Free Archimedean Packet & Pairing Producer Bounds -/

/-- **Explicit Prime-Free Archimedean Packet Producer Bound:**
Bounds `packetEnergy f N` purely in terms of `autocorr f 0`, the `L¹` norm of the hyperbolic gauge
derivative `f' - f/2`, and the cutoff scale `N`, with **zero** occurrences of `Λ`, `ψ`,
`normalizedLogError`, or `discreteChebyshevCellSum`:
$$\operatorname{archimedeanPacketProducerBound}(f, N)
  := 3\bigl(10 + \operatorname{chebyshevProducerSlope}^2 (N + 2)\bigr)\,\operatorname{autocorr}(f, 0)
    + 3\left(\int_{\mathbb{R}} |f'(u) - f(u)/2|\,du\right)^2
      \bigl(\operatorname{chebyshevProducerSlope}^2 (N + 1) + 2\bigr).$$ -/
def archimedeanPacketProducerBound (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  3 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) * autocorr f 0 +
  3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
    (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2)

theorem archimedeanPacketProducerBound_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) :
    0 ≤ archimedeanPacketProducerBound f N := by
  unfold archimedeanPacketProducerBound
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  positivity

/-- **Unconditional Domination of `discreteCellGaugeBound` by `archimedeanPacketProducerBound`:**
For every `f : C_c(ℝ, ℝ)` and `N : ℕ`,
`discreteCellGaugeBound f N ≤ archimedeanPacketProducerBound f N`. -/
theorem discreteCellGaugeBound_le_archimedeanPacketProducerBound (f : C_c(ℝ, ℝ)) (N : ℕ) :
    discreteCellGaugeBound f N ≤ archimedeanPacketProducerBound f N := by
  unfold discreteCellGaugeBound archimedeanPacketProducerBound
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hcut := normalizedLogError_cutoff_sq_le N
  have hcell := discreteChebyshevCellSum_le N
  have h1 :
      3 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
          autocorr f 0 ≤
        3 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) * autocorr f 0 := by
    nlinarith
  have h2 :
      3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (discreteChebyshevCellSum N + 2) ≤
        3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **Unconditional Prime-Free Archimedean Producer Bound on `packetEnergy`:**
For every `C¹` compactly supported source `f` and every `N : ℕ`,
`packetEnergy f N ≤ archimedeanPacketProducerBound f N`. -/
theorem packetEnergy_le_archimedeanPacketProducerBound (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤ archimedeanPacketProducerBound f N :=
  (packetEnergy_le_discreteCellGaugeBound f hf N).trans
    (discreteCellGaugeBound_le_archimedeanPacketProducerBound f N)

/-- **Unconditional Young-Envelope Pairing Bound from `pairing_sq_le_packetEnergy`:**
For every `f : C_c(ℝ, ℝ)`, `N : ℕ`, and `c : ℝ`,
`2 * |SignedPrimePolar.pairing N (autocorr f)| ≤ e^c * autocorr f 0 + e^{-c} * packetEnergy f N`. -/
theorem two_mul_abs_pairing_le_exp_add_packetEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) (c : ℝ) :
    2 * |SignedPrimePolar.pairing N (autocorr f)| ≤
      Real.exp c * autocorr f 0 + Real.exp (-c) * SignedPrimePolar.packetEnergy f N := by
  set P := SignedPrimePolar.pairing N (autocorr f)
  set A := autocorr f 0
  set E := SignedPrimePolar.packetEnergy f N
  have hP2 : P ^ 2 ≤ A * E := SignedPrimePolar.pairing_sq_le_packetEnergy f N
  have hA : 0 ≤ A := autocorr_zero_nonneg f
  have hE : 0 ≤ E := SignedPrimePolar.packetEnergy_nonneg f N
  have he : Real.exp c * Real.exp (-c) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq_abs : |P| ^ 2 = P ^ 2 := sq_abs P
  have hdiff :
      0 ≤ (Real.exp c * A + Real.exp (-c) * E) ^ 2 - (2 * |P|) ^ 2 := by
    have hid :
        (Real.exp c * A + Real.exp (-c) * E) ^ 2 - (2 * |P|) ^ 2 =
          (Real.exp c * A - Real.exp (-c) * E) ^ 2 +
            4 * ((Real.exp c * Real.exp (-c)) * (A * E) - |P| ^ 2) := by ring
    rw [hid, he, one_mul, hsq_abs]
    have hsq_nonneg := sq_nonneg (Real.exp c * A - Real.exp (-c) * E)
    linarith
  have hrhs_nonneg : 0 ≤ Real.exp c * A + Real.exp (-c) * E := by positivity
  have hlhs_nonneg : 0 ≤ 2 * |P| := by positivity
  by_contra hlt
  have hlt' : Real.exp c * A + Real.exp (-c) * E < 2 * |P| := not_le.mp hlt
  nlinarith

/-- **Unconditional Prime-Free Archimedean Producer Bound on `|pairing N (autocorr f)|`:**
For every `C¹` compactly supported source `f`, `N : ℕ`, and `c : ℝ`,
`2 * |SignedPrimePolar.pairing N (autocorr f)| ≤ e^c * autocorr f 0 + e^{-c} * archimedeanPacketProducerBound f N`. -/
theorem two_mul_abs_pairing_le_archimedeanPacketProducerBound (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) (c : ℝ) :
    2 * |SignedPrimePolar.pairing N (autocorr f)| ≤
      Real.exp c * autocorr f 0 + Real.exp (-c) * archimedeanPacketProducerBound f N := by
  refine (two_mul_abs_pairing_le_exp_add_packetEnergy f N c).trans ?_
  refine add_le_add le_rfl ?_
  exact mul_le_mul_of_nonneg_left
    (packetEnergy_le_archimedeanPacketProducerBound f hf N) (Real.exp_pos (-c)).le

/-! ## §4. Unconditional Prime-Free Archimedean Full Weil Functional Bounds Across All Test Spaces -/

namespace RealWeilTestFn

/-- **Unconditional Prime-Free Archimedean Packet Energy Bound on `RealWeilTestFn`:**
For every `f : RealWeilTestFn` and `N : ℕ` (with **zero hypotheses**!),
`packetEnergy f.toCompactlySupported N ≤ archimedeanPacketProducerBound f.toCompactlySupported N`. -/
theorem packetEnergy_le_archimedeanPacketProducerBound (f : RealWeilTestFn) (N : ℕ) :
    SignedPrimePolar.packetEnergy f.toCompactlySupported N ≤
      BiScaleUncertainty.archimedeanPacketProducerBound f.toCompactlySupported N :=
  BiScaleUncertainty.packetEnergy_le_archimedeanPacketProducerBound
    f.toCompactlySupported f.contDiff_one_source N

/-- **Unconditional Direct Prime-Free Archimedean Full Weil Functional Bound on `RealWeilTestFn`
(`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_bound`):**
For EVERY `f : RealWeilTestFn` and EVERY `c : ℝ` (with **zero hypotheses**, **zero `chebyshevWork`**,
and **zero arithmetic functions** on the bound side!):
$$\Bigl|(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  - \operatorname{poleWeightArchRe}(0, f.1)\Bigr|$$
$$\le\; e^c\,\operatorname{autocorr}(f.\mathrm{source}, 0)
  + e^{-c}\,\operatorname{archimedeanPacketProducerBound}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale}).$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_bound
    (f : RealWeilTestFn) (c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1| ≤
      Real.exp c * autocorr f.source 0 +
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanPacketProducerBound
            f.toCompactlySupported f.supportScale := by
  have hid := f.re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing
  have hsub :
      (weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1 =
      -(2 * SignedPrimePolar.pairing f.supportScale (autocorr f.source)) := by
    linarith only [hid]
  rw [hsub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact BiScaleUncertainty.two_mul_abs_pairing_le_archimedeanPacketProducerBound
    f.toCompactlySupported f.contDiff_one_source f.supportScale c

/-- **Unconditional Direct Prime-Free Archimedean Full Weil Functional Lower Bound on `RealWeilTestFn`
(`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound`):**
For EVERY `f : RealWeilTestFn` and EVERY `c : ℝ` (with **zero hypotheses**!), the full untruncated
Weil explicit-formula functional of `Λ` is bounded below by a 100% explicit, prime-free archimedean
functional of `f`:
$$\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
  - e^c\,\operatorname{autocorr}(f.\mathrm{source}, 0)
  - e^{-c}\,\operatorname{archimedeanPacketProducerBound}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    (f : RealWeilTestFn) (c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanPacketProducerBound
            f.toCompactlySupported f.supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have habs := f.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_bound c
  have hlow := neg_le_of_abs_le habs
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  linarith only [hlow, hpole]

end RealWeilTestFn

/-- **Unconditional Direct Prime-Free Archimedean Full Weil Functional Lower Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `c : ℝ` (with **zero hypotheses**!), -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    (g : RealEvenPolarTestFn) (c : ℝ) :
    biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        Real.exp c * autocorr g.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanPacketProducerBound
            (RealEvenPolarTestFn.toCompactlySupported g)
            (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re :=
  (RealEvenPolarTestFn.toRealWeilTestFn g).unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    c

/-- **Unconditional Direct Prime-Free Archimedean Full Weil Functional Lower Bound on `RealSmoothEvenPolarTestFn`:**
For EVERY `g : RealSmoothEvenPolarTestFn` and EVERY `c : ℝ` (with **zero hypotheses**!), -/
theorem RealSmoothEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    (g : RealSmoothEvenPolarTestFn) (c : ℝ) :
    biScaleLevyEnergy g.toRealEvenPolar.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
        Real.exp c * autocorr g.toRealEvenPolar.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanPacketProducerBound
            (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar)
            (RealEvenPolarTestFn.toRealWeilTestFn g.toRealEvenPolar).supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1.1 g.1.1.1.1)).re :=
  RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    g.toRealEvenPolar c

namespace RealOddTestFn

/-- **Unconditional Direct Prime-Free Archimedean Full Weil Functional Lower Bound on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn` and EVERY `c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    (f : RealOddTestFn) (c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanPacketProducerBound
            f.toCompactlySupported f.toRealWeilTestFn.supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound c

end RealOddTestFn

namespace RealHyperplaneGenerator

/-- **Unconditional Direct Prime-Free Archimedean Full Weil Functional Lower Bound on `RealHyperplaneGenerator`:**
For EVERY `x : RealHyperplaneGenerator` and EVERY `c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    (x : RealHyperplaneGenerator) (c : ℝ) :
    biScaleLevyEnergy (RealHyperplaneGenerator.source x) +
        EF.gammaBracket 0 *
          (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
            (RealHyperplaneGenerator.toRealWeilTestFn x).1.1 0).re -
        Real.exp c * autocorr (RealHyperplaneGenerator.source x) 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanPacketProducerBound
            (RealHyperplaneGenerator.toRealWeilTestFn x).toCompactlySupported
            (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
          (RealHyperplaneGenerator.toRealWeilTestFn x).1.1)).re :=
  (RealHyperplaneGenerator.toRealWeilTestFn x).unconditional_weilFullFunctional_vonMangoldt_archimedeanProducer_lower_bound
    c

end RealHyperplaneGenerator

end

end GaloisForLFunctions.BiScaleUncertainty
