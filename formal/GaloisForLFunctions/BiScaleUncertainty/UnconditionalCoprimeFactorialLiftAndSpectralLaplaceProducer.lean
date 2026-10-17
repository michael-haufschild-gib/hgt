import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialProducer
import GaloisForLFunctions.BiScaleUncertainty.SpectralLaplaceEnergyCriticalLine
import GaloisForLFunctions.BiScaleUncertainty.UnconditionalLaplaceEnergyAndRoughCollarWeilProducer

/-!
# Pillar XXXII: Unconditional Coprime `(2, 3)` Factorial-Lift Producer & Boundary-Free Spectral Laplace Weil Producers

This module develops **Pillar XXXII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**,
unifying the coprime factorial-stencil producer hierarchy with the real-ratio factorial lift and
the critical-line spectral Laplace energy representation:

1. **Unconditional Coprime `(2, 3)` Harmonic Correction & Real-Ratio Factorial-Lift Producer (§1–§2):**
   - For the coprime `(2, 3)` stencil `(1, -2, -3, +6)` at `(6N, 3N, 2N, N)` (corresponding in
     Mellin space to $(1 - 2\cdot 2^{-s})(1 - 3\cdot 3^{-s})$), we define the harmonic second
     difference
     $$\operatorname{coprimeHarmonicCorrection}(N)
       := 6N\bigl(H_{6N} - H_{3N} - H_{2N} + H_N\bigr)$$
     and prove unconditionally that $0 \le \operatorname{coprimeHarmonicCorrection}(N) \le 3$ for
     all $N \ge 1$.
   - Lifting the stencil via `factorialLift` gives the explicit producer test function
     $$\operatorname{factorialCoprimeTwoThree}(N, x)
       := \frac{\operatorname{factorialLift}(6N, x) - 2\operatorname{factorialLift}(3N, x)
         - 3\operatorname{factorialLift}(2N, x) + 6\operatorname{factorialLift}(N, x)}{\sqrt{N}}.$$
   - We prove that `factorialCoprimeTwoThree N` vanishes at $x = 0$, takes the fixed non-zero
     amplitude $\sqrt{6}$ at the top atom $\log(6N)$ (hence cannot be any autocorrelation receiver
     `autocorr f`), is admissible for `fullPairing`, and satisfies the exact identity
     $$\operatorname{fullPairing}\bigl(\operatorname{factorialCoprimeTwoThree} N\bigr)
       = \frac{2\,\operatorname{coprimeTwoThreeChebyshevProducer}(N)
         - \operatorname{coprimeHarmonicCorrection}(N)}{\sqrt{N}}$$
     together with the **unconditional $O(\log N / \sqrt{N})$ bound**:
     $$\bigl|\operatorname{fullPairing}\bigl(\operatorname{factorialCoprimeTwoThree} N\bigr)\bigr|
       \;\le\; \frac{24\log(6N + 1) + 7}{\sqrt{N}}.$$

2. **Boundary-Free Laplace & Spectral Critical-Line Packet and Full Weil Producers (§3–§4):**
   - Combining `CausalCorrelationPacketRepresentation.packetEnergy_le_laplaceEnergy` with
     `SpectralLaplaceEnergyCriticalLine.laplaceEnergy_eq_integral_fourierPairing_sq` and Pillar
     XXXI's `laplaceEnergy_le_laplaceEnergyProducerBound`, we prove:
     - **Unconditional Spectral Critical-Line Mean-Square Producer Bound:**
       $$\int_{\mathbb{R}} \frac{\|\hat{\nu}_N(\xi)\|^2}{1/4 + (2\pi\xi)^2}\,d\xi
         \;\le\; \operatorname{laplaceEnergyProducerBound}(N),$$
     - **Boundary-Free Multiplicative Packet Producer Bound:**
       $$\operatorname{packetEnergy}(f, N)
         \;\le\; \left(\int_{\mathbb{R}} |f'(t) - f(t)/2|\,dt\right)^2
           \operatorname{laplaceEnergyProducerBound}(N),$$
     - **Boundary-Free Collar Packet Producer Bound (for any rough `f : C_c(ℝ, ℝ)`):**
       $$\operatorname{packetEnergy}(\operatorname{collarSource} f a b, N)
         \;\le\; \operatorname{collarGaugeBudget}(f, a, b)\cdot
           \operatorname{laplaceEnergyProducerBound}(N),$$
     eliminating the separate cutoff boundary term `3 * (10 + normalizedLogError (cutoff N)^2)`
     completely and yielding boundary-free full Weil functional lower bounds across all test spaces.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. The Coprime `(2, 3)` Harmonic Correction and Its Unconditional `[0, 3]` Bound -/

/-- Elementary step of `realHarmonic`: `H_{n+1} = H_n + 1/(n+1)`. -/
theorem realHarmonic_succ_eq (n : ℕ) :
    realHarmonic (n + 1) = realHarmonic n + 1 / ((n : ℝ) + 1) := by
  unfold realHarmonic
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  push_cast
  rfl

/-- Elementary reciprocal pair `1/(2x + 1) - 1/(2x + 2)`. -/
def coprimeReciprocalPair (x : ℝ) : ℝ := 1 / (2 * x + 1) - 1 / (2 * x + 2)

/-- Dyadic harmonic increment identity: `H_{2n} - H_n = ∑ k ∈ range n, (1/(2k+1) - 1/(2k+2))`. -/
theorem realHarmonic_two_mul_sub (n : ℕ) :
    realHarmonic (2 * n) - realHarmonic n =
      ∑ k ∈ Finset.range n, coprimeReciprocalPair (k : ℝ) := by
  induction n with
  | zero => simp [realHarmonic]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      realHarmonic_succ_eq (2 * n + 1), realHarmonic_succ_eq (2 * n), realHarmonic_succ_eq n,
      Finset.sum_range_succ]
    push_cast
    unfold coprimeReciprocalPair at ih ⊢
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hcancel : 2 / (2 * (n : ℝ) + 2) = 1 / ((n : ℝ) + 1) := by
      field_simp
    linear_combination ih + hcancel

/-- **The Coprime `(2, 3)` Harmonic Correction:**
`coprimeHarmonicCorrection N := 6N * (H_{6N} - H_{3N} - H_{2N} + H_N)`. -/
def coprimeHarmonicCorrection (N : ℕ) : ℝ :=
  6 * (N : ℝ) *
    (realHarmonic (6 * N) - realHarmonic (3 * N) - realHarmonic (2 * N) + realHarmonic N)

/-- Exact positive-pair representation of `coprimeHarmonicCorrection N`. -/
theorem coprimeHarmonicCorrection_eq_pairs (N : ℕ) :
    coprimeHarmonicCorrection N =
      6 * (N : ℝ) * ∑ k ∈ Finset.range (2 * N), coprimeReciprocalPair ((N : ℝ) + k) := by
  have h1 := realHarmonic_two_mul_sub N
  have h3 := realHarmonic_two_mul_sub (3 * N)
  rw [show 2 * (3 * N) = 6 * N by omega] at h3
  have hs : (∑ k ∈ Finset.range (3 * N), coprimeReciprocalPair (k : ℝ)) =
      (∑ k ∈ Finset.range N, coprimeReciprocalPair (k : ℝ)) +
        ∑ k ∈ Finset.range (2 * N), coprimeReciprocalPair ((N : ℝ) + k) := by
    rw [show 3 * N = N + 2 * N by omega, Finset.sum_range_add]
    push_cast
    rfl
  unfold coprimeHarmonicCorrection
  congr 1
  linear_combination h3 - h1 + hs

theorem coprimeReciprocalPair_bounds {N k : ℕ} (hN : 1 ≤ N) :
    0 ≤ coprimeReciprocalPair ((N : ℝ) + k) ∧
      coprimeReciprocalPair ((N : ℝ) + k) ≤ 1 / (4 * (N : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hden1 : 0 < 2 * ((N : ℝ) + k) + 1 := by positivity
  have hden2 : 0 < 2 * ((N : ℝ) + k) + 2 := by positivity
  have heq : coprimeReciprocalPair ((N : ℝ) + k) =
      1 / ((2 * ((N : ℝ) + k) + 1) * (2 * ((N : ℝ) + k) + 2)) := by
    unfold coprimeReciprocalPair
    field_simp
    ring
  rw [heq]
  constructor
  · positivity
  · apply one_div_le_one_div_of_le (by positivity : 0 < 4 * (N : ℝ) ^ 2)
    nlinarith [sq_nonneg (k : ℝ), mul_nonneg hn.le hk]

/-- **Unconditional `[0, 3]` Bound on `coprimeHarmonicCorrection N`:**
For every `N ≥ 1`, `0 ≤ coprimeHarmonicCorrection N ≤ 3`. -/
theorem coprimeHarmonicCorrection_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ coprimeHarmonicCorrection N ∧ coprimeHarmonicCorrection N ≤ 3 := by
  rw [coprimeHarmonicCorrection_eq_pairs]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => (coprimeReciprocalPair_bounds (k := k) hN).1)
  · have hs : (∑ k ∈ Finset.range (2 * N), coprimeReciprocalPair ((N : ℝ) + k)) ≤
        (2 * (N : ℝ)) * (1 / (4 * (N : ℝ) ^ 2)) := by
      calc (∑ k ∈ Finset.range (2 * N), coprimeReciprocalPair ((N : ℝ) + k))
          ≤ ∑ _k ∈ Finset.range (2 * N), 1 / (4 * (N : ℝ) ^ 2) :=
            Finset.sum_le_sum fun k _ => (coprimeReciprocalPair_bounds (k := k) hN).2
        _ = (2 * (N : ℝ)) * (1 / (4 * (N : ℝ) ^ 2)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    calc 6 * (N : ℝ) * ∑ k ∈ Finset.range (2 * N), coprimeReciprocalPair ((N : ℝ) + k)
        ≤ 6 * (N : ℝ) * ((2 * (N : ℝ)) * (1 / (4 * (N : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 3 := by field_simp; ring

/-! ## §2. The Coprime `(2, 3)` Real-Ratio Factorial-Lift Producer (`factorialCoprimeTwoThree`) -/

/-- **Explicit Coprime `(2, 3)` Real-Ratio Factorial-Lift Producer:**
Applies the `(1, -2, -3, +6)` dilation stencil at `(6N, 3N, 2N, N)` to `factorialLift`, normalized
by `√N`. -/
def factorialCoprimeTwoThree (N : ℕ) (x : ℝ) : ℝ :=
  (factorialLift (6 * N) x - 2 * factorialLift (3 * N) x -
    3 * factorialLift (2 * N) x + 6 * factorialLift N x) / Real.sqrt N

/-- `factorialCoprimeTwoThree N` vanishes at the origin `x = 0`. -/
theorem factorialCoprimeTwoThree_zero (N : ℕ) : factorialCoprimeTwoThree N 0 = 0 := by
  have hz (K : ℕ) : factorialLift K 0 = K := by
    simpa using (factorialLift_at_log (K := K) (n := 1) (by omega))
  unfold factorialCoprimeTwoThree
  rw [hz, hz, hz, hz]
  push_cast
  ring

/-- `factorialCoprimeTwoThree N` has fixed positive amplitude `√6` at the top atom `log(6N)`. -/
theorem factorialCoprimeTwoThree_top {N : ℕ} (hN : 1 ≤ N) :
    factorialCoprimeTwoThree N (Real.log (6 * (N : ℝ))) = Real.sqrt 6 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (6 * (N : ℝ)) = Real.sqrt 6 * Real.sqrt N :=
    Real.sqrt_mul (by norm_num) (N : ℝ)
  have hdiv1 : N / (6 * N) = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv2 : (2 * N) / (6 * N) = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv3 : (3 * N) / (6 * N) = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv6 : (6 * N) / (6 * N) = 1 := Nat.div_self (by omega)
  have hcast : 6 * (N : ℝ) = ((6 * N : ℕ) : ℝ) := by push_cast; rfl
  unfold factorialCoprimeTwoThree
  rw [hcast,
    factorialLift_at_log (by omega : 1 ≤ 6 * N),
    factorialLift_at_log (by omega : 1 ≤ 6 * N),
    factorialLift_at_log (by omega : 1 ≤ 6 * N),
    factorialLift_at_log (by omega : 1 ≤ 6 * N),
    hdiv6, hdiv3, hdiv2, hdiv1]
  push_cast
  rw [hs]
  have hsn : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  field_simp

/-- `factorialCoprimeTwoThree (n + 1)` is a genuine producer, not an autocorrelation receiver. -/
theorem factorialCoprimeTwoThree_ne_autocorr (n : ℕ) (f : C_c(ℝ, ℝ)) :
    factorialCoprimeTwoThree (n + 1) ≠ RHTower.ArchimedeanAnomaly.autocorr f := by
  intro heq
  have hz := congrFun heq 0
  rw [factorialCoprimeTwoThree_zero] at hz
  have ht := congrFun heq (Real.log (6 * ((n + 1 : ℕ) : ℝ)))
  rw [factorialCoprimeTwoThree_top (by omega)] at ht
  have hc := autocorr_eq_zero_of_zero_eq_zero f.hasCompactSupport f.continuous hz.symm
    (Real.log (6 * ((n + 1 : ℕ) : ℝ)))
  have hsqrt6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  linarith

private theorem primeTerm_factorialCoprimeTwoThree (N n : ℕ) :
    primeTerm (factorialCoprimeTwoThree N) n =
      (primeTerm (factorialLift (6 * N)) n - 2 * primeTerm (factorialLift (3 * N)) n -
        3 * primeTerm (factorialLift (2 * N)) n + 6 * primeTerm (factorialLift N) n) /
        Real.sqrt N := by
  unfold primeTerm factorialCoprimeTwoThree
  split_ifs <;> ring

private theorem primeTerm_factorialCoprimeTwoThree_tail (N n : ℕ)
    (hn : n ∉ Finset.Icc 1 (6 * N)) :
    primeTerm (factorialCoprimeTwoThree N) n = 0 := by
  have h3 : n ∉ Finset.Icc 1 (3 * N) := by simp only [Finset.mem_Icc] at *; omega
  have h2 : n ∉ Finset.Icc 1 (2 * N) := by simp only [Finset.mem_Icc] at *; omega
  have h1 : n ∉ Finset.Icc 1 N := by simp only [Finset.mem_Icc] at *; omega
  rw [primeTerm_factorialCoprimeTwoThree,
    primeTerm_factorialLift_tail _ _ hn,
    primeTerm_factorialLift_tail _ _ h3,
    primeTerm_factorialLift_tail _ _ h2,
    primeTerm_factorialLift_tail _ _ h1]
  simp

theorem integrable_polar_factorialCoprimeTwoThree (N : ℕ) :
    Integrable (fun x => polarDensity x * factorialCoprimeTwoThree N x) := by
  have heq : (fun x => polarDensity x * factorialCoprimeTwoThree N x) =
      fun x => ((polarDensity x * factorialLift (6 * N) x) -
        2 * (polarDensity x * factorialLift (3 * N) x) -
        3 * (polarDensity x * factorialLift (2 * N) x) +
        6 * (polarDensity x * factorialLift N x)) / Real.sqrt N := by
    funext x
    unfold factorialCoprimeTwoThree
    ring
  rw [heq]
  exact ((((integrable_polar_factorialLift (6 * N)).sub
    ((integrable_polar_factorialLift (3 * N)).const_mul 2)).sub
    ((integrable_polar_factorialLift (2 * N)).const_mul 3)).add
    ((integrable_polar_factorialLift N).const_mul 6)).div_const _

/-- Full half-line domain admissibility for `factorialCoprimeTwoThree N`. -/
theorem factorialCoprimeTwoThree_admissible (N : ℕ) :
    (Function.support (primeTerm (factorialCoprimeTwoThree N))).Finite ∧
      Summable (fun n => |primeTerm (factorialCoprimeTwoThree N) n|) ∧
      IntegrableOn (fun x => polarDensity x * factorialCoprimeTwoThree N x) (Ici 0) := by
  refine ⟨?_, ?_, (integrable_polar_factorialCoprimeTwoThree N).integrableOn⟩
  · apply (Finset.finite_toSet (Finset.Icc 1 (6 * N))).subset
    intro n hn
    by_contra hout
    exact hn (primeTerm_factorialCoprimeTwoThree_tail N n hout)
  · apply summable_of_ne_finset_zero (s := Finset.Icc 1 (6 * N))
    intro n hn
    rw [primeTerm_factorialCoprimeTwoThree_tail N n hn, abs_zero]

private theorem fullPairing_factorialCoprimeTwoThree_linear (N : ℕ) :
    fullPairing (factorialCoprimeTwoThree N) =
      (fullPairing (factorialLift (6 * N)) - 2 * fullPairing (factorialLift (3 * N)) -
        3 * fullPairing (factorialLift (2 * N)) + 6 * fullPairing (factorialLift N)) /
        Real.sqrt N := by
  have hs (K : ℕ) : Summable (primeTerm (factorialLift K)) :=
    (factorialLift_admissible K).2.1.of_abs
  have hi (K : ℕ) : IntegrableOn (fun x => polarDensity x * factorialLift K x) (Ici 0) :=
    (factorialLift_admissible K).2.2
  have hi3 : IntegrableOn (fun x => 2 * (polarDensity x * factorialLift (3 * N) x)) (Ici 0) :=
    (hi (3 * N)).const_mul 2
  have hi2 : IntegrableOn (fun x => 3 * (polarDensity x * factorialLift (2 * N) x)) (Ici 0) :=
    (hi (2 * N)).const_mul 3
  have hi1 : IntegrableOn (fun x => 6 * (polarDensity x * factorialLift N x)) (Ici 0) :=
    (hi N).const_mul 6
  have hsub1 : IntegrableOn (fun x => polarDensity x * factorialLift (6 * N) x -
      2 * (polarDensity x * factorialLift (3 * N) x)) (Ici 0) := (hi (6 * N)).sub hi3
  have hsub2 : IntegrableOn (fun x => polarDensity x * factorialLift (6 * N) x -
      2 * (polarDensity x * factorialLift (3 * N) x) -
      3 * (polarDensity x * factorialLift (2 * N) x)) (Ici 0) := hsub1.sub hi2
  have hp : (fun x => polarDensity x * factorialCoprimeTwoThree N x) =
      fun x => ((polarDensity x * factorialLift (6 * N) x) -
        2 * (polarDensity x * factorialLift (3 * N) x) -
        3 * (polarDensity x * factorialLift (2 * N) x) +
        6 * (polarDensity x * factorialLift N x)) / Real.sqrt N := by
    funext x
    unfold factorialCoprimeTwoThree
    ring
  have hs_sub1 : Summable (fun n => primeTerm (factorialLift (6 * N)) n -
      2 * primeTerm (factorialLift (3 * N)) n) :=
    (hs (6 * N)).sub ((hs (3 * N)).mul_left 2)
  have hs_sub2 : Summable (fun n => primeTerm (factorialLift (6 * N)) n -
      2 * primeTerm (factorialLift (3 * N)) n -
      3 * primeTerm (factorialLift (2 * N)) n) :=
    hs_sub1.sub ((hs (2 * N)).mul_left 3)
  unfold fullPairing
  simp_rw [primeTerm_factorialCoprimeTwoThree]
  rw [tsum_div_const,
    Summable.tsum_add hs_sub2 ((hs N).mul_left 6),
    Summable.tsum_sub hs_sub1 ((hs (2 * N)).mul_left 3),
    Summable.tsum_sub (hs (6 * N)) ((hs (3 * N)).mul_left 2),
    tsum_mul_left, tsum_mul_left, tsum_mul_left,
    hp, integral_div,
    integral_add hsub2 hi1, integral_sub hsub1 hi2, integral_sub (hi (6 * N)) hi3,
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- **Exact Evaluation of `fullPairing (factorialCoprimeTwoThree N)`:**
Both the `N log N` and `N` poles cancel identically across the coprime primes `2` and `3`, leaving
only `2 * coprimeTwoThreeChebyshevProducer N - coprimeHarmonicCorrection N` over `√N`. -/
theorem fullPairing_factorialCoprimeTwoThree_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (factorialCoprimeTwoThree N) =
      (2 * coprimeTwoThreeChebyshevProducer N - coprimeHarmonicCorrection N) / Real.sqrt N := by
  rw [fullPairing_factorialCoprimeTwoThree_linear]
  simp_rw [fullPairing_factorialLift_eq]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog2 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) hn
  have hlog3 : Real.log (3 * (N : ℝ)) = Real.log 3 + Real.log N :=
    Real.log_mul (by norm_num) hn
  have hlog6 : Real.log (6 * (N : ℝ)) = Real.log 2 + Real.log 3 + Real.log N := by
    rw [Real.log_mul (by norm_num) hn]
    have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h6, add_assoc]
  unfold coprimeTwoThreeChebyshevProducer coprimeHarmonicCorrection
  push_cast
  rw [hlog2, hlog3, hlog6]
  ring

/-- **Unconditional `O(log N / √N)` Bound for `fullPairing (factorialCoprimeTwoThree N)`:**
For every `N ≥ 1`,
`|fullPairing (factorialCoprimeTwoThree N)| ≤ (24 * log(6N + 1) + 7) / √N`. -/
theorem abs_fullPairing_factorialCoprimeTwoThree_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (factorialCoprimeTwoThree N)| ≤
      (24 * Real.log (6 * (N : ℝ) + 1) + 7) / Real.sqrt N := by
  rw [fullPairing_factorialCoprimeTwoThree_eq hN, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hb := abs_coprimeTwoThreeChebyshevProducer_le hN
  obtain ⟨hc0, hc1⟩ := coprimeHarmonicCorrection_bounds hN
  calc |2 * coprimeTwoThreeChebyshevProducer N - coprimeHarmonicCorrection N|
      ≤ |2 * coprimeTwoThreeChebyshevProducer N| + |coprimeHarmonicCorrection N| := abs_sub _ _
    _ = 2 * |coprimeTwoThreeChebyshevProducer N| + coprimeHarmonicCorrection N := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hc0]
    _ ≤ 24 * Real.log (6 * (N : ℝ) + 1) + 7 := by linarith

/-- **Public Unconditional Coprime `(2, 3)` Producer Package:**
Requires only the scale index `n : ℕ`. -/
theorem factorialCoprimeTwoThree_producer (n : ℕ) :
    (Function.support (primeTerm (factorialCoprimeTwoThree (n + 1)))).Finite ∧
      Summable (fun m => |primeTerm (factorialCoprimeTwoThree (n + 1)) m|) ∧
      IntegrableOn (fun x => polarDensity x * factorialCoprimeTwoThree (n + 1) x) (Ici 0) ∧
      |fullPairing (factorialCoprimeTwoThree (n + 1))| ≤
        (24 * Real.log (6 * ((n + 1 : ℕ) : ℝ) + 1) + 7) / Real.sqrt (n + 1 : ℕ) := by
  obtain ⟨hf, hs, hi⟩ := factorialCoprimeTwoThree_admissible (n + 1)
  exact ⟨hf, hs, hi, abs_fullPairing_factorialCoprimeTwoThree_le (by omega)⟩

/-! ## §3. Boundary-Free Laplace & Spectral Critical-Line Packet Producers -/

/-- **Unconditional Pointwise Prime-Free Spectral Producer Bound on the Critical Line:**
For every `N : ℕ` and frequency `ξ : ℝ`,
`‖fourierPairing N ξ‖ ≤ massProducerBound N`. -/
theorem norm_fourierPairing_le_massProducerBound (N : ℕ) (ξ : ℝ) :
    ‖ChebyshevGauge.fourierPairing N ξ‖ ≤ massProducerBound N :=
  (ChebyshevGauge.norm_fourierPairing_le N ξ).trans (mass_le_massProducerBound N)

/-- **Unconditional Prime-Free Spectral Critical-Line Mean-Square Producer Bound:**
For every `N : ℕ`,
`∫ ξ, ‖fourierPairing N ξ‖² / (1/4 + (2πξ)²) dξ ≤ laplaceEnergyProducerBound N`. -/
theorem spectral_fourierPairing_integral_le_laplaceEnergyProducerBound (N : ℕ) :
    (∫ ξ, ‖ChebyshevGauge.fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * Real.pi * ξ) ^ 2)) ≤
      laplaceEnergyProducerBound N := by
  rw [← ChebyshevGauge.laplaceEnergy_eq_integral_fourierPairing_sq]
  exact laplaceEnergy_le_laplaceEnergyProducerBound N

/-- **Boundary-Free Spectral Packet Bound:**
Every `C¹` compactly supported source `f` has `packetEnergy f N` controlled purely by the product
of `(∫ |f' - f/2|)²` and the critical-line spectral integral of `fourierPairing N`, with **zero
separate cutoff boundary term**. -/
theorem packetEnergy_le_spectral_fourierPairing (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤
      (∫ t, |ChebyshevGauge.gaugeDerivative f t|) ^ 2 *
        ∫ ξ, ‖ChebyshevGauge.fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * Real.pi * ξ) ^ 2) := by
  rw [← ChebyshevGauge.laplaceEnergy_eq_integral_fourierPairing_sq]
  exact ChebyshevGauge.packetEnergy_le_laplaceEnergy f hf N

/-- **Boundary-Free Prime-Free Multiplicative Packet Producer Bound:**
For every `C¹` compactly supported source `f` and `N : ℕ`,
`packetEnergy f N ≤ (∫ t, |gaugeDerivative f t|) ^ 2 * laplaceEnergyProducerBound N`. -/
theorem packetEnergy_le_gauge_sq_mul_laplaceEnergyProducerBound (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤
      (∫ t, |ChebyshevGauge.gaugeDerivative f t|) ^ 2 * laplaceEnergyProducerBound N :=
  (ChebyshevGauge.packetEnergy_le_laplaceEnergy f hf N).trans
    (mul_le_mul_of_nonneg_left (laplaceEnergy_le_laplaceEnergyProducerBound N) (sq_nonneg _))

/-- **Boundary-Free Laplace Packet Bound for the Constructed Collar (`collarSource f a b`):**
For every continuous `f : C_c(ℝ, ℝ)` (with **zero differentiability hypotheses**!),
`packetEnergy (collarSource f a b) N ≤ collarGaugeBudget f a b * laplaceEnergy N`. -/
theorem collar_packetEnergy_le_budget_mul_laplaceEnergy
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.packetEnergy (SignedPrimePolar.collarSource f a b) N ≤
      SignedPrimePolar.collarGaugeBudget f a b * ChebyshevGauge.laplaceEnergy N := by
  have h1 := ChebyshevGauge.packetEnergy_le_laplaceEnergy
    (SignedPrimePolar.collarSource f a b)
    (SignedPrimePolar.contDiff_collarSource f a b) N
  rw [SignedPrimePolar.gaugeDerivative_collarSource] at h1
  have h2 : (∫ t, |SignedPrimePolar.collarGaugeSource f a b t|) ^ 2 ≤
      SignedPrimePolar.collarGaugeBudget f a b :=
    SignedPrimePolar.collarGaugeL1_sq_le_budget f a b
  exact h1.trans
    (mul_le_mul_of_nonneg_right h2 (ChebyshevGauge.laplaceEnergy_nonneg N))

/-- **Boundary-Free Prime-Free Collar Packet Producer Bound:**
For every continuous `f : C_c(ℝ, ℝ)` (with **zero differentiability hypotheses**!),
`packetEnergy (collarSource f a b) N ≤ collarGaugeBudget f a b * laplaceEnergyProducerBound N`. -/
theorem collar_packetEnergy_le_budget_mul_laplaceEnergyProducerBound
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.packetEnergy (SignedPrimePolar.collarSource f a b) N ≤
      SignedPrimePolar.collarGaugeBudget f a b * laplaceEnergyProducerBound N :=
  (collar_packetEnergy_le_budget_mul_laplaceEnergy f a b N).trans
    (mul_le_mul_of_nonneg_left (laplaceEnergy_le_laplaceEnergyProducerBound N)
      (SignedPrimePolar.collarGaugeBudget_nonneg f a b))

/-! ## §4. Boundary-Free Spectral Laplace Full Weil Functional Bounds Across All Test Spaces -/

namespace RealWeilTestFn

/-- **Unconditional Boundary-Free Laplace Full Weil Functional Bound on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `c : ℝ` (with **zero hypotheses**, **zero arithmetic
functions**, and **no separate cutoff boundary term**!): -/
theorem unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_bound
    (f : RealWeilTestFn) (c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1| ≤
      Real.exp c * autocorr f.source 0 +
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative f.toCompactlySupported t|) ^ 2 *
            BiScaleUncertainty.laplaceEnergyProducerBound f.supportScale) := by
  have hid := f.re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing
  have hsub :
      (weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1 =
      -(2 * SignedPrimePolar.pairing f.supportScale (autocorr f.source)) := by
    linarith only [hid]
  rw [hsub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine (BiScaleUncertainty.two_mul_abs_pairing_le_exp_add_packetEnergy
    f.toCompactlySupported f.supportScale c).trans ?_
  refine add_le_add le_rfl ?_
  exact mul_le_mul_of_nonneg_left
    (BiScaleUncertainty.packetEnergy_le_gauge_sq_mul_laplaceEnergyProducerBound
      f.toCompactlySupported f.contDiff_one_source f.supportScale)
    (Real.exp_pos (-c)).le

/-- **Unconditional Boundary-Free Laplace Full Weil Functional Lower Bound on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound
    (f : RealWeilTestFn) (c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative f.toCompactlySupported t|) ^ 2 *
            BiScaleUncertainty.laplaceEnergyProducerBound f.supportScale) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have habs := f.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_bound c
  have hlow := neg_le_of_abs_le habs
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  linarith only [hlow, hpole]

end RealWeilTestFn

/-- **Unconditional Boundary-Free Laplace Full Weil Functional Lower Bound on `RealEvenPolarTestFn`:** -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound
    (g : RealEvenPolarTestFn) (c : ℝ) :
    biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        Real.exp c * autocorr g.source 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative
              (RealEvenPolarTestFn.toCompactlySupported g) t|) ^ 2 *
            BiScaleUncertainty.laplaceEnergyProducerBound
              (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re :=
  (RealEvenPolarTestFn.toRealWeilTestFn g).unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound
    c

namespace RealOddTestFn

/-- **Unconditional Boundary-Free Laplace Full Weil Functional Lower Bound on `RealOddTestFn`:** -/
theorem unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound
    (f : RealOddTestFn) (c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative f.toCompactlySupported t|) ^ 2 *
            BiScaleUncertainty.laplaceEnergyProducerBound f.toRealWeilTestFn.supportScale) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound c

end RealOddTestFn

namespace RealHyperplaneGenerator

/-- **Unconditional Boundary-Free Laplace Full Weil Functional Lower Bound on `RealHyperplaneGenerator`:** -/
theorem unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound
    (x : RealHyperplaneGenerator) (c : ℝ) :
    biScaleLevyEnergy (RealHyperplaneGenerator.source x) +
        EF.gammaBracket 0 *
          (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
            (RealHyperplaneGenerator.toRealWeilTestFn x).1.1 0).re -
        Real.exp c * autocorr (RealHyperplaneGenerator.source x) 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative
              (RealHyperplaneGenerator.toRealWeilTestFn x).toCompactlySupported t|) ^ 2 *
            BiScaleUncertainty.laplaceEnergyProducerBound
              (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
          (RealHyperplaneGenerator.toRealWeilTestFn x).1.1)).re :=
  (RealHyperplaneGenerator.toRealWeilTestFn x).unconditional_weilFullFunctional_vonMangoldt_laplaceProducer_lower_bound
    c

end RealHyperplaneGenerator

end

end GaloisForLFunctions.BiScaleUncertainty
