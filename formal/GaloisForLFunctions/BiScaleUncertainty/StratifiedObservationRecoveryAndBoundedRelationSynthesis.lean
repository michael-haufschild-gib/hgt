import GaloisForLFunctions.BiScaleUncertainty.SievePhysicalTranslationStability
import GaloisForLFunctions.BiScaleUncertainty.SieveLocalVisibilityClassification
import GaloisForLFunctions.BiScaleUncertainty.SievePrimePowerLocalRegularity
import GaloisForLFunctions.BezoutValuationIncidence.StableRelationSpectrumFromPolynomialWindows
import GaloisForLFunctions.BezoutValuationIncidence.PolynomialHorizonRecoveryFromArbitraryPhaseWindows
import GaloisForLFunctions.BezoutValuationIncidence.RelationSpectrumDeterminesTheRowUpToTheCompanion
import GaloisForLFunctions.BezoutValuationIncidence.CompleteClassificationOfZeroProductRelations
import GaloisForLFunctions.BezoutValuationIncidence.ChineseRemainderBezoutPeriodicityAndSawtoothDefect

/-!
# Stratified Observation Recovery, Cutoff-Independent Constants, Windowed Protocols, and Bounded-Length Relation Synthesis

This module establishes the stratified and cutoff-independent stability laws, finite-horizon
windowed recovery theorems, and the quantitative bounded-length relation organizing theorem of the
arithmetic observation theory:

1. **Cutoff-Independent Global Coordinate, Reflection, and Clock-Period $L^2$ Stability (§1):**
   - For any cutoff $N \in \mathbb{N}$ and any two divisor-sieve rows $c, e : \mathbb{N} \to \mathbb{R}$
     whose fifth and sixth translated moment arrays agree within $\delta^6$ ($0 \le \delta \le 1$,
     equivalently $\varepsilon \in [0, 1]$ with $\delta = \varepsilon^{1/6}$), let
     $h_{\mathrm{rd}} = \mathrm{canonicalShift}\,N\,(\mathrm{thresholdSourceWeights}\,N\,c\,\delta)$.
     Then either $c^* = c$ or $c^* = \mathrm{HalfPeriod.reflection}\,N\,h_{\mathrm{rd}}\,c$ satisfies
     $|Y_{N,e}(q) - Y_{N,c^*}(q)| \le 3\delta = 3\varepsilon^{1/6}$ for all $q \in [1, N]$
     (`exists_cutoff_independent_coordinate_and_reflection_error`,
     `exists_cutoff_independent_coordinate_and_reflection_holder`), with coordinate constant $3$
     independent of $N$ (and constant $2$ on the top-anchor stratum).
   - At any common multiple $M$ of $[1, N]$ (including $M = \mathrm{horizonObservationModulus}\,N = \mathrm{lcm}(1, \dots, N)$
     and $M = N!$), the prefix $L^2$ distance between any two rows equals $M$ times their totient-weighted
     Selberg coordinate distance (`sum_sieveSeq_sub_sq_eq_selberg_of_forall_dvd`), giving the
     cutoff-independent normalized $L^2$ stability bound $9\varepsilon^{1/3}$ globally (and
     $4\varepsilon^{2/3}$ on the top-anchor stratum).

2. **Sharper Physical Constants on Stated Support Strata, Fixed Finite Supports, and the Dyadic Tower (§2):**
   - On any mode stratum $S$ containing $\mathrm{activeModes}\,N\,c$ and $\mathrm{activeModes}\,N\,e$,
     the global sixth-root physical translation constant sharpens from $3\sum_{q \le N} \varphi(q)$
     to $3\sum_{q \in S} \varphi(q)$ (`exists_stratum_physical_translate_error`,
     `exists_stratum_physical_translate_holder`), and the top-anchor cube-root constant sharpens
     from $2\sum_{q \le N} \varphi(q)$ to $2\sum_{q \in S} \varphi(q)$
     (`exists_topAnchor_stratum_translate_error`, `exists_topAnchor_stratum_translate_holder`).
   - For rows supported on any fixed finite mode set $S_0 \subset \mathbb{N}$, the pointwise
     physical translation constant $3\sum_{q \in S_0} \varphi(q)$ is completely independent of the
     cutoff $N$. On the dyadic tower $S_{\mathrm{dyad}}(N) = \{2^k : k \le \lfloor\log_2 N\rfloor\}$,
     $\sum_{q \in S_{\mathrm{dyad}}(N)} \varphi(q) = 2^{\lfloor\log_2 N\rfloor} = \mathrm{topOrder}\,N \le N$
     (`sum_totient_dyadicTowerOrders_eq_topOrder`), reducing the quadratic $\Phi(N)$ constant to linear.

3. **Windowed and Reduced Observation Protocols with Quantified Cutoff Cost (§3):**
   - Global sixth-root coordinate and physical translation recovery lift unconditionally to
     polynomial-horizon windows at arbitrary unknown phases, with quantified cutoff cost in both
     the $\ell^1$ transfer scale $(\|c\|_1^m + \|e\|_1^m)/K$ and the Selberg-energy transfer scale
     $\mathrm{windowTransferError}\,N\,m\,K\,c = (e^{19/4} N \sqrt{Q_{\mathrm{Sel}}(N, c)})^m / K$
     (`exists_global_physical_translate_of_windows_l1`,
     `exists_global_physical_translate_of_windowMoments`).
   - From the $N$ two-point lags $g \in \{1, \dots, N\}$ on a single window at unknown phase, the
     square-root inequality $(|x| - |y|)^2 \le |x^2 - y^2|$ recovers every Selberg coordinate
     magnitude $|Y_{N,c}(q)|$ ($2 \le q \le N$) with explicit harmonic-variance cutoff cost
     (`abs_selbergCoord_abs_sub_sq_le_of_single_window_lags`).

4. **The Quantitative Bounded-Length Relation Organizing Theorem (§4):**
   - The standard additive character $\mathrm{ZMod.stdAddChar}$ maps every zero-sum frequency word
     $r : \mathrm{Fin}\,m \to \mathrm{ZMod}\,N!$ with orders in $[1, N]$ to a multiplicative
     zero-product tuple $\zeta \in \mathrm{zeroProductTuples}\,N\,m$ preserving element orders
     (`orderOf_stdAddChar`, `stdAddChar_mem_zeroProductTuples`, `relationCoeff_stdAddChar`).
   - Missing-mode spikes $\mathrm{spikeWeights}\,N\,b\,q\,(-t)$ coincide on $[1, N]$ with the
     elementary sign-character twist $\mathrm{scaledSelbergRow}\,N\,(\mathrm{spikeWeights}\,N\,b\,q\,t)\,(\mathrm{modeSignChar}\,q)$
     (`spikeWeights_neg_eq_scaledSelbergRow`), so the Parseval relation-energy law simultaneously
     governs in-support sign orientation and out-of-support missing-mode visibility with explicit
     energy and realization bounds on both sides (`quantitative_sign_relation_dichotomy`,
     `quantitative_visibility_relation_dichotomy`).
-/

open scoped BigOperators
open Finset

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments

open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open ValuationPhase LinearVisibility

set_option autoImplicit false

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-! ## §1. Cutoff-Independent Global Coordinate, Reflection, and Clock-Period $L^2$ Stability -/

/-- Linearity of `sieveSeq N` in the divisor weight `c`. -/
theorem sieveSeq_sub (N : ℕ) (a b : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (fun d => a d - b d) k = sieveSeq N a k - sieveSeq N b k := by
  unfold sieveSeq
  rw [Finset.sum_sub_distrib]

/-- Linearity of `selbergMultiplesCoord N` in the divisor weight `c`. -/
theorem selbergMultiplesCoord_sub (N : ℕ) (a b : ℕ → ℝ) (q : ℕ) :
    selbergMultiplesCoord N (fun d => a d - b d) q =
      selbergMultiplesCoord N a q - selbergMultiplesCoord N b q := by
  unfold selbergMultiplesCoord
  simp only [sub_div, Finset.sum_sub_distrib]

/-- **Exact Clock-Period $L^2$ Parseval Identity:**
Whenever every $d \in [1, N]$ divides $M$ (in particular at $M = \mathrm{horizonObservationModulus}\,N$
and $M = N!$), the prefix $L^2$ distance $\sum_{k=1}^M (s_{N,a}(k) - s_{N,b}(k))^2$ equals $M$ times
the totient-weighted Selberg coordinate distance. -/
theorem sum_sieveSeq_sub_sq_eq_selberg_of_forall_dvd (N M : ℕ) (a b : ℕ → ℝ)
    (hdvd : ∀ d ∈ Finset.Icc 1 N, d ∣ M) :
    (∑ k ∈ Finset.Icc 1 M, (sieveSeq N a k - sieveSeq N b k) ^ 2) =
      (M : ℝ) * ∑ q ∈ Finset.Icc 1 N,
        (q.totient : ℝ) * (selbergMultiplesCoord N a q - selbergMultiplesCoord N b q) ^ 2 := by
  have h1 := sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N M (fun d => a d - b d)
  rw [signedLcmFractDefect_eq_zero_of_forall_dvd N M (fun d => a d - b d) hdvd, sub_zero] at h1
  simp_rw [sieveSeq_sub] at h1
  rw [h1]
  unfold selbergTotientDiagonalForm
  simp_rw [selbergMultiplesCoord_sub]

/-- Every $d \in [1, N]$ divides `horizonObservationModulus N = lcm(1, …, N)`. -/
theorem dvd_horizonObservationModulus {N d : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    d ∣ horizonObservationModulus N :=
  Finset.dvd_lcm hd

/-- Every $d \in [1, N]$ divides $N!$. -/
theorem dvd_factorial_of_mem_Icc {N d : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    d ∣ N.factorial :=
  Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2

/-- **Support-Stratum Pointwise Amplification Bound:**
If two rows $a, b$ have equal Selberg coordinates outside a mode set $S : \mathrm{Finset}\,\mathbb{N}$
and differ by at most $\eta \ge 0$ on $S \cap [1, N]$, then $|s_{N,a}(n) - s_{N,b}(n)| \le (\sum_{q \in S} \varphi(q)) \eta$
for every $n \in \mathbb{N}$. -/
theorem sieveSeq_error_le_support_totient_sum (N : ℕ) (S : Finset ℕ) (a b : ℕ → ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hout : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N a q = selbergMultiplesCoord N b q)
    (hin : ∀ q ∈ Finset.Icc 1 N, q ∈ S →
      |selbergMultiplesCoord N a q - selbergMultiplesCoord N b q| ≤ η)
    (n : ℕ) :
    |sieveSeq N a n - sieveSeq N b n| ≤ (∑ q ∈ S, (q.totient : ℝ)) * η := by
  calc |sieveSeq N a n - sieveSeq N b n|
      ≤ ∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ) *
          |selbergMultiplesCoord N a q - selbergMultiplesCoord N b q| :=
        sieveSeq_error_le_coordinate_sum N a b n
    _ ≤ ∑ q ∈ (Finset.Icc 1 N).filter (· ∈ S), (q.totient : ℝ) * η := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun q hq => ?_
        by_cases hqS : q ∈ S
        · rw [if_pos hqS]
          exact mul_le_mul_of_nonneg_left (hin q hq hqS) (Nat.cast_nonneg _)
        · rw [if_neg hqS, hout q hq hqS, sub_self, abs_zero, mul_zero]
    _ ≤ ∑ q ∈ S, (q.totient : ℝ) * η := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq => (Finset.mem_filter.mp hq).2) (fun q _ _ => mul_nonneg (Nat.cast_nonneg _) hη)
    _ = (∑ q ∈ S, (q.totient : ℝ)) * η := (Finset.sum_mul _ _ _).symm

/-- **Cutoff-Independent Global Coordinate and Half-Period Reflection Stability:**
For any cutoff $N \in \mathbb{N}$, any rows $c, e : \mathbb{N} \to \mathbb{R}$, and any $\delta \in [0, 1]$
with fifth and sixth translated moments within $\delta^6$, let
$h_{\mathrm{rd}} = \mathrm{canonicalShift}\,N\,(\mathrm{thresholdSourceWeights}\,N\,c\,\delta)$.
Then either $c^* = c$ or $c^* = \mathrm{HalfPeriod.reflection}\,N\,h_{\mathrm{rd}}\,c$ satisfies
$|Y_{N,e}(q) - Y_{N,c^*}(q)| \le 3\delta$ for every $q \in [1, N]$, and hence
$\sum_{q=1}^N \varphi(q)(Y_{N,e}(q) - Y_{N,c^*}(q))^2 \le 9(\sum_{q=1}^N \varphi(q))\delta^2$. -/
theorem exists_cutoff_independent_coordinate_and_reflection_error (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h5 : ∀ h : Fin 5 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ δ ^ 6)
    (h6 : ∀ h : Fin 6 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ δ ^ 6) :
    let h_rd := canonicalShift N (thresholdSourceWeights N c δ)
    ((∀ q ∈ Finset.Icc 1 N, |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 3 * δ) ∧
      (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ) *
        (selbergMultiplesCoord N e q - selbergMultiplesCoord N c q) ^ 2 ≤
          9 * (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ ^ 2)) ∨
    ((∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ 3 * δ) ∧
      (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ) *
        (selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q) ^ 2 ≤
          9 * (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ ^ 2)) := by
  let c' := thresholdSourceWeights N c δ
  let e' := thresholdTargetWeights N c e δ
  let h_rd := canonicalShift N c'
  have h5' := threshold_moments_eq N c e δ hδ hδ1 h6 5 (Or.inl rfl) h5
  have h6' := threshold_moments_eq N c e δ hδ hδ1 h6 6 (Or.inr rfl) h6
  have hsrc (q : ℕ) : |selbergMultiplesCoord N c q - selbergMultiplesCoord N c' q| ≤ δ := by
    rw [coordinate_thresholdSource N c δ hδ]
    exact Threshold.source_error δ _ hδ
  have htgt (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
      |selbergMultiplesCoord N e q - selbergMultiplesCoord N e' q| ≤ 2 * δ := by
    rw [coordinate_thresholdTarget N c e δ hδ]
    exact Threshold.target_error δ _ _ hδ (coordinate_magnitude_error N c e δ hδ h6 q hq)
  have hsq_sum (c_star : ℕ → ℝ)
      (hcoord : ∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N c_star q| ≤ 3 * δ) :
      ∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ) *
        (selbergMultiplesCoord N e q - selbergMultiplesCoord N c_star q) ^ 2 ≤
          9 * (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ ^ 2 := by
    calc ∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ) *
          (selbergMultiplesCoord N e q - selbergMultiplesCoord N c_star q) ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ) * (3 * δ) ^ 2 := by
          refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord q hq) 2
      _ = 9 * (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  rcases coefficients_eq_or_companion_of_moments N c' e' h5' h6' with he | he
  · left
    have hcoord (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 3 * δ := by
      have heq : selbergMultiplesCoord N e' q = selbergMultiplesCoord N c' q :=
        (sieve_active_coefficients_eq_iff N e' c').mp he q hq
      have h2 : |selbergMultiplesCoord N e' q - selbergMultiplesCoord N c q| ≤ δ := by
        rw [heq, abs_sub_comm]
        exact hsrc q
      calc |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q|
          ≤ |selbergMultiplesCoord N e q - selbergMultiplesCoord N e' q| +
              |selbergMultiplesCoord N e' q - selbergMultiplesCoord N c q| := abs_sub_le _ _ _
        _ ≤ 2 * δ + δ := add_le_add (htgt q hq) h2
        _ = 3 * δ := by ring
    exact ⟨hcoord, hsq_sum c hcoord⟩
  · right
    have hcoord (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
        |selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ 3 * δ := by
      have heq : selbergMultiplesCoord N e' q =
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c') q :=
        (sieve_active_coefficients_eq_iff N e' (companion N c')).mp he q hq
      have href_diff :
          |selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c') q -
            selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ δ := by
        rw [HalfPeriod.coordinate_reflection, HalfPeriod.coordinate_reflection]
        by_cases hdiv : q ∣ h_rd
        · rw [if_pos hdiv, if_pos hdiv, abs_sub_comm]
          exact hsrc q
        · rw [if_neg hdiv, if_neg hdiv, neg_sub_neg]
          exact hsrc q
      have h2 : |selbergMultiplesCoord N e' q -
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ δ := by
        rw [heq]
        exact href_diff
      calc |selbergMultiplesCoord N e q -
            selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q|
          ≤ |selbergMultiplesCoord N e q - selbergMultiplesCoord N e' q| +
              |selbergMultiplesCoord N e' q -
                selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| := abs_sub_le _ _ _
        _ ≤ 2 * δ + δ := add_le_add (htgt q hq) h2
        _ = 3 * δ := by ring
    exact ⟨hcoord, hsq_sum (HalfPeriod.reflection N h_rd c) hcoord⟩

/-- **Cutoff-Independent Global Sixth-Root Coordinate Stability (`exists_cutoff_independent_coordinate_and_reflection_holder`):**
In the raw fifth/sixth moment error scale $\varepsilon \in [0, 1]$, every Selberg coordinate of $e$
agrees within $3\varepsilon^{1/6}$ (constant $3$ independent of $N$) with either $c$ or its
threshold half-period reflection. -/
theorem exists_cutoff_independent_coordinate_and_reflection_holder (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h5 : ∀ h : Fin 5 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ ε)
    (h6 : ∀ h : Fin 6 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ ε) :
    let h_rd := canonicalShift N (thresholdSourceWeights N c (ε ^ (1 / 6 : ℝ)))
    (∀ q ∈ Finset.Icc 1 N,
      |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 3 * ε ^ (1 / 6 : ℝ)) ∨
    (∀ q ∈ Finset.Icc 1 N,
      |selbergMultiplesCoord N e q -
        selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ 3 * ε ^ (1 / 6 : ℝ)) := by
  have hp : (ε ^ (1 / 6 : ℝ)) ^ 6 = ε := by
    simpa only [Nat.cast_ofNat, one_div] using
      (Real.rpow_inv_natCast_pow (n := 6) hε (by norm_num))
  rcases exists_cutoff_independent_coordinate_and_reflection_error N c e (ε ^ (1 / 6 : ℝ))
    (Real.rpow_nonneg hε _) (Real.rpow_le_one hε hε1 (by norm_num))
    (by simpa only [hp] using h5) (by simpa only [hp] using h6) with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ## §2. Sharper Physical Constants on Stated Support Strata, Fixed Finite Supports, and the Dyadic Tower -/

private theorem sieveSeq_eq_of_weights (N : ℕ) (a b : ℕ → ℝ)
    (hab : ∀ d ∈ Finset.Icc 1 N, a d = b d) (n : ℕ) :
    sieveSeq N a n = sieveSeq N b n := by
  unfold sieveSeq
  exact Finset.sum_congr rfl fun d hd => hab d (Finset.mem_filter.mp hd).1

/-- **Global Support-Stratum Physical Translation Recovery (`exists_stratum_physical_translate_error`):**
If $c$ and $e$ have vanishing Selberg coordinates outside $S : \mathrm{Finset}\,\mathbb{N}$ on $[1, N]$
(in particular when $\mathrm{activeModes}\,N\,c \subseteq S$ and $\mathrm{activeModes}\,N\,e \subseteq S$)
and fifth/sixth moments within $\delta^6$ ($0 \le \delta \le 1$), then there exists a shift $t \in \mathbb{N}$
such that $|s_{N,e}(n) - s_{N,c}(n + t)| \le 3 (\sum_{q \in S} \varphi(q)) \delta$ for all $n \in \mathbb{N}$. -/
theorem exists_stratum_physical_translate_error (N : ℕ) (S : Finset ℕ) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N c q = 0)
    (heS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N e q = 0)
    (h5 : ∀ h : Fin 5 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ δ ^ 6)
    (h6 : ∀ h : Fin 6 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ δ ^ 6) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + t)| ≤
      3 * (∑ q ∈ S, (q.totient : ℝ)) * δ := by
  let c' := thresholdSourceWeights N c δ
  let e' := thresholdTargetWeights N c e δ
  have h5' := threshold_moments_eq N c e δ hδ hδ1 h6 5 (Or.inl rfl) h5
  have h6' := threshold_moments_eq N c e δ hδ hδ1 h6 6 (Or.inr rfl) h6
  have hshift : ∃ t : ℕ, ∀ n, sieveSeq N e' n = sieveSeq N c' (n + t) := by
    rcases coefficients_eq_or_companion_of_moments N c' e' h5' h6' with he | he
    · exact ⟨0, fun n => by simpa using sieveSeq_eq_of_weights N e' c' he n⟩
    · exact ⟨canonicalShift N c', fun n =>
        (sieveSeq_eq_of_weights N e' (companion N c') he n).trans (sieveSeq_companion N c' n)⟩
  obtain ⟨t, ht⟩ := hshift
  have hsource (n : ℕ) : |sieveSeq N c n - sieveSeq N c' n| ≤
      (∑ q ∈ S, (q.totient : ℝ)) * δ := by
    refine sieveSeq_error_le_support_totient_sum N S c c' δ hδ ?_ ?_ n
    · intro q hq hqS
      rw [coordinate_thresholdSource N c δ hδ, hcS q hq hqS]
      simp [Threshold.source, not_lt.mpr hδ]
    · intro q _ _
      rw [coordinate_thresholdSource N c δ hδ]
      exact Threshold.source_error δ _ hδ
  have htarget (n : ℕ) : |sieveSeq N e n - sieveSeq N e' n| ≤
      (∑ q ∈ S, (q.totient : ℝ)) * (2 * δ) := by
    refine sieveSeq_error_le_support_totient_sum N S e e' (2 * δ) (by linarith) ?_ ?_ n
    · intro q hq hqS
      rw [coordinate_thresholdTarget N c e δ hδ, hcS q hq hqS, heS q hq hqS]
      simp [Threshold.target, not_lt.mpr hδ]
    · intro q hq _
      rw [coordinate_thresholdTarget N c e δ hδ]
      exact Threshold.target_error δ _ _ hδ (coordinate_magnitude_error N c e δ hδ h6 q hq)
  refine ⟨t, fun n => ?_⟩
  calc |sieveSeq N e n - sieveSeq N c (n + t)|
      ≤ |sieveSeq N e n - sieveSeq N e' n| +
          |sieveSeq N e' n - sieveSeq N c (n + t)| := abs_sub_le _ _ _
    _ ≤ (∑ q ∈ S, (q.totient : ℝ)) * (2 * δ) +
          (∑ q ∈ S, (q.totient : ℝ)) * δ := by
        refine add_le_add (htarget n) ?_
        rw [ht, abs_sub_comm]
        exact hsource (n + t)
    _ = 3 * (∑ q ∈ S, (q.totient : ℝ)) * δ := by ring

/-- **Global Support-Stratum Sixth-Root Hölder Stability (`exists_stratum_physical_translate_holder`):**
For rows with $\mathrm{activeModes}\,N\,c \subseteq S$ and $\mathrm{activeModes}\,N\,e \subseteq S$,
fifth and sixth moments within $\varepsilon \in [0, 1]$ give physical translation recovery with
stratum constant $3 \sum_{q \in S} \varphi(q)$. -/
theorem exists_stratum_physical_translate_holder (N : ℕ) (S : Finset ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hcS : activeModes N c ⊆ S) (heS : activeModes N e ⊆ S)
    (h5 : ∀ h : Fin 5 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ ε)
    (h6 : ∀ h : Fin 6 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ ε) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + t)| ≤
      3 * (∑ q ∈ S, (q.totient : ℝ)) * ε ^ (1 / 6 : ℝ) := by
  have hp : (ε ^ (1 / 6 : ℝ)) ^ 6 = ε := by
    simpa only [Nat.cast_ofNat, one_div] using
      (Real.rpow_inv_natCast_pow (n := 6) hε (by norm_num))
  refine exists_stratum_physical_translate_error N S c e (ε ^ (1 / 6 : ℝ))
    (Real.rpow_nonneg hε _) (Real.rpow_le_one hε hε1 (by norm_num))
    (fun q _ hqS => coordinate_zero_of_not_active N c q fun h => hqS (hcS h))
    (fun q _ hqS => coordinate_zero_of_not_active N e q fun h => hqS (heS h))
    (by simpa only [hp] using h5) (by simpa only [hp] using h6)

/-- **Top-Anchor Support-Stratum Cube-Root Stability (`exists_topAnchor_stratum_translate_error`):**
On the top-anchor stratum ($1 \le |Y_{N,c}(\mathrm{topOrder}\,N)|$, $1 \le |Y_{N,e}(\mathrm{topOrder}\,N)|$, $N \ge 2$)
with coordinates vanishing outside $S$, fifth and sixth moments within $\delta^3$ ($0 \le \delta \le 1$)
give both cutoff-independent coordinate recovery within $2\delta$ and physical translation recovery
within $2(\sum_{q \in S} \varphi(q))\delta$. -/
theorem exists_topAnchor_stratum_translate_error (N : ℕ) (hN : 2 ≤ N) (S : Finset ℕ)
    (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc : 1 ≤ |selbergMultiplesCoord N c (TopAnchor.topOrder N)|)
    (he : 1 ≤ |selbergMultiplesCoord N e (TopAnchor.topOrder N)|)
    (hcS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N c q = 0)
    (heS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N e q = 0)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 3)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 3) :
    ((∀ q ∈ Finset.Icc 1 N, |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 2 * δ) ∧
      (∀ n : ℕ, |sieveSeq N e n - sieveSeq N c n| ≤ 2 * (∑ q ∈ S, (q.totient : ℝ)) * δ)) ∨
    ((∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N (companion N c) q| ≤ 2 * δ) ∧
      (∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + canonicalShift N c)| ≤
        2 * (∑ q ∈ S, (q.totient : ℝ)) * δ)) := by
  have hp := TopAnchor.topOrder_mem N hN
  have ha := coordinate_sixth_error N c e (δ ^ 3) h6 (TopAnchor.topOrder N) hp
  have hδ3 : δ ^ 3 ≤ 2 * δ := by
    have h₁ := mul_nonneg hδ (sub_nonneg.mpr hδ1)
    have h₂ := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ1)
    nlinarith only [h₁, h₂, hδ]
  have hlow (q : ℕ) (hq : q ∈ Finset.Icc 1 N) (hne : q ≠ TopAnchor.topOrder N) :
      |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 2 * δ := by
    have hdepth : q.factorization 2 < (TopAnchor.topOrder N).factorization 2 := by
      rw [TopAnchor.topOrder_depth]
      exact TopAnchor.depth_lt_top hq hne
    have hh := TopAnchor.lower_error (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q)
      (selbergMultiplesCoord N c (TopAnchor.topOrder N))
      (selbergMultiplesCoord N e (TopAnchor.topOrder N))
      δ hc he hδ hδ1 ha (coordinate_sixth_error N c e (δ ^ 3) h6 q hq)
      (TopAnchor.lower_product_error N c e (δ ^ 3) h5 hq hp hdepth)
    simpa only [abs_sub_comm] using hh
  rcases TopAnchor.upper_error (selbergMultiplesCoord N c (TopAnchor.topOrder N))
    (selbergMultiplesCoord N e (TopAnchor.topOrder N)) (δ ^ 3) hc ha with hs | hs
  · left
    have hcoord (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 2 * δ := by
      by_cases hqtop : q = TopAnchor.topOrder N
      · subst q; exact hs.trans hδ3
      · exact hlow q hq hqtop
    refine ⟨hcoord, fun n => ?_⟩
    have hh := sieveSeq_error_le_support_totient_sum N S e c (2 * δ) (by linarith)
      (fun q hq hqS => by rw [heS q hq hqS, hcS q hq hqS])
      (fun q hq _ => hcoord q hq) n
    linarith
  · right
    have hc0 : selbergMultiplesCoord N c (TopAnchor.topOrder N) ≠ 0 := by
      intro hz; rw [hz, abs_zero] at hc; linarith
    have hcoord (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N (companion N c) q| ≤ 2 * δ := by
      rw [TopAnchor.coordinate_companion_top N hN c hc0 q hq]
      by_cases hqtop : q = TopAnchor.topOrder N
      · rw [if_pos hqtop, hqtop, sub_neg_eq_add]; exact hs.trans hδ3
      · rw [if_neg hqtop]; exact hlow q hq hqtop
    refine ⟨hcoord, fun n => ?_⟩
    have hh := sieveSeq_error_le_support_totient_sum N S e (companion N c) (2 * δ) (by linarith)
      (fun q hq hqS => by
        rw [heS q hq hqS, coordinate_companion N c q hq, hcS q hq hqS]
        split_ifs <;> ring)
      (fun q hq _ => hcoord q hq) n
    rw [sieveSeq_companion] at hh
    linarith

/-- The dyadic tower orders $\{2^k : k \le \lfloor\log_2 N\rfloor\}$ at cutoff $N$. -/
def dyadicTowerOrders (N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 N + 1)).image (fun k => 2 ^ k)

/-- **Exact Totient Sum on the Dyadic Tower (`sum_totient_dyadicTowerOrders_eq_topOrder`):**
The totient mass of `dyadicTowerOrders N` telescopes to $2^{\lfloor\log_2 N\rfloor} = \mathrm{topOrder}\,N$,
which is at most $N$ for $N \ge 1$. -/
theorem sum_totient_dyadicTowerOrders_eq_topOrder (N : ℕ) :
    (∑ q ∈ dyadicTowerOrders N, (q.totient : ℝ)) = (TopAnchor.topOrder N : ℝ) := by
  unfold dyadicTowerOrders TopAnchor.topOrder
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k) :=
    Nat.pow_right_injective (by decide : 2 ≤ 2)
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  have htel : ∀ m : ℕ, (∑ k ∈ Finset.range (m + 1), ((2 ^ k).totient : ℝ)) = (2 ^ m : ℕ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]
      simp only [Nat.reduceSub]
      push_cast
      ring
  exact htel (Nat.log 2 N)

/-- On the dyadic tower stratum `dyadicTowerOrders N`, the global sixth-root physical translation
constant is $3 \cdot \mathrm{topOrder}\,N \le 3N$ (linear in $N$ rather than quadratic). -/
theorem exists_dyadicTower_physical_translate_holder {N : ℕ} (hN : 1 ≤ N) (c e : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hcS : activeModes N c ⊆ dyadicTowerOrders N)
    (heS : activeModes N e ⊆ dyadicTowerOrders N)
    (h5 : ∀ h : Fin 5 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ ε)
    (h6 : ∀ h : Fin 6 → ℕ, |translatedMoment N c h - translatedMoment N e h| ≤ ε) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + t)| ≤
      3 * (N : ℝ) * ε ^ (1 / 6 : ℝ) := by
  obtain ⟨t, ht⟩ := exists_stratum_physical_translate_holder N (dyadicTowerOrders N)
    c e ε hε hε1 hcS heS h5 h6
  rw [sum_totient_dyadicTowerOrders_eq_topOrder] at ht
  have htop_le : (TopAnchor.topOrder N : ℝ) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hrpow_nn : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  refine ⟨t, fun n => (ht n).trans ?_⟩
  nlinarith only [htop_le, hrpow_nn]

/-! ## §3. Windowed and Reduced Observation Protocols with Quantified Cutoff Cost -/

/-- **Unconditional Global Sixth-Root Recovery from Polynomial Windows in the $\ell^1$ Scale
(`exists_global_physical_translate_of_windows_l1`):**
Without any top-anchor or support-gap hypothesis, if the fifth and sixth window sums on windows of
length $K > 0$ at arbitrary phases $A, B$ agree within $K\eta$ and
$\eta + (\|c\|_1^m + \|e\|_1^m)/K \le \delta^6$ for $m \in \{5, 6\}$, then every coordinate of $e$
agrees within $3\delta$ with $c$ or its threshold reflection, and there exists $t \in \mathbb{N}$
such that $|s_{N,e}(n) - s_{N,c}(n + t)| \le 3(\sum_{q \in S} \varphi(q))\delta$ on any common
support stratum $S$. -/
theorem exists_global_physical_translate_of_windows_l1 (N : ℕ) (S : Finset ℕ) (c e : ℕ → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N c q = 0)
    (heS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N e q = 0)
    (A B : ℕ) {K : ℕ} (hK : 0 < K) (η : ℝ)
    (hw5 : ∀ v : Fin 5 → ℕ,
      |(∑ k ∈ Finset.Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
        ∑ k ∈ Finset.Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)| ≤ K * η)
    (hw6 : ∀ v : Fin 6 → ℕ,
      |(∑ k ∈ Finset.Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
        ∑ k ∈ Finset.Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)| ≤ K * η)
    (hb5 : η + ((∑ d ∈ Finset.Icc 1 N, |c d|) ^ 5 + (∑ d ∈ Finset.Icc 1 N, |e d|) ^ 5) / K ≤ δ ^ 6)
    (hb6 : η + ((∑ d ∈ Finset.Icc 1 N, |c d|) ^ 6 + (∑ d ∈ Finset.Icc 1 N, |e d|) ^ 6) / K ≤ δ ^ 6) :
    let h_rd := canonicalShift N (thresholdSourceWeights N c δ)
    (((∀ q ∈ Finset.Icc 1 N, |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 3 * δ) ∨
      (∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ 3 * δ)) ∧
      ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + t)| ≤
        3 * (∑ q ∈ S, (q.totient : ℝ)) * δ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlift : ∀ (m : ℕ) (v : Fin m → ℕ),
      |(∑ k ∈ Finset.Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
        ∑ k ∈ Finset.Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)| ≤ K * η →
      |translatedMoment N c v - translatedMoment N e v| ≤
        η + ((∑ d ∈ Finset.Icc 1 N, |c d|) ^ m + (∑ d ∈ Finset.Icc 1 N, |e d|) ^ m) / K := by
    intro m v hv
    have h1 := abs_window_translatedMoment_sub_le N c v A K
    have h2 := abs_window_translatedMoment_sub_le N e v B K
    set Wc := ∑ k ∈ Finset.Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)
    set We := ∑ k ∈ Finset.Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)
    set Tc := translatedMoment N c v
    set Te := translatedMoment N e v
    have key : |(K : ℝ) * (Tc - Te)| ≤
        K * η + ((∑ d ∈ Finset.Icc 1 N, |c d|) ^ m + (∑ d ∈ Finset.Icc 1 N, |e d|) ^ m) := by
      have hsplit : (K : ℝ) * (Tc - Te) = (Wc - We) - (Wc - K * Tc) + (We - K * Te) := by ring
      rw [hsplit]
      calc |(Wc - We) - (Wc - K * Tc) + (We - K * Te)|
          ≤ |(Wc - We) - (Wc - K * Tc)| + |We - K * Te| := abs_add_le _ _
        _ ≤ |Wc - We| + |Wc - K * Tc| + |We - K * Te| := by
            have := abs_sub (Wc - We) (Wc - K * Tc)
            linarith
        _ ≤ _ := by linarith
    rw [abs_mul, abs_of_pos hKR] at key
    rw [add_div' _ _ _ hKR.ne', le_div_iff₀ hKR]
    nlinarith [key]
  have h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 6 :=
    fun v => (hlift 5 v (hw5 v)).trans hb5
  have h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 6 :=
    fun v => (hlift 6 v (hw6 v)).trans hb6
  refine ⟨?_, exists_stratum_physical_translate_error N S c e δ hδ hδ1 hcS heS h5 h6⟩
  rcases exists_cutoff_independent_coordinate_and_reflection_error N c e δ hδ hδ1 h5 h6 with
    ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **Unconditional Global Sixth-Root Recovery from Polynomial Window Averages in the Selberg Energy Scale
(`exists_global_physical_translate_of_windowMoments`):**
If the degree-5 and degree-6 window averages `windowMoment` at arbitrary shift-dependent phases
$\varphi_m(v), \psi_m(v)$ agree within $\eta_m$ and
$\eta_m + \mathrm{windowTransferError}\,N\,m\,K\,c + \mathrm{windowTransferError}\,N\,m\,K\,e \le \delta^6$
for $m \in \{5, 6\}$, then global coordinate recovery holds within $3\delta$ and physical translation
recovery on $S$ holds within $3(\sum_{q \in S} \varphi(q))\delta$. -/
theorem exists_global_physical_translate_of_windowMoments (N : ℕ) (S : Finset ℕ) (c e : ℕ → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N c q = 0)
    (heS : ∀ q ∈ Finset.Icc 1 N, q ∉ S → selbergMultiplesCoord N e q = 0)
    {K : ℕ} (hK : 0 < K)
    (φ5 ψ5 : (Fin 5 → ℕ) → ℕ) (φ6 ψ6 : (Fin 6 → ℕ) → ℕ) (η5 η6 : ℝ)
    (hw5 : ∀ v : Fin 5 → ℕ, |windowMoment N c v (φ5 v) K - windowMoment N e v (ψ5 v) K| ≤ η5)
    (hw6 : ∀ v : Fin 6 → ℕ, |windowMoment N c v (φ6 v) K - windowMoment N e v (ψ6 v) K| ≤ η6)
    (hb5 : η5 + (windowTransferError N 5 K c + windowTransferError N 5 K e) ≤ δ ^ 6)
    (hb6 : η6 + (windowTransferError N 6 K c + windowTransferError N 6 K e) ≤ δ ^ 6) :
    let h_rd := canonicalShift N (thresholdSourceWeights N c δ)
    (((∀ q ∈ Finset.Icc 1 N, |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 3 * δ) ∨
      (∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (HalfPeriod.reflection N h_rd c) q| ≤ 3 * δ)) ∧
      ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + t)| ≤
        3 * (∑ q ∈ S, (q.totient : ℝ)) * δ) := by
  have hpt (m : ℕ) (φ ψ : (Fin m → ℕ) → ℕ) (η : ℝ)
      (hw : ∀ v : Fin m → ℕ, |windowMoment N c v (φ v) K - windowMoment N e v (ψ v) K| ≤ η)
      (hb : η + (windowTransferError N m K c + windowTransferError N m K e) ≤ δ ^ 6)
      (v : Fin m → ℕ) :
      |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 6 := by
    have h1 := abs_windowMoment_sub_le N c v (φ v) hK
    have h2 := abs_windowMoment_sub_le N e v (ψ v) hK
    have h3 := hw v
    rw [abs_sub_comm] at h1
    have hsplit : translatedMoment N c v - translatedMoment N e v =
        (translatedMoment N c v - windowMoment N c v (φ v) K) +
          (windowMoment N c v (φ v) K - windowMoment N e v (ψ v) K) +
          (windowMoment N e v (ψ v) K - translatedMoment N e v) := by ring
    rw [hsplit]
    calc |(translatedMoment N c v - windowMoment N c v (φ v) K) +
          (windowMoment N c v (φ v) K - windowMoment N e v (ψ v) K) +
          (windowMoment N e v (ψ v) K - translatedMoment N e v)|
        ≤ |translatedMoment N c v - windowMoment N c v (φ v) K| +
          |windowMoment N c v (φ v) K - windowMoment N e v (ψ v) K| +
          |windowMoment N e v (ψ v) K - translatedMoment N e v| :=
            (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ δ ^ 6 := by linarith
  have h5 := hpt 5 φ5 ψ5 η5 hw5 hb5
  have h6 := hpt 6 φ6 ψ6 η6 hw6 hb6
  refine ⟨?_, exists_stratum_physical_translate_error N S c e δ hδ hδ1 hcS heS h5 h6⟩
  rcases exists_cutoff_independent_coordinate_and_reflection_error N c e δ hδ hδ1 h5 h6 with
    ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- For all $x, y \in \mathbb{R}$, $(|x| - |y|)^2 \le |x^2 - y^2|$. -/
theorem sq_abs_sub_abs_le_abs_sq_sub_sq (x y : ℝ) :
    (|x| - |y|) ^ 2 ≤ |x ^ 2 - y ^ 2| := by
  have hxy : x ^ 2 - y ^ 2 = (|x| - |y|) * (|x| + |y|) := by
    rw [← sq_abs x, ← sq_abs y]
    ring
  rw [hxy, abs_mul, abs_of_nonneg (by positivity : 0 ≤ |x| + |y|)]
  rcases le_total |y| |x| with hle | hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    nlinarith [abs_nonneg x, abs_nonneg y, sub_nonneg.mpr hle]
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    nlinarith [abs_nonneg x, abs_nonneg y, sub_nonpos.mpr hle]

/-- **Reduced Observation Protocol: All Selberg Coordinate Magnitudes from $N$ Lags on One Window
(`abs_selbergCoord_abs_sub_sq_le_of_single_window_lags`):**
Observing only the $N$ two-point lag covariances $g \in \{1, \dots, N\}$ on a single window of
length $K > 0$ at unknown phases $A, B$ recovers the magnitude $|Y_{N,c}(q)|$ of every mode
$q \in [2, N]$ within the harmonic-variance cutoff bound. -/
theorem abs_selbergCoord_abs_sub_sq_le_of_single_window_lags {N q : ℕ} (hq : q ∈ Finset.Icc 2 N)
    (c e : ℕ → ℝ) (A B : ℕ) {K : ℕ} (hK : 0 < K) :
    (|selbergMultiplesCoord N c q| - |selbergMultiplesCoord N e q|) ^ 2 ≤
      |lagSpectrumReadout N q (windowLagCovariance N c A K) -
        lagSpectrumReadout N q (windowLagCovariance N e B K)| +
      (harmonic N : ℝ) ^ 2 *
        (sieveWindowObservabilityConstant N * (sieveVariance N c + sieveVariance N e) / K) := by
  have hc := abs_lagSpectrumReadout_window_sub_le hq c A hK
  have he := abs_lagSpectrumReadout_window_sub_le hq e B hK
  set Lc := lagSpectrumReadout N q (windowLagCovariance N c A K)
  set Le := lagSpectrumReadout N q (windowLagCovariance N e B K)
  set Yc := selbergMultiplesCoord N c q
  set Ye := selbergMultiplesCoord N e q
  have hsplit : Yc ^ 2 - Ye ^ 2 = (Lc - Le) - (Lc - Yc ^ 2) + (Le - Ye ^ 2) := by ring
  refine (sq_abs_sub_abs_le_abs_sq_sub_sq Yc Ye).trans ?_
  rw [hsplit]
  calc |(Lc - Le) - (Lc - Yc ^ 2) + (Le - Ye ^ 2)|
      ≤ |(Lc - Le) - (Lc - Yc ^ 2)| + |Le - Ye ^ 2| := abs_add_le _ _
    _ ≤ |Lc - Le| + |Lc - Yc ^ 2| + |Le - Ye ^ 2| := by
        have := abs_sub (Lc - Le) (Lc - Yc ^ 2)
        linarith
    _ ≤ |Lc - Le| +
        (harmonic N : ℝ) ^ 2 *
          (sieveWindowObservabilityConstant N * (sieveVariance N c + sieveVariance N e) / K) := by
        have hsum : (harmonic N : ℝ) ^ 2 * (sieveWindowObservabilityConstant N * sieveVariance N c / K) +
            (harmonic N : ℝ) ^ 2 * (sieveWindowObservabilityConstant N * sieveVariance N e / K) =
            (harmonic N : ℝ) ^ 2 *
              (sieveWindowObservabilityConstant N * (sieveVariance N c + sieveVariance N e) / K) := by
          ring
        linarith

/-! ## §4. The Quantitative Bounded-Length Relation Organizing Theorem -/

/-- **Additive-to-Multiplicative Order Preservation (`orderOf_stdAddChar`):**
For every positive modulus $P$ (`[NeZero P]`) and every residue $r : \mathrm{ZMod}\,P$, the
multiplicative order of $\mathrm{ZMod.stdAddChar}\,r \in \mathbb{C}$ equals the additive order
$\mathrm{addOrderOf}\,r$. -/
theorem orderOf_stdAddChar {P : ℕ} [NeZero P] (r : ZMod P) :
    orderOf (ZMod.stdAddChar r) = addOrderOf r := by
  refine orderOf_eq_iff (addOrderOf_pos r) |>.mpr ⟨?_, fun m hm hm0 => ?_⟩
  · rw [← AddChar.map_nsmul_eq_pow, addOrderOf_nsmul_eq_zero, AddChar.map_zero_eq_one]
  · intro hpow
    rw [← AddChar.map_nsmul_eq_pow] at hpow
    have hzero : m • r = 0 := ZMod.injective_stdAddChar (by simpa using hpow)
    have hdvd : addOrderOf r ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
    exact not_le_of_gt hm (Nat.le_of_dvd hm0 hdvd)

/-- Every $r : \mathrm{ZMod}\,N!$ with $\mathrm{addOrderOf}\,r \in [1, N]$ maps under
$\mathrm{ZMod.stdAddChar}$ into `responseRoots N`. -/
theorem stdAddChar_mem_responseRoots {N : ℕ} {r : ZMod N.factorial}
    (hr : addOrderOf r ∈ Finset.Icc 1 N) :
    ZMod.stdAddChar r ∈ responseRoots N := by
  refine Finset.mem_biUnion.mpr ⟨addOrderOf r, hr, ?_⟩
  rw [Polynomial.mem_nthRootsFinset (addOrderOf_pos r), ← AddChar.map_nsmul_eq_pow,
    addOrderOf_nsmul_eq_zero, AddChar.map_zero_eq_one]

/-- **Bridge from Zero-Sum Frequency Words in $\mathrm{ZMod}\,N!$ to Multiplicative Zero-Product Tuples:**
Every zero-sum word $r : \mathrm{Fin}\,m \to \mathrm{ZMod}\,N!$ ($\sum_i r_i = 0$) whose orders lie
in $[1, N]$ maps via $\mathrm{ZMod.stdAddChar}$ to an element of `zeroProductTuples N m` whose
`relationCoeff` equals $\prod_i Y_{N,c}(\mathrm{addOrderOf}\,r_i)$. -/
theorem stdAddChar_mem_zeroProductTuples {N m : ℕ} {r : Fin m → ZMod N.factorial}
    (hz : (∑ i, r i) = 0) (hr : ∀ i, addOrderOf (r i) ∈ Finset.Icc 1 N) :
    (fun i => ZMod.stdAddChar (r i)) ∈ zeroProductTuples N m := by
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
    stdAddChar_mem_responseRoots (hr i), ?_⟩
  have hmap : ∀ s : Finset (Fin m),
      (∏ i ∈ s, ZMod.stdAddChar (r i)) = ZMod.stdAddChar (∑ i ∈ s, r i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, AddChar.map_add_eq_mul]
  rw [hmap Finset.univ, hz, AddChar.map_zero_eq_one]

theorem relationCoeff_stdAddChar {N m : ℕ} (c : ℕ → ℝ) (r : Fin m → ZMod N.factorial) :
    relationCoeff N c (fun i => ZMod.stdAddChar (r i)) =
      ∏ i, selbergMultiplesCoord N c (addOrderOf (r i)) := by
  unfold relationCoeff
  simp_rw [orderOf_stdAddChar]

/-- The elementary sign character at mode $q$, flipping the sign of mode $q$ and fixing all others. -/
def modeSignChar (q : ℕ) (u : ℕ) : ℝ :=
  if u = q then -1 else 1

theorem modeSignChar_self (q : ℕ) : modeSignChar q q = -1 := by
  simp [modeSignChar]

theorem modeSignChar_ne {q u : ℕ} (h : u ≠ q) : modeSignChar q u = 1 := by
  simp [modeSignChar, h]

theorem modeSignChar_values (q u : ℕ) : modeSignChar q u = 1 ∨ modeSignChar q u = -1 := by
  unfold modeSignChar
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Missing-Mode Spikes Are Elementary Sign-Character Twists (`spikeWeights_neg_eq_scaledSelbergRow`):**
For every mode $q \in [1, N]$ and amplitude $t \in \mathbb{R}$, the opposite missing-mode spike
$\mathrm{spikeWeights}\,N\,b\,q\,(-t)$ has identical Selberg coordinates on $[1, N]$, identical
divisor weights on $[1, N]$, identical response sequence `sieveSeq`, and identical translated
moments in all degrees to the sign-twisted row
$\mathrm{scaledSelbergRow}\,N\,(\mathrm{spikeWeights}\,N\,b\,q\,t)\,(\mathrm{modeSignChar}\,q)$. -/
theorem spikeWeights_neg_eq_scaledSelbergRow {N q : ℕ} (hq : q ∈ Finset.Icc 1 N)
    (b : ℕ → ℝ) (t : ℝ) :
    (∀ u ∈ Finset.Icc 1 N,
      selbergMultiplesCoord N (spikeWeights N b q (-t)) u =
        selbergMultiplesCoord N (scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q)) u) ∧
    (∀ d ∈ Finset.Icc 1 N,
      spikeWeights N b q (-t) d =
        scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q) d) ∧
    (∀ n : ℕ,
      sieveSeq N (spikeWeights N b q (-t)) n =
        sieveSeq N (scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q)) n) ∧
    (∀ (m : ℕ) (v : Fin m → ℕ),
      translatedMoment N (spikeWeights N b q (-t)) v =
        translatedMoment N (scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q)) v) := by
  have hcoord : ∀ u ∈ Finset.Icc 1 N,
      selbergMultiplesCoord N (spikeWeights N b q (-t)) u =
        selbergMultiplesCoord N (scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q)) u := by
    intro u hu
    rw [coordinate_spikeWeights N b q (-t) hq u,
      selbergMultiplesCoord_scaledSelbergRow (spikeWeights N b q t) (modeSignChar q) hu,
      coordinate_spikeWeights N b q t hq u]
    unfold spikeProfile modeSignChar
    split_ifs <;> ring
  have hweights : ∀ d ∈ Finset.Icc 1 N,
      spikeWeights N b q (-t) d =
        scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q) d :=
    (sieve_active_coefficients_eq_iff N _ _).mpr hcoord
  have hseq : ∀ n : ℕ,
      sieveSeq N (spikeWeights N b q (-t)) n =
        sieveSeq N (scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q)) n :=
    fun n => Finset.sum_congr rfl fun d hd => hweights d (Finset.mem_filter.mp hd).1
  refine ⟨hcoord, hweights, hseq, fun m v => ?_⟩
  unfold translatedMoment
  congr 2
  ext n
  exact Finset.prod_congr rfl fun i _ => hseq (n + v i)

/-- **Exact Parseval Relation-Energy Identity for Missing-Mode Spikes
(`sum_sq_translatedMoment_spikeWeights_eq`):**
The mean-square degree-$m$ moment difference between $\mathrm{spikeWeights}\,N\,b\,q\,t$ and
$\mathrm{spikeWeights}\,N\,b\,q\,(-t)$ equals $4(N!)^m$ times the relation energy of zero-product
tuples with odd $q$-multiplicity ($\prod_i \mathrm{modeSignChar}\,q\,(\mathrm{ord}\,\zeta_i) = -1$). -/
theorem sum_sq_translatedMoment_spikeWeights_eq {N q : ℕ} (hq : q ∈ Finset.Icc 1 N)
    (b : ℕ → ℝ) (t : ℝ) (m : ℕ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
        (translatedMoment N (spikeWeights N b q t) v -
          translatedMoment N (spikeWeights N b q (-t)) v) ^ 2 =
      4 * (N.factorial : ℝ) ^ m * ∑ ζ ∈ (zeroProductTuples N m).filter
        (fun ζ => ∏ i, modeSignChar q (orderOf (ζ i)) = -1),
          relationCoeff N (spikeWeights N b q t) ζ ^ 2 := by
  have hmom := (spikeWeights_neg_eq_scaledSelbergRow hq b t).2.2.2 m
  have hrw : ∀ v : Fin m → ℕ,
      (translatedMoment N (spikeWeights N b q t) v -
        translatedMoment N (spikeWeights N b q (-t)) v) ^ 2 =
      (translatedMoment N (scaledSelbergRow N (spikeWeights N b q t) (modeSignChar q)) v -
        translatedMoment N (spikeWeights N b q t) v) ^ 2 := by
    intro v
    rw [hmom v]
    ring
  simp_rw [hrw]
  exact sum_sq_translatedMoment_signFlip_sub_eq N m (spikeWeights N b q t) (modeSignChar_values q)

/-- **Half I of the Organizing Theorem: Quantitative Sign-Character Relation Dichotomy
(`quantitative_sign_relation_dichotomy`):**
For any row $c$, any sign character $\varepsilon : \mathbb{N} \to \{\pm 1\}$, and any degree $m \in \mathbb{N}$:
1. The complete-period mean-square moment separation equals $4$ times the odd-relation energy.
2. Whenever a layer-admissible active $m$-tuple $q : \mathrm{Fin}\,m \to \mathbb{N}$ has
   $\prod_i \varepsilon(q_i) = -1$, there exist a primitive zero-product relation $\zeta \in \mathcal{Z}_{N,m}$
   with $\mathrm{orderOf}(\zeta_i) = q_i$ and a shift vector $v \in [0, N!)^m$ such that both the
   normalized mean-square moment energy and $|M_m(c_\varepsilon; v) - M_m(c; v)|^2$ are at least
   $4 \prod_i Y_{N,c}(q_i)^2$.
3. Conversely, if no layer-admissible active $m$-tuple has $\prod_i \varepsilon(q_i) \ne 1$, then
   $M_m(c_\varepsilon; v) = M_m(c; v)$ for all $v : \mathrm{Fin}\,m \to \mathbb{N}$. -/
theorem quantitative_sign_relation_dichotomy (N m : ℕ) (c : ℕ → ℝ) {ε : ℕ → ℝ}
    (hε : ∀ q, ε q = 1 ∨ ε q = -1) :
    (∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
        (translatedMoment N (scaledSelbergRow N c ε) v - translatedMoment N c v) ^ 2 =
      4 * (N.factorial : ℝ) ^ m * ∑ ζ ∈ (zeroProductTuples N m).filter
        (fun ζ => ∏ i, ε (orderOf (ζ i)) = -1), relationCoeff N c ζ ^ 2) ∧
    (∀ q : Fin m → ℕ,
      (∀ i, q i ∈ Finset.Icc 1 N ∧ selbergMultiplesCoord N c (q i) ≠ 0) →
      ∏ i, ε (q i) = -1 → IsLayerAdmissible q →
      (4 * (N.factorial : ℝ) ^ m * (∏ i, selbergMultiplesCoord N c (q i)) ^ 2 ≤
        ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
          (translatedMoment N (scaledSelbergRow N c ε) v - translatedMoment N c v) ^ 2) ∧
      ∃ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
        2 * |∏ i, selbergMultiplesCoord N c (q i)| ≤
          |translatedMoment N (scaledSelbergRow N c ε) v - translatedMoment N c v|) ∧
    ((¬∃ q : Fin m → ℕ,
        (∀ i, q i ∈ Finset.Icc 1 N ∧ selbergMultiplesCoord N c (q i) ≠ 0) ∧
          ∏ i, ε (q i) ≠ 1 ∧ IsLayerAdmissible q) →
      ∀ v : Fin m → ℕ, translatedMoment N (scaledSelbergRow N c ε) v = translatedMoment N c v) := by
  classical
  refine ⟨sum_sq_translatedMoment_signFlip_sub_eq N m c hε, ?_, ?_⟩
  · intro q hq hprod_neg hadm
    obtain ⟨ζ, hζ, hζ1⟩ := exists_zeroProduct_of_isLayerAdmissible q
      (fun i => (Finset.mem_Icc.mp (hq i).1).1) hadm
    have hζ_mem : ζ ∈ (zeroProductTuples N m).filter (fun ζ => ∏ i, ε (orderOf (ζ i)) = -1) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
        primitiveRoot_mem_responseRoots (hq i).1 (hζ i), hζ1⟩, ?_⟩
      have hord : ∀ i, orderOf (ζ i) = q i := fun i => (hζ i).eq_orderOf.symm
      simp_rw [hord]
      exact hprod_neg
    have hcoeff : relationCoeff N c ζ = ∏ i, selbergMultiplesCoord N c (q i) := by
      unfold relationCoeff
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(hζ i).eq_orderOf]
    have hsingle : (∏ i, selbergMultiplesCoord N c (q i)) ^ 2 ≤
        ∑ ξ ∈ (zeroProductTuples N m).filter (fun ξ => ∏ i, ε (orderOf (ξ i)) = -1),
          relationCoeff N c ξ ^ 2 := by
      rw [← hcoeff]
      exact Finset.single_le_sum (fun _ _ => sq_nonneg _) hζ_mem
    have hsum_le : 4 * (N.factorial : ℝ) ^ m * (∏ i, selbergMultiplesCoord N c (q i)) ^ 2 ≤
        ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
          (translatedMoment N (scaledSelbergRow N c ε) v - translatedMoment N c v) ^ 2 := by
      rw [sum_sq_translatedMoment_signFlip_sub_eq N m c hε]
      exact mul_le_mul_of_nonneg_left hsingle (by positivity)
    refine ⟨hsum_le, ?_⟩
    set V := Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial)
    set B := 2 * |∏ i, selbergMultiplesCoord N c (q i)|
    by_contra! hall
    have hB_sq : B ^ 2 = 4 * (∏ i, selbergMultiplesCoord N c (q i)) ^ 2 := by
      dsimp [B]
      rw [mul_pow, sq_abs]
      ring
    have hV_nonempty : V.Nonempty := ⟨fun _ => 0,
      Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr (Nat.factorial_pos N)⟩
    have hlt : ∑ v ∈ V,
        (translatedMoment N (scaledSelbergRow N c ε) v - translatedMoment N c v) ^ 2 <
        (N.factorial : ℝ) ^ m * B ^ 2 := by
      calc ∑ v ∈ V, (translatedMoment N (scaledSelbergRow N c ε) v - translatedMoment N c v) ^ 2
          < ∑ _v ∈ V, B ^ 2 := by
            refine Finset.sum_lt_sum_of_nonempty hV_nonempty fun v hv => ?_
            rw [← sq_abs]
            exact pow_lt_pow_left₀ (hall v hv) (abs_nonneg _) two_ne_zero
        _ = (N.factorial : ℝ) ^ m * B ^ 2 := by
            rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    rw [hB_sq] at hlt
    linarith
  · intro hno v
    by_contra hne
    exact hno ((exists_translatedMoment_ne_iff N c ε m).mp ⟨v, hne⟩)

/-- **Half II of the Organizing Theorem: Quantitative Missing-Mode Visibility Dichotomy via Bounded-Length Relations
(`quantitative_visibility_relation_dichotomy`):**
For any base row $b : \mathbb{N} \to \mathbb{R}$ and any missing mode $q \in [1, N] \setminus \mathrm{activeModes}\,N\,b$:
1. **Visible case (`Visible N (activeModes N b) q`):**
   - *Relation energy & shift-realization lower bound*: There exist $m \in \{5, 6\}$ and a zero-sum
     word $r : \mathrm{Fin}\,m \to \mathrm{ZMod}\,N!$ with $\mathrm{addOrderOf}(r_i) = q$ and
     companion product $B_r = \prod_{j \ne i} |Y_{N,b}(\mathrm{addOrderOf}\,r_j)| > 0$ such that
     for every $t \in \mathbb{R}$, $\zeta_r = \mathrm{stdAddChar} \circ r \in \mathcal{Z}_{N,m}$ has
     $\prod_j \mathrm{modeSignChar}\,q\,(\mathrm{ord}\,\zeta_{r,j}) = -1$,
     $$4 (N!)^m B_r^2 t^2 \le \sum_{v \in [0, N!)^m} \bigl(M_m(b_{+t}; v) - M_m(b_{-t}; v)\bigr)^2,$$
     and there exists $v \in [0, N!)^m$ with $2 B_r |t| \le |M_m(b_{+t}; v) - M_m(b_{-t}; v)|$.
   - *Lipschitz coordinate recovery*: For any two rows $c, e$ bounded by $M \ge 1$ in Selberg
     coordinates, $\varepsilon$-close on $\mathrm{activeModes}\,N\,b$ (where $|Y_{N,c}| \ge 1$), and
     $\varepsilon$-close in fifth and sixth moments ($\varepsilon \ge 0$),
     $|Y_{N,c}(q) - Y_{N,e}(q)| \le (1 + 6 M^7) \varepsilon$.
2. **Invisible case (`¬Visible N (activeModes N b) q`):**
   - *Cubic moment and relation-energy upper bound*: For every $t \in [0, 1]$ and $m \in \{5, 6\}$,
     every shift vector $v : \mathrm{Fin}\,m \to \mathbb{N}$ satisfies
     $|M_m(b_{+t}; v) - M_m(b_{-t}; v)| \le 2 (N!)^6 (\mathrm{coordinateBudget}\,N\,b)^6 t^3$,
     and the relation-spectrum energy satisfies
     $\sum_{\zeta \in \mathcal{Z}_{N,m}} (A_{b_{+t}}(\zeta) - A_{b_{-t}}(\zeta))^2 \le 4 (N!)^{12} (\mathrm{coordinateBudget}\,N\,b)^{12} t^6$.
   - *Linear clock-period $L^2$ realization lower bound*: For all $t \in \mathbb{R}$ and any common
     multiple $M$ of $[1, N]$, $\sum_{k=1}^M (s_{N,b_{+t}}(k) - s_{N,b_{-t}}(k))^2 = 4 M \varphi(q) t^2$. -/
theorem quantitative_visibility_relation_dichotomy {N q : ℕ} (hq : q ∈ Finset.Icc 1 N)
    (b : ℕ → ℝ) (hq_miss : q ∉ activeModes N b) :
    (Visible N (activeModes N b) q →
      (∃ (m : ℕ), (m = 5 ∨ m = 6) ∧ ∃ (r : Fin m → ZMod N.factorial) (i : Fin m),
        (∑ j, r j) = 0 ∧ addOrderOf (r i) = q ∧
        (∀ j, j ≠ i → addOrderOf (r j) ∈ activeModes N b) ∧
        0 < (∏ j ∈ Finset.univ.erase i, |selbergMultiplesCoord N b (addOrderOf (r j))|) ∧
        ∀ t : ℝ,
          4 * (N.factorial : ℝ) ^ m *
            ((∏ j ∈ Finset.univ.erase i, |selbergMultiplesCoord N b (addOrderOf (r j))|) * |t|) ^ 2 ≤
            ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
              (translatedMoment N (spikeWeights N b q t) v -
                translatedMoment N (spikeWeights N b q (-t)) v) ^ 2 ∧
          ∃ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
            2 * (∏ j ∈ Finset.univ.erase i, |selbergMultiplesCoord N b (addOrderOf (r j))|) * |t| ≤
              |translatedMoment N (spikeWeights N b q t) v -
                translatedMoment N (spikeWeights N b q (-t)) v|) ∧
      (∀ (c e : ℕ → ℝ) (M ε : ℝ), 1 ≤ M → 0 ≤ ε →
        (∀ u ∈ activeModes N b, 1 ≤ |selbergMultiplesCoord N c u|) →
        (∀ u ∈ Finset.Icc 1 N, |selbergMultiplesCoord N c u| ≤ M) →
        (∀ u ∈ Finset.Icc 1 N, |selbergMultiplesCoord N e u| ≤ M) →
        (∀ u ∈ activeModes N b, |selbergMultiplesCoord N c u - selbergMultiplesCoord N e u| ≤ ε) →
        (∀ v : Fin 5 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ ε) →
        (∀ v : Fin 6 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ ε) →
        |selbergMultiplesCoord N c q - selbergMultiplesCoord N e q| ≤ (1 + 6 * M ^ 7) * ε)) ∧
    (¬Visible N (activeModes N b) q →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (∀ (m : ℕ), (m = 5 ∨ m = 6) →
          (∀ v : Fin m → ℕ,
            |translatedMoment N (spikeWeights N b q t) v -
              translatedMoment N (spikeWeights N b q (-t)) v| ≤
              2 * (N.factorial : ℝ) ^ 6 * (coordinateBudget N b) ^ 6 * t ^ 3) ∧
          (∑ ζ ∈ zeroProductTuples N m,
            (relationCoeff N (spikeWeights N b q t) ζ -
              relationCoeff N (spikeWeights N b q (-t)) ζ) ^ 2 ≤
            (2 * (N.factorial : ℝ) ^ 6 * (coordinateBudget N b) ^ 6 * t ^ 3) ^ 2)) ∧
        (∀ M : ℕ, (∀ d ∈ Finset.Icc 1 N, d ∣ M) →
          ∑ k ∈ Finset.Icc 1 M,
            (sieveSeq N (spikeWeights N b q t) k - sieveSeq N (spikeWeights N b q (-t)) k) ^ 2 =
            4 * (M : ℝ) * (q.totient : ℝ) * t ^ 2)) := by
  classical
  have hS_sub : activeModes N b ⊆ Finset.Icc 1 N := fun u hu => (Finset.mem_filter.mp hu).1
  refine ⟨fun hvis => ⟨?_, ?_⟩, fun hinv t ht ht1 => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm, r, hz, i, hi, hr⟩ := hvis
    set s := Finset.univ.erase i
    set B := ∏ j ∈ s, |selbergMultiplesCoord N b (addOrderOf (r j))|
    have hB_pos : 0 < B := by
      refine Finset.prod_pos fun j hj => abs_pos.mpr ?_
      exact (Finset.mem_filter.mp (hr j (Finset.mem_erase.mp hj).1)).2
    have hr_Icc : ∀ j : Fin m, addOrderOf (r j) ∈ Finset.Icc 1 N := by
      intro j
      by_cases hji : j = i
      · subst hji; rw [hi]; exact hq
      · exact hS_sub (hr j hji)
    refine ⟨m, hm, r, i, hz, hi, hr, hB_pos, fun t => ?_⟩
    let ζ : Fin m → ℂ := fun j => ZMod.stdAddChar (r j)
    have hζ_mem : ζ ∈ (zeroProductTuples N m).filter
        (fun ξ => ∏ j, modeSignChar q (orderOf (ξ j)) = -1) := by
      refine Finset.mem_filter.mpr ⟨stdAddChar_mem_zeroProductTuples hz hr_Icc, ?_⟩
      dsimp only [ζ]
      simp_rw [orderOf_stdAddChar]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hi, modeSignChar_self]
      have hrest : ∏ j ∈ s, modeSignChar q (addOrderOf (r j)) = 1 := by
        refine Finset.prod_eq_one fun j hj => modeSignChar_ne fun h_eq => ?_
        have hmem := hr j (Finset.mem_erase.mp hj).1
        rw [h_eq] at hmem
        exact hq_miss hmem
      rw [hrest, mul_one]
    have hcoeff_sq : relationCoeff N (spikeWeights N b q t) ζ ^ 2 = (B * |t|) ^ 2 := by
      dsimp only [ζ]
      rw [relationCoeff_stdAddChar]
      have hprod_abs : |∏ j, selbergMultiplesCoord N (spikeWeights N b q t) (addOrderOf (r j))| =
          B * |t| := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), abs_mul,
          coordinate_spikeWeights N b q t hq, hi]
        simp only [spikeProfile, if_true]
        have hrest : |∏ j ∈ s, selbergMultiplesCoord N (spikeWeights N b q t) (addOrderOf (r j))| = B := by
          rw [Finset.abs_prod]
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [coordinate_spikeWeights N b q t hq]
          have hne : addOrderOf (r j) ≠ q := fun h_eq => by
            have hmem := hr j (Finset.mem_erase.mp hj).1
            rw [h_eq] at hmem
            exact hq_miss hmem
          simp [spikeProfile, hne]
        rw [hrest, mul_comm]
      rw [← sq_abs, hprod_abs]
    have hsum_le : 4 * (N.factorial : ℝ) ^ m * (B * |t|) ^ 2 ≤
        ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial),
          (translatedMoment N (spikeWeights N b q t) v -
            translatedMoment N (spikeWeights N b q (-t)) v) ^ 2 := by
      rw [sum_sq_translatedMoment_spikeWeights_eq hq b t m, ← hcoeff_sq]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun _ _ => sq_nonneg _) hζ_mem) (by positivity)
    refine ⟨hsum_le, ?_⟩
    set V := Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial)
    by_contra! hall
    have hV_nonempty : V.Nonempty := ⟨fun _ => 0,
      Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr (Nat.factorial_pos N)⟩
    have hlt : ∑ v ∈ V,
        (translatedMoment N (spikeWeights N b q t) v -
          translatedMoment N (spikeWeights N b q (-t)) v) ^ 2 <
        (N.factorial : ℝ) ^ m * (2 * B * |t|) ^ 2 := by
      calc ∑ v ∈ V, (translatedMoment N (spikeWeights N b q t) v -
            translatedMoment N (spikeWeights N b q (-t)) v) ^ 2
          < ∑ _v ∈ V, (2 * B * |t|) ^ 2 := by
            refine Finset.sum_lt_sum_of_nonempty hV_nonempty fun v hv => ?_
            rw [← sq_abs]
            exact pow_lt_pow_left₀ (hall v hv) (abs_nonneg _) two_ne_zero
        _ = (N.factorial : ℝ) ^ m * (2 * B * |t|) ^ 2 := by
            rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have heq_sq : (N.factorial : ℝ) ^ m * (2 * B * |t|) ^ 2 =
        4 * (N.factorial : ℝ) ^ m * (B * |t|) ^ 2 := by ring
    linarith
  · intro c e M ε hM hε hcS hcM heM hclose h5 h6
    exact coordinate_error_of_visible N (activeModes N b) c e M ε hS_sub hM hε
      hcS hcM heM hclose h5 h6 q hq hvis
  · intro m hm
    have hraw : ∀ v : Fin m → ℕ,
        |translatedMoment N (spikeWeights N b q t) v -
          translatedMoment N (spikeWeights N b q (-t)) v| ≤
          2 * (N.factorial : ℝ) ^ 6 * (coordinateBudget N b) ^ 6 * t ^ 3 :=
      fun v => invisible_raw_error N b q hq hinv t ht ht1 m hm v
    refine ⟨hraw, ?_⟩
    set K := 2 * (N.factorial : ℝ) ^ 6 * (coordinateBudget N b) ^ 6 * t ^ 3
    set V := Fintype.piFinset (fun _ : Fin m => Finset.range N.factorial)
    have hP : (0 : ℝ) < (N.factorial : ℝ) ^ m := by positivity
    have hsum : ∑ v ∈ V,
        (translatedMoment N (spikeWeights N b q t) v -
          translatedMoment N (spikeWeights N b q (-t)) v) ^ 2 ≤
        (N.factorial : ℝ) ^ m * K ^ 2 := by
      calc ∑ v ∈ V, (translatedMoment N (spikeWeights N b q t) v -
            translatedMoment N (spikeWeights N b q (-t)) v) ^ 2
          ≤ ∑ _v ∈ V, K ^ 2 := Finset.sum_le_sum fun v _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hraw v) 2
        _ = (N.factorial : ℝ) ^ m * K ^ 2 := by
            rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    rw [sum_sq_translatedMoment_sub_eq] at hsum
    exact le_of_mul_le_mul_left hsum hP
  · intro M hdvd
    rw [sum_sieveSeq_sub_sq_eq_selberg_of_forall_dvd N M _ _ hdvd]
    have hterm : ∑ u ∈ Finset.Icc 1 N, (u.totient : ℝ) *
        (selbergMultiplesCoord N (spikeWeights N b q t) u -
          selbergMultiplesCoord N (spikeWeights N b q (-t)) u) ^ 2 =
        4 * (q.totient : ℝ) * t ^ 2 := by
      have hrw : ∀ u ∈ Finset.Icc 1 N,
          (u.totient : ℝ) *
            (selbergMultiplesCoord N (spikeWeights N b q t) u -
              selbergMultiplesCoord N (spikeWeights N b q (-t)) u) ^ 2 =
          if u = q then 4 * (q.totient : ℝ) * t ^ 2 else 0 := by
        intro u _
        rw [coordinate_spikeWeights N b q t hq u, coordinate_spikeWeights N b q (-t) hq u]
        unfold spikeProfile
        split_ifs with hu
        · subst hu; ring
        · ring
      rw [Finset.sum_congr rfl hrw, Finset.sum_ite_eq', if_pos hq]
    rw [hterm]
    ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
