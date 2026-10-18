import GaloisForLFunctions.TransHorizonIncidenceMechanics.RadicalCheckpointSignRigidityAndGaugeLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SecondAndThirdBandRenormalizedDefectCalculus
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SuccessorStateObstructionAndPhaseRefinement

/-!
# Short-Window Shifted Correlation Defects and Iso-State Classification (`ShortWindowCorrelationDefectAndIsoStateClassification`)

## 1. Central Problem & Classical Baseline ($M \ll L_N = \operatorname{lcm}(1, \dots, N)$)

In the classical theory of Selberg quadratic forms (Selberg 1947) and shifted correlations of
finite Ramanujan expansions (Coppola–Murty–Saha 2016, `arXiv:1612.03136`), let
$$s_{N,c}(k) = \sum_{\substack{d \mid k \\ d \le N}} c(d) = \sum_{q=1}^N Y_q c_q(k), \qquad
  Y_q = \sum_{\substack{d \le N \\ q \mid d}} \frac{c(d)}{d}.$$
On a short interval $[M_0 + 1, M_0 + M]$ of length $M \ll L_N = \operatorname{lcm}(1, \dots, N)$
starting at an arbitrary offset $M_0 \in \mathbb{N}$, expanding the second moment
$V_N(M_0, M; c) = \sum_{k=M_0+1}^{M_0+M} s_{N,c}(k)^2$ and the unit-shifted correlation
$C_N(M_0, M; c) = \sum_{k=M_0+1}^{M_0+M} s_{N,c}(k) s_{N,c}(k + 1)$ by swapping summation over
divisor pairs $(d_1, d_2) \in [1, N]^2$ produces:
- The complete-period main-term difference
  $$M \sum_{q=1}^N \mu(q) Y_q^2 - M \sum_{q=1}^N \varphi(q) Y_q^2 =
    -M \sum_{q=2}^N \bigl(\varphi(q) - \mu(q)\bigr) Y_q^2 =
    -M \cdot \operatorname{sieveSuccessorReserve}(N, c),$$
- Plus $N^2$ incomplete-period LCM fractional-part jumps and $N^2$ coprime CRT remainder jumps:
  $$\Delta R_{\mathrm{Comb}}(N, M_0, M; c) =
    \bigl(\operatorname{signedLcmFractDefect}(N, M_0 + M, c) -
      \operatorname{signedLcmFractDefect}(N, M_0, c)\bigr) +
    \bigl(\operatorname{bezoutSawtoothRemainderForm}(M_0 + M, N, c) -
      \operatorname{bezoutSawtoothRemainderForm}(M_0, N, c)\bigr).$$
In the classical baseline, bounding these $N^2$ incomplete-period remainder jumps via the triangle
inequality yields an error of $O\bigl((\sum_{d=1}^N |c(d)|)^2\bigr) = O(N^2)$, which exceeds the
main term whenever $M \ll N^2$.

## 2. Organizing Principle: Endpoint Fiber Collisions Replace Period Return

Define the **short-window renormalized correlation defect** on $[M_0 + 1, M_0 + M]$:
$$\widetilde{\mathcal{D}}_N(M_0, M; c) :=
  \widetilde{\mathcal{D}}_N(M_0 + M; c) - \widetilde{\mathcal{D}}_N(M_0; c) =
  C_N(M_0, M; c) - V_N(M_0, M; c).$$
By short-window Dirichlet polarization (`two_mul_shortWindowRenormalizedDefect_eq`),
$$2\,\widetilde{\mathcal{D}}_N(M_0, M; c) =
  -\sum_{k=M_0+1}^{M_0+M} \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2 +
    s_{N,c}(M_0 + M + 1)^2 - s_{N,c}(M_0 + 1)^2.$$
Crucially, the boundary error $s_{N,c}(M_0 + M + 1)^2 - s_{N,c}(M_0 + 1)^2$ does **not** require
the full additive phase $k \bmod L_N$ to return ($L_N \mid M$); it depends **only on the
multiplicative observation fibers** $\sigma_N(M_0 + M + 1)$ and $\sigma_N(M_0 + 1)$ (or the
radical fibers $\operatorname{rad}_N(M_0 + M + 1)$ and $\operatorname{rad}_N(M_0 + 1)$ for
squarefree-supported weights).

## 3. Main Theorems (Labelled Against the Classical Baseline)

1. **Exact Short-Window Remainder & Polarization Identity — `[New formulation / synthesis]`
   (`shortWindowRenormalizedDefect_eq_corr_sub_var`,
   `shortWindowRenormalizedDefect_eq_classical_remainders_sub_reserve`,
   `two_mul_shortWindowRenormalizedDefect_eq`):**
   Links the short-window difference of the classical Selberg and Coppola–Murty–Saha remainders on
   $[M_0 + 1, M_0 + M]$ directly to $-\frac{1}{2} E_N(M_0, M; c) + \frac{1}{2}(s_{N,c}(M_0+M+1)^2 - s_{N,c}(M_0+1)^2)$
   for all $N, M_0, M \in \mathbb{N}$.

2. **Sharp Iso-State & Iso-Radical Short-Window Classification — `[Candidate new theorem]`
   (`forall_weight_shortWindowRenormalizedDefect_nonpos_iff_state_eq`,
   `forall_squarefree_shortWindowRenormalizedDefect_nonpos_iff_radicalState_eq`):**
   For every horizon $N : \mathbb{N}$, starting phase $M_0 : \mathbb{N}$, and window length
   $M : \mathbb{N}$:
   - $\widetilde{\mathcal{D}}_N(M_0, M; c) \le 0$ for **all** weights $c : \mathbb{N} \to \mathbb{R}$
     **if and only if** $\operatorname{horizonObservationState}(N, M_0 + M + 1) = \operatorname{horizonObservationState}(N, M_0 + 1)$.
   - $\widetilde{\mathcal{D}}_N(M_0, M; c) \le 0$ for **all** squarefree-supported weights $c$
     **if and only if** $\operatorname{horizonRadicalState}(N, M_0 + M + 1) = \operatorname{horizonRadicalState}(N, M_0 + 1)$.

3. **Reusable Short-Window Contraction Across Three Arithmetic Regimes — `[Candidate new theorems]`:**
   - **Divisor-Multiplied & Power Windows (`shortWindowRenormalizedDefect_mul_dvd_eq_neg_half_dirichlet`,
     `shortWindowRenormalizedDefect_pow_eq_neg_half_dirichlet`):**
     For any squarefree-supported weight $c$, $a \ge 1$, $d \mid a$, and $m \ge 1$, the short
     windows $[a, d \cdot a - 1]$ and $[a, a^m - 1]$ have zero boundary defect and satisfy
     $2\widetilde{\mathcal{D}}_N = -E_N \le 0$ at every horizon $N$.
   - **Starting-Phase-Free Right-Zero-Cone Contraction for $\mu$
     (`shortWindowRenormalizedDefect_nonpos_of_right_endpoint_eq_zero`,
     `shortWindowRenormalizedDefect_moebiusReal_nonpos_of_right_zero_cone`):**
     Whenever the right endpoint $M_0 + M + 1 = q \cdot r$ lies in the Möbius zero cone
     ($2 \le q \le N$ and $r$ $N$-rough), $\widetilde{\mathcal{D}}_N(M_0, M; \mu) \le -\frac{1}{2} s_{N,\mu}(M_0 + 1)^2 \le 0$
     for **every** starting offset $M_0 \in \mathbb{N}$, regardless of how large $|s_{N,\mu}(M_0 + 1)|$ is.
   - **Rough-Start Power-Damped Windows (`shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_le_three_mul_nonpos`):**
     For $\varepsilon \ge 0$, whenever $M_0 + 1$ is $N$-rough and $2 \le M_0 + M + 1 \le 3N$,
     $\widetilde{\mathcal{D}}_N(M_0, M; c_\varepsilon) \le 0$.

4. **Matched-Assumption Domination Over Classical $\ell^1$ Remainder Bounds — `[Corollary]`
   (`abs_sieveSeq_le_sum_abs`, `shortWindowRenormalizedDefect_le_half_sum_abs_sq`):**
   For all $N, M_0, M \in \mathbb{N}$ and all weights $c$,
   $\widetilde{\mathcal{D}}_N(M_0, M; c) \le \frac{1}{2} s_{N,c}(M_0 + M + 1)^2 \le \frac{1}{2}(\sum_{d=1}^N |c(d)|)^2$.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Short-Window Observables & Exact Classical Remainder Comparison -/

/-- **Short-Window Second Moment (`shortWindowVariance`):**
The uncentered $L^2$ sum $\sum_{k=M_0+1}^{M_0+M} s_{N,c}(k)^2$ on $[M_0 + 1, M_0 + M]$. -/
def shortWindowVariance (N M₀ M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M), sieveSeq N c k ^ (2 : ℕ)

/-- **Short-Window Shifted Correlation (`shortWindowShiftedCorrelation`):**
The unit-shifted correlation $\sum_{k=M_0+1}^{M_0+M} s_{N,c}(k) s_{N,c}(k + 1)$ on
$[M_0 + 1, M_0 + M]$. -/
def shortWindowShiftedCorrelation (N M₀ M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M), sieveSeq N c k * sieveSeq N c (k + 1)

/-- **Short-Window Unit-Step Dirichlet Energy (`shortWindowDirichletEnergy`):**
The forward-difference energy $\sum_{k=M_0+1}^{M_0+M} (s_{N,c}(k + 1) - s_{N,c}(k))^2$ on
$[M_0 + 1, M_0 + M]$. -/
def shortWindowDirichletEnergy (N M₀ M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)

/-- **Short-Window Renormalized Correlation Defect (`shortWindowRenormalizedDefect`):**
The increment $\widetilde{\mathcal{D}}_N(M_0 + M; c) - \widetilde{\mathcal{D}}_N(M_0; c)$ across the
short window $[M_0 + 1, M_0 + M]$. -/
def shortWindowRenormalizedDefect (N M₀ M : ℕ) (c : ℕ → ℝ) : ℝ :=
  sieveRenormalizedPrefixDefect N (M₀ + M) c - sieveRenormalizedPrefixDefect N M₀ c

/-- Disjoint splitting of `Finset.Icc 1 (M₀ + M)` into `Finset.Icc 1 M₀` and
`Finset.Icc (M₀ + 1) (M₀ + M)`. -/
theorem sum_Icc_one_add_sub_eq_sum_Icc (M₀ M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (M₀ + M), f k) - (∑ k ∈ Finset.Icc 1 M₀, f k) =
      ∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M), f k := by
  have hsplit : Finset.Icc 1 (M₀ + M) =
      Finset.Icc 1 M₀ ∪ Finset.Icc (M₀ + 1) (M₀ + M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 M₀) (Finset.Icc (M₀ + 1) (M₀ + M)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]

/-- **Short-Window Forward-Difference Sum Formula
(`shortWindowRenormalizedDefect_eq_sum_mul_addDiff`):**
For every $N, M_0, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) =
  \sum_{k=M_0+1}^{M_0+M} s_{N,c}(k) \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr).$$ -/
theorem shortWindowRenormalizedDefect_eq_sum_mul_addDiff (N M₀ M : ℕ) (c : ℕ → ℝ) :
    shortWindowRenormalizedDefect N M₀ M c =
      ∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M),
        sieveSeq N c k * (sieveSeq N c (k + 1) - sieveSeq N c k) := by
  unfold shortWindowRenormalizedDefect
  rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff,
    sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff,
    sum_Icc_one_add_sub_eq_sum_Icc]

/-- **Short-Window Correlation-Minus-Variance Formula
(`shortWindowRenormalizedDefect_eq_corr_sub_var`):**
For every $N, M_0, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) =
  \operatorname{shortWindowShiftedCorrelation}(N, M_0, M, c) -
    \operatorname{shortWindowVariance}(N, M_0, M, c).$$ -/
theorem shortWindowRenormalizedDefect_eq_corr_sub_var (N M₀ M : ℕ) (c : ℕ → ℝ) :
    shortWindowRenormalizedDefect N M₀ M c =
      shortWindowShiftedCorrelation N M₀ M c - shortWindowVariance N M₀ M c := by
  rw [shortWindowRenormalizedDefect_eq_sum_mul_addDiff]
  unfold shortWindowShiftedCorrelation shortWindowVariance
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **Exact Link to Classical Selberg & Coppola–Murty–Saha Remainders
(`shortWindowRenormalizedDefect_eq_classical_remainders_sub_reserve`):**
For every $N, M_0, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$,
`shortWindowRenormalizedDefect N M₀ M c` equals the increment of the Selberg LCM fractional-part
defect plus the increment of the Bézout CRT sawtooth remainder minus
$M \cdot \operatorname{sieveSuccessorReserve}(N, c)$. -/
theorem shortWindowRenormalizedDefect_eq_classical_remainders_sub_reserve
    (N M₀ M : ℕ) (c : ℕ → ℝ) :
    shortWindowRenormalizedDefect N M₀ M c =
      (signedLcmFractDefect N (M₀ + M) c - signedLcmFractDefect N M₀ c) +
        (bezoutSawtoothRemainderForm (M₀ + M) N c - bezoutSawtoothRemainderForm M₀ N c) -
        (M : ℝ) * sieveSuccessorReserve N c := by
  unfold shortWindowRenormalizedDefect sieveRenormalizedPrefixDefect sieveCombinedPrefixDefect
  push_cast
  ring

/-- Telescoping of squared values on `Finset.Icc (M₀ + 1) (M₀ + M)`. -/
theorem sum_Icc_sq_sub_sq_telescope (M₀ M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M), (f (k + 1) ^ (2 : ℕ) - f k ^ (2 : ℕ))) =
      f (M₀ + M + 1) ^ (2 : ℕ) - f (M₀ + 1) ^ (2 : ℕ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show M₀ + (M + 1) = (M₀ + M) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega : M₀ + 1 ≤ (M₀ + M) + 1), ih]
    ring

/-- **Short-Window Dirichlet Polarization Identity (`two_mul_shortWindowRenormalizedDefect_eq`):**
For every $N, M_0, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$:
$$2 \cdot \operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) =
  -\operatorname{shortWindowDirichletEnergy}(N, M_0, M, c) +
    s_{N,c}(M_0 + M + 1)^2 - s_{N,c}(M_0 + 1)^2.$$ -/
theorem two_mul_shortWindowRenormalizedDefect_eq (N M₀ M : ℕ) (c : ℕ → ℝ) :
    2 * shortWindowRenormalizedDefect N M₀ M c =
      -shortWindowDirichletEnergy N M₀ M c +
        sieveSeq N c (M₀ + M + 1) ^ (2 : ℕ) - sieveSeq N c (M₀ + 1) ^ (2 : ℕ) := by
  rw [shortWindowRenormalizedDefect_eq_sum_mul_addDiff]
  unfold shortWindowDirichletEnergy
  have htel := sum_Icc_sq_sub_sq_telescope M₀ M (sieveSeq N c)
  have hpt : (∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M),
      (sieveSeq N c (k + 1) ^ (2 : ℕ) - sieveSeq N c k ^ (2 : ℕ))) =
      2 * (∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M),
        sieveSeq N c k * (sieveSeq N c (k + 1) - sieveSeq N c k)) +
      ∑ k ∈ Finset.Icc (M₀ + 1) (M₀ + M),
        (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  linarith

/-! ## §2. Sharp Necessary-and-Sufficient Iso-State Classification for Short Windows -/

/-- **Unit-Shift Affine Law on Short Windows (`shortWindowRenormalizedDefect_unitShiftWeight`):**
Shifting the unit divisor coefficient $c(1) \mapsto c(1) + a$ changes the short-window renormalized
defect affinely by $a (s_{N,c}(M_0 + M + 1) - s_{N,c}(M_0 + 1))$. -/
theorem shortWindowRenormalizedDefect_unitShiftWeight (N M₀ M : ℕ) (c : ℕ → ℝ) (a : ℝ) :
    shortWindowRenormalizedDefect N M₀ M (sieveUnitShiftWeight c a) =
      shortWindowRenormalizedDefect N M₀ M c +
        a * (sieveSeq N c (M₀ + M + 1) - sieveSeq N c (M₀ + 1)) := by
  unfold shortWindowRenormalizedDefect
  rw [sieveRenormalizedPrefixDefect_unitShiftWeight,
    sieveRenormalizedPrefixDefect_unitShiftWeight]
  ring

/-- **Equal-Endpoint Characterization of Unit-Shift Non-Positivity
(`shortWindowRenormalizedDefect_all_unitShifts_nonpos_iff`):**
For any $N, M_0, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$, the unit-shift family
`sieveUnitShiftWeight c a` has non-positive short-window defect for all $a \in \mathbb{R}$ **if and
only if** $s_{N,c}(M_0 + M + 1) = s_{N,c}(M_0 + 1)$. -/
theorem shortWindowRenormalizedDefect_all_unitShifts_nonpos_iff (N M₀ M : ℕ) (c : ℕ → ℝ) :
    (∀ a : ℝ, shortWindowRenormalizedDefect N M₀ M (sieveUnitShiftWeight c a) ≤ 0) ↔
      sieveSeq N c (M₀ + M + 1) = sieveSeq N c (M₀ + 1) := by
  constructor
  · intro h
    by_contra hne
    have hdiff_ne : sieveSeq N c (M₀ + M + 1) - sieveSeq N c (M₀ + 1) ≠ 0 :=
      sub_ne_zero.mpr hne
    let a := (1 - shortWindowRenormalizedDefect N M₀ M c) /
      (sieveSeq N c (M₀ + M + 1) - sieveSeq N c (M₀ + 1))
    have hle := h a
    rw [shortWindowRenormalizedDefect_unitShiftWeight] at hle
    dsimp [a] at hle
    rw [div_mul_cancel₀ _ hdiff_ne] at hle
    linarith
  · intro heq a
    rw [shortWindowRenormalizedDefect_unitShiftWeight, heq, sub_self, mul_zero, add_zero]
    have hpol := two_mul_shortWindowRenormalizedDefect_eq N M₀ M c
    rw [heq] at hpol
    have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M c :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith

/-- **Sharp All-Weight Iso-State Classification for Short Windows
(`forall_weight_shortWindowRenormalizedDefect_nonpos_iff_state_eq`):**
For every horizon $N : \mathbb{N}$, starting offset $M_0 : \mathbb{N}$, and window length
$M : \mathbb{N}$:
$$\bigl(\forall c : \mathbb{N} \to \mathbb{R},\;
  \operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) \le 0\bigr) \iff
  \operatorname{horizonObservationState}(N, M_0 + M + 1) =
    \operatorname{horizonObservationState}(N, M_0 + 1).$$ -/
theorem forall_weight_shortWindowRenormalizedDefect_nonpos_iff_state_eq (N M₀ M : ℕ) :
    (∀ c : ℕ → ℝ, shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonObservationState N (M₀ + M + 1) = horizonObservationState N (M₀ + 1) := by
  rw [horizonObservationState_eq_iff_all_sieveSeq]
  constructor
  · intro h c
    exact (shortWindowRenormalizedDefect_all_unitShifts_nonpos_iff N M₀ M c).mp
      fun a => h (sieveUnitShiftWeight c a)
  · intro h c
    have h0 := (shortWindowRenormalizedDefect_all_unitShifts_nonpos_iff N M₀ M c).mpr (h c) 0
    have heq : sieveUnitShiftWeight c 0 = c := by
      funext d
      simp [sieveUnitShiftWeight]
    rwa [heq] at h0

/-- **Sharp Squarefree-Weight Iso-Radical Classification for Short Windows
(`forall_squarefree_shortWindowRenormalizedDefect_nonpos_iff_radicalState_eq`):**
For every horizon $N : \mathbb{N}$, starting offset $M_0 : \mathbb{N}$, and window length
$M : \mathbb{N}$:
$$\bigl(\forall c : \mathbb{N} \to \mathbb{R},\;
  (\forall d, \neg\operatorname{Squarefree}(d) \to c(d) = 0) \to
  \operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) \le 0\bigr) \iff
  \operatorname{horizonRadicalState}(N, M_0 + M + 1) =
    \operatorname{horizonRadicalState}(N, M_0 + 1).$$ -/
theorem forall_squarefree_shortWindowRenormalizedDefect_nonpos_iff_radicalState_eq
    (N M₀ M : ℕ) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
      shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonRadicalState N (M₀ + M + 1) = horizonRadicalState N (M₀ + 1) := by
  rw [horizonRadicalState_eq_iff_all_squarefree_sieveSeq]
  constructor
  · intro h c hc
    exact (shortWindowRenormalizedDefect_all_unitShifts_nonpos_iff N M₀ M c).mp
      fun a => h (sieveUnitShiftWeight c a) (sieveUnitShiftWeight_squarefree_support hc a)
  · intro h c hc
    have h0 := (shortWindowRenormalizedDefect_all_unitShifts_nonpos_iff N M₀ M c).mpr (h c hc) 0
    have heq : sieveUnitShiftWeight c 0 = c := by
      funext d
      simp [sieveUnitShiftWeight]
    rwa [heq] at h0

/-! ## §3. Reusable Short-Window Contraction Across Three Arithmetic Regimes -/

/-- **Divisor-Multiplied Short-Window Pure-Dirichlet Identity
(`shortWindowRenormalizedDefect_mul_dvd_eq_neg_half_dirichlet`):**
For any squarefree-supported weight $c$, any $a \ge 1$, and any $d \ge 1$ with $d \mid a$, the
short window from $M_0 = a - 1$ to $M_0 + M = d \cdot a - 1$ has identical endpoint radical states
at every horizon $N$, so its renormalized defect equals $-\frac{1}{2}$ times its Dirichlet energy:
$$2 \cdot \operatorname{shortWindowRenormalizedDefect}(N, a - 1, d \cdot a - a, c) =
  -\operatorname{shortWindowDirichletEnergy}(N, a - 1, d \cdot a - a, c) \le 0.$$ -/
theorem shortWindowRenormalizedDefect_mul_dvd_eq_neg_half_dirichlet
    (N : ℕ) {c : ℕ → ℝ} (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0)
    {a d : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d) (hda : d ∣ a) :
    2 * shortWindowRenormalizedDefect N (a - 1) (d * a - a) c =
        -shortWindowDirichletEnergy N (a - 1) (d * a - a) c ∧
      shortWindowRenormalizedDefect N (a - 1) (d * a - a) c ≤ 0 := by
  have hle : a ≤ d * a := Nat.le_mul_of_pos_left a hd
  have h1 : a - 1 + 1 = a := Nat.sub_add_cancel ha
  have h2 : a - 1 + (d * a - a) + 1 = d * a := by omega
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N (a - 1) (d * a - a) c
  rw [h1, h2, sieveSeq_mul_of_dvd_of_squarefree_support N hc hda] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N (a - 1) (d * a - a) c :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- **Power-Interval Short-Window Pure-Dirichlet Identity
(`shortWindowRenormalizedDefect_pow_eq_neg_half_dirichlet`):**
For any squarefree-supported weight $c$, any $a \ge 1$, and any exponent $m \ge 1$, the short window
from $M_0 = a - 1$ to $M_0 + M = a^m - 1$ has zero boundary defect at every horizon $N$:
$$2 \cdot \operatorname{shortWindowRenormalizedDefect}(N, a - 1, a^m - a, c) =
  -\operatorname{shortWindowDirichletEnergy}(N, a - 1, a^m - a, c) \le 0.$$ -/
theorem shortWindowRenormalizedDefect_pow_eq_neg_half_dirichlet
    (N : ℕ) {c : ℕ → ℝ} (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0)
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    2 * shortWindowRenormalizedDefect N (a - 1) (a ^ m - a) c =
        -shortWindowDirichletEnergy N (a - 1) (a ^ m - a) c ∧
      shortWindowRenormalizedDefect N (a - 1) (a ^ m - a) c ≤ 0 := by
  have hle : a ≤ a ^ m := Nat.le_self_pow (by omega : m ≠ 0) a
  have h1 : a - 1 + 1 = a := Nat.sub_add_cancel ha
  have h2 : a - 1 + (a ^ m - a) + 1 = a ^ m := by omega
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N (a - 1) (a ^ m - a) c
  rw [h1, h2, sieveSeq_pow_of_squarefree_support N hc a hm] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N (a - 1) (a ^ m - a) c :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- **Starting-Phase-Free Right-Zero-Endpoint Contraction
(`shortWindowRenormalizedDefect_nonpos_of_right_endpoint_eq_zero`):**
Whenever the right endpoint satisfies $s_{N,c}(M_0 + M + 1) = 0$, the short-window renormalized
defect is non-positive for **every** starting offset $M_0 \in \mathbb{N}$ (losing both the
short-window Dirichlet energy and the initial spike $s_{N,c}(M_0 + 1)^2$):
$$2 \cdot \operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) =
  -\operatorname{shortWindowDirichletEnergy}(N, M_0, M, c) - s_{N,c}(M_0 + 1)^2 \le 0.$$ -/
theorem shortWindowRenormalizedDefect_nonpos_of_right_endpoint_eq_zero
    (N M₀ M : ℕ) (c : ℕ → ℝ) (hz : sieveSeq N c (M₀ + M + 1) = 0) :
    2 * shortWindowRenormalizedDefect N M₀ M c =
        -shortWindowDirichletEnergy N M₀ M c - sieveSeq N c (M₀ + 1) ^ (2 : ℕ) ∧
      shortWindowRenormalizedDefect N M₀ M c ≤ 0 := by
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N M₀ M c
  rw [hz] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M c :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : 0 ≤ sieveSeq N c (M₀ + 1) ^ (2 : ℕ) := sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- **Starting-Phase-Free Right-Zero-Cone Contraction for `moebiusReal`
(`shortWindowRenormalizedDefect_moebiusReal_nonpos_of_right_zero_cone`):**
Whenever $M_0 + M + 1 = q \cdot r$ with $2 \le q \le N$ and $r$ $N$-rough (`IsTransHorizonRough N r`),
$s_{N,\mu}(M_0 + M + 1) = 0$, so for **every** starting phase $M_0 \in \mathbb{N}$:
$$2 \cdot \operatorname{shortWindowRenormalizedDefect}(N, M_0, M, \mu) =
  -\operatorname{shortWindowDirichletEnergy}(N, M_0, M, \mu) - s_{N,\mu}(M_0 + 1)^2 \le 0.$$ -/
theorem shortWindowRenormalizedDefect_moebiusReal_nonpos_of_right_zero_cone
    {N M₀ M q r : ℕ} (hq2 : 2 ≤ q) (hqN : q ≤ N) (hr : IsTransHorizonRough N r)
    (hend : M₀ + M + 1 = q * r) :
    2 * shortWindowRenormalizedDefect N M₀ M moebiusReal =
        -shortWindowDirichletEnergy N M₀ M moebiusReal -
          sieveSeq N moebiusReal (M₀ + 1) ^ (2 : ℕ) ∧
      shortWindowRenormalizedDefect N M₀ M moebiusReal ≤ 0 := by
  apply shortWindowRenormalizedDefect_nonpos_of_right_endpoint_eq_zero
  rw [hend]
  exact sieveSeq_moebiusReal_mul_eq_zero_of_isTransHorizonRough hq2 hqN hr

/-- **Rough-Start Power-Damped Short-Window Contraction Across the First Two Bands
(`shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_le_three_mul_nonpos`):**
For every $\varepsilon \ge 0$, horizon $N \ge 1$, starting offset $M_0$ such that $M_0 + 1$ is
$N$-rough (`IsTransHorizonRough N (M₀ + 1)`), and window length $M$ with $2 \le M_0 + M + 1 \le 3N$:
$$2 \cdot \operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c_\varepsilon) \le
  -\operatorname{shortWindowDirichletEnergy}(N, M_0, M, c_\varepsilon) \le 0.$$ -/
theorem shortWindowRenormalizedDefect_pmPowerDampedRealWeight_rough_start_le_three_mul_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N M₀ M : ℕ} (hN : 1 ≤ N)
    (hstart : IsTransHorizonRough N (M₀ + 1))
    (hlo : 2 ≤ M₀ + M + 1) (hhi : M₀ + M + 1 ≤ 3 * N) :
    2 * shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤
        -shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) ∧
      shortWindowRenormalizedDefect N M₀ M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N M₀ M (pmPowerDampedRealWeight ε)
  have hinit : sieveSeq N (pmPowerDampedRealWeight ε) (M₀ + 1) = 1 := by
    rw [sieveSeq_of_isTransHorizonRough hstart,
      sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl hN,
      pmPowerDampedDivisorCoeff_one]
  have hend_abs : |sieveSeq N (pmPowerDampedRealWeight ε) (M₀ + M + 1)| ≤ 1 :=
    abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_le_three_mul hε hlo hhi
  have hend_sq : sieveSeq N (pmPowerDampedRealWeight ε) (M₀ + M + 1) ^ (2 : ℕ) ≤ 1 := by
    rwa [sq_le_one_iff_abs_le_one]
  rw [hinit, one_pow] at hpol
  have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M (pmPowerDampedRealWeight ε) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-! ## §4. Matched-Assumption Quantitative Domination Over Classical $\ell^1$ Remainder Bounds -/

/-- Pointwise $\ell^1$ envelope: $|s_{N,c}(k)| \le \sum_{d=1}^N |c(d)|$ for every $k \in \mathbb{N}$. -/
theorem abs_sieveSeq_le_sum_abs (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    |sieveSeq N c k| ≤ ∑ d ∈ Finset.Icc 1 N, |c d| := by
  unfold sieveSeq
  calc
    |∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ k), c d|
      ≤ ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ k), |c d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, |c d| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _

/-- **Universal Short-Window Upper Envelope (`shortWindowRenormalizedDefect_le_half_sum_abs_sq`):**
For every $N, M_0, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\operatorname{shortWindowRenormalizedDefect}(N, M_0, M, c) \le
  \frac{1}{2} s_{N,c}(M_0 + M + 1)^2 \le
  \frac{1}{2} \Bigl(\sum_{d=1}^N |c(d)|\Bigr)^2.$$ -/
theorem shortWindowRenormalizedDefect_le_half_sum_abs_sq (N M₀ M : ℕ) (c : ℕ → ℝ) :
    shortWindowRenormalizedDefect N M₀ M c ≤
        (1 / 2 : ℝ) * sieveSeq N c (M₀ + M + 1) ^ (2 : ℕ) ∧
      (1 / 2 : ℝ) * sieveSeq N c (M₀ + M + 1) ^ (2 : ℕ) ≤
        (1 / 2 : ℝ) * (∑ d ∈ Finset.Icc 1 N, |c d|) ^ (2 : ℕ) := by
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N M₀ M c
  have henergy : 0 ≤ shortWindowDirichletEnergy N M₀ M c :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinit_sq : 0 ≤ sieveSeq N c (M₀ + 1) ^ (2 : ℕ) := sq_nonneg _
  have habs := abs_sieveSeq_le_sum_abs N c (M₀ + M + 1)
  have hsum_nonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 N, |c d| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsq_le : sieveSeq N c (M₀ + M + 1) ^ (2 : ℕ) ≤
      (∑ d ∈ Finset.Icc 1 N, |c d|) ^ (2 : ℕ) := by
    rw [← sq_abs (sieveSeq N c (M₀ + M + 1))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  exact ⟨by linarith, by linarith⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
