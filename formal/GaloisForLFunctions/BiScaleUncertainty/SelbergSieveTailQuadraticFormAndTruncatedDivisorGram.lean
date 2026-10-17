import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearArithmeticWeightsAndChebyshevCellIncrement
import GaloisForLFunctions.RHTower.Sieve.LcmQuadraticDiagonalization

/-!
# Pillar XXXII: Selberg $\Lambda^2$-Sieve Tail Quadratic Form & Truncated Divisor Gram Matrix

This module develops **Component 1** of the FZZ-P / `BiScaleUncertainty` synthesis, resolving the
structural gap between the periodic Franel Gram matrix on $L^2([0, 1], dx)$ and the truncated
step-cell / divisor-sum Gram structure on $L^2((0, 1], dt)$, together with the Selberg
$\Lambda^2$-sieve diagonalization governing the small-$t$ origin tail $t < 1/(N+1)$ ($m = \lfloor 1/t \rfloor > N$):

1. **Step-Cell Decomposition of General Finite Nyman Approximants on $(0, 1]$:**
   For any finite sieve weight $c : \mathbb{N} \to \mathbb{R}$ supported on $\{1, \dots, N\}$,
   `generalFiniteNymanError N c t` decomposes unconditionally into the indicator $\mathbf{1}_{(0,1]}(t)$
   plus the harmonic drift $H_c(N)/t$ minus the step-cell floor sum $\Phi_c(N, 1/t) = \sum_{d=1}^N c_d \lfloor 1/(dt) \rfloor$.
2. **Truncated Sieve Weights & Origin-Tail Step Increments ($m > N$):**
   Stepping from $m$ to $m + 1$ changes the floor sum $\Phi_c(N, m)$ by the **sieved divisor sum**
   $$s_{N,c}(m+1) = \sum_{\substack{d \mid (m+1) \\ 1 \le d \le N}} c_d.$$
   On the bulk head $1 \le k \le N$, no divisor of $k$ exceeds $N$, so $s_{N,c}(k)$ coincides with
   the full Dirichlet divisor sum $\sum_{d \mid k} c_d$. Beyond the cutoff ($k = N + 1, \dots, N + K$,
   corresponding to the small-$t$ origin tail $t < 1/(N+1)$), divisors $d > N$ are omitted, turning
   the tail residual into a Selberg $\Lambda^2$-sieve sum.
3. **Truncated $[1, N]^2$ LCM Gram Matrix & Selberg Totient Diagonalization:**
   For any tail horizon $N + K$, the mean square $\sum_{k=1}^{N+K} s_{N,c}(k)^2$ reduces identically
   from $[1, N+K]^2$ to the $[1, N]^2$ LCM Gram quadratic form
   $$\sum_{(d_1, d_2) \in [1, N]^2} c_{d_1} c_{d_2} \left\lfloor \frac{N + K}{\operatorname{lcm}(d_1, d_2)} \right\rfloor,$$
   whose smooth main term diagonalizes via Euler's totient $\varphi(e)$ into a sum of squares:
   $$\sum_{(d_1, d_2) \in [1, N]^2} \frac{c_{d_1} c_{d_2}}{\operatorname{lcm}(d_1, d_2)}
     = \sum_{e=1}^N \varphi(e) \Bigl(\sum_{\substack{1 \le d \le N \\ e \mid d}} \frac{c_d}{d}\Bigr)^2 \ge 0,$$
   yielding an unconditional upper bound on the origin-tail mean square $\sum_{k=N+1}^{N+K} s_{N,c}(k)^2$.
-/

open Complex MeasureTheory Set Filter Topology Finset
open GaloisForLFunctions.NymanMellin
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Finite Nyman Error Step-Cell Decomposition on `(0, 1]` -/

/-- The finite harmonic sum `H_c(N) = ∑_{d=1}^N c(d) / d` governing the `1/t` pole coefficient. -/
def finiteHarmonicSum (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ)

/-- The finite floor sum `Φ_c(N, x) = ∑_{d=1}^N c(d) ⌊x / d⌋` governing the discrete step profile. -/
def finiteFloorSum (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, c d * (⌊x / (d : ℝ)⌋ : ℝ)

/-- The finite Nyman error `1_{(0,1]}(t) + ∑_{d=1}^N c(d) {1/(dt)}` for a general sieve weight `c`. -/
def generalFiniteNymanError (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t +
    ∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * nymanGen (d : ℝ) t

/-- **Generator Sum Decomposition into Harmonic Pole and Floor Sum:**
For any `N : ℕ`, coefficient vector `c : ℕ → ℝ`, and `t : ℝ`,
`∑_{d=1}^N c(d) {1/(dt)} = H_c(N)/t - Φ_c(N, 1/t)`. -/
theorem sum_coeff_nymanGen_eq_harmonic_sub_floor (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * nymanGen (d : ℝ) t) =
      ((finiteHarmonicSum N c / t - finiteFloorSum N c (1 / t) : ℝ) : ℂ) := by
  rw [finiteHarmonicSum, finiteFloorSum, Finset.sum_div, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold nymanGen Int.fract
  rw [show 1 / ((d : ℝ) * t) = (1 / t) / (d : ℝ) by ring]
  push_cast
  ring

/-- **Unconditional Pointwise Decomposition of `generalFiniteNymanError`:**
For every `N : ℕ`, `c : ℕ → ℝ`, and `t : ℝ`, the finite Nyman error separates into the indicator
`1_{(0, 1]}(t)` plus `H_c(N)/t - Φ_c(N, 1/t)`. -/
theorem generalFiniteNymanError_eq_indicator_add_harmonic_sub_floor
    (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    generalFiniteNymanError N c t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t +
        ((finiteHarmonicSum N c / t - finiteFloorSum N c (1 / t) : ℝ) : ℂ) := by
  rw [generalFiniteNymanError, sum_coeff_nymanGen_eq_harmonic_sub_floor]

/-! ## §2. Truncated Sieve Weights & Discrete Step Increments in the Origin Tail (`m > N`) -/

/-- The sieve weight `c_{≤ N}(d)` supported on `1 ≤ d ≤ N`. -/
def truncatedSieveWeight (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ∈ Finset.Icc 1 N then c d else 0

/-- The sieved divisor sum `s_{N,c}(k) = ∑_{d ∣ k, 1 ≤ d ≤ N} c(d)`. -/
def sievedDivisorSum (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, truncatedSieveWeight N c d

/-- **Sieved Divisor Sum as a Filtered `[1, N]` Sum:**
For every `N k : ℕ` and `c : ℕ → ℝ`, `sievedDivisorSum N c (k + 1)` is the sum of `c(d)` over
`d ∈ [1, N]` dividing `k + 1`. -/
theorem sievedDivisorSum_succ_eq_sum_filter_Icc (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sievedDivisorSum N c (k + 1) =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ (k + 1)), c d := by
  unfold sievedDivisorSum truncatedSieveWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  exact ⟨fun ⟨⟨hdk, _⟩, hd1, hdN⟩ => ⟨⟨hd1, hdN⟩, hdk⟩,
    fun ⟨⟨hd1, hdN⟩, hdk⟩ => ⟨⟨hdk, Nat.succ_ne_zero k⟩, hd1, hdN⟩⟩

/-- **Exact Agreement with the Full Divisor Sum on the Bulk Head (`k + 1 ≤ k + 1 + K`):**
When the cutoff is `k + 1 + K`, every divisor `d ∣ (k + 1)` satisfies `1 ≤ d ≤ k + 1 + K`, so no
divisor is omitted by the cutoff. -/
theorem sievedDivisorSum_succ_eq_full_divisorSum (k K : ℕ) (c : ℕ → ℝ) :
    sievedDivisorSum (k + 1 + K) c (k + 1) = ∑ d ∈ (k + 1).divisors, c d := by
  unfold sievedDivisorSum truncatedSieveWeight
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdk : d ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) (Nat.dvd_of_mem_divisors hd)
  rw [if_pos (Finset.mem_Icc.mpr ⟨hdpos, by omega⟩)]

/-- On the bulk head `k ∈ Finset.Icc 1 N`, any function `F` of `sievedDivisorSum N c k` agrees
identically with `F` of the full divisor sum `∑ d ∈ k.divisors, c d`. -/
theorem sum_Icc_sievedDivisorSum_eq_full (N : ℕ) (c : ℕ → ℝ) (F : ℝ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, F (sievedDivisorSum N c k)) =
      ∑ k ∈ Finset.Icc 1 N, F (∑ d ∈ k.divisors, c d) := by
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  have hk_eq : k = (k - 1) + 1 := by omega
  have hN_eq : N = (k - 1) + 1 + (N - k) := by omega
  rw [hk_eq, hN_eq, sievedDivisorSum_succ_eq_full_divisorSum (k - 1) (N - k) c]

/-- At natural integer arguments `m d : ℕ`, `⌊(m : ℝ) / (d : ℝ)⌋ = floorDivSeq d m`. -/
theorem intFloor_natCast_div_eq_floorDivSeq (m d : ℕ) :
    (⌊(m : ℝ) / (d : ℝ)⌋ : ℝ) = floorDivSeq d m := by
  unfold floorDivSeq
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hfl : ⌊(m : ℝ) / (d : ℝ)⌋ = ((m / d : ℕ) : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      refine ⟨Nat.cast_div_le, ?_⟩
      rw [div_lt_iff₀ hdR]
      have hmod : d * (m / d) + m % d = m := Nat.div_add_mod m d
      have hlt : m % d < d := Nat.mod_lt m hd
      have hnat : m < (m / d + 1) * d := by
        calc m = d * (m / d) + m % d := hmod.symm
          _ < d * (m / d) + d := by omega
          _ = (m / d + 1) * d := by ring
      have hcast : (m : ℝ) < (((m / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
        exact_mod_cast hnat
      exact hcast
    rw [hfl]
    norm_cast

/-- At integer arguments `m : ℕ`, `finiteFloorSum N c (m : ℝ)` coincides with `weightedFloorSumSeq c N m`. -/
theorem finiteFloorSum_nat_eq_weightedFloorSumSeq (N m : ℕ) (c : ℕ → ℝ) :
    finiteFloorSum N c (m : ℝ) = weightedFloorSumSeq c N m := by
  unfold finiteFloorSum weightedFloorSumSeq
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [intFloor_natCast_div_eq_floorDivSeq]

/-- **Coprime Step Increment of the Finite Floor Sum:**
Stepping from `m` to `m + 1` changes `finiteFloorSum N c` by the sieved divisor sum at `m + 1`. -/
theorem finiteFloorSum_nat_succ_sub (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    finiteFloorSum N c ((m + 1 : ℕ) : ℝ) - finiteFloorSum N c (m : ℝ) =
      sievedDivisorSum N c (m + 1) := by
  rw [finiteFloorSum_nat_eq_weightedFloorSumSeq, finiteFloorSum_nat_eq_weightedFloorSumSeq]
  change addDiff (weightedFloorSumSeq c N) m = sievedDivisorSum N c (m + 1)
  rw [addDiff_weightedFloorSumSeq_eq_sum_filter_dvd, sievedDivisorSum_succ_eq_sum_filter_Icc]

/-- `finiteFloorSum` vanishes at `x = 0`. -/
@[simp]
theorem finiteFloorSum_zero (N : ℕ) (c : ℕ → ℝ) :
    finiteFloorSum N c 0 = 0 := by
  unfold finiteFloorSum
  simp

/-- **Telescoping Identity for `finiteFloorSum` at Integer Arguments:**
For every `m : ℕ`, `Φ_c(N, m) = ∑_{k=1}^m s_{N,c}(k)`. -/
theorem finiteFloorSum_nat_eq_sum_sievedDivisorSum (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    finiteFloorSum N c (m : ℝ) = ∑ k ∈ Finset.Icc 1 m, sievedDivisorSum N c k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep := finiteFloorSum_nat_succ_sub N c m
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp), ← ih]
    linarith

/-- **Head + Origin-Tail Split of `finiteFloorSum` Beyond the Cutoff (`N + K`):**
For every `N K : ℕ`, the floor sum at `N + K` splits into the exact (unsieved) divisor sums on the
head `1 ≤ k ≤ N` plus the truncated Selberg sieve sums on the origin tail `N + 1 ≤ k ≤ N + K`. -/
theorem finiteFloorSum_nat_add_eq_head_add_tail (N K : ℕ) (c : ℕ → ℝ) :
    finiteFloorSum N c ((N + K : ℕ) : ℝ) =
      (∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, c d) +
        ∑ k ∈ Finset.Icc (N + 1) (N + K), sievedDivisorSum N c k := by
  rw [finiteFloorSum_nat_eq_sum_sievedDivisorSum]
  have hunion : Finset.Icc 1 (N + K) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (N + K) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (N + K)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [hunion, Finset.sum_union hdisj,
    sum_Icc_sievedDivisorSum_eq_full N c (fun x => x)]

/-! ## §3. Truncated LCM Gram Matrix & Selberg `Λ²`-Sieve Totient Diagonalization -/

/-- Support reduction lemma: summing a bilinear form against `truncatedSieveWeight N c` over
`[1, N + K]²` reduces unconditionally to `[1, N]²`. -/
theorem sum_product_truncatedSieveWeight_eq_Icc (N K : ℕ) (c : ℕ → ℝ)
    (G : ℕ → ℕ → ℝ) :
    (∑ p ∈ (Finset.Icc 1 (N + K)) ×ˢ (Finset.Icc 1 (N + K)),
      truncatedSieveWeight N c p.1 * truncatedSieveWeight N c p.2 * G p.1 p.2) =
    ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      c p.1 * c p.2 * G p.1 p.2 := by
  have hNM : N ≤ N + K := Nat.le_add_right N K
  have hsub : (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ⊆
      (Finset.Icc 1 (N + K)) ×ˢ (Finset.Icc 1 (N + K)) :=
    Finset.product_subset_product (Finset.Icc_subset_Icc_right hNM)
      (Finset.Icc_subset_Icc_right hNM)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    simp only [truncatedSieveWeight, if_pos hp1, if_pos hp2]
  · intro p _ hpnot
    rw [Finset.mem_product] at hpnot
    unfold truncatedSieveWeight
    by_cases hp1 : p.1 ∈ Finset.Icc 1 N
    · have hp2 : p.2 ∉ Finset.Icc 1 N := fun h2 => hpnot ⟨hp1, h2⟩
      rw [if_pos hp1, if_neg hp2, mul_zero, zero_mul]
    · rw [if_neg hp1, zero_mul, zero_mul]

/-- **Sieved Divisor Mean Square as a Truncated `[1, N]²` LCM Gram Matrix:**
For every `N K : ℕ`, the mean square of `sievedDivisorSum N c k` over `1 ≤ k ≤ N + K` equals the
`[1, N]²` LCM quadratic form with integer-quotient weights `⌊(N + K) / lcm(d₁, d₂)⌋`. -/
theorem sievedDivisorMeanSquare_eq_truncated_lcm_gram (N K : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (N + K), sievedDivisorSum N c k ^ (2 : ℕ)) =
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        c p.1 * c p.2 * (((N + K) / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  unfold sievedDivisorSum
  rw [sum_sq_divisorSum_eq_lcm_quadratic (N + K) (truncatedSieveWeight N c)]
  exact sum_product_truncatedSieveWeight_eq_Icc N K c
    (fun d1 d2 => (((N + K) / Nat.lcm d1 d2 : ℕ) : ℝ))

/-- The union of divisors of all `m ∈ [1, N]` is `[1, N]`. -/
theorem biUnion_divisors_Icc_eq_Icc (N : ℕ) :
    (Finset.Icc 1 N).biUnion Nat.divisors = Finset.Icc 1 N := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨m, ⟨hm1, hmN⟩, hem, _⟩
    exact ⟨Nat.pos_of_dvd_of_pos hem hm1, (Nat.le_of_dvd hm1 hem).trans hmN⟩
  · rintro ⟨he1, heN⟩
    exact ⟨e, ⟨he1, heN⟩, dvd_rfl, (by omega)⟩

/-- **Selberg Totient Diagonalization of the Smooth `[1, N]²` LCM Gram Form:**
`∑_{d₁, d₂ ∈ [1, N]} c(d₁) c(d₂) / lcm(d₁, d₂) = ∑_{e=1}^N φ(e) (∑_{d ∈ [1, N], e ∣ d} c(d)/d)²`. -/
theorem truncated_lcm_smooth_eq_selberg_totient_diagonal (N : ℕ) (c : ℕ → ℝ) :
    (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ)) =
    ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ)) ^ (2 : ℕ) := by
  rw [sum_div_lcm_eq_totient_diagonal (Finset.Icc 1 N)
    (fun m hm => (Finset.mem_Icc.mp hm).1) c, biUnion_divisors_Icc_eq_Icc]

/-- **Positive Semidefiniteness of the Smooth LCM Gram Form:**
The smooth LCM quadratic form is non-negative for all coefficient vectors `c`. -/
theorem truncated_lcm_smooth_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ) := by
  rw [truncated_lcm_smooth_eq_selberg_totient_diagonal]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- **Upper Bound on the Sieved Divisor Mean Square via Selberg Diagonalization:**
For every `N K : ℕ`, the mean square `∑_{k=1}^{N+K} s_{N,c}(k)²` is bounded from above by `N + K`
times the Selberg totient diagonal form plus the `ℓ¹`-norm squared `(∑_{d=1}^N |c(d)|)²`. -/
theorem sievedDivisorMeanSquare_le_selberg_diagonal_add_l1_sq (N K : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (N + K), sievedDivisorSum N c k ^ (2 : ℕ)) ≤
      ((N + K : ℕ) : ℝ) * (∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ)) ^ (2 : ℕ)) +
      (∑ d ∈ Finset.Icc 1 N, |c d|) ^ (2 : ℕ) := by
  have hgraham := abs_sum_sq_divisorSum_sub_lcm_main_le (N + K) (truncatedSieveWeight N c)
  have hmain : (∑ p ∈ (Finset.Icc 1 (N + K)) ×ˢ (Finset.Icc 1 (N + K)),
      truncatedSieveWeight N c p.1 * truncatedSieveWeight N c p.2 *
        (((N + K : ℕ) : ℝ) / (Nat.lcm p.1 p.2 : ℝ))) =
      ((N + K : ℕ) : ℝ) * ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ)) ^ (2 : ℕ) := by
    rw [sum_product_truncatedSieveWeight_eq_Icc N K c
      (fun d1 d2 => ((N + K : ℕ) : ℝ) / (Nat.lcm d1 d2 : ℝ)),
      ← truncated_lcm_smooth_eq_selberg_totient_diagonal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  have hl1 : (∑ p ∈ (Finset.Icc 1 (N + K)) ×ˢ (Finset.Icc 1 (N + K)),
      |truncatedSieveWeight N c p.1| * |truncatedSieveWeight N c p.2|) =
      (∑ d ∈ Finset.Icc 1 N, |c d|) ^ (2 : ℕ) := by
    have habs : ∀ d, |truncatedSieveWeight N c d| = truncatedSieveWeight N (fun k => |c k|) d := by
      intro d
      unfold truncatedSieveWeight
      split_ifs <;> simp
    simp_rw [habs]
    have h1 := sum_product_truncatedSieveWeight_eq_Icc N K (fun k => |c k|) (fun _ _ => 1)
    simp only [mul_one] at h1
    rw [h1, sq, Finset.sum_mul_sum, Finset.sum_product]
  have hle := (le_abs_self _).trans hgraham
  unfold sievedDivisorSum
  linarith

/-- **Origin-Tail Sieved Divisor Mean Square Upper Bound (`N + 1 ≤ k ≤ N + K`):**
Isolating the small-`t` tail `k ∈ [N + 1, N + K]` (`t < 1/(N+1)`) subtracts the exact bulk head
energy `∑_{k=1}^N (∑_{d ∣ k} c(d))²` from the Selberg totient upper bound. -/
theorem tailSievedDivisorMeanSquare_le_selberg_diagonal (N K : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc (N + 1) (N + K), sievedDivisorSum N c k ^ (2 : ℕ)) ≤
      ((N + K : ℕ) : ℝ) * (∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ)) ^ (2 : ℕ)) +
      (∑ d ∈ Finset.Icc 1 N, |c d|) ^ (2 : ℕ) -
      ∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, c d) ^ (2 : ℕ) := by
  have hunion : Finset.Icc 1 (N + K) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (N + K) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (N + K)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hsplit : (∑ k ∈ Finset.Icc 1 (N + K), sievedDivisorSum N c k ^ (2 : ℕ)) =
      (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, c d) ^ (2 : ℕ)) +
        ∑ k ∈ Finset.Icc (N + 1) (N + K), sievedDivisorSum N c k ^ (2 : ℕ) := by
    rw [hunion, Finset.sum_union hdisj,
      sum_Icc_sievedDivisorSum_eq_full N c (fun x => x ^ (2 : ℕ))]
  have hbound := sievedDivisorMeanSquare_le_selberg_diagonal_add_l1_sq N K c
  linarith

end GaloisForLFunctions.BiScaleUncertainty
