import GaloisForLFunctions.TransHorizonIncidenceMechanics.QuadraticLongWindowThreshold
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RoughPrimeBoundaryUniformDampingDefectSign
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MobiusEnvelopeLadderAndPrimeShellResponses
import GaloisForLFunctions.BezoutValuationIncidence.WindowSandwichWithTheMontgomeryVaughanConstant
import GaloisForLFunctions.BezoutValuationIncidence.QuadraticOrderL1ObservabilityConstant

/-!
# Montgomery–Vaughan Window Dirichlet Laws, Prime-Pairing Radical Envelopes, and Small-Horizon Defect Nonpositivity

This module establishes the direct Fourier/Montgomery–Vaughan window Dirichlet and dissipation laws,
the variational characterization of the optimal window sandwich and reserve Dirichlet constants, the
prime-pairing divisor-window identity and $2^{\omega(r)-2}$ radical envelope, and unconditional
all-prefix defect nonpositivity across small horizons:

1. **Direct reserve-proportional window Dirichlet sandwich, lag covariance, Poincaré inequality, and
   $2N^2 - 2$ long-window dissipation**:
   - The forward-difference sequence $s_{N,c}(k+1) - s_{N,c}(k)$ is a single trigonometric
     polynomial over `responseRoots N` with Fourier coefficient energy
     $\sum_{\zeta \in T_N} \|b(\zeta)(\zeta - 1)\|^2 = 2\mathcal{R}_N(c)$.
   - Applying the Montgomery–Vaughan roots-of-unity window inequality directly to
     $b(\zeta)(\zeta - 1)$ yields the reserve-proportional sandwich
     $$\bigl|\operatorname{shortWindowDirichletEnergy}(N, A, K, c) - 2K\mathcal{R}_N(c)\bigr| \le
       2N(N-1)\mathcal{R}_N(c) \le 4N(N-1)V(c),$$
     and the coercivity lower bound
     $$\operatorname{shortWindowDirichletEnergy}(N, A, K, c) \ge
       2\bigl(K - N(N-1)\bigr)\mathcal{R}_N(c) \ge \bigl(K - N(N-1)\bigr)V(c),$$
     improving the coercivity threshold from $8N^2 - 4$ to $N(N-1)$.
   - Consequently, the window Poincaré inequality holds with constant $2N(N-1)$, the window lag
     covariance error is bounded by $N(N-1)V(c)$, and the long-window dissipation bound holds at
     every phase and prefix with quadratic threshold $2N^2 - 2$:
     $$2\widetilde{\mathcal{D}}_N(M; c) \le 2H_c(N)^2 - s_{N,c}(1)^2 - \bigl(M - (2N^2 - 2)\bigr)V(c).$$
   - For the Möbius weight $\mu$, $\widetilde{\mathcal{D}}_N(M; \mu) \le 0$ for every $N \ge 2$ and
     every $M \ge 2N^2 + 2N - 2$ (and $< 0$ for $M > 2N^2 + 2N - 2$); for the power-damped weight
     $c_\varepsilon$, $\widetilde{\mathcal{D}}_N(M; c_\varepsilon) \le 0$ for every
     $M \ge 2N^2 - 2 + 34N^{1+2\varepsilon}$.

2. **Exact variational characterization of the optimal window sandwich and reserve Dirichlet
   constants**:
   - The infimal window sandwich constant $S_{\mathrm{opt}}(N) = \inf\{S \mid \operatorname{IsWindowSandwichConstant}\ N\ S\}$
     and the infimal reserve Dirichlet constant
     $R_{\mathrm{opt}}(N) = \inf\{R \mid 0 \le R \wedge \operatorname{IsReserveWindowDirichletConstant}\ N\ R\}$
     are attained for every $N \ge 2$, satisfy $\Phi(N) - 2 \le S_{\mathrm{opt}}(N) \le N(N-1)$ and
     $0 \le R_{\mathrm{opt}}(N) \le N(N-1)$, and govern the sharp window Poincaré and prefix
     dissipation inequalities.

3. **Prime-pairing divisor-window identity, the $2^{\omega(r)-2}$ radical envelope, and three-prime
   radical nonpositivity**:
   - For any prime $p$ and any $a \ge 1$ with $p \nmid a$, pairing each divisor $d \mid a$ with
     $pd \mid pa$ cancels all divisors with $pd \le N$, leaving only the top window:
     $$s_{N,\mu}(pa) = \sum_{\substack{d \mid a \\ N < pd,\; d \le N}} \mu(d).$$
   - For any squarefree $a \ge 2$ and any divisor subset, zero-sum complementarity gives
     $2\bigl|\sum_{d \in S} \mu(d)\bigr| \le |a.\mathrm{divisors}| = 2^{\omega(a)}$. Hence every
     squarefree $r \ge 2$ with $\omega(r) \ge 2$ satisfies $|s_{N,\mu}(r)| \le 2^{\omega(r)-2}$.
   - In particular, at every horizon $N \in \mathbb{N}$ and every integer $k \ge 1$ whose radical
     state $r = \gcd(k, N\#)$ has $\omega(r) \le 3$, $|s_{N,\mu}(k)| \le 2$ and
     $\widetilde{\mathcal{D}}_N(k-1; \mu) \le 0$.

4. **All-prefix defect nonpositivity across small horizons**:
   - For $N \le 4$ and all $\varepsilon \ge 0$, $N\# \le 6 < 5(N+1)$, so $|s_{N,c_\varepsilon}(k)| \le 1$
     and $\widetilde{\mathcal{D}}_N(M; c_\varepsilon) \le 0$ for all $M \in \mathbb{N}$; for $N \le 6$,
     $N\# \le 30 < 6(N+1)$, so $|s_{N,c_\varepsilon}(k)| \le 2$ for all $k \ge 1$.
   - For $N \le 10$, $|s_{N,\mu}(k)| \le 2$ and $\widetilde{\mathcal{D}}_N(M; \mu) \le 0$ for all
     $k, M \in \mathbb{N}$.
   - At $N \in \{11, 12\}$, the $|s_{N,\mu}(k)| \le 2$ envelope holds for every $k$ not divisible by
     $3 \cdot 5 \cdot 7 \cdot 11 = 1155$ (in particular all $M < 1154$), while the Montgomery–Vaughan
     long-window threshold $2N^2 + 2N - 2 \le 310 < 1154$ certifies all $M \ge 310$, yielding
     unconditional all-prefix nonpositivity $\widetilde{\mathcal{D}}_N(M; \mu) \le 0$ for every
     $N \le 12$ and every $M \in \mathbb{N}$.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Direct Reserve-Proportional Window Dirichlet Sandwich, Lag Covariance, Poincaré Inequality, and $2N^2 - 2$ Long-Window Dissipation -/

/-- **Montgomery–Vaughan Window Inequality on `responseRoots N`
(`abs_window_responseRoots_sub_le_mv`):**
For every $N \ge 2$, window $[A+1, A+K]$, and coefficient family $a : \mathbb{C} \to \mathbb{C}$,
the window $\ell^2$ energy of $\sum_{\zeta \in \mathrm{responseRoots}(N)} a(\zeta)\zeta^k$
deviates from $K \sum_{\zeta} \|a(\zeta)\|^2$ by at most $N(N-1) \sum_{\zeta} \|a(\zeta)\|^2$. -/
theorem abs_window_responseRoots_sub_le_mv {N : ℕ} (hN : 2 ≤ N)
    (A K : ℕ) (a : ℂ → ℂ) :
    |(∑ k ∈ Finset.Icc (A + 1) (A + K),
        ‖∑ ζ ∈ responseRoots N, a ζ * ζ ^ k‖ ^ (2 : ℕ)) -
      (K : ℝ) * ∑ ζ ∈ responseRoots N, ‖a ζ‖ ^ (2 : ℕ)| ≤
      ((N : ℝ) * ((N : ℝ) - 1)) * ∑ ζ ∈ responseRoots N, ‖a ζ‖ ^ (2 : ℕ) :=
  abs_window_rootsOfUnity_sub_le hN (T := responseRoots N)
    (fun _ hζ => exists_pow_eq_one_of_mem_responseRoots hζ) a A K

/-- **Montgomery–Vaughan Window Lag Covariance Inequality (`abs_window_lag_covariance_sub_le_mv`):**
For every $N \ge 2$, weight $c$, lag $g$, and window $[A+1, A+K]$, the window lag covariance
deviates from $K \cdot \operatorname{periodCovariance}(N, c, g)$ by at most
$N(N-1) \cdot \operatorname{sieveVariance}(N, c)$. -/
theorem abs_window_lag_covariance_sub_le_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K g : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K),
        (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c) -
      (K : ℝ) * TwoLagSieve.periodCovariance N c g| ≤
      ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c := by
  set H := finiteHarmonicSum N c
  set c' := sieveRowShift c H
  have hN1 : 1 ≤ N := by omega
  have hs' : ∀ k, sieveSeq N c k - H = sieveSeq N c' k := fun k =>
    (sieveSeq_sieveRowShift hN1 k c H).symm
  set b : ℂ → ℝ := fun ζ => selbergMultiplesCoord N c' (orderOf ζ) with hb
  have hspec : ∀ k, (sieveSeq N c' k : ℂ) = ∑ ζ ∈ responseRoots N, (b ζ : ℂ) * ζ ^ k :=
    fun k => sieveSeq_eq_sum_responseRoots N c' k
  set ap : ℂ → ℂ := fun ζ => (b ζ : ℂ) * (1 + ζ ^ g) with hap
  set am : ℂ → ℂ := fun ζ => (b ζ : ℂ) * (1 - ζ ^ g) with ham
  have hup : ∀ k, (sieveSeq N c' k + sieveSeq N c' (k + g)) ^ 2 =
      ‖∑ ζ ∈ responseRoots N, ap ζ * ζ ^ k‖ ^ 2 := fun k => by
    have : ((sieveSeq N c' k + sieveSeq N c' (k + g) : ℝ) : ℂ) =
        ∑ ζ ∈ responseRoots N, ap ζ * ζ ^ k := by
      rw [Complex.ofReal_add, hspec, hspec, ← sum_add_distrib]
      refine sum_congr rfl fun ζ _ => ?_
      rw [hap, pow_add]
      ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hum : ∀ k, (sieveSeq N c' k - sieveSeq N c' (k + g)) ^ 2 =
      ‖∑ ζ ∈ responseRoots N, am ζ * ζ ^ k‖ ^ 2 := fun k => by
    have : ((sieveSeq N c' k - sieveSeq N c' (k + g) : ℝ) : ℂ) =
        ∑ ζ ∈ responseRoots N, am ζ * ζ ^ k := by
      rw [Complex.ofReal_sub, hspec, hspec, ← sum_sub_distrib]
      refine sum_congr rfl fun ζ _ => ?_
      rw [ham, pow_add]
      ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hP := abs_window_responseRoots_sub_le_mv hN A K ap
  have hM := abs_window_responseRoots_sub_le_mv hN A K am
  simp only [← hup] at hP
  simp only [← hum] at hM
  have hnorm : ∀ ζ ∈ responseRoots N, ‖ζ ^ g‖ = 1 := fun ζ hζ => by
    rw [norm_pow, norm_eq_one_of_mem_responseRoots hζ, one_pow]
  have hcoef : ∀ ζ ∈ responseRoots N,
      ‖ap ζ‖ ^ 2 - ‖am ζ‖ ^ 2 = 4 * (b ζ ^ 2 * (ζ ^ g).re) ∧
        ‖ap ζ‖ ^ 2 + ‖am ζ‖ ^ 2 = 4 * b ζ ^ 2 := by
    intro ζ hζ
    have hz := hnorm ζ hζ
    have hre : (ζ ^ g).re ^ 2 + (ζ ^ g).im ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq (ζ ^ g)
      rw [hz, Complex.normSq_apply] at h
      nlinarith
    simp only [hap, ham, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.sub_re,
      Complex.sub_im]
    constructor <;> nlinarith
  set Bp := ∑ ζ ∈ responseRoots N, ‖ap ζ‖ ^ 2
  set Bm := ∑ ζ ∈ responseRoots N, ‖am ζ‖ ^ 2
  have hdiff : Bp - Bm = 4 * ∑ ζ ∈ responseRoots N, b ζ ^ 2 * (ζ ^ g).re := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun ζ hζ => (hcoef ζ hζ).1
  have hsum : Bp + Bm = 4 * ∑ ζ ∈ responseRoots N, b ζ ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ζ hζ => (hcoef ζ hζ).2
  have hcov : ∑ ζ ∈ responseRoots N, b ζ ^ 2 * (ζ ^ g).re =
      TwoLagSieve.periodCovariance N c g := by
    have h := sum_responseRoots_orderOf_mul_pow N (fun q => selbergMultiplesCoord N c' q ^ 2) g
    have hre := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    have hl : ∀ ζ ∈ responseRoots N,
        (((selbergMultiplesCoord N c' (orderOf ζ) ^ 2 : ℝ) : ℂ) * ζ ^ g).re =
          b ζ ^ 2 * (ζ ^ g).re := fun ζ _ => by
      rw [Complex.re_ofReal_mul]
    rw [sum_congr rfl hl] at hre
    have hIoc : Ioc 1 N = Icc 2 N := by
      ext e
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hre, periodCovariance_eq_ramanujanLagWeight_diagonal, Icc_eq_cons_Ioc hN1,
      sum_cons, hIoc]
    have h1 : selbergMultiplesCoord N c' 1 = 0 := by
      have := finiteHarmonicSum_sieveRowShift hN1 c H
      unfold finiteHarmonicSum at this
      simp only [selbergMultiplesCoord, one_dvd, filter_true]
      rw [this]
      exact sub_self _
    rw [h1, zero_pow two_ne_zero, zero_mul, zero_add]
    refine sum_congr rfl fun e he => ?_
    rw [selbergMultiplesCoord_sieveRowShift_of_two_le N c H (mem_Icc.mp he).1, mul_comm]
  have hvar : ∑ ζ ∈ responseRoots N, b ζ ^ 2 = sieveVariance N c := by
    rw [sum_responseRoots_selberg_sq, selbergTotientDiagonalForm_sieveRowShift hN1, sub_self,
      zero_pow two_ne_zero, zero_add]
  have hpol : ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - H) * (sieveSeq N c (k + g) - H) =
      (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c' k + sieveSeq N c' (k + g)) ^ 2 -
        ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c' k - sieveSeq N c' (k + g)) ^ 2) / 4 := by
    rw [← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [hs', hs']
    ring
  rw [hpol, ← hcov, ← hvar]
  have hP' := abs_le.mp hP
  have hM' := abs_le.mp hM
  have hsum_N :
      ((N : ℝ) * ((N : ℝ) - 1)) * Bp + ((N : ℝ) * ((N : ℝ) - 1)) * Bm =
        4 * (((N : ℝ) * ((N : ℝ) - 1)) * ∑ ζ ∈ responseRoots N, b ζ ^ 2) := by
    have := congrArg (((N : ℝ) * ((N : ℝ) - 1)) * ·) hsum
    linarith
  have hdiff_K :
      (K : ℝ) * Bp - (K : ℝ) * Bm =
        4 * ((K : ℝ) * ∑ ζ ∈ responseRoots N, b ζ ^ 2 * (ζ ^ g).re) := by
    have := congrArg ((K : ℝ) * ·) hdiff
    linarith
  rw [abs_le]
  constructor <;> linarith [hP'.1, hP'.2, hM'.1, hM'.2, hsum_N, hdiff_K]

/-- **Two-sided Montgomery–Vaughan Window Lag Covariance Sandwich (`window_lag_covariance_sandwich_mv`):**
Two-sided form of `abs_window_lag_covariance_sub_le_mv`. -/
theorem window_lag_covariance_sandwich_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K g : ℕ) :
    (K : ℝ) * TwoLagSieve.periodCovariance N c g -
        ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c ≤
      ∑ k ∈ Finset.Icc (A + 1) (A + K),
        (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c) ∧
    ∑ k ∈ Finset.Icc (A + 1) (A + K),
        (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c) ≤
      (K : ℝ) * TwoLagSieve.periodCovariance N c g +
        ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c := by
  have h := abs_le.mp (abs_window_lag_covariance_sub_le_mv hN c A K g)
  exact ⟨by linarith, by linarith⟩

/-- **Direct Reserve-Proportional Window Dirichlet Sandwich
(`abs_shortWindowDirichletEnergy_sub_reserve_le_mv`):**
For every $N \ge 2$, weight $c$, and window $[A+1, A+K]$, the short-window Dirichlet energy
deviates from $2K\mathcal{R}_N(c)$ by at most $2N(N-1)\mathcal{R}_N(c)$. -/
theorem abs_shortWindowDirichletEnergy_sub_reserve_le_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K : ℕ) :
    |shortWindowDirichletEnergy N A K c -
        2 * (K : ℝ) * sieveSuccessorReserve N c| ≤
      2 * ((N : ℝ) * ((N : ℝ) - 1)) * sieveSuccessorReserve N c := by
  set H := finiteHarmonicSum N c
  set c' := sieveRowShift c H
  have hN1 : 1 ≤ N := by omega
  have hs' : ∀ k, sieveSeq N c k - H = sieveSeq N c' k := fun k =>
    (sieveSeq_sieveRowShift hN1 k c H).symm
  set b : ℂ → ℝ := fun ζ => selbergMultiplesCoord N c' (orderOf ζ) with hb
  have hspec : ∀ k, (sieveSeq N c' k : ℂ) = ∑ ζ ∈ responseRoots N, (b ζ : ℂ) * ζ ^ k :=
    fun k => sieveSeq_eq_sum_responseRoots N c' k
  set am : ℂ → ℂ := fun ζ => (b ζ : ℂ) * (1 - ζ) with ham
  set ap : ℂ → ℂ := fun ζ => (b ζ : ℂ) * (1 + ζ) with hap
  have hum : ∀ k, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 =
      ‖∑ ζ ∈ responseRoots N, am ζ * ζ ^ k‖ ^ 2 := fun k => by
    have hdiff : sieveSeq N c (k + 1) - sieveSeq N c k =
        -(sieveSeq N c' k - sieveSeq N c' (k + 1)) := by
      rw [← hs', ← hs']
      ring
    have hcomplex : ((sieveSeq N c' k - sieveSeq N c' (k + 1) : ℝ) : ℂ) =
        ∑ ζ ∈ responseRoots N, am ζ * ζ ^ k := by
      rw [Complex.ofReal_sub, hspec, hspec, ← sum_sub_distrib]
      refine sum_congr rfl fun ζ _ => ?_
      rw [ham, pow_succ]
      ring
    rw [hdiff, neg_sq, ← sq_abs (sieveSeq N c' k - sieveSeq N c' (k + 1)),
      ← Real.norm_eq_abs, ← Complex.norm_real, hcomplex]
  have hdir : shortWindowDirichletEnergy N A K c =
      ∑ k ∈ Icc (A + 1) (A + K), ‖∑ ζ ∈ responseRoots N, am ζ * ζ ^ k‖ ^ 2 := by
    unfold shortWindowDirichletEnergy
    exact sum_congr rfl fun k _ => hum k
  have hM := abs_window_responseRoots_sub_le_mv hN A K am
  rw [← hdir] at hM
  have hnorm : ∀ ζ ∈ responseRoots N, ‖ζ‖ = 1 :=
    fun ζ hζ => norm_eq_one_of_mem_responseRoots hζ
  have hcoef : ∀ ζ ∈ responseRoots N,
      ‖ap ζ‖ ^ 2 - ‖am ζ‖ ^ 2 = 4 * (b ζ ^ 2 * ζ.re) ∧
        ‖ap ζ‖ ^ 2 + ‖am ζ‖ ^ 2 = 4 * b ζ ^ 2 := by
    intro ζ hζ
    have hz := hnorm ζ hζ
    have hre : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq ζ
      rw [hz, Complex.normSq_apply] at h
      nlinarith
    simp only [hap, ham, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.sub_re,
      Complex.sub_im]
    constructor <;> nlinarith
  set Bp := ∑ ζ ∈ responseRoots N, ‖ap ζ‖ ^ 2
  set Bm := ∑ ζ ∈ responseRoots N, ‖am ζ‖ ^ 2
  have hdiff : Bp - Bm = 4 * ∑ ζ ∈ responseRoots N, b ζ ^ 2 * ζ.re := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun ζ hζ => (hcoef ζ hζ).1
  have hsum : Bp + Bm = 4 * ∑ ζ ∈ responseRoots N, b ζ ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ζ hζ => (hcoef ζ hζ).2
  have hcov : ∑ ζ ∈ responseRoots N, b ζ ^ 2 * ζ.re =
      TwoLagSieve.periodCovariance N c 1 := by
    have h := sum_responseRoots_orderOf_mul_pow N (fun q => selbergMultiplesCoord N c' q ^ 2) 1
    have hre := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.ofReal_re, pow_one] at hre
    have hl : ∀ ζ ∈ responseRoots N,
        (((selbergMultiplesCoord N c' (orderOf ζ) ^ 2 : ℝ) : ℂ) * ζ).re =
          b ζ ^ 2 * ζ.re := fun ζ _ => by
      rw [Complex.re_ofReal_mul]
    rw [sum_congr rfl hl] at hre
    have hIoc : Ioc 1 N = Icc 2 N := by
      ext e
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hre, periodCovariance_eq_ramanujanLagWeight_diagonal, Icc_eq_cons_Ioc hN1,
      sum_cons, hIoc]
    have h1 : selbergMultiplesCoord N c' 1 = 0 := by
      have := finiteHarmonicSum_sieveRowShift hN1 c H
      unfold finiteHarmonicSum at this
      simp only [selbergMultiplesCoord, one_dvd, filter_true]
      rw [this]
      exact sub_self _
    rw [h1, zero_pow two_ne_zero, zero_mul, zero_add]
    refine sum_congr rfl fun e he => ?_
    rw [selbergMultiplesCoord_sieveRowShift_of_two_le N c H (mem_Icc.mp he).1, mul_comm]
  have hvar : ∑ ζ ∈ responseRoots N, b ζ ^ 2 = sieveVariance N c := by
    rw [sum_responseRoots_selberg_sq, selbergTotientDiagonalForm_sieveRowShift hN1, sub_self,
      zero_pow two_ne_zero, zero_add]
  have hcov1 := periodCovariance_one_eq_sub_reserve hN1 c
  have hBm : Bm = 2 * sieveSuccessorReserve N c := by
    linarith [hdiff, hsum, hcov, hvar, hcov1]
  change |shortWindowDirichletEnergy N A K c - (K : ℝ) * Bm| ≤
    ((N : ℝ) * ((N : ℝ) - 1)) * Bm at hM
  rw [hBm] at hM
  calc |shortWindowDirichletEnergy N A K c - 2 * (K : ℝ) * sieveSuccessorReserve N c|
      = |shortWindowDirichletEnergy N A K c - (K : ℝ) * (2 * sieveSuccessorReserve N c)| := by
          ring_nf
    _ ≤ ((N : ℝ) * ((N : ℝ) - 1)) * (2 * sieveSuccessorReserve N c) := hM
    _ = 2 * ((N : ℝ) * ((N : ℝ) - 1)) * sieveSuccessorReserve N c := by ring

/-- **Two-Sided Reserve-Proportional and Variance-Proportional Window Dirichlet Bounds
(`shortWindowDirichletEnergy_bounds_mv`):**
For every $N \ge 2$, weight $c$, and window $[A+1, A+K]$:
1. $2(K - N(N-1))\mathcal{R}_N(c) \le D_W \le 2(K + N(N-1))\mathcal{R}_N(c)$,
2. $|D_W - 2K\mathcal{R}_N(c)| \le 4N(N-1)V(c)$,
3. $(K - N(N-1))V(c) \le D_W$. -/
theorem shortWindowDirichletEnergy_bounds_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K : ℕ) :
    2 * ((K : ℝ) - (N : ℝ) * ((N : ℝ) - 1)) * sieveSuccessorReserve N c ≤
        shortWindowDirichletEnergy N A K c ∧
      shortWindowDirichletEnergy N A K c ≤
        2 * ((K : ℝ) + (N : ℝ) * ((N : ℝ) - 1)) * sieveSuccessorReserve N c ∧
      |shortWindowDirichletEnergy N A K c - 2 * (K : ℝ) * sieveSuccessorReserve N c| ≤
        4 * ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c ∧
      ((K : ℝ) - (N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c ≤
        shortWindowDirichletEnergy N A K c := by
  have habs := abs_shortWindowDirichletEnergy_sub_reserve_le_mv hN c A K
  have h1 := (abs_le.mp habs).1
  have h2 := (abs_le.mp habs).2
  have hN_nonneg : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  obtain ⟨hvar_le, hres_le⟩ := half_sieveVariance_le_sieveSuccessorReserve (by omega : 1 ≤ N) c
  have hvar_nonneg : 0 ≤ sieveVariance N c :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hdir_nonneg : 0 ≤ shortWindowDirichletEnergy N A K c := by
    unfold shortWindowDirichletEnergy
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨by linarith, by linarith, by nlinarith, ?_⟩
  rcases le_or_gt ((N : ℝ) * ((N : ℝ) - 1)) (K : ℝ) with hK | hK
  · nlinarith
  · have : ((K : ℝ) - (N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c ≤ 0 := by
      nlinarith
    linarith

/-- **Montgomery–Vaughan Centered Window Variance Bound (`window_sum_sq_centered_bounds_mv`):**
For every $N \ge 2$, weight $c$, and window $[A+1, A+K]$,
$|\sum_{k=A+1}^{A+K} (s_{N,c}(k) - H_c(N))^2 - K V(c)| \le N(N-1)V(c)$. -/
theorem window_sum_sq_centered_bounds_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) ^ 2 -
        (K : ℝ) * sieveVariance N c| ≤
      ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c := by
  have h := isWindowSandwichConstant_mv hN A K c (finiteHarmonicSum N c)
  rwa [sub_self, zero_pow two_ne_zero, zero_add] at h

/-- **Montgomery–Vaughan Window Poincaré Inequality (`window_poincare_mv`):**
For every $N \ge 2$, weight $c$, and window $[A+1, A+K]$,
$$\sum_{k=A+1}^{A+K} \bigl(s_{N,c}(k) - H_c(N)\bigr)^2 \le
  \operatorname{shortWindowDirichletEnergy}(N, A, K, c) +
    2N(N-1)\operatorname{sieveVariance}(N, c).$$ -/
theorem window_poincare_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K : ℕ) :
    (∑ k ∈ Finset.Icc (A + 1) (A + K),
        (sieveSeq N c k - finiteHarmonicSum N c) ^ (2 : ℕ)) ≤
      shortWindowDirichletEnergy N A K c +
        2 * ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c := by
  have hup := (abs_le.mp (window_sum_sq_centered_bounds_mv hN c A K)).2
  have hlow := (shortWindowDirichletEnergy_bounds_mv hN c A K).2.2.2
  linarith

/-- **Sharpened Long-Window Dissipation at Every Phase (`two_mul_shortWindowRenormalizedDefect_le_mv`):**
For every $N \ge 2$, weight $c$, phase $A$, and length $K$:
$$2\widetilde{\mathcal{D}}_N(A, K; c) \le
  2H_c(N)^2 - s_{N,c}(A+1)^2 - \bigl(K - (2N^2 - 2)\bigr)V(c) \le
  2H_c(N)^2 - \bigl(K - (2N^2 - 2)\bigr)V(c).$$ -/
theorem two_mul_shortWindowRenormalizedDefect_le_mv {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (A K : ℕ) :
    2 * shortWindowRenormalizedDefect N A K c ≤
        2 * finiteHarmonicSum N c ^ (2 : ℕ) - sieveSeq N c (A + 1) ^ (2 : ℕ) -
          ((K : ℝ) - (2 * (N : ℝ) ^ (2 : ℕ) - 2)) * sieveVariance N c ∧
      2 * shortWindowRenormalizedDefect N A K c ≤
        2 * finiteHarmonicSum N c ^ (2 : ℕ) -
          ((K : ℝ) - (2 * (N : ℝ) ^ (2 : ℕ) - 2)) * sieveVariance N c := by
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N A K c
  have hdir := (shortWindowDirichletEnergy_bounds_mv hN c A K).2.2.2
  have hpt := sieveSeq_sub_harmonic_sq_le (by omega : 1 ≤ N) c (A + K + 1)
  have hphi : 2 * (cyclotomicIncidenceOrder N : ℝ) ≤ (N : ℝ) * ((N : ℝ) + 1) := by
    exact_mod_cast two_mul_cyclotomicIncidenceOrder_le N
  have hvar_nonneg : 0 ≤ sieveVariance N c :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hsq : sieveSeq N c (A + K + 1) ^ (2 : ℕ) ≤
      2 * (sieveSeq N c (A + K + 1) - finiteHarmonicSum N c) ^ (2 : ℕ) +
        2 * finiteHarmonicSum N c ^ (2 : ℕ) := by
    have : 0 ≤ (sieveSeq N c (A + K + 1) - 2 * finiteHarmonicSum N c) ^ (2 : ℕ) := sq_nonneg _
    linarith
  have hstart : 0 ≤ sieveSeq N c (A + 1) ^ (2 : ℕ) := sq_nonneg _
  have h1 : 2 * shortWindowRenormalizedDefect N A K c ≤
      2 * finiteHarmonicSum N c ^ (2 : ℕ) - sieveSeq N c (A + 1) ^ (2 : ℕ) -
        ((K : ℝ) - (2 * (N : ℝ) ^ (2 : ℕ) - 2)) * sieveVariance N c := by
    nlinarith [hpol, hdir, hpt, hphi, hvar_nonneg, hsq]
  exact ⟨h1, by linarith⟩

private theorem shortWindowRenormalizedDefect_zero_eq_prefix (N M : ℕ) (c : ℕ → ℝ) :
    shortWindowRenormalizedDefect N 0 M c = sieveRenormalizedPrefixDefect N M c := by
  unfold shortWindowRenormalizedDefect
  simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]

/-- **Sharpened Prefix Dissipation at Quadratic Order $2N^2 - 2$
(`two_mul_sieveRenormalizedPrefixDefect_le_mv`):**
For every $N \ge 2$, weight $c$, and prefix $M$:
$$2\widetilde{\mathcal{D}}_N(M; c) \le
  2H_c(N)^2 - s_{N,c}(1)^2 - \bigl(M - (2N^2 - 2)\bigr)V(c).$$ -/
theorem two_mul_sieveRenormalizedPrefixDefect_le_mv {N : ℕ} (hN : 2 ≤ N)
    (M : ℕ) (c : ℕ → ℝ) :
    2 * sieveRenormalizedPrefixDefect N M c ≤
      2 * finiteHarmonicSum N c ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) -
        ((M : ℝ) - (2 * (N : ℝ) ^ (2 : ℕ) - 2)) * sieveVariance N c := by
  have hw := (two_mul_shortWindowRenormalizedDefect_le_mv hN c 0 M).1
  simpa only [shortWindowRenormalizedDefect_zero_eq_prefix, zero_add] using hw

/-- **Sharpened Möbius Long-Window Dissipation Bound (`two_mul_moebius_defect_le_mv_window`):**
For every $N \ge 2$ and every $M \ge 2N^2 - 2$:
$$2\widetilde{\mathcal{D}}_N(M; \mu) \le 1 - \frac{M - (2N^2 - 2)}{2N}.$$ -/
theorem two_mul_moebius_defect_le_mv_window {N M : ℕ} (hN : 2 ≤ N)
    (hM : 2 * (N : ℝ) ^ 2 - 2 ≤ (M : ℝ)) :
    2 * sieveRenormalizedPrefixDefect N M moebiusReal ≤
      1 - ((M : ℝ) - (2 * (N : ℝ) ^ 2 - 2)) / (2 * (N : ℝ)) := by
  have hdiss := two_mul_sieveRenormalizedPrefixDefect_le_mv hN M moebiusReal
  have hH_sq : finiteHarmonicSum N moebiusReal ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (abs_finiteHarmonicSum_moebiusReal_le_one N)
  have hs1 : sieveSeq N moebiusReal 1 = 1 := by
    rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) (by omega), if_pos rfl]
  obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hN
  obtain ⟨hpI, hpp, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpN⟩ := mem_Icc.mp hpI
  have hμ : moebiusReal p = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hpp]; norm_num
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpNR : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hmode : 1 / (2 * (N : ℝ)) ≤ (p.totient : ℝ) * (moebiusReal p / (p : ℝ)) ^ 2 := by
    rw [Nat.totient_prime hpp, hμ, Nat.cast_sub (by omega), div_pow, neg_one_sq, Nat.cast_one]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hV := hmode.trans (primeTail_mode_le_sieveVariance hp moebiusReal)
  have hgap0 : 0 ≤ (M : ℝ) - (2 * (N : ℝ) ^ 2 - 2) := by linarith
  have hcomp : ((M : ℝ) - (2 * (N : ℝ) ^ 2 - 2)) / (2 * (N : ℝ)) ≤
      ((M : ℝ) - (2 * (N : ℝ) ^ 2 - 2)) * sieveVariance N moebiusReal := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hV hgap0
  rw [hs1] at hdiss
  linarith

/-- **Unconditional Möbius Defect Nonpositivity Above $2N^2 + 2N - 2$
(`moebius_defect_nonpos_of_mv_window`):**
For every $N \ge 2$ and every $M \ge 2N^2 + 2N - 2$,
$\widetilde{\mathcal{D}}_N(M; \mu) \le 0$. -/
theorem moebius_defect_nonpos_of_mv_window {N M : ℕ} (hN : 2 ≤ N)
    (hM : 2 * (N : ℝ) ^ 2 + 2 * (N : ℝ) - 2 ≤ (M : ℝ)) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := two_mul_moebius_defect_le_mv_window hN (by linarith)
  have hdiv : 1 ≤ ((M : ℝ) - (2 * (N : ℝ) ^ 2 - 2)) / (2 * (N : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- **Strict Möbius Defect Negativity Above $2N^2 + 2N - 2$
(`moebius_defect_neg_of_mv_window`):**
For every $N \ge 2$ and every $M > 2N^2 + 2N - 2$,
$\widetilde{\mathcal{D}}_N(M; \mu) < 0$. -/
theorem moebius_defect_neg_of_mv_window {N M : ℕ} (hN : 2 ≤ N)
    (hM : 2 * (N : ℝ) ^ 2 + 2 * (N : ℝ) - 2 < (M : ℝ)) :
    sieveRenormalizedPrefixDefect N M moebiusReal < 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := two_mul_moebius_defect_le_mv_window hN (by linarith)
  have hdiv : 1 < ((M : ℝ) - (2 * (N : ℝ) ^ 2 - 2)) / (2 * (N : ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  linarith

/-- **Sharpened Power-Damped Long-Window Defect Nonpositivity
(`pmPowerDamped_defect_nonpos_of_mv_window`):**
For every $N \ge 2$, $\varepsilon > 0$, and $M$ satisfying
$2N^2 - 2 + 34N^{1+2\varepsilon} \le M$,
$\widetilde{\mathcal{D}}_N(M; c_\varepsilon) \le 0$. -/
theorem pmPowerDamped_defect_nonpos_of_mv_window {N M : ℕ} {ε : ℝ}
    (hN : 2 ≤ N) (hε : 0 < ε)
    (hM : 2 * (N : ℝ) ^ 2 - 2 + 34 * (N : ℝ) ^ (1 + 2 * ε) ≤ (M : ℝ)) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow0 : 0 ≤ (N : ℝ) ^ (1 + 2 * ε) := Real.rpow_nonneg hNpos.le _
  have hdiss := two_mul_sieveRenormalizedPrefixDefect_le_mv hN M (pmPowerDampedRealWeight ε)
  have hH_sq : finiteHarmonicSum N (pmPowerDampedRealWeight ε) ^ 2 ≤ 9 := by
    have h := abs_finiteHarmonicSum_pmPowerDamped_le_three hε N
    rw [← sq_abs]
    nlinarith [abs_nonneg (finiteHarmonicSum N (pmPowerDampedRealWeight ε))]
  have hs1 : sieveSeq N (pmPowerDampedRealWeight ε) 1 = 1 := by
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega),
      pmPowerDampedDivisorCoeff_one]
  obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hN
  obtain ⟨hpI, hpp, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpN⟩ := mem_Icc.mp hpI
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hpNR : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hμ : moebiusReal p ^ 2 = 1 := by
    unfold moebiusReal; rw [moebius_apply_prime hpp]; norm_num
  have hpow : ((p : ℝ) ^ (-ε)) ^ 2 = (p : ℝ) ^ (-(2 * ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; push_cast; ring_nf
  have hNp : (N : ℝ) ^ (-(2 * ε)) ≤ (p : ℝ) ^ (-(2 * ε)) :=
    Real.rpow_le_rpow_of_nonpos hp0 hpNR (by linarith)
  have hmode : (N : ℝ) ^ (-(2 * ε)) / (2 * N) ≤
      (p.totient : ℝ) * (pmPowerDampedRealWeight ε p / (p : ℝ)) ^ 2 := by
    rw [Nat.totient_prime hpp, Nat.cast_sub (by omega), Nat.cast_one, pmPowerDampedRealWeight,
      div_pow, mul_pow, hμ, one_mul, hpow]
    have h1 : 1 / (2 * (N : ℝ)) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc (N : ℝ) ^ (-(2 * ε)) / (2 * N) = (N : ℝ) ^ (-(2 * ε)) * (1 / (2 * N)) := by ring
      _ ≤ (p : ℝ) ^ (-(2 * ε)) * (((p : ℝ) - 1) / (p : ℝ) ^ 2) :=
          mul_le_mul hNp h1 (by positivity) (Real.rpow_nonneg hp0.le _)
      _ = _ := by ring
  have hV := hmode.trans (primeTail_mode_le_sieveVariance hp (pmPowerDampedRealWeight ε))
  have hgap0 : 0 ≤ (M : ℝ) - (2 * (N : ℝ) ^ 2 - 2) := by linarith
  have hcomp := mul_le_mul_of_nonneg_left hV hgap0
  have hsplit : (N : ℝ) ^ (1 + 2 * ε) * (N : ℝ) ^ (-(2 * ε)) = N := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hq : 17 ≤ ((M : ℝ) - (2 * (N : ℝ) ^ 2 - 2)) * ((N : ℝ) ^ (-(2 * ε)) / (2 * N)) := by
    calc (17 : ℝ) = 34 * ((N : ℝ) ^ (1 + 2 * ε) * (N : ℝ) ^ (-(2 * ε))) / (2 * N) := by
          rw [hsplit]; field_simp; ring
      _ = 34 * (N : ℝ) ^ (1 + 2 * ε) * ((N : ℝ) ^ (-(2 * ε)) / (2 * N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [hs1] at hdiss
  linarith

/-! ## §2. Exact Variational Characterization of the Optimal Window Sandwich and Reserve Dirichlet Constants -/

/-- **Optimal Window Sandwich Constant (`optimalWindowSandwichConstant`):**
The infimum of all admissible window variance sandwich constants at horizon $N$. -/
def optimalWindowSandwichConstant (N : ℕ) : ℝ :=
  sInf {S : ℝ | IsWindowSandwichConstant N S}

/-- **Admissible Reserve-Proportional Window Dirichlet Constant (`IsReserveWindowDirichletConstant`):**
A constant $R \in \mathbb{R}$ is an admissible reserve window Dirichlet constant at horizon $N$ if
for all weights $c$ and all windows $[A+1, A+K]$,
$|\operatorname{shortWindowDirichletEnergy}(N, A, K, c) - 2K\mathcal{R}_N(c)| \le 2R\mathcal{R}_N(c)$. -/
def IsReserveWindowDirichletConstant (N : ℕ) (R : ℝ) : Prop :=
  ∀ (c : ℕ → ℝ) (A K : ℕ),
    |shortWindowDirichletEnergy N A K c - 2 * (K : ℝ) * sieveSuccessorReserve N c| ≤
      2 * R * sieveSuccessorReserve N c

/-- **Optimal Reserve Window Dirichlet Constant (`optimalReserveDirichletConstant`):**
The infimum of all nonnegative admissible reserve window Dirichlet constants at horizon $N$. -/
def optimalReserveDirichletConstant (N : ℕ) : ℝ :=
  sInf {R : ℝ | 0 ≤ R ∧ IsReserveWindowDirichletConstant N R}

/-- **Attainment and Exact Quadratic Sandwich for `optimalWindowSandwichConstant`
(`optimalWindowSandwichConstant_bounds`):**
For every $N \ge 2$, `optimalWindowSandwichConstant N` is itself an admissible window sandwich
constant and satisfies $\Phi(N) - 2 \le S_{\mathrm{opt}}(N) \le N(N-1)$. -/
theorem optimalWindowSandwichConstant_bounds {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N (optimalWindowSandwichConstant N) ∧
      (cyclotomicIncidenceOrder N : ℝ) - 2 ≤ optimalWindowSandwichConstant N ∧
      optimalWindowSandwichConstant N ≤ (N : ℝ) * ((N : ℝ) - 1) := by
  let E : Set ℝ := {S : ℝ | IsWindowSandwichConstant N S}
  have hmv : (N : ℝ) * ((N : ℝ) - 1) ∈ E := isWindowSandwichConstant_mv hN
  have hne : E.Nonempty := ⟨_, hmv⟩
  have hbdd : BddBelow E := ⟨(cyclotomicIncidenceOrder N : ℝ) - 2, fun S hS =>
    cyclotomicIncidenceOrder_sub_two_le_of_isWindowSandwichConstant hN hS⟩
  have hatt : IsWindowSandwichConstant N (optimalWindowSandwichConstant N) := by
    intro A K c κ
    set err := |∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - κ) ^ 2 -
      (K : ℝ) * ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c)|
    set V := (finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c
    have hV_nonneg : 0 ≤ V := add_nonneg (sq_nonneg _)
      (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    rcases eq_or_lt_of_le hV_nonneg with hV0 | hV_pos
    · have h0 := hmv A K c κ
      change err ≤ ((N : ℝ) * ((N : ℝ) - 1)) * V at h0
      rw [← hV0, mul_zero] at h0
      change err ≤ optimalWindowSandwichConstant N * V
      rw [← hV0, mul_zero]
      exact h0
    · change err ≤ optimalWindowSandwichConstant N * V
      rw [← div_le_iff₀ hV_pos]
      exact le_csInf hne fun S hS => (div_le_iff₀ hV_pos).mpr (hS A K c κ)
  refine ⟨hatt, ?_, csInf_le hbdd hmv⟩
  exact cyclotomicIncidenceOrder_sub_two_le_of_isWindowSandwichConstant hN hatt

/-- **Attainment and Montgomery–Vaughan Bound for `optimalReserveDirichletConstant`
(`optimalReserveDirichletConstant_bounds`):**
For every $N \ge 2$, `optimalReserveDirichletConstant N` is nonnegative, is itself an admissible
reserve window Dirichlet constant, and satisfies $0 \le R_{\mathrm{opt}}(N) \le N(N-1)$. -/
theorem optimalReserveDirichletConstant_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ optimalReserveDirichletConstant N ∧
      IsReserveWindowDirichletConstant N (optimalReserveDirichletConstant N) ∧
      optimalReserveDirichletConstant N ≤ (N : ℝ) * ((N : ℝ) - 1) := by
  let E : Set ℝ := {R : ℝ | 0 ≤ R ∧ IsReserveWindowDirichletConstant N R}
  have hN_nonneg : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hmv : (N : ℝ) * ((N : ℝ) - 1) ∈ E :=
    ⟨hN_nonneg, fun c A K => abs_shortWindowDirichletEnergy_sub_reserve_le_mv hN c A K⟩
  have hne : E.Nonempty := ⟨_, hmv⟩
  have hbdd : BddBelow E := ⟨0, fun R hR => hR.1⟩
  have hnonneg : 0 ≤ optimalReserveDirichletConstant N :=
    le_csInf hne fun R hR => hR.1
  have hatt : IsReserveWindowDirichletConstant N (optimalReserveDirichletConstant N) := by
    intro c A K
    set err := |shortWindowDirichletEnergy N A K c - 2 * (K : ℝ) * sieveSuccessorReserve N c|
    set twoR := 2 * sieveSuccessorReserve N c
    have hvar_nonneg : 0 ≤ sieveVariance N c :=
      sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hres_nonneg : 0 ≤ sieveSuccessorReserve N c := by
      have := (half_sieveVariance_le_sieveSuccessorReserve (by omega : 1 ≤ N) c).1
      linarith
    have hR_nonneg : 0 ≤ twoR := by linarith
    rcases eq_or_lt_of_le hR_nonneg with hR0 | hR_pos
    · have h0 := hmv.2 c A K
      change err ≤ 2 * ((N : ℝ) * ((N : ℝ) - 1)) * sieveSuccessorReserve N c at h0
      have h0' : 2 * ((N : ℝ) * ((N : ℝ) - 1)) * sieveSuccessorReserve N c =
          ((N : ℝ) * ((N : ℝ) - 1)) * twoR := by ring
      rw [h0', ← hR0, mul_zero] at h0
      have hgoal : 2 * optimalReserveDirichletConstant N * sieveSuccessorReserve N c =
          optimalReserveDirichletConstant N * twoR := by ring
      rw [hgoal, ← hR0, mul_zero]
      exact h0
    · have hgoal : 2 * optimalReserveDirichletConstant N * sieveSuccessorReserve N c =
          optimalReserveDirichletConstant N * twoR := by ring
      rw [hgoal, ← div_le_iff₀ hR_pos]
      refine le_csInf hne fun R hR => (div_le_iff₀ hR_pos).mpr ?_
      have hR_eq : R * twoR = 2 * R * sieveSuccessorReserve N c := by ring
      rw [hR_eq]
      exact hR.2 c A K
  exact ⟨hnonneg, hatt, csInf_le hbdd hmv⟩

/-- **Optimal-Constant Window Poincaré and Prefix Dissipation Law
(`window_poincare_and_prefix_dissipation_optimal`):**
For every $N \ge 2$, weight $c$, window $[A+1, A+K]$, and prefix $M$:
1. $\sum_{k=A+1}^{A+K} (s_{N,c}(k) - H_c(N))^2 \le D_W + (S_{\mathrm{opt}}(N) + R_{\mathrm{opt}}(N))V(c)$,
2. $2\widetilde{\mathcal{D}}_N(M; c) \le 2H_c(N)^2 - s_{N,c}(1)^2 -
   (M - (R_{\mathrm{opt}}(N) + 2\Phi(N) - 2))V(c)$. -/
theorem window_poincare_and_prefix_dissipation_optimal {N : ℕ} (hN : 2 ≤ N)
    (M : ℕ) (c : ℕ → ℝ) (A K : ℕ) :
    (∑ k ∈ Finset.Icc (A + 1) (A + K),
        (sieveSeq N c k - finiteHarmonicSum N c) ^ (2 : ℕ)) ≤
      shortWindowDirichletEnergy N A K c +
        (optimalWindowSandwichConstant N + optimalReserveDirichletConstant N) *
          sieveVariance N c ∧
    2 * sieveRenormalizedPrefixDefect N M c ≤
      2 * finiteHarmonicSum N c ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) -
        ((M : ℝ) - (optimalReserveDirichletConstant N + 2 * (cyclotomicIncidenceOrder N : ℝ) - 2)) *
          sieveVariance N c := by
  have hS := (optimalWindowSandwichConstant_bounds hN).1
  have hR_all := optimalReserveDirichletConstant_bounds hN
  have hR_nonneg := hR_all.1
  have hR := hR_all.2.1
  have hvar_le := (half_sieveVariance_le_sieveSuccessorReserve (by omega : 1 ≤ N) c).1
  have hvar_nonneg : 0 ≤ sieveVariance N c :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hcoercive : ∀ A₀ K₀ : ℕ,
      ((K₀ : ℝ) - optimalReserveDirichletConstant N) * sieveVariance N c ≤
        shortWindowDirichletEnergy N A₀ K₀ c := by
    intro A₀ K₀
    have hlow := (abs_le.mp (hR c A₀ K₀)).1
    have hdir_nonneg : 0 ≤ shortWindowDirichletEnergy N A₀ K₀ c :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rcases le_or_gt (optimalReserveDirichletConstant N) (K₀ : ℝ) with hK | hK
    · nlinarith
    · have : ((K₀ : ℝ) - optimalReserveDirichletConstant N) * sieveVariance N c ≤ 0 := by
        nlinarith
      linarith
  have hS_win := hS A K c (finiteHarmonicSum N c)
  rw [sub_self, zero_pow two_ne_zero, zero_add] at hS_win
  have hup := (abs_le.mp hS_win).2
  have hco1 := hcoercive A K
  have hco2 := hcoercive 0 M
  have hpol := two_mul_shortWindowRenormalizedDefect_eq N 0 M c
  rw [shortWindowRenormalizedDefect_zero_eq_prefix, zero_add, zero_add] at hpol
  have hpt := sieveSeq_sub_harmonic_sq_le (by omega : 1 ≤ N) c (M + 1)
  have hsq : sieveSeq N c (M + 1) ^ (2 : ℕ) ≤
      2 * (sieveSeq N c (M + 1) - finiteHarmonicSum N c) ^ (2 : ℕ) +
        2 * finiteHarmonicSum N c ^ (2 : ℕ) := by
    have : 0 ≤ (sieveSeq N c (M + 1) - 2 * finiteHarmonicSum N c) ^ (2 : ℕ) := sq_nonneg _
    linarith
  refine ⟨by linarith, by linarith⟩

/-! ## §3. Prime-Pairing Divisor-Window Identity, the $2^{\omega(r)-2}$ Radical Envelope, and Three-Prime Radical Nonpositivity -/

/-- **Prime-Pairing Divisor-Window Identity (`sieveSeq_moebiusReal_prime_mul_eq_window`):**
For any horizon $N$, prime $p$, and positive integer $a$ with $p \nmid a$, pairing each divisor
$d \mid a$ with $pd \mid pa$ cancels all divisors satisfying $pd \le N$, leaving only the top
divisor window $N < pd$ and $d \le N$:
$$s_{N,\mu}(pa) = \sum_{\substack{d \mid a \\ N < pd \wedge d \le N}} \mu(d).$$ -/
theorem sieveSeq_moebiusReal_prime_mul_eq_window (N : ℕ) {p a : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hpa : ¬ p ∣ a) :
    sieveSeq N moebiusReal (p * a) =
      ∑ d ∈ a.divisors.filter (fun d => N < p * d ∧ d ≤ N), moebiusReal d := by
  have hpa0 : p * a ≠ 0 := mul_ne_zero hp.ne_zero ha
  have hdiv_eq : (Finset.Icc 1 N).filter (fun q => q ∣ p * a) =
      (p * a).divisors.filter (fun q => q ≤ N) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, hqN⟩, hvd⟩
      exact ⟨⟨hvd, hpa0⟩, hqN⟩
    · rintro ⟨⟨hvd, _⟩, hqN⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hvd (Nat.pos_of_ne_zero hpa0), hqN⟩, hvd⟩
  unfold sieveSeq
  rw [hdiv_eq, ← Finset.sum_filter_add_sum_filter_not
    ((p * a).divisors.filter (fun q => q ≤ N)) (fun q => p ∣ q)]
  have hnot_p :
      ((p * a).divisors.filter (fun q => q ≤ N)).filter (fun q => ¬ p ∣ q) =
        a.divisors.filter (fun d => d ≤ N) := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hvd, _⟩, hqN⟩, hnp⟩
      have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hnp
      exact ⟨⟨hcop.symm.dvd_of_dvd_mul_left hvd, ha⟩, hqN⟩
    · rintro ⟨⟨hda, _⟩, hqN⟩
      exact ⟨⟨⟨dvd_mul_of_dvd_right hda p, hpa0⟩, hqN⟩, fun hpk => hpa (hpk.trans hda)⟩
  have hp_div :
      (∑ q ∈ ((p * a).divisors.filter (fun q => q ≤ N)).filter (fun q => p ∣ q), moebiusReal q) =
        -∑ d ∈ a.divisors.filter (fun d => p * d ≤ N), moebiusReal d := by
    rw [← Finset.sum_neg_distrib]
    refine (Finset.sum_nbij (fun d => p * d) ?_ ?_ ?_ ?_).symm
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      exact ⟨⟨⟨mul_dvd_mul_left p hd.1.1, hpa0⟩, hd.2⟩, dvd_mul_right p d⟩
    · intro d₁ _ d₂ _ hmul
      exact mul_left_cancel₀ hp.ne_zero hmul
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hq
      obtain ⟨d, rfl⟩ := hq.2
      refine ⟨d, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨(mul_dvd_mul_iff_left hp.ne_zero).mp hq.1.1.1, ha⟩, hq.1.2⟩
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      have hcop : Nat.Coprime p d :=
        hp.coprime_iff_not_dvd.mpr fun hpd => hpa (hpd.trans hd.1.1)
      unfold moebiusReal
      rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]
      push_cast
      ring
  rw [hnot_p, hp_div, add_comm, ← sub_eq_add_neg]
  have hsub : a.divisors.filter (fun d => p * d ≤ N) ⊆ a.divisors.filter (fun d => d ≤ N) := by
    intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    refine ⟨hd.1, ?_⟩
    have : 1 * d ≤ p * d := Nat.mul_le_mul_right d hp.one_le
    omega
  rw [← Finset.sum_sdiff_eq_sub hsub]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_sdiff, Finset.mem_filter, not_and]
  constructor
  · rintro ⟨⟨hd, hdN⟩, hnot⟩
    have hgt : ¬ p * d ≤ N := hnot hd
    exact ⟨hd, by omega, hdN⟩
  · rintro ⟨hd, hgt, hdN⟩
    exact ⟨⟨hd, hdN⟩, fun _ => by omega⟩

/-- **Squarefree Divisor Cardinality Identity (`card_divisors_eq_two_pow_primeFactors`):**
Every squarefree positive integer $a$ has exactly $2^{\omega(a)}$ divisors:
$a.\mathrm{divisors}.\mathrm{card} = 2^{a.\mathrm{primeFactors}.\mathrm{card}}$. -/
theorem card_divisors_eq_two_pow_primeFactors {a : ℕ} (ha : Squarefree a) :
    a.divisors.card = 2 ^ a.primeFactors.card := by
  have hprod := ArithmeticFunction.isMultiplicative_zeta.prodPrimeFactors_one_add_of_squarefree ha
  have hlhs : (∏ p ∈ a.primeFactors, (1 + (ArithmeticFunction.zeta : ArithmeticFunction ℕ) p)) =
      2 ^ a.primeFactors.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [ArithmeticFunction.zeta_apply_ne hp0]
  have hrhs : (∑ d ∈ a.divisors, (ArithmeticFunction.zeta : ArithmeticFunction ℕ) d) =
      a.divisors.card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [ArithmeticFunction.zeta_apply_ne hd0]
  omega

/-- **Zero-Sum Subset Half-Cardinality Bound (`abs_sum_filter_divisors_moebiusReal_le_half_card`):**
For any squarefree integer $a \ge 2$ and any predicate $P : \mathbb{N} \to \mathrm{Prop}$,
since $\sum_{d \mid a} \mu(d) = 0$, the sum of $\mu(d)$ over the filtered divisor subset has
magnitude at most half the total number of divisors:
$$2\left|\sum_{d \in a.\mathrm{divisors}.\mathrm{filter}\ P} \mu(d)\right| \le
  (a.\mathrm{divisors}.\mathrm{card} : \mathbb{R}) = 2^{\omega(a)}.$$ -/
theorem abs_sum_filter_divisors_moebiusReal_le_half_card {a : ℕ} (ha : Squarefree a)
    (ha2 : 2 ≤ a) (P : ℕ → Prop) [DecidablePred P] :
    2 * |∑ d ∈ a.divisors.filter P, moebiusReal d| ≤ (a.divisors.card : ℝ) ∧
      |∑ d ∈ a.divisors.filter P, moebiusReal d| ≤
        (2 : ℝ) ^ (a.primeFactors.card - 1) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not a.divisors P moebiusReal
  have hzero := sum_divisors_moebiusReal_eq_zero ha2
  have hneg : (∑ d ∈ a.divisors.filter (fun d => ¬ P d), moebiusReal d) =
      -(∑ d ∈ a.divisors.filter P, moebiusReal d) := by linarith
  have habs_eq : |∑ d ∈ a.divisors.filter (fun d => ¬ P d), moebiusReal d| =
      |∑ d ∈ a.divisors.filter P, moebiusReal d| := by
    rw [hneg, abs_neg]
  have hle1 : |∑ d ∈ a.divisors.filter P, moebiusReal d| ≤
      ∑ d ∈ a.divisors.filter P, |moebiusReal d| := abs_sum_le_sum_abs _ _
  have hle2 : |∑ d ∈ a.divisors.filter (fun d => ¬ P d), moebiusReal d| ≤
      ∑ d ∈ a.divisors.filter (fun d => ¬ P d), |moebiusReal d| := abs_sum_le_sum_abs _ _
  have hsum_abs :
      (∑ d ∈ a.divisors.filter P, |moebiusReal d|) +
        (∑ d ∈ a.divisors.filter (fun d => ¬ P d), |moebiusReal d|) =
      ∑ d ∈ a.divisors, |moebiusReal d| :=
    Finset.sum_filter_add_sum_filter_not a.divisors P (fun d => |moebiusReal d|)
  have hcard : (∑ d ∈ a.divisors, |moebiusReal d|) ≤ (a.divisors.card : ℝ) := by
    calc ∑ d ∈ a.divisors, |moebiusReal d|
        ≤ ∑ _d ∈ a.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ => by
          unfold moebiusReal
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = (a.divisors.card : ℝ) := by simp
  have htwo : 2 * |∑ d ∈ a.divisors.filter P, moebiusReal d| ≤ (a.divisors.card : ℝ) := by
    linarith
  refine ⟨htwo, ?_⟩
  have hcard_pow := card_divisors_eq_two_pow_primeFactors ha
  have homega_pos : 1 ≤ a.primeFactors.card := by
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
    have hmem : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpa, by omega⟩
    exact Finset.card_pos.mpr ⟨p, hmem⟩
  have hpow_eq : (a.divisors.card : ℝ) = 2 * (2 : ℝ) ^ (a.primeFactors.card - 1) := by
    rw [hcard_pow]
    have hk : a.primeFactors.card = (a.primeFactors.card - 1) + 1 := (Nat.sub_add_cancel homega_pos).symm
    rw [hk, pow_succ']
    push_cast
    ring
  linarith

/-- **The $2^{\omega(r)-2}$ Radical Envelope (`abs_sieveSeq_moebiusReal_squarefree_le_two_pow_sub_two`):**
For every horizon $N$ and every squarefree integer $r$ with $\omega(r) \ge 2$
(`2 ≤ r.primeFactors.card`),
$$|s_{N,\mu}(r)| \le 2^{\omega(r) - 2}.$$ -/
theorem abs_sieveSeq_moebiusReal_squarefree_le_two_pow_sub_two (N : ℕ) {r : ℕ}
    (hr : Squarefree r) (hω : 2 ≤ r.primeFactors.card) :
    |sieveSeq N moebiusReal r| ≤ (2 : ℝ) ^ (r.primeFactors.card - 2) := by
  have hne : r.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp_mem⟩ := hne
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp_mem
  set a := r / p
  have hr_eq : r = p * a := (Nat.mul_div_cancel' hpr).symm
  have hr_sf : Squarefree (p * a) := hr_eq ▸ hr
  obtain ⟨hcop, -, ha_sf⟩ := Nat.squarefree_mul_iff.mp hr_sf
  have hpa : ¬ p ∣ a := hp.coprime_iff_not_dvd.mp hcop
  have ha0 : a ≠ 0 := ha_sf.ne_zero
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
  have hpf_a : a.primeFactors = r.primeFactors.erase p := by
    have h1 := Nat.primeFactors_div_gcd hr hp.ne_zero
    rw [Nat.gcd_eq_right hpr, hp.primeFactors, Finset.sdiff_singleton_eq_erase] at h1
    exact h1
  have hcard_a : a.primeFactors.card = r.primeFactors.card - 1 := by
    rw [hpf_a, Finset.card_erase_of_mem hp_mem]
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have ha1 : a = 1 := by omega
    have hcard0 : a.primeFactors.card = 0 := by simp [ha1]
    omega
  have hbound := (abs_sum_filter_divisors_moebiusReal_le_half_card ha_sf ha2
    (fun d => N < p * d ∧ d ≤ N)).2
  have hsub : a.primeFactors.card - 1 = r.primeFactors.card - 2 := by omega
  have hwin := sieveSeq_moebiusReal_prime_mul_eq_window N hp ha0 hpa
  rw [← hr_eq] at hwin
  rw [hwin, ← hsub]
  exact hbound

/-- **Prime-Power and Biprime Envelope (`abs_sieveSeq_moebiusReal_le_one_of_card_primeFactors_radical_le_two`):**
At every horizon $N$ and every integer $k$ whose radical state $r = \gcd(k, N\#)$ has at most two
distinct prime factors ($\omega(r) \le 2$), $|s_{N,\mu}(k)| \le 1$. -/
theorem abs_sieveSeq_moebiusReal_le_one_of_card_primeFactors_radical_le_two {N k : ℕ}
    (hω : (horizonRadicalState N k).primeFactors.card ≤ 2) :
    |sieveSeq N moebiusReal k| ≤ 1 := by
  have hsf : ∀ d : ℕ, ¬ Squarefree d → moebiusReal d = 0 := fun d hd => by
    unfold moebiusReal; rw [moebius_eq_zero_of_not_squarefree hd]; simp
  rw [← sieveSeq_horizonRadicalState N k hsf]
  have hr_sf := horizonRadicalState_squarefree N k
  rcases (show (horizonRadicalState N k).primeFactors.card = 0 ∨
      (horizonRadicalState N k).primeFactors.card = 1 ∨
      (horizonRadicalState N k).primeFactors.card = 2 by omega) with h0 | h1 | h2
  · have hr1 : horizonRadicalState N k = 1 := by
      have hemp : (horizonRadicalState N k).primeFactors = ∅ := Finset.card_eq_zero.mp h0
      have hprod := Nat.prod_primeFactors_of_squarefree hr_sf
      rw [hemp, Finset.prod_empty] at hprod
      exact hprod.symm
    rw [hr1]
    unfold sieveSeq
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : (Finset.Icc 1 N).filter (fun d => d ∣ 1) ⊆ (1 : ℕ).divisors := by
      intro d hd
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, one_ne_zero⟩
    calc ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ 1), |moebiusReal d|
        ≤ ∑ _d ∈ (1 : ℕ).divisors, (1 : ℝ) := by
          refine (Finset.sum_le_sum fun d _ => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le_one)
          unfold moebiusReal
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = 1 := by simp
  · obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ (horizonRadicalState N k).primeFactors := by
      rw [hp_eq]; exact Finset.mem_singleton_self p
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hr_eq : horizonRadicalState N k = p * 1 := by
      have hprod := Nat.prod_primeFactors_of_squarefree hr_sf
      rw [hp_eq, Finset.prod_singleton] at hprod
      omega
    rw [hr_eq, sieveSeq_moebiusReal_prime_mul_eq_window N hp one_ne_zero hp.not_dvd_one]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : (1 : ℕ).divisors.filter (fun d => N < p * d ∧ d ≤ N) ⊆ (1 : ℕ).divisors :=
      Finset.filter_subset _ _
    calc ∑ d ∈ (1 : ℕ).divisors.filter (fun d => N < p * d ∧ d ≤ N), |moebiusReal d|
        ≤ ∑ _d ∈ (1 : ℕ).divisors, (1 : ℝ) := by
          refine (Finset.sum_le_sum fun d _ => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le_one)
          unfold moebiusReal
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = 1 := by simp
  · have hb := abs_sieveSeq_moebiusReal_squarefree_le_two_pow_sub_two N hr_sf h2.ge
    simpa [h2] using hb

/-- **Three-Prime Radical Envelope (`abs_sieveSeq_moebiusReal_le_two_of_card_primeFactors_radical_le_three`):**
At every horizon $N$ and every integer $k$ whose radical state $r = \gcd(k, N\#)$ has at most three
distinct prime factors ($\omega(r) \le 3$), $|s_{N,\mu}(k)| \le 2$. -/
theorem abs_sieveSeq_moebiusReal_le_two_of_card_primeFactors_radical_le_three {N k : ℕ}
    (hω : (horizonRadicalState N k).primeFactors.card ≤ 3) :
    |sieveSeq N moebiusReal k| ≤ 2 := by
  rcases (show (horizonRadicalState N k).primeFactors.card ≤ 2 ∨
      (horizonRadicalState N k).primeFactors.card = 3 by omega) with hle2 | heq3
  · linarith [abs_sieveSeq_moebiusReal_le_one_of_card_primeFactors_radical_le_two hle2]
  · have hsf : ∀ d : ℕ, ¬ Squarefree d → moebiusReal d = 0 := fun d hd => by
      unfold moebiusReal; rw [moebius_eq_zero_of_not_squarefree hd]; simp
    rw [← sieveSeq_horizonRadicalState N k hsf]
    have hb := abs_sieveSeq_moebiusReal_squarefree_le_two_pow_sub_two N
      (horizonRadicalState_squarefree N k) (by omega)
    simpa [heq3] using hb

/-- **Three-Prime Radical Defect Nonpositivity
(`moebius_prefix_defect_nonpos_of_card_primeFactors_radical_le_three`):**
At every horizon $N$ and every prefix $M$ such that $\omega(\gcd(M+1, N\#)) \le 3$,
$\widetilde{\mathcal{D}}_N(M; \mu) \le 0$ (and $\le -1$ whenever $\omega(\gcd(M+1, N\#)) \le 2$,
$N \ge 2$, and $M \ge 1$). -/
theorem moebius_prefix_defect_nonpos_of_card_primeFactors_radical_le_three {N M : ℕ}
    (hω : (horizonRadicalState N (M + 1)).primeFactors.card ≤ 3) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 :=
  moebius_prefix_defect_nonpos_of_abs_le_two
    (abs_sieveSeq_moebiusReal_le_two_of_card_primeFactors_radical_le_three hω)

theorem moebius_prefix_defect_le_neg_one_of_card_primeFactors_radical_le_two {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M)
    (hω : (horizonRadicalState N (M + 1)).primeFactors.card ≤ 2) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ -1 :=
  moebius_prefix_defect_le_neg_one_of_abs_le_one hN hM
    (abs_sieveSeq_moebiusReal_le_one_of_card_primeFactors_radical_le_two hω)

/-- **Three-Prime Input Corollary (`moebius_prefix_defect_nonpos_of_card_primeFactors_le_three`):**
At every horizon $N$ and every prefix $M$ with $\omega(M + 1) \le 3$,
$|s_{N,\mu}(M + 1)| \le 2$ and $\widetilde{\mathcal{D}}_N(M; \mu) \le 0$. -/
theorem moebius_prefix_defect_nonpos_of_card_primeFactors_le_three {N M : ℕ}
    (hω : (M + 1).primeFactors.card ≤ 3) :
    |sieveSeq N moebiusReal (M + 1)| ≤ 2 ∧
      sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  have hsub : (horizonRadicalState N (M + 1)).primeFactors ⊆ (M + 1).primeFactors :=
    Nat.primeFactors_mono (horizonRadicalState_dvd N (M + 1)) (by omega)
  have hrad : (horizonRadicalState N (M + 1)).primeFactors.card ≤ 3 :=
    (Finset.card_le_card hsub).trans hω
  exact ⟨abs_sieveSeq_moebiusReal_le_two_of_card_primeFactors_radical_le_three hrad,
    moebius_prefix_defect_nonpos_of_card_primeFactors_radical_le_three hrad⟩

/-! ## §4. All-Prefix Defect Nonpositivity Across Small Horizons -/

private theorem primorial_small_values :
    primorial 0 = 1 ∧ primorial 1 = 1 ∧ primorial 2 = 2 ∧ primorial 3 = 6 ∧
      primorial 4 = 6 ∧ primorial 5 = 30 ∧ primorial 6 = 30 := by
  decide

/-- **All-Prefix Uniform Damping Nonpositivity for $N \le 4$
(`pmPowerDamped_defect_nonpos_of_le_four`):**
For every horizon $N \le 4$, every damping $\varepsilon \ge 0$, and every prefix $M \in \mathbb{N}$:
$|s_{N,c_\varepsilon}(M + 1)| \le 1$ and $\widetilde{\mathcal{D}}_N(M; c_\varepsilon) \le 0$. -/
theorem pmPowerDamped_defect_nonpos_of_le_four {N : ℕ} (hN : N ≤ 4)
    {ε : ℝ} (hε : 0 ≤ ε) (M : ℕ) :
    |sieveSeq N (pmPowerDampedRealWeight ε) (M + 1)| ≤ 1 ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hle : horizonRadicalState N (M + 1) ≤ primorial N :=
    Nat.le_of_dvd (primorial_pos N) (horizonRadicalState_dvd_primorial N (M + 1))
  obtain ⟨p0, p1, p2, p3, p4, -, -⟩ := primorial_small_values
  have hlt : horizonRadicalState N (M + 1) < 5 * (N + 1) := by
    interval_cases N <;> omega
  exact ⟨abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_radical_lt_five_succ hε hlt,
    (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_radical_five_succ_bound hε hlt).2⟩

/-- **All-Integer Damped Envelope $\le 2$ for $N \le 6$
(`abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_le_six`):**
For every horizon $N \le 6$, every damping $\varepsilon \ge 0$, and every integer $k$,
$|s_{N,c_\varepsilon}(k)| \le 2$. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_le_six {N : ℕ}
    (hN : N ≤ 6) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 2 := by
  have hle : horizonRadicalState N k ≤ primorial N :=
    Nat.le_of_dvd (primorial_pos N) (horizonRadicalState_dvd_primorial N k)
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := primorial_small_values
  have hlt : horizonRadicalState N k < 6 * (N + 1) := by
    interval_cases N <;> omega
  exact abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_radical_lt_six_succ hε hlt

/-- **Sieve Response as a Truncated Divisor Sum on `Icc 1 B` (`sieveSeq_eq_sum_Icc_ite_of_le`):**
Whenever $N \le B$, $s_{N,c}(k) = \sum_{q \in \mathrm{Icc}\ 1\ B} (\text{if } q \mid k \wedge q \le N \text{ then } c(q) \text{ else } 0)$. -/
theorem sieveSeq_eq_sum_Icc_ite_of_le {N B : ℕ} (hNB : N ≤ B) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N c k =
      ∑ q ∈ Finset.Icc 1 B, (if q ∣ k ∧ q ≤ N then c q else 0) := by
  unfold sieveSeq
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hq1, hqN⟩, hqk⟩
    exact ⟨⟨hq1, hqN.trans hNB⟩, hqk, hqN⟩
  · rintro ⟨⟨hq1, _⟩, hqk, hqN⟩
    exact ⟨⟨hq1, hqN⟩, hqk⟩

/-- **Global Envelope $|s_{N,\mu}(k)| \le 2$ and All-Prefix Defect Nonpositivity for $N \le 10$
(`moebius_defect_nonpos_of_le_ten`):**
For every horizon $N \le 10$ and every $k, M \in \mathbb{N}$:
$|s_{N,\mu}(k)| \le 2$ and $\widetilde{\mathcal{D}}_N(M; \mu) \le 0$. -/
theorem moebius_defect_nonpos_of_le_ten {N : ℕ} (hN : N ≤ 10) (k M : ℕ) :
    |sieveSeq N moebiusReal k| ≤ 2 ∧
      sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  have habs : ∀ m : ℕ, |sieveSeq N moebiusReal m| ≤ 2 := by
    intro m
    rw [sieveSeq_eq_sum_Icc_ite_of_le hN moebiusReal m]
    exact abs_truncated_moebius_divisor_sum_le_two m N
  exact ⟨habs k, moebius_prefix_defect_nonpos_of_abs_le_two (habs (M + 1))⟩

/-- **Global Envelope $|s_{N,\mu}(k)| \le 3$ for $N \le 12$
(`abs_sieveSeq_moebiusReal_le_three_of_le_twelve`):**
For every horizon $N \le 12$ and every $k \in \mathbb{N}$, $|s_{N,\mu}(k)| \le 3$. -/
theorem abs_sieveSeq_moebiusReal_le_three_of_le_twelve {N : ℕ} (hN : N ≤ 12) (k : ℕ) :
    |sieveSeq N moebiusReal k| ≤ 3 := by
  rw [sieveSeq_eq_sum_Icc_ite_of_le hN moebiusReal k]
  exact abs_truncated_moebius_divisor_sum_le_three k N

/-- **Exact Sub-1155 Envelope $|s_{N,\mu}(k)| \le 2$ for $N \le 12$
(`abs_sieveSeq_moebiusReal_le_two_of_le_twelve_of_not_dvd`):**
For every horizon $N \le 12$ and every integer $k$ not divisible by $3 \cdot 5 \cdot 7 \cdot 11 = 1155$,
$|s_{N,\mu}(k)| \le 2$. -/
theorem abs_sieveSeq_moebiusReal_le_two_of_le_twelve_of_not_dvd {N k : ℕ}
    (hN : N ≤ 12) (hk : ¬ 1155 ∣ k) :
    |sieveSeq N moebiusReal k| ≤ 2 := by
  rcases (show N ≤ 10 ∨ N = 11 ∨ N = 12 by omega) with h10 | rfl | rfl
  · exact (moebius_defect_nonpos_of_le_ten h10 k 0).1
  · have hnot : ¬ (3 ∣ k ∧ 5 ∣ k ∧ 7 ∣ k ∧ 11 ∣ k) := by
      rintro ⟨h3, h5, h7, h11⟩
      apply hk
      have h15 : 15 ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h3 h5
      have h105 : 105 ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h15 h7
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h105 h11
    have h6 : 6 ∣ k ↔ 2 ∣ k ∧ 3 ∣ k := by omega
    have h10 : 10 ∣ k ↔ 2 ∣ k ∧ 5 ∣ k := by omega
    have p2 := moebius_apply_prime Nat.prime_two
    have p3 := moebius_apply_prime Nat.prime_three
    have p5 := moebius_apply_prime Nat.prime_five
    have p7 := moebius_apply_prime (by norm_num : Nat.Prime 7)
    have p11 := moebius_apply_prime (by norm_num : Nat.Prime 11)
    have m6 : μ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
        p2, p3]
      rfl
    have m10 : μ 10 = 1 := by
      rw [show (10 : ℕ) = 2 * 5 by rfl, isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
        p2, p5]
      rfl
    have m4 : μ 4 = 0 := by decide
    have m8 : μ 8 = 0 := by decide
    have m9 : μ 9 = 0 := by
      rw [show (9 : ℕ) = 3 ^ 2 by rfl, moebius_apply_prime_pow Nat.prime_three (by norm_num)]
      rfl
    unfold sieveSeq moebiusReal
    rw [Finset.sum_filter, show Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} by decide]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      moebius_apply_one, p2, p3, p5, p7, p11, m6, m10, m4, m8, m9, h6, h10, one_dvd, ite_true,
      Int.cast_one, Int.cast_neg, Int.cast_zero, ite_self, Nat.reduceEqDiff, or_self,
      not_false_eq_true, OfNat.one_ne_ofNat]
    by_cases h2 : 2 ∣ k <;> by_cases h3 : 3 ∣ k <;> by_cases h5 : 5 ∣ k <;>
      by_cases h7 : 7 ∣ k <;> by_cases h11 : 11 ∣ k <;>
      (try (exfalso; exact hnot ⟨h3, h5, h7, h11⟩)) <;>
      norm_num [h2, h3, h5, h7, h11]
  · have h12 : sieveSeq 12 moebiusReal k = sieveSeq 11 moebiusReal k := by
      unfold sieveSeq
      rw [Finset.sum_filter, Finset.sum_filter,
        Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 11 + 1)]
      have m12 : moebiusReal 12 = 0 := by
        unfold moebiusReal
        have : μ 12 = 0 := by decide
        simp [this]
      simp [m12]
    rw [h12]
    exact abs_sieveSeq_moebiusReal_le_two_of_le_twelve_of_not_dvd (by omega) hk

/-- **Unconditional All-Prefix Möbius Defect Nonpositivity for $N \le 12$
(`moebius_defect_nonpos_of_le_twelve`):**
For every horizon $N \le 12$ and every prefix $M \in \mathbb{N}$,
$\widetilde{\mathcal{D}}_N(M; \mu) \le 0$. -/
theorem moebius_defect_nonpos_of_le_twelve {N : ℕ} (hN : N ≤ 12) (M : ℕ) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  rcases (show N ≤ 10 ∨ 2 ≤ N by omega) with h10 | hN2
  · exact (moebius_defect_nonpos_of_le_ten h10 0 M).2
  · rcases (show M < 1154 ∨ 310 ≤ M by omega) with hlt | hge
    · have hndvd : ¬ 1155 ∣ M + 1 := by
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      exact moebius_prefix_defect_nonpos_of_abs_le_two
        (abs_sieveSeq_moebiusReal_le_two_of_le_twelve_of_not_dvd hN hndvd)
    · apply moebius_defect_nonpos_of_mv_window hN2
      have hNR : (N : ℝ) ≤ 12 := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hMR : (310 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hge
      nlinarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
