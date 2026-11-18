import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.EulerProductDiscUniformCarlsonTail
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Self-Return Confinement, Smooth Alternating Euler Tails, Universal Two-Prime Dilations, and Fractional-Part Laws

This module formalizes four analytic and arithmetic laws governing off-line zeros and the
single-quartet stratum `HasSingleOffLineQuartet ρ₀`:

1. **Compact self-return confinement and failure of weak recurrence under a single quartet**
   (`not_zetaZeroDiscWeaklyRecurrent_of_singleQuartet`,
   `zetaReturnSet_confined_of_singleQuartet`):
   Under `HasSingleOffLineQuartet ρ₀`, `¬ RHTower.ZetaZeroDiscWeaklyRecurrent` (hence
   `¬ RHTower.ZetaWeaklyRecurrent` and `¬ RHTower.ZetaDiscRecurrent`). Quantitatively, on every
   strip disc `closedBall ρ₀ r` (`1/2 < Re ρ₀ - r`, `Re ρ₀ + r < 1`) and tolerance
   `ε < zetaNonvanishingDistance ρ₀ r`, every self-return shift `τ` satisfies
   `|τ| ≤ r ∨ |τ + 2 Im ρ₀| ≤ r` (in particular `|τ| ≤ 2 |Im ρ₀| + r`).

2. **`N`-smooth alternating Euler-product nonvanishing and Rouché tail floor**
   (`smoothAltEulerProduct`, `altDirichletPoly`, `smoothAltTail`,
   `hasSum_smoothAltEulerProduct`, `smoothAltEulerProduct_eq_head_add_tail`,
   `smoothAltEulerProduct_analytic_and_ne_zero_on_strip`,
   `smoothAltTail_lower_bound_near_zero`):
   For `N ≥ 2` and any multiplicative `ω : ℕ →* ℂ` with `‖ω p‖ ≤ 1` on primes and `‖ω 2‖ = 1`,
   `(1 - 2^{1 - s} ω 2) ∏_{p ≤ N} (1 - ω p · p^{-s})⁻¹` expands on `{Re s > 0}` into the
   `(N+1)`-smooth alternating Dirichlet series `∑_{P^+(n) ≤ N} (-1)^{n - 1} ω(n) n^{-s}`, is
   analytic and everywhere nonvanishing on `{0 < Re s < 1}`, and forces the `(N+1)`-smooth tail
   beyond `N` to stay bounded below on any isolating disc around an off-line zero `ρ₀` whenever the
   head `∑_{1 ≤ n ≤ N} (-1)^{n - 1} ω(n) n^{-s}` approximates `(1 - 2^{1 - s}) ζ(s)`.

3. **Universal all-scale two-prime dilation span law under a single quartet**
   (`sin_mul_log_two_ne_zero_or_three_ne_zero`, `dilationAlpha`, `dilationBeta`,
   `cpow_eq_dilationAlpha_add_dilationBeta`,
   `singleQuartet_universal_twoPrime_chebyshev_span`):
   For any `γ ≠ 0`, at least one of `sin(γ log 2)`, `sin(γ log 3)` is nonzero. Under
   `HasSingleOffLineQuartet ρ₀`, there exist `q₀ ∈ ({2, 3} : Finset ℕ)` with
   `sin(Im ρ₀ · log q₀) ≠ 0` and `C ≥ 0` such that **for every scale `u ≥ 1` and `x ≥ 16`**, both
   `ψ(u x) - u x` and `θ(u x) - u x` equal the same explicit linear combination of their readings at
   `x` and `q₀ x` up to `O(√(u x) log²(u x) + (|α(u)| + |β(u)|) √x log² x)`.

4. **Zero-pinned fractional-part Mellin equivalences and upper-range divisor concentration**
   (`riemannZeta_eq_zero_iff_fract_mellin_strip`,
   `sum_vonMangoldt_mul_fract_eq_harmonic_sub_log`,
   `sum_vonMangoldt_mul_fract_upper_sqrt_concentration`):
   On `{0 < Re s < 1}`, `ζ(s) = 0` iff `∫_0^∞ {c u} u^{-s - 1} du = 0` (`c > 0`) iff
   `∫_1^∞ {t} t^{-s - 1} dt = 1 / (s - 1)`. Arithmetic summation of `Λ(d) {X / d}` (`X ≥ 1`)
   equals `X ∑_{d ≤ X} Λ(d) / d - ∑_{m ≤ X} log m`, with `1 ≤ d ≤ ⌊√X⌋₊` confined to
   `[0, ψ(√X)]`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Metric MeasureTheory Finset
open scoped ComplexConjugate
open GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ## 1. Compact self-return confinement and failure of weak recurrence under a single quartet -/

/-- **Failure of weak zero-disc recurrence under `HasSingleOffLineQuartet ρ₀`.**
Because a single off-line quartet satisfies `FiniteOffLine` (`ZerosApproachLine`) while violating
`RiemannHypothesis`, `ζ` cannot be weakly recurrent around off-line zero discs (nor weakly or
strongly disc-recurrent). -/
theorem not_zetaZeroDiscWeaklyRecurrent_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    ¬ RHTower.ZetaZeroDiscWeaklyRecurrent ∧
      ¬ RHTower.ZetaWeaklyRecurrent ∧
      ¬ RHTower.ZetaDiscRecurrent := by
  have hnot_zero : ¬ RHTower.ZetaZeroDiscWeaklyRecurrent := by
    intro hW
    have hzal := RHTower.BacklundConverse.zerosApproachLine_of_finiteOffLine hq.finiteOffLine
    exact hq.not_riemannHypothesis
      (RHTower.riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent.mpr ⟨hzal, hW⟩)
  exact ⟨hnot_zero, fun h => hnot_zero h.zeroDisc,
    fun h => hnot_zero h.zetaWeaklyRecurrent.zeroDisc⟩

/-- **Quantitative compact confinement of `zetaReturnSet` under `HasSingleOffLineQuartet ρ₀`.**
For any radius `r > 0` with `1/2 < Re ρ₀ - r` and `Re ρ₀ + r < 1`:
1. `0 < zetaNonvanishingDistance ρ₀ r`;
2. Below that threshold (`ε < zetaNonvanishingDistance ρ₀ r`), every self-return shift
   `τ ∈ zetaReturnSet (closedBall ρ₀ r) ε` lies in `[-r, r] ∪ [-2 Im ρ₀ - r, -2 Im ρ₀ + r]`,
   and in particular satisfies `|τ| ≤ 2 |Im ρ₀| + r`. -/
theorem zetaReturnSet_confined_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {r : ℝ} (hr : 0 < r) (h0 : 1 / 2 < ρ₀.re - r) (h1 : ρ₀.re + r < 1) :
    0 < RHTower.zetaNonvanishingDistance ρ₀ r ∧
      ∀ {ε τ : ℝ}, ε < RHTower.zetaNonvanishingDistance ρ₀ r →
        τ ∈ RHTower.zetaReturnSet (closedBall ρ₀ r) ε →
          (|τ| ≤ r ∨ |τ + 2 * ρ₀.im| ≤ r) ∧ |τ| ≤ 2 * |ρ₀.im| + r := by
  have hd : 0 < RHTower.zetaNonvanishingDistance ρ₀ r :=
    RHTower.zetaNonvanishingDistance_pos_of_zero hr h0 h1 (mem_ball_self hr) hq.2.1.1
  refine ⟨hd, fun {ε τ} hε hτ => ?_⟩
  obtain ⟨z, hz, hζ_shift⟩ := RHTower.exists_zero_of_mem_zetaReturnSet_of_lt_distance hr h1 hε hτ
  have hnorm : ‖z - ρ₀‖ ≤ r := mem_closedBall_iff_norm.mp hz
  have hre_le := abs_le.mp ((Complex.abs_re_le_norm (z - ρ₀)).trans hnorm)
  have him_le := abs_le.mp ((Complex.abs_im_le_norm (z - ρ₀)).trans hnorm)
  rw [Complex.sub_re] at hre_le
  rw [Complex.sub_im] at him_le
  set w : ℂ := z + (τ : ℂ) * I
  have hw_re : w.re = z.re := by simp [w]
  have hw_im : w.im = z.im + τ := by simp [w]
  have hw_gt_half : 1 / 2 < w.re := by linarith
  have hw_lt1 : w.re < 1 := by linarith
  have hw_mem : w ∈ zeroQuartetSet ρ₀ := by
    rw [← hq.2.2]
    exact ⟨⟨hζ_shift, by linarith, hw_lt1⟩, ne_of_gt hw_gt_half⟩
  have hor : |τ| ≤ r ∨ |τ + 2 * ρ₀.im| ≤ r := by
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hw_mem
    rcases hw_mem with heq | heq | heq | heq
    · left
      have him := congrArg Complex.im heq
      rw [hw_im] at him
      rw [abs_le]
      constructor <;> linarith
    · right
      have him := congrArg Complex.im heq
      rw [hw_im, Complex.conj_im] at him
      rw [abs_le]
      constructor <;> linarith
    · exfalso
      have hre := congrArg Complex.re heq
      rw [hw_re, Complex.sub_re, Complex.one_re] at hre
      linarith [hq.1]
    · exfalso
      have hre := congrArg Complex.re heq
      rw [hw_re, Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
      linarith [hq.1]
  refine ⟨hor, ?_⟩
  rcases hor with hleft | hright
  · linarith [abs_nonneg ρ₀.im]
  · have htri := abs_sub_le (τ + 2 * ρ₀.im) (2 * ρ₀.im) 0
    rw [sub_zero, sub_zero, add_sub_cancel_right, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
    linarith

/-! ## 2. `N`-smooth alternating Euler-product nonvanishing and Rouché tail floor -/

/-- `(N+1)`-smooth alternating Euler product `(1 - 2^{1 - s} ω(2)) ∏_{p ≤ N, prime} (1 - ω(p) p^{-s})⁻¹`. -/
def smoothAltEulerProduct (N : ℕ) (ω : ℕ →* ℂ) (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s) * ω 2) *
    ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - ω p * (p : ℂ) ^ (-s))⁻¹

/-- Truncated alternating Dirichlet polynomial `∑_{1 ≤ n ≤ N} (-1)^{n - 1} ω(n) n^{-s}`. -/
def altDirichletPoly (N : ℕ) (ω : ℕ →* ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (-1 : ℂ) ^ (n - 1) * ω n * (n : ℂ) ^ (-s)

/-- `(N+1)`-smooth alternating tail `∑_{k ≥ 0} 1_{smooth(N+1)}(k + N + 1) (-1)^{k + N} ω(k + N + 1) (k + N + 1)^{-s}`. -/
def smoothAltTail (N : ℕ) (ω : ℕ →* ℂ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, (Nat.smoothNumbers (N + 1)).indicator
    (fun n : ℕ => (-1 : ℂ) ^ (n - 1) * ω n * (n : ℂ) ^ (-s)) (k + (N + 1))

private def eulerPhaseMonoidHom (ω : ℕ →* ℂ) (s : ℂ) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else ω n * (n : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn), map_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring

private theorem two_mul_mem_smoothNumbers_iff {N m : ℕ} (hN : 2 ≤ N) :
    2 * m ∈ Nat.smoothNumbers (N + 1) ↔ m ∈ Nat.smoothNumbers (N + 1) := by
  simp only [Nat.mem_smoothNumbers]
  constructor
  · rintro ⟨hm0, hall⟩
    have hm_ne : m ≠ 0 := fun h => hm0 (by simp [h])
    refine ⟨hm_ne, fun p hp => hall p ?_⟩
    have hp_prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    exact (Nat.mem_primeFactorsList hm0).mpr ⟨hp_prime, dvd_mul_of_dvd_right hdvd 2⟩
  · rintro ⟨hm_ne, hall⟩
    have h2m_ne : 2 * m ≠ 0 := mul_ne_zero two_ne_zero hm_ne
    refine ⟨h2m_ne, fun p hp => ?_⟩
    obtain ⟨hp_prime, hdvd⟩ := (Nat.mem_primeFactorsList h2m_ne).mp hp
    rcases hp_prime.dvd_mul.mp hdvd with hp2 | hpm
    · have hp_eq2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hp2
      omega
    · exact hall p ((Nat.mem_primeFactorsList hm_ne).mpr ⟨hp_prime, hpm⟩)

/-- **Exact `(N+1)`-smooth Dirichlet series of `smoothAltEulerProduct N ω`.**
For `N ≥ 2`, `‖ω p‖ ≤ 1` on primes, and `Re s > 0`, `smoothAltEulerProduct N ω s` is the sum of
`(-1)^{n - 1} ω(n) n^{-s}` over `(N+1)`-smooth integers `n`. -/
theorem hasSum_smoothAltEulerProduct {N : ℕ} (hN : 2 ≤ N) {ω : ℕ →* ℂ}
    (hω : ∀ p : ℕ, p.Prime → ‖ω p‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (Nat.smoothNumbers (N + 1)).indicator
        (fun n : ℕ => (-1 : ℂ) ^ (n - 1) * ω n * (n : ℂ) ^ (-s)) n)
      (smoothAltEulerProduct N ω s) := by
  have hp_lt : ∀ {p : ℕ}, p.Prime → ‖eulerPhaseMonoidHom ω s p‖ < 1 := by
    intro p hprime
    change ‖if p = 0 then 0 else ω p * (p : ℂ) ^ (-s)‖ < 1
    rw [if_neg hprime.ne_zero, norm_mul, Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
    have hpow_lt : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_neg_of_pos hs)
    calc ‖ω p‖ * (p : ℝ) ^ (-s.re)
        ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right (hω p hprime) (by positivity)
      _ < 1 := by linarith
  obtain ⟨_, hsum_sub⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp_lt (N + 1)
  set S := Nat.smoothNumbers (N + 1)
  set E : ℂ := ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - ω p * (p : ℂ) ^ (-s))⁻¹
  have hprod_eq : (∏ p ∈ Nat.primesBelow (N + 1), (1 - eulerPhaseMonoidHom ω s p)⁻¹) = E := by
    unfold Nat.primesBelow E
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 := (Finset.mem_filter.mp hp).2.ne_zero
    change (1 - (if p = 0 then 0 else _))⁻¹ = _
    rw [if_neg hp0]
  rw [hprod_eq] at hsum_sub
  set f : ℕ → ℂ := S.indicator fun n => ω n * (n : ℂ) ^ (-s)
  have hf_sum : HasSum f E := by
    refine (hasSum_subtype_iff_indicator (s := S)).mp (hsum_sub.congr_fun fun n => ?_)
    change eulerPhaseMonoidHom ω s (n : ℕ) = _
    dsimp [eulerPhaseMonoidHom]
    rw [if_neg (Nat.ne_zero_of_mem_smoothNumbers n.2)]
  -- Even subseries via the injective doubling map `m ↦ 2 * m`.
  set g : ℕ → ℂ := fun n => if 2 ∣ n then f (n / 2) * (ω 2 * (2 : ℂ) ^ (-s)) else 0
  have hinj : Function.Injective (fun m : ℕ => 2 * m) :=
    mul_right_injective₀ two_ne_zero
  have hg_comp : (fun m : ℕ => g (2 * m)) = fun m : ℕ => f m * (ω 2 * (2 : ℂ) ^ (-s)) := by
    funext m
    dsimp [g]
    rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m (by decide : 0 < 2)]
  have hg_sum : HasSum g (E * (ω 2 * (2 : ℂ) ^ (-s))) := by
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro n hn
      have hndvd : ¬ 2 ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
      simp [g, hndvd]
    · rw [hg_comp]
      exact hf_sum.mul_right (ω 2 * (2 : ℂ) ^ (-s))
  have hdiff := hf_sum.sub (hg_sum.mul_left 2)
  have hval : E - 2 * (E * (ω 2 * (2 : ℂ) ^ (-s))) = smoothAltEulerProduct N ω s := by
    unfold smoothAltEulerProduct
    have h2pow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
    rw [h2pow]
    dsimp [E]
    ring
  rw [hval] at hdiff
  refine hdiff.congr_fun fun n => ?_
  by_cases hnS : n ∈ S
  · have hn0 : n ≠ 0 := (Nat.mem_smoothNumbers.mp hnS).1
    by_cases hdvd : 2 ∣ n
    · obtain ⟨m, rfl⟩ := hdvd
      have hm0 : m ≠ 0 := fun hm => hn0 (by simp [hm])
      have hmS : m ∈ S := (two_mul_mem_smoothNumbers_iff hN).mp hnS
      have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
      dsimp [f, g]
      rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m (by decide : 0 < 2),
        Set.indicator_of_mem hnS, Set.indicator_of_mem hmS, Set.indicator_of_mem hnS,
        hodd.neg_one_pow, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_ofNat]
      ring
    · have hodd : Odd n := Nat.not_even_iff_odd.mp (even_iff_two_dvd.not.mpr hdvd)
      obtain ⟨k, rfl⟩ := hodd
      have heven : Even (2 * k + 1 - 1) := ⟨k, by omega⟩
      dsimp [f, g]
      rw [if_neg hdvd, Set.indicator_of_mem hnS, Set.indicator_of_mem hnS, heven.neg_one_pow]
      ring
  · dsimp [f, g]
    rw [Set.indicator_of_notMem hnS, Set.indicator_of_notMem hnS]
    by_cases hdvd : 2 ∣ n
    · obtain ⟨m, rfl⟩ := hdvd
      have hmS : m ∉ S := fun hm => hnS ((two_mul_mem_smoothNumbers_iff hN).mpr hm)
      rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m (by decide : 0 < 2),
        Set.indicator_of_notMem hmS]
      ring
    · rw [if_neg hdvd]; ring

/-- **Head-plus-smooth-tail decomposition of `smoothAltEulerProduct N ω`.**
Because every integer `1 ≤ n ≤ N` is `(N+1)`-smooth, `smoothAltEulerProduct N ω s` splits on
`{Re s > 0}` into the exact `N`-term alternating Dirichlet polynomial `altDirichletPoly N ω s` plus
the `(N+1)`-smooth tail `smoothAltTail N ω s`. -/
theorem smoothAltEulerProduct_eq_head_add_tail {N : ℕ} (hN : 2 ≤ N) {ω : ℕ →* ℂ}
    (hω : ∀ p : ℕ, p.Prime → ‖ω p‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    smoothAltEulerProduct N ω s = altDirichletPoly N ω s + smoothAltTail N ω s := by
  have hhas := hasSum_smoothAltEulerProduct hN hω hs
  have hsplit := hhas.summable.sum_add_tsum_nat_add (N + 1)
  rw [hhas.tsum_eq] at hsplit
  rw [← hsplit]
  congr 1
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hrange, Finset.sum_insert (by simp),
    Set.indicator_of_notMem (RHTower.zero_notMem_smoothNumbers N), zero_add]
  unfold altDirichletPoly
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn_sm : n ∈ Nat.smoothNumbers (N + 1) := by
    rw [Nat.mem_smoothNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  exact Set.indicator_of_mem hn_sm _

/-- **Strip holomorphy and global nonvanishing of `smoothAltEulerProduct N ω` on `{0 < Re s < 1}`.** -/
theorem smoothAltEulerProduct_analytic_and_ne_zero_on_strip (N : ℕ) {ω : ℕ →* ℂ}
    (hω : ∀ p : ℕ, p.Prime → ‖ω p‖ ≤ 1) (hω2 : ‖ω 2‖ = 1) :
    AnalyticOnNhd ℂ (smoothAltEulerProduct N ω) {s : ℂ | 0 < s.re ∧ s.re < 1} ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 → smoothAltEulerProduct N ω s ≠ 0 := by
  have h2_nz : ∀ {s : ℂ}, s.re < 1 → 1 - (2 : ℂ) ^ (1 - s) * ω 2 ≠ 0 := by
    intro s hs1 heq
    have h1 := sub_eq_zero.mp heq
    have hn : ‖(2 : ℂ) ^ (1 - s) * ω 2‖ = (2 : ℝ) ^ (1 - s.re) := by
      rw [norm_mul, hω2, mul_one,
        show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
        Complex.sub_re, Complex.one_re]
    have hgt : 1 < (2 : ℝ) ^ (1 - s.re) := Real.one_lt_rpow (by norm_num) (by linarith)
    rw [← hn, ← h1, norm_one] at hgt
    exact lt_irrefl 1 hgt
  have hp_nz : ∀ {p : ℕ}, p ∈ (Finset.range (N + 1)).filter Nat.Prime →
      ∀ {s : ℂ}, 0 < s.re → 1 - ω p * (p : ℂ) ^ (-s) ≠ 0 := by
    intro p hp s hs0 heq
    have hprime := (Finset.mem_filter.mp hp).2
    have h1 := sub_eq_zero.mp heq
    have hn : ‖ω p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
      calc ‖ω p‖ * (p : ℝ) ^ (-s.re)
          ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right (hω p hprime) (by positivity)
        _ < 1 := by
          rw [one_mul]
          exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (by linarith)
    rw [← h1, norm_one] at hn
    exact lt_irrefl 1 hn
  have hU_open : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hdiff : DifferentiableOn ℂ (smoothAltEulerProduct N ω) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    have hfun : smoothAltEulerProduct N ω =
        fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s) * ω 2) *
          (∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            fun z : ℂ => (1 - ω p * (p : ℂ) ^ (-z))⁻¹) s := by
      funext s; rw [smoothAltEulerProduct, Finset.prod_apply]
    rw [hfun]
    refine DifferentiableOn.mul ?_ (DifferentiableOn.finsetProd fun p hp => ?_)
    · exact (differentiableOn_const 1).sub
        (((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).const_cpow
          (Or.inl two_ne_zero) |>.mul (differentiableOn_const _))
    · have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
      refine DifferentiableOn.inv ?_ fun s hs => hp_nz hp hs.1
      exact (differentiableOn_const 1).sub
        ((differentiableOn_const (ω p)).mul (differentiableOn_id.neg.const_cpow (Or.inl hp0)))
  refine ⟨hdiff.analyticOnNhd hU_open, fun s hs0 hs1 => ?_⟩
  unfold smoothAltEulerProduct
  exact mul_ne_zero (h2_nz hs1)
    (Finset.prod_ne_zero_iff.mpr fun p hp => inv_ne_zero (hp_nz hp hs0))

/-- **Rouché / nonvanishing-distance lower bound on `smoothAltTail N ω` near any right-of-line zero.**
Around any zero `ρ₀` of `ζ` with `1/2 < Re ρ₀ - r` and `Re ρ₀ + r < 1` (`r > 0`), for every
`N ≥ 2` and multiplicative `ω : ℕ →* ℂ` with `‖ω p‖ ≤ 1` on primes and `‖ω 2‖ = 1`, if
`altDirichletPoly N ω` approximates `(1 - 2^{1 - z}) ζ(z)` within `ε` on `closedBall ρ₀ r`, then
`smoothAltTail N ω` attains norm at least `(2^{1 - (Re ρ₀ + r)} - 1) · zetaNonvanishingDistance ρ₀ r - ε`
somewhere on `closedBall ρ₀ r`. -/
theorem smoothAltTail_lower_bound_near_zero {ρ₀ : ℂ} (hζ₀ : riemannZeta ρ₀ = 0)
    {r : ℝ} (hr : 0 < r) (h0 : 1 / 2 < ρ₀.re - r) (h1 : ρ₀.re + r < 1)
    {N : ℕ} (hN : 2 ≤ N) {ω : ℕ →* ℂ}
    (hω : ∀ p : ℕ, p.Prime → ‖ω p‖ ≤ 1) (hω2 : ‖ω 2‖ = 1)
    {ε : ℝ}
    (happrox : ∀ z ∈ closedBall ρ₀ r,
      ‖altDirichletPoly N ω z - (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z‖ ≤ ε) :
    0 < ((2 : ℝ) ^ (1 - (ρ₀.re + r)) - 1) * RHTower.zetaNonvanishingDistance ρ₀ r ∧
      ∃ z ∈ closedBall ρ₀ r,
        ((2 : ℝ) ^ (1 - (ρ₀.re + r)) - 1) * RHTower.zetaNonvanishingDistance ρ₀ r - ε ≤
          ‖smoothAltTail N ω z‖ := by
  have hd_pos : 0 < RHTower.zetaNonvanishingDistance ρ₀ r :=
    RHTower.zetaNonvanishingDistance_pos_of_zero hr h0 h1 (mem_ball_self hr) hζ₀
  set m₂ : ℝ := (2 : ℝ) ^ (1 - (ρ₀.re + r)) - 1
  have hm₂_pos : 0 < m₂ := by
    dsimp [m₂]
    linarith [Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < 1 - (ρ₀.re + r))]
  refine ⟨mul_pos hm₂_pos hd_pos, ?_⟩
  obtain ⟨han_sm, hnz_sm⟩ := smoothAltEulerProduct_analytic_and_ne_zero_on_strip N hω hω2
  -- Show `g(z) := smoothAltEulerProduct N ω z / (1 - 2^{1 - z})` lies in `nonvanishingDiscTargets ρ₀ r`.
  set η : ℝ := min ((ρ₀.re - r - 1 / 2) / 2) ((1 - (ρ₀.re + r)) / 2)
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
  have hball_strip : ∀ z ∈ ball ρ₀ (r + η), 0 < z.re ∧ z.re < 1 := by
    intro z hz
    have hre := abs_lt.mp ((Complex.abs_re_le_norm (z - ρ₀)).trans_lt (mem_ball_iff_norm.mp hz))
    rw [Complex.sub_re] at hre
    have hη1 : η ≤ (ρ₀.re - r - 1 / 2) / 2 := min_le_left _ _
    have hη2 : η ≤ (1 - (ρ₀.re + r)) / 2 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  have h1_sub_nz : ∀ {z : ℂ}, z.re < 1 → 1 - (2 : ℂ) ^ (1 - z) ≠ 0 := by
    intro z hz1 heq
    have h1' := sub_eq_zero.mp heq
    have hgt : 1 < (2 : ℝ) ^ (1 - z.re) := Real.one_lt_rpow (by norm_num) (by linarith)
    have hn : ‖(2 : ℂ) ^ (1 - z)‖ = (2 : ℝ) ^ (1 - z.re) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
        Complex.sub_re, Complex.one_re]
    rw [← hn, ← h1', norm_one] at hgt
    exact lt_irrefl 1 hgt
  set g : ℂ → ℂ := fun z => smoothAltEulerProduct N ω z / (1 - (2 : ℂ) ^ (1 - z))
  have hg_target : g ∈ RHTower.nonvanishingDiscTargets ρ₀ r := by
    refine ⟨η, hη_pos, ?_, fun z hz => div_ne_zero
      (hnz_sm z (hball_strip z hz).1 (hball_strip z hz).2)
      (h1_sub_nz (hball_strip z hz).2)⟩
    intro z hz
    have hden_an : AnalyticAt ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) z := by
      refine DifferentiableOn.analyticAt (s := Set.univ) ?_ Filter.univ_mem
      exact (differentiableOn_const 1).sub
        (((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).const_cpow
          (Or.inl two_ne_zero))
    exact (han_sm z (hball_strip z hz)).div hden_an (h1_sub_nz (hball_strip z hz).2)
  -- Continuous difference `z ↦ ‖riemannZeta z - g z‖` attains a maximum `≥ d` on `closedBall ρ₀ r`.
  have hcont_diff : ContinuousOn (fun z : ℂ => ‖riemannZeta z - g z‖) (closedBall ρ₀ r) := by
    have hsub : closedBall ρ₀ r ⊆ ball ρ₀ (r + η) := closedBall_subset_ball (by linarith)
    obtain ⟨_, _, hg_an, _⟩ := hg_target
    exact ((RHTower.continuousOn_riemannZeta_closedBall h1).sub
      (hg_an.continuousOn.mono hsub)).norm
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall ρ₀ r).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hr.le) hcont_diff
  have hd_le_max : RHTower.zetaNonvanishingDistance ρ₀ r ≤ ‖riemannZeta z₀ - g z₀‖ := by
    by_contra hlt
    rw [not_le] at hlt
    set ε₁ : ℝ := (‖riemannZeta z₀ - g z₀‖ + RHTower.zetaNonvanishingDistance ρ₀ r) / 2
    have hε₁_lt : ε₁ < RHTower.zetaNonvanishingDistance ρ₀ r := by dsimp [ε₁]; linarith
    refine RHTower.not_mem_zetaNonvanishingTolerances_of_lt_distance hr.le hε₁_lt
      ⟨g, hg_target, fun z hz => ?_⟩
    have hle : ‖riemannZeta z - g z‖ ≤ ‖riemannZeta z₀ - g z₀‖ := isMaxOn_iff.mp hmax z hz
    dsimp [ε₁]; linarith
  -- Lower bound `m₂ ≤ ‖1 - 2^{1 - z₀}‖` on `closedBall ρ₀ r`.
  have hz₀_re_le : z₀.re ≤ ρ₀.re + r := by
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z₀ - ρ₀)).trans (mem_closedBall_iff_norm.mp hz₀))
    rw [Complex.sub_re] at hre; linarith
  have hz₀_re_pos : 0 < z₀.re := by
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z₀ - ρ₀)).trans (mem_closedBall_iff_norm.mp hz₀))
    rw [Complex.sub_re] at hre; linarith
  have hm₂_le : m₂ ≤ ‖1 - (2 : ℂ) ^ (1 - z₀)‖ := by
    have hn2 : ‖(2 : ℂ) ^ (1 - z₀)‖ = (2 : ℝ) ^ (1 - z₀.re) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
        Complex.sub_re, Complex.one_re]
    have hpow_mono : (2 : ℝ) ^ (1 - (ρ₀.re + r)) ≤ (2 : ℝ) ^ (1 - z₀.re) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have htri := norm_sub_le ((2 : ℂ) ^ (1 - z₀)) ((2 : ℂ) ^ (1 - z₀) - 1)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at htri
    dsimp [m₂]; linarith
  have hprod_eq : ‖1 - (2 : ℂ) ^ (1 - z₀)‖ * ‖riemannZeta z₀ - g z₀‖ =
      ‖(1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀ - smoothAltEulerProduct N ω z₀‖ := by
    rw [← norm_mul]
    congr 1
    dsimp [g]
    field_simp [h1_sub_nz (by linarith : z₀.re < 1)]
  have hmul_le : m₂ * RHTower.zetaNonvanishingDistance ρ₀ r ≤
      ‖(1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀ - smoothAltEulerProduct N ω z₀‖ := by
    rw [← hprod_eq]
    exact mul_le_mul hm₂_le hd_le_max hd_pos.le (norm_nonneg _)
  refine ⟨z₀, hz₀, ?_⟩
  rw [smoothAltEulerProduct_eq_head_add_tail hN hω hz₀_re_pos] at hmul_le
  have htri : ‖(1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀ -
      (altDirichletPoly N ω z₀ + smoothAltTail N ω z₀)‖ ≤
      ‖altDirichletPoly N ω z₀ - (1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀‖ +
        ‖smoothAltTail N ω z₀‖ := by
    calc ‖(1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀ -
            (altDirichletPoly N ω z₀ + smoothAltTail N ω z₀)‖
        = ‖-(altDirichletPoly N ω z₀ - (1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀) -
            smoothAltTail N ω z₀‖ := by ring_nf
      _ ≤ ‖-(altDirichletPoly N ω z₀ - (1 - (2 : ℂ) ^ (1 - z₀)) * riemannZeta z₀)‖ +
            ‖smoothAltTail N ω z₀‖ := norm_sub_le _ _
      _ = _ := by rw [norm_neg]
  linarith [hmul_le, htri, happrox z₀ hz₀]

/-! ## 3. Universal all-scale two-prime dilation span law under a single quartet -/

/-- For every nonzero ordinate `γ ≠ 0`, `sin(γ log 2)` and `sin(γ log 3)` cannot both vanish. -/
theorem sin_mul_log_two_ne_zero_or_three_ne_zero {γ : ℝ} (hγ : γ ≠ 0) :
    Real.sin (γ * Real.log 2) ≠ 0 ∨ Real.sin (γ * Real.log 3) ≠ 0 := by
  by_contra hboth
  push Not at hboth
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hboth.1
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hboth.2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm_ne : (m : ℝ) ≠ 0 := by
    intro hm0
    rw [hm0, zero_mul] at hm
    exact mul_ne_zero hγ hlog2.ne' hm.symm
  have hrat : Real.log 3 / Real.log 2 = ((n : ℚ) / (m : ℚ) : ℝ) := by
    push_cast
    have hdiv : (γ * Real.log 3) / (γ * Real.log 2) = Real.log 3 / Real.log 2 :=
      mul_div_mul_left _ _ hγ
    rw [← hdiv, ← hn, ← hm, mul_div_mul_right _ _ Real.pi_pos.ne']
  exact GaloisForLFunctions.RHTower.irrational_log_ratio
    Nat.prime_two Nat.prime_three (by decide) ⟨(n : ℚ) / (m : ℚ), hrat.symm⟩

/-- First real two-scale spanning coefficient `α_{ρ₀, q₀}(u)` solving `u^{ρ₀} = α + β q₀^{ρ₀}`. -/
def dilationAlpha (ρ₀ : ℂ) (q₀ : ℕ) (u : ℝ) : ℝ :=
  u ^ ρ₀.re * Real.sin (ρ₀.im * (Real.log q₀ - Real.log u)) / Real.sin (ρ₀.im * Real.log q₀)

/-- Second real two-scale spanning coefficient `β_{ρ₀, q₀}(u)` solving `u^{ρ₀} = α + β q₀^{ρ₀}`. -/
def dilationBeta (ρ₀ : ℂ) (q₀ : ℕ) (u : ℝ) : ℝ :=
  (u ^ ρ₀.re / (q₀ : ℝ) ^ ρ₀.re) * Real.sin (ρ₀.im * Real.log u) /
    Real.sin (ρ₀.im * Real.log q₀)

/-- **Exact complex power decomposition `u^{ρ₀} = α(u) + β(u) q₀^{ρ₀}`** whenever
`sin(Im ρ₀ · log q₀) ≠ 0`. -/
theorem cpow_eq_dilationAlpha_add_dilationBeta (ρ₀ : ℂ) {q₀ : ℕ} (hq₀ : 0 < q₀)
    (hsin : Real.sin (ρ₀.im * Real.log q₀) ≠ 0) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ ρ₀ =
      (dilationAlpha ρ₀ q₀ u : ℂ) + (dilationBeta ρ₀ q₀ u : ℂ) * (q₀ : ℂ) ^ ρ₀ := by
  have hq_pos : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hq_rpow : (0 : ℝ) < (q₀ : ℝ) ^ ρ₀.re := Real.rpow_pos_of_pos hq_pos ρ₀.re
  have hcpow_polar : ∀ {y : ℝ}, 0 < y →
      (y : ℂ) ^ ρ₀ = ((y ^ ρ₀.re : ℝ) : ℂ) *
        ((Real.cos (ρ₀.im * Real.log y) : ℂ) + (Real.sin (ρ₀.im * Real.log y) : ℂ) * I) := by
    intro y hy
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [Complex.cpow_def_of_ne_zero hy_ne, ← Complex.ofReal_log hy.le]
    have hexp : Complex.log y * ρ₀ =
        ((Real.log y * ρ₀.re : ℝ) : ℂ) + ((ρ₀.im * Real.log y : ℝ) : ℂ) * I := by
      rw [← Complex.ofReal_log hy.le]
      apply Complex.ext <;> simp [mul_comm]
    rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hy,
      Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hcpow_polar hu, show (q₀ : ℂ) = ((q₀ : ℝ) : ℂ) by push_cast; rfl, hcpow_polar hq_pos]
  unfold dilationAlpha dilationBeta
  have hsub_sin : Real.sin (ρ₀.im * (Real.log q₀ - Real.log u)) =
      Real.sin (ρ₀.im * Real.log q₀) * Real.cos (ρ₀.im * Real.log u) -
        Real.cos (ρ₀.im * Real.log q₀) * Real.sin (ρ₀.im * Real.log u) := by
    rw [mul_sub, Real.sin_sub]
  rw [hsub_sin]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    field_simp [hsin, hq_rpow.ne']
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    field_simp [hsin, hq_rpow.ne']
    ring

/-- **Universal all-scale two-prime Chebyshev span law under `HasSingleOffLineQuartet ρ₀`.**
Under `HasSingleOffLineQuartet ρ₀`, there exist `q₀ ∈ ({2, 3} : Finset ℕ)` with
`sin(Im ρ₀ · log q₀) ≠ 0` and `C ≥ 0` such that **for every scale `u ≥ 1` and every `x ≥ 16`**,
both `ψ(u x) - u x` and `θ(u x) - u x` are reconstructed from `{x, q₀ x}` with identical
weights `(dilationAlpha ρ₀ q₀ u, dilationBeta ρ₀ q₀ u)` up to explicit square-root-log errors. -/
theorem singleQuartet_universal_twoPrime_chebyshev_span {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    ∃ q₀ ∈ ({2, 3} : Finset ℕ), Real.sin (ρ₀.im * Real.log q₀) ≠ 0 ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ {u x : ℝ}, 1 ≤ u → 16 ≤ x →
        |(Chebyshev.psi (u * x) - u * x) -
            dilationAlpha ρ₀ q₀ u * (Chebyshev.psi x - x) -
            dilationBeta ρ₀ q₀ u * (Chebyshev.psi ((q₀ : ℝ) * x) - (q₀ : ℝ) * x)| ≤
          C * (Real.sqrt (u * x) * Real.log (u * x) ^ 2 +
            (|dilationAlpha ρ₀ q₀ u| + |dilationBeta ρ₀ q₀ u|) *
              Real.sqrt x * Real.log x ^ 2) ∧
        |(Chebyshev.theta (u * x) - u * x) -
            dilationAlpha ρ₀ q₀ u * (Chebyshev.theta x - x) -
            dilationBeta ρ₀ q₀ u * (Chebyshev.theta ((q₀ : ℝ) * x) - (q₀ : ℝ) * x)| ≤
          C * (Real.sqrt (u * x) * Real.log (u * x) ^ 2 +
            (|dilationAlpha ρ₀ q₀ u| + |dilationBeta ρ₀ q₀ u|) *
              Real.sqrt x * Real.log x ^ 2) := by
  have hchoice : ∃ q₀ ∈ ({2, 3} : Finset ℕ), Real.sin (ρ₀.im * Real.log q₀) ≠ 0 := by
    rcases sin_mul_log_two_ne_zero_or_three_ne_zero hq.im_ne_zero with h2 | h3
    · exact ⟨2, by simp, by simpa using h2⟩
    · exact ⟨3, by simp, by simpa using h3⟩
  obtain ⟨q₀, hq_mem, hsin⟩ := hchoice
  have hq_ge2 : 2 ≤ q₀ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq_mem
    rcases hq_mem with rfl | rfl <;> omega
  have hq_le3 : (q₀ : ℝ) ≤ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq_mem
    rcases hq_mem with rfl | rfl <;> norm_num
  have hq_pos : 0 < q₀ := by omega
  have hq_r1 : (1 : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ q₀)
  obtain ⟨K, hK⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hq.1 hq.2.1).mp hq
  -- For `q₀ ≤ 3` and `x ≥ 16`, `√(q₀ x) log²(q₀ x) ≤ 8 √x log² x`.
  have hscale_q : ∀ {x : ℝ}, 16 ≤ x →
      Real.sqrt ((q₀ : ℝ) * x) * Real.log ((q₀ : ℝ) * x) ^ 2 ≤
        8 * (Real.sqrt x * Real.log x ^ 2) := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    have hq_rpos : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hq_pos
    have hlog_le : Real.log (q₀ : ℝ) ≤ Real.log x :=
      Real.log_le_log hq_rpos (by linarith)
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlog_sq : Real.log ((q₀ : ℝ) * x) ^ 2 ≤ 4 * Real.log x ^ 2 := by
      rw [Real.log_mul hq_rpos.ne' hx_pos.ne']
      have h1 : 0 ≤ Real.log (q₀ : ℝ) + Real.log x :=
        add_nonneg (Real.log_nonneg hq_r1) hlog_nn
      nlinarith
    have hsqrt_le : Real.sqrt (q₀ : ℝ) ≤ 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul hq_rpos.le]
    calc Real.sqrt (q₀ : ℝ) * Real.sqrt x * Real.log ((q₀ : ℝ) * x) ^ 2
        ≤ 2 * Real.sqrt x * (4 * Real.log x ^ 2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hsqrt_le (Real.sqrt_nonneg x))
            hlog_sq (sq_nonneg _) (by positivity)
      _ = 8 * (Real.sqrt x * Real.log x ^ 2) := by ring
  -- Also `|ψ(y) - θ(y)| ≤ 2 √y log² y` for `y ≥ 16` (`log y ≥ 2 > 1`).
  have hpsi_theta : ∀ {y : ℝ}, 16 ≤ y →
      |Chebyshev.psi y - Chebyshev.theta y| ≤ 2 * Real.sqrt y * Real.log y ^ 2 := by
    intro y hy
    have hdiff := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ y)
    have hnn : 0 ≤ Chebyshev.psi y - Chebyshev.theta y :=
      sub_nonneg.mpr (Chebyshev.theta_le_psi y)
    have hlog1 : 1 ≤ Real.log y := by
      linarith [RHTower.two_le_log_of_sixteen_le hy]
    rw [abs_of_nonneg hnn]
    calc Chebyshev.psi y - Chebyshev.theta y
        ≤ 2 * Real.sqrt y * Real.log y := hdiff
      _ ≤ 2 * Real.sqrt y * Real.log y ^ 2 := by
          have : Real.log y ≤ Real.log y ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_left this (by positivity)
  set C₀ : ℝ := 8 * (|K| + 2)
  refine ⟨q₀, hq_mem, hsin, C₀, by dsimp [C₀]; positivity, fun {u x} hu hx => ?_⟩
  have hx_pos : 0 < x := by linarith
  have hu_pos : 0 < u := zero_lt_one.trans_le hu
  have hux16 : 16 ≤ u * x := by nlinarith
  have hqx16 : 16 ≤ (q₀ : ℝ) * x := by nlinarith
  set α := dilationAlpha ρ₀ q₀ u
  set β := dilationBeta ρ₀ q₀ u
  set W : ℝ → ℝ := fun y => -(2 * (quartetCopyMult ρ₀ : ℝ) * ((y : ℂ) ^ ρ₀ / ρ₀).re)
  set η : ℝ → ℝ := fun y => (Chebyshev.psi y - y) - W y
  -- The wave `W` cancels identically: `W(u x) - α W(x) - β W(q₀ x) = 0`.
  have hW_cancel : W (u * x) - α * W x - β * W ((q₀ : ℝ) * x) = 0 := by
    have hspan := cpow_eq_dilationAlpha_add_dilationBeta ρ₀ hq_pos hsin hu_pos
    have hmul_ux : ((u * x : ℝ) : ℂ) ^ ρ₀ = (u : ℂ) ^ ρ₀ * (x : ℂ) ^ ρ₀ := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu_pos.le hx_pos.le]
    have hmul_qx : (((q₀ : ℝ) * x : ℝ) : ℂ) ^ ρ₀ = (q₀ : ℂ) ^ ρ₀ * (x : ℂ) ^ ρ₀ := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hx_pos.le]
      push_cast; rfl
    have hcomb : ((u * x : ℝ) : ℂ) ^ ρ₀ / ρ₀ =
        (α : ℂ) * ((x : ℂ) ^ ρ₀ / ρ₀) + (β : ℂ) * ((((q₀ : ℝ) * x : ℝ) : ℂ) ^ ρ₀ / ρ₀) := by
      rw [hmul_ux, hmul_qx, hspan]
      dsimp [α, β]
      ring
    have hre := congrArg Complex.re hcomb
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
    dsimp [W]
    linear_combination -(2 * (quartetCopyMult ρ₀ : ℝ)) * hre
  have hη_le : ∀ {y : ℝ}, 16 ≤ y → |η y| ≤ |K| * Real.sqrt y * Real.log y ^ 2 := by
    intro y hy
    have hk_y := hK y hy
    have heq_y : η y = Chebyshev.psi y - y +
        2 * (quartetCopyMult ρ₀ : ℝ) * ((y : ℂ) ^ ρ₀ / ρ₀).re := by
      dsimp [η, W]; ring
    rw [heq_y]
    exact hk_y.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.sqrt_nonneg y)) (sq_nonneg _))
  have hpsi_id : (Chebyshev.psi (u * x) - u * x) - α * (Chebyshev.psi x - x) -
      β * (Chebyshev.psi ((q₀ : ℝ) * x) - (q₀ : ℝ) * x) =
      η (u * x) - α * η x - β * η ((q₀ : ℝ) * x) := by
    dsimp [η]; linear_combination hW_cancel
  have hη_ux := hη_le hux16
  have hη_x := hη_le hx
  have hη_qx : |η ((q₀ : ℝ) * x)| ≤ 8 * |K| * (Real.sqrt x * Real.log x ^ 2) := by
    calc |η ((q₀ : ℝ) * x)|
        ≤ |K| * (Real.sqrt ((q₀ : ℝ) * x) * Real.log ((q₀ : ℝ) * x) ^ 2) := by
          linarith [hη_le hqx16]
      _ ≤ |K| * (8 * (Real.sqrt x * Real.log x ^ 2)) :=
          mul_le_mul_of_nonneg_left (hscale_q hx) (abs_nonneg K)
      _ = 8 * |K| * (Real.sqrt x * Real.log x ^ 2) := by ring
  constructor
  · rw [hpsi_id]
    have htri : |η (u * x) - α * η x - β * η ((q₀ : ℝ) * x)| ≤
        |η (u * x)| + |α| * |η x| + |β| * |η ((q₀ : ℝ) * x)| := by
      calc |η (u * x) - α * η x - β * η ((q₀ : ℝ) * x)|
          ≤ |η (u * x) - α * η x| + |β * η ((q₀ : ℝ) * x)| := abs_sub _ _
        _ ≤ |η (u * x)| + |α * η x| + |β * η ((q₀ : ℝ) * x)| :=
            add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_mul, abs_mul]
    have h1 : |α| * |η x| ≤ 8 * |K| * |α| * (Real.sqrt x * Real.log x ^ 2) := by
      calc |α| * |η x|
          ≤ |α| * (|K| * Real.sqrt x * Real.log x ^ 2) :=
            mul_le_mul_of_nonneg_left hη_x (abs_nonneg α)
        _ ≤ 8 * |K| * |α| * (Real.sqrt x * Real.log x ^ 2) := by
            have : 0 ≤ |α| * |K| * (Real.sqrt x * Real.log x ^ 2) := by positivity
            linarith
    have h2 : |β| * |η ((q₀ : ℝ) * x)| ≤ 8 * |K| * |β| * (Real.sqrt x * Real.log x ^ 2) := by
      calc |β| * |η ((q₀ : ℝ) * x)|
          ≤ |β| * (8 * |K| * (Real.sqrt x * Real.log x ^ 2)) :=
            mul_le_mul_of_nonneg_left hη_qx (abs_nonneg β)
        _ = 8 * |K| * |β| * (Real.sqrt x * Real.log x ^ 2) := by ring
    have h0 : |η (u * x)| ≤ C₀ * (Real.sqrt (u * x) * Real.log (u * x) ^ 2) := by
      dsimp [C₀]
      have : 0 ≤ Real.sqrt (u * x) * Real.log (u * x) ^ 2 := by positivity
      nlinarith [abs_nonneg K]
    dsimp [C₀] at h0 ⊢
    have hrx : 0 ≤ (|α| + |β|) * Real.sqrt x * Real.log x ^ 2 := by positivity
    nlinarith [htri, h0, h1, h2]
  · -- Companion `θ` bound by transferring `|ψ - θ| ≤ 2 √y log² y`.
    set ηθ : ℝ → ℝ := fun y => (Chebyshev.theta y - y) - W y
    have hηθ_le : ∀ {y : ℝ}, 16 ≤ y → |ηθ y| ≤ (|K| + 2) * Real.sqrt y * Real.log y ^ 2 := by
      intro y hy
      have hsplit : ηθ y = η y - (Chebyshev.psi y - Chebyshev.theta y) := by
        dsimp [ηθ, η]; ring
      rw [hsplit]
      calc |η y - (Chebyshev.psi y - Chebyshev.theta y)|
          ≤ |η y| + |Chebyshev.psi y - Chebyshev.theta y| := abs_sub _ _
        _ ≤ |K| * Real.sqrt y * Real.log y ^ 2 + 2 * Real.sqrt y * Real.log y ^ 2 :=
            add_le_add (hη_le hy) (hpsi_theta hy)
        _ = (|K| + 2) * Real.sqrt y * Real.log y ^ 2 := by ring
    have htheta_id : (Chebyshev.theta (u * x) - u * x) - α * (Chebyshev.theta x - x) -
        β * (Chebyshev.theta ((q₀ : ℝ) * x) - (q₀ : ℝ) * x) =
        ηθ (u * x) - α * ηθ x - β * ηθ ((q₀ : ℝ) * x) := by
      dsimp [ηθ]; linear_combination hW_cancel
    rw [htheta_id]
    have htri : |ηθ (u * x) - α * ηθ x - β * ηθ ((q₀ : ℝ) * x)| ≤
        |ηθ (u * x)| + |α| * |ηθ x| + |β| * |ηθ ((q₀ : ℝ) * x)| := by
      calc |ηθ (u * x) - α * ηθ x - β * ηθ ((q₀ : ℝ) * x)|
          ≤ |ηθ (u * x) - α * ηθ x| + |β * ηθ ((q₀ : ℝ) * x)| := abs_sub _ _
        _ ≤ |ηθ (u * x)| + |α * ηθ x| + |β * ηθ ((q₀ : ℝ) * x)| :=
            add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_mul, abs_mul]
    have hθ_ux := hηθ_le hux16
    have hθ_x := hηθ_le hx
    have hθ_qx : |ηθ ((q₀ : ℝ) * x)| ≤ C₀ * (Real.sqrt x * Real.log x ^ 2) := by
      dsimp [C₀]
      calc |ηθ ((q₀ : ℝ) * x)|
          ≤ (|K| + 2) * (Real.sqrt ((q₀ : ℝ) * x) * Real.log ((q₀ : ℝ) * x) ^ 2) := by
            linarith [hηθ_le hqx16]
        _ ≤ (|K| + 2) * (8 * (Real.sqrt x * Real.log x ^ 2)) :=
            mul_le_mul_of_nonneg_left (hscale_q hx) (by positivity)
        _ = 8 * (|K| + 2) * (Real.sqrt x * Real.log x ^ 2) := by ring
    have h1 : |α| * |ηθ x| ≤ C₀ * |α| * (Real.sqrt x * Real.log x ^ 2) := by
      dsimp [C₀]
      calc |α| * |ηθ x|
          ≤ |α| * ((|K| + 2) * Real.sqrt x * Real.log x ^ 2) :=
            mul_le_mul_of_nonneg_left hθ_x (abs_nonneg α)
        _ ≤ 8 * (|K| + 2) * |α| * (Real.sqrt x * Real.log x ^ 2) := by
            have : 0 ≤ |α| * (|K| + 2) * (Real.sqrt x * Real.log x ^ 2) := by positivity
            linarith
    have h2 : |β| * |ηθ ((q₀ : ℝ) * x)| ≤ C₀ * |β| * (Real.sqrt x * Real.log x ^ 2) := by
      calc |β| * |ηθ ((q₀ : ℝ) * x)|
          ≤ |β| * (C₀ * (Real.sqrt x * Real.log x ^ 2)) :=
            mul_le_mul_of_nonneg_left hθ_qx (abs_nonneg β)
        _ = C₀ * |β| * (Real.sqrt x * Real.log x ^ 2) := by ring
    have h0 : |ηθ (u * x)| ≤ C₀ * (Real.sqrt (u * x) * Real.log (u * x) ^ 2) := by
      dsimp [C₀]
      have : 0 ≤ (|K| + 2) * (Real.sqrt (u * x) * Real.log (u * x) ^ 2) := by positivity
      linarith
    nlinarith [htri, h0, h1, h2]

/-! ## 4. Zero-pinned fractional-part Mellin equivalences and upper-range divisor concentration -/

/-- **Zero-pinned fractional-part Mellin equivalences on `{0 < Re s < 1}`.**
For any `0 < Re s < 1` and dilation `c > 0`, the following are equivalent:
1. `riemannZeta s = 0`;
2. `∫_{u > 0} {u} u^{-(s + 1)} du = 0`;
3. `∫_{t > 1} {t} t^{-(s + 1)} dt = 1 / (s - 1)`;
4. `∫_{t > 0} {c t} t^{-(s + 1)} dt = 0`. -/
theorem riemannZeta_eq_zero_iff_fract_mellin_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {c : ℝ} (hc : 0 < c) :
    (riemannZeta s = 0 ↔
        (∫ u in Ioi (0 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))) = 0) ∧
      (riemannZeta s = 0 ↔
        (∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) = 1 / (s - 1)) ∧
      (riemannZeta s = 0 ↔
        (∫ t in Ioi (0 : ℝ), ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) = 0) := by
  have hs_ne0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; exact lt_irrefl 1 hs1
  have hc_pow_ne : ((c : ℝ) : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  refine ⟨?_, ?_, ?_⟩
  · rw [RHTower.integral_Ioi_zero_fract_cpow hs0 hs1, neg_eq_zero, div_eq_zero_iff]
    exact ⟨fun h => Or.inl h, fun h => h.resolve_right hs_ne0⟩
  · rw [RHTower.integral_Ioi_one_fract_cpow_of_re_pos hs0 hs_ne1, sub_eq_self, div_eq_zero_iff]
    exact ⟨fun h => Or.inl h, fun h => h.resolve_right hs_ne0⟩
  · rw [RHTower.integral_Ioi_zero_fract_dilate_cpow hs0 hs1 hc, mul_eq_zero, neg_eq_zero,
      div_eq_zero_iff]
    exact ⟨fun h => Or.inr (Or.inl h),
      fun h => (h.resolve_left hc_pow_ne).resolve_right hs_ne0⟩

/-- **Exact Chebyshev fractional-part divisor identity (`X ≥ 0`).**
`∑_{1 ≤ d ≤ ⌊X⌋₊} Λ(d) {X / d} = X ∑_{1 ≤ d ≤ ⌊X⌋₊} Λ(d) / d - ∑_{1 ≤ m ≤ ⌊X⌋₊} log m`. -/
theorem sum_vonMangoldt_mul_fract_eq_harmonic_sub_log {X : ℝ} (hX : 0 ≤ X) :
    ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt d : ℝ) * Int.fract (X / d) =
      X * (∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt d : ℝ) / d) -
        ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Real.log m := by
  set N : ℕ := ⌊X⌋₊
  have hfloor : ∀ d : ℕ, (⌊X / (d : ℝ)⌋ : ℝ) = ((N / d : ℕ) : ℝ) := by
    intro d
    have h := Int.natCast_floor_eq_floor (div_nonneg hX (Nat.cast_nonneg d))
    have h2 : ((⌊X / (d : ℝ)⌋₊ : ℕ) : ℝ) = (⌊X / (d : ℝ)⌋ : ℝ) := by exact_mod_cast h
    rw [← h2, Nat.floor_div_natCast]
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt d : ℝ) * Int.fract (X / d) =
        X * ((ArithmeticFunction.vonMangoldt d : ℝ) / d) -
          (ArithmeticFunction.vonMangoldt d : ℝ) * ((N / d : ℕ) : ℝ) := by
    intro d _
    rw [Int.fract, hfloor d]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    RHTower.Mertens.log_summatory_eq N]

/-- **Upper-range (`d > √X`) concentration of `∑_{d ≤ X} Λ(d) {X / d}`.**
For every `X ≥ 1`:
1. The sub-square-root divisor sum `1 ≤ d ≤ ⌊√X⌋₊` lies in `[0, ψ(√X)]`;
2. Consequently, the super-square-root divisor sum `⌊√X⌋₊ + 1 ≤ d ≤ ⌊X⌋₊` equals
   `X ∑_{d ≤ X} Λ(d) / d - ∑_{m ≤ X} log m` up to `[ -ψ(√X), 0 ]`. -/
theorem sum_vonMangoldt_mul_fract_upper_sqrt_concentration {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊,
        (ArithmeticFunction.vonMangoldt d : ℝ) * Int.fract (X / d) ∧
      (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊,
          (ArithmeticFunction.vonMangoldt d : ℝ) * Int.fract (X / d)) ≤
        Chebyshev.psi (Real.sqrt X) ∧
      |(∑ d ∈ Finset.Icc (⌊Real.sqrt X⌋₊ + 1) ⌊X⌋₊,
          (ArithmeticFunction.vonMangoldt d : ℝ) * Int.fract (X / d)) -
        (X * (∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt d : ℝ) / d) -
          ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Real.log m)| ≤
        Chebyshev.psi (Real.sqrt X) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hsqrt_le_X : Real.sqrt X ≤ X := by
    have h1 : 1 ≤ Real.sqrt X := (Real.le_sqrt zero_le_one hX0).mpr (by ring_nf; exact hX)
    have hsq := Real.mul_self_sqrt hX0
    nlinarith
  have hM_le_N : ⌊Real.sqrt X⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hsqrt_le_X
  set f : ℕ → ℝ := fun d => (ArithmeticFunction.vonMangoldt d : ℝ) * Int.fract (X / d)
  have hf_nn : 0 ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, f d :=
    Finset.sum_nonneg fun d _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Int.fract_nonneg _)
  have hf_le_psi : (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, f d) ≤ Chebyshev.psi (Real.sqrt X) := by
    have hpsi_eq : Chebyshev.psi (Real.sqrt X) =
        ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, (ArithmeticFunction.vonMangoldt d : ℝ) := by
      rw [Chebyshev.psi_eq_sum_Icc,
        show Finset.Icc 0 ⌊Real.sqrt X⌋₊ = insert 0 (Finset.Icc 1 ⌊Real.sqrt X⌋₊) from by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
        Finset.sum_insert (by simp)]
      simp
    rw [hpsi_eq]
    refine Finset.sum_le_sum fun d _ => ?_
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Int.fract_lt_one _).le
  -- Partition `Icc 1 ⌊X⌋₊ = Icc 1 ⌊√X⌋₊ ∪ Icc (⌊√X⌋₊ + 1) ⌊X⌋₊`.
  have hdisj : Disjoint (Finset.Icc 1 ⌊Real.sqrt X⌋₊)
      (Finset.Icc (⌊Real.sqrt X⌋₊ + 1) ⌊X⌋₊) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    have h1 := (Finset.mem_Icc.mp hd1).2
    have h2 := (Finset.mem_Icc.mp hd2).1
    omega
  have hunion : Finset.Icc 1 ⌊Real.sqrt X⌋₊ ∪ Finset.Icc (⌊Real.sqrt X⌋₊ + 1) ⌊X⌋₊ =
      Finset.Icc 1 ⌊X⌋₊ := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hsplit_sum : (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, f d) +
      (∑ d ∈ Finset.Icc (⌊Real.sqrt X⌋₊ + 1) ⌊X⌋₊, f d) =
      ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, f d := by
    rw [← Finset.sum_union hdisj, hunion]
  have htot := sum_vonMangoldt_mul_fract_eq_harmonic_sub_log hX0
  refine ⟨hf_nn, hf_le_psi, ?_⟩
  rw [abs_le]
  constructor <;> linarith

end GaloisForLFunctions.ExceptionalLayerTheory
