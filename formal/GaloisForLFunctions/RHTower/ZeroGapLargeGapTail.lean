import GaloisForLFunctions.RHTower.ZeroGapWindowPrimePolynomial
import GaloisForLFunctions.RHTower.VonMangoldtNonPrimeSqrtSum
import GaloisForLFunctions.RHTower.WeilConePrimePolynomialMoments

/-!
# Large gaps between zeros are rare under RH

Under RH, for every `k` there are `C, T₀` with (`riemannHypothesis_measureReal_zeroGap_le`)

  `|{t ∈ [T, 2T] : N_ξ(t + h) = N_ξ(t)}| ≤ C T / (1 + h log T)^k`   for `T ≥ T₀`, `h > 0`,

and in fact `≤ C T e^{−c h log T}` (`riemannHypothesis_measureReal_zeroGap_le_exp`).

Write `η = h log T`.  If `N_ξ(t + h) = N_ξ(t)`, no ordinate lies in `(t, t + h]`, so every zero
is at distance `≥ h/2` from `c = t + h/2` (`le_abs_im_sub_of_xiZeroCount_eq`).  The window
explicit formula at scale `ℓ = 2D/h` (`gap_primePoly_large`) turns this into a large value of a
prime polynomial of length `X = e^{2ℓ} = T^{4D/η}`:

  `‖Σ_{p ≤ X} log p · β(p) p^{−½−ic}‖ ≥ log T/12`,   `|β| ≤ 1`   (`gap_norm_edPoly_large`),

after the proper prime powers are bounded by `2 log X + O(1)`
(`sum_nonprime_vonMangoldt_div_sqrt_le`).  For `η ≥ η₀(m)` the `2m`-th moment of a prime
polynomial with `X^m ≤ T^{1/4}` is diagonal (`measureReal_large_primePoly_le_factorial`), and
`Σ_{p ≤ X} log²p/p ≤ 18ℓ²` gives the measure bound `4 m! (10368 D²)^m T/η^{2m}`
(`measureReal_zeroGap_le_of_large`).  Small `η` is trivial, and for `h > 2D` the set is empty
by Littlewood's short windows (`riemannHypothesis_eventually_xiZeroCount_window_ge`).
-/

open Complex MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-! ## Gaps in the zero count -/

theorem one_le_N_of_mem_window (Z : ZeroConfig) {a b : ℝ} {ρ : ℂ} (hρ : ρ ∈ Z.window a b) :
    1 ≤ Z.N a b := by
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc 1 ≤ Z.mult ρ := Z.one_le_mult ρ hρ.1
    _ ≤ ∑ i ∈ hfin.toFinset, Z.mult i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr hρ)

/-- If `N_ξ(t + h) = N_ξ(t)`, every zero has ordinate at distance `≥ h/2` from `t + h/2`. -/
theorem le_abs_im_sub_of_xiZeroCount_eq {t h : ℝ} (ht : 0 ≤ t) (hh : 0 < h)
    (hgap : xiZeroCount (t + h) = xiZeroCount t) :
    ∀ ρ ∈ zetaZeroConfig.carrier, h / 2 ≤ |ρ.im - (t + h / 2)| := by
  intro ρ hρ
  have hN := xiZeroCount_sub_eq ht (by linarith : t ≤ t + h)
  rw [hgap, sub_self] at hN
  have hN0 : zetaZeroConfig.N t (t + h) = 0 := by exact_mod_cast hN.symm
  by_contra hlt
  rw [not_le, abs_lt] at hlt
  have hw : ρ ∈ zetaZeroConfig.window t (t + h) :=
    ⟨hρ, by constructor <;> linarith [hlt.1, hlt.2]⟩
  have := one_le_N_of_mem_window zetaZeroConfig hw
  omega

/-! ## The normalised gap polynomial -/

/-- The window coefficient `b_ℓ(n) = ŵ₁(log n)/(D/ℓ)² − ŵ₀(log n)` of `gap_primePoly_large`. -/
def gapWeight (ℓ : ℝ) (n : ℕ) : ℝ :=
  wcos ℓ 1 (Real.log n) / (windowD / ℓ) ^ 2 - wcos ℓ 0 (Real.log n)

theorem energy_one_div_windowD_sq_le : energy 1 / windowD ^ 2 ≤ energy 0 / 2 := by
  have hE0 := energy_zero_pos
  have hD := one_le_windowD
  rw [div_le_iff₀ (by positivity), windowD_sq]
  have e : energy 0 / 2 * (2 * energy 1 / energy 0 + 1) = energy 1 + energy 0 / 2 := by
    field_simp
  rw [e]; linarith

/-- `|b_ℓ(n)| ≤ 3πℓE₀`. -/
theorem abs_gapWeight_le {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    |gapWeight ℓ n| ≤ 3 * Real.pi * ℓ * energy 0 := by
  have hD := one_le_windowD
  have hE0 := energy_zero_pos
  have hE1 := energy_nonneg 1
  set v := Real.log n
  have h1 : |wcos ℓ 1 v| ≤ 2 * Real.pi * energy 1 / ℓ :=
    (abs_wcos_le hℓ 1 v).trans_eq (integral_psi_one hℓ)
  have h0 : |wcos ℓ 0 v| ≤ 2 * Real.pi * ℓ * energy 0 :=
    (abs_wcos_le hℓ 0 v).trans_eq (integral_psi_zero hℓ)
  have hE1D := energy_one_div_windowD_sq_le
  rw [div_le_iff₀ (by positivity)] at hE1D
  have hq : |wcos ℓ 1 v / (windowD / ℓ) ^ 2| ≤ Real.pi * ℓ * energy 0 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (windowD / ℓ) ^ 2),
      div_le_iff₀ (by positivity)]
    have e : Real.pi * ℓ * energy 0 * (windowD / ℓ) ^ 2 =
        Real.pi * energy 0 * windowD ^ 2 / ℓ := by field_simp
    rw [e]
    refine h1.trans (div_le_div_of_nonneg_right ?_ hℓ.le)
    have := mul_le_mul_of_nonneg_left hE1D (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  unfold gapWeight
  calc |wcos ℓ 1 v / (windowD / ℓ) ^ 2 - wcos ℓ 0 v|
      ≤ |wcos ℓ 1 v / (windowD / ℓ) ^ 2| + |wcos ℓ 0 v| := abs_sub _ _
    _ ≤ Real.pi * ℓ * energy 0 + 2 * Real.pi * ℓ * energy 0 := add_le_add hq h0
    _ = 3 * Real.pi * ℓ * energy 0 := by ring

/-- The coefficients `Λ(p) b_ℓ(p)/(3πℓE₀)` on the primes `p ≤ N`; they satisfy `|·| ≤ Λ`. -/
def gapCoeff (ℓ : ℝ) (N n : ℕ) : ℝ :=
  if n.Prime ∧ n ≤ N then Λ n * (gapWeight ℓ n / (3 * Real.pi * ℓ * energy 0)) else 0

theorem abs_gapCoeff_le {ℓ : ℝ} (hℓ : 0 < ℓ) (N n : ℕ) : |gapCoeff ℓ N n| ≤ Λ n := by
  unfold gapCoeff
  split_ifs
  · have hA : 0 < 3 * Real.pi * ℓ * energy 0 := by have := energy_zero_pos; positivity
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_div, abs_of_pos hA]
    refine mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg ?_
    rw [div_le_one hA]
    exact abs_gapWeight_le hℓ n
  · simp

/-- The prime polynomial `Σ_{p ≤ N} gapCoeff(p) p^{−s}` as an arithmetic function. -/
def gapPoly (ℓ : ℝ) (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => ((gapCoeff ℓ N n : ℝ) : ℂ), by simp [gapCoeff, Nat.not_prime_zero]⟩

theorem gapPoly_apply (ℓ : ℝ) (N n : ℕ) : gapPoly ℓ N n = ((gapCoeff ℓ N n : ℝ) : ℂ) := rfl

theorem gapPoly_prime {ℓ : ℝ} {N : ℕ} : ∀ k, gapPoly ℓ N k ≠ 0 → k.Prime := by
  intro k hk
  by_contra hp
  apply hk
  simp [gapPoly_apply, gapCoeff, hp]

theorem gapPoly_le {ℓ : ℝ} {N : ℕ} : ∀ k, gapPoly ℓ N k ≠ 0 → k ≤ N := by
  intro k hk
  by_contra hp
  apply hk
  simp [gapPoly_apply, gapCoeff, hp]

/-! ## The real part on the critical line -/

theorem re_natCast_cpow_neg_displaced {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    (((n : ℝ) : ℂ) ^ (-displacedLinePt 0 c)).re = Real.cos (c * Real.log n) / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), ← Complex.ofReal_log hn0.le,
    Complex.exp_re]
  have hs : Real.sqrt n = Real.exp (Real.log n * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
  rw [hs, div_eq_mul_inv, ← Real.exp_neg]
  simp only [displacedLinePt, sub_zero, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  rw [mul_comm (Real.cos _)]
  congr 1
  · congr 1; ring
  · rw [← Real.cos_neg]; congr 1; ring

theorem re_edPoly_gapPoly (ℓ c : ℝ) (N : ℕ) :
    (edPoly (gapPoly ℓ N) (Finset.Icc 1 N) (displacedLinePt 0 c)).re =
      ∑ n ∈ Finset.Icc 1 N, gapCoeff ℓ N n * (Real.cos (c * Real.log n) / Real.sqrt n) := by
  unfold edPoly
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [gapPoly_apply, Complex.re_ofReal_mul,
    re_natCast_cpow_neg_displaced (Finset.mem_Icc.mp hn).1]

/-! ## A gap forces a large value -/

theorem sum_sq_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Λ n ^ 2 / n ≤ Real.log N * (Real.log N + Real.log 4 + 4) := by
  have hm := Mertens.mertens_first N hN
  rw [abs_le] at hm
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc ∑ n ∈ Finset.Icc 1 N, Λ n ^ 2 / n
      ≤ ∑ n ∈ Finset.Icc 1 N, Real.log N * (Λ n / n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 := Finset.mem_Icc.mp hn
        have hΛ : Λ n ≤ Real.log N := ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log (by exact_mod_cast hn1.1) (by exact_mod_cast hn1.2))
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hΛ
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
    _ = Real.log N * ∑ n ∈ Finset.Icc 1 N, Λ n / n := by rw [Finset.mul_sum]
    _ ≤ Real.log N * (Real.log N + Real.log 4 + 4) := mul_le_mul_of_nonneg_left (by linarith) hL

theorem log_floor_exp_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    1 ≤ ⌊Real.exp (2 * ℓ)⌋₊ ∧ Real.log ⌊Real.exp (2 * ℓ)⌋₊ ≤ 2 * ℓ := by
  have hX1 : 1 ≤ Real.exp (2 * ℓ) := Real.one_le_exp (by positivity)
  have hN1 : 1 ≤ ⌊Real.exp (2 * ℓ)⌋₊ := (Nat.one_le_floor_iff _).mpr hX1
  refine ⟨hN1, ?_⟩
  have hN0 : (0 : ℝ) < ⌊Real.exp (2 * ℓ)⌋₊ := by exact_mod_cast hN1
  calc Real.log ⌊Real.exp (2 * ℓ)⌋₊ ≤ Real.log (Real.exp (2 * ℓ)) :=
        Real.log_le_log hN0 (Nat.floor_le (Real.exp_pos _).le)
    _ = 2 * ℓ := Real.log_exp _

/-- **A gap forces a large value of the normalised prime polynomial.**  Under RH there is `K` such
that for `ℓ ≥ 1`, `c ≥ 2`, `e^{2ℓ} ≤ c`, if every zero has ordinate at distance `≥ D/ℓ` from `c`,
then `log c/6 − K − 4ℓ ≤ ‖Σ_{p ≤ e^{2ℓ}} gapCoeff(p) p^{−½−ic}‖`. -/
theorem gap_norm_edPoly_large (hRH : RiemannHypothesis) :
    ∃ K : ℝ, ∀ ℓ c : ℝ, 1 ≤ ℓ → 2 ≤ c → Real.exp (2 * ℓ) ≤ c →
      (∀ ρ ∈ zetaZeroConfig.carrier, windowD / ℓ ≤ |ρ.im - c|) →
      Real.log c / 6 - K - 4 * ℓ ≤
        ‖edPoly (gapPoly ℓ ⌊Real.exp (2 * ℓ)⌋₊) (Finset.Icc 1 ⌊Real.exp (2 * ℓ)⌋₊)
          (displacedLinePt 0 c)‖ := by
  obtain ⟨K, hK⟩ := gap_primePoly_large hRH
  refine ⟨K / (3 * energy 0) + (4 * Real.log 4 + 16), fun ℓ c hℓ hc hXc hgap => ?_⟩
  have key := hK ℓ c hℓ hc hXc hgap
  have hℓ0 : 0 < ℓ := by linarith
  have hE0 := energy_zero_pos
  have hπ := Real.pi_pos
  obtain ⟨hN1, hlogN⟩ := log_floor_exp_le hℓ0.le
  set N := ⌊Real.exp (2 * ℓ)⌋₊ with hNdef
  set A := 3 * Real.pi * ℓ * energy 0 with hA
  have hA0 : 0 < A := by positivity
  set E := edPoly (gapPoly ℓ N) (Finset.Icc 1 N) (displacedLinePt 0 c)
  set g : ℕ → ℝ := fun n => Λ n / Real.sqrt n * ((wcos ℓ 1 (Real.log n) / (windowD / ℓ) ^ 2 -
    wcos ℓ 0 (Real.log n)) * Real.cos (c * Real.log n)) with hg
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) Nat.Prime g
  -- the primes give `A · Re E`
  have hP : ∑ n ∈ Finset.Ioc 0 N with n.Prime, g n = A * E.re := by
    rw [re_edPoly_gapPoly, Finset.mul_sum, Finset.sum_filter,
      show Finset.Icc 1 N = Finset.Ioc 0 N from Finset.val_inj.mp rfl]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
    unfold gapCoeff
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos ⟨hp, hnN⟩, hg]
      unfold gapWeight
      field_simp
      rw [hA]; ring
    · rw [if_neg hp, if_neg (fun h => hp h.1), zero_mul, mul_zero]
  -- the proper prime powers are `O(log N)`
  have hQ : |∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, g n| ≤
      A * (2 * Real.log N + 4 * Real.log 4 + 16) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, |g n|
        ≤ ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, A * (Λ n / Real.sqrt n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have hb := abs_gapWeight_le hℓ0 n
          unfold gapWeight at hb
          rw [hg]
          simp only
          rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.sqrt_nonneg _))]
          have hcos := Real.abs_cos_le_one (c * Real.log n)
          have hw : 0 ≤ Λ n / Real.sqrt n :=
            div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
          calc Λ n / Real.sqrt n * (|wcos ℓ 1 (Real.log n) / (windowD / ℓ) ^ 2 -
                wcos ℓ 0 (Real.log n)| * |Real.cos (c * Real.log n)|)
              ≤ Λ n / Real.sqrt n * (A * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul hb hcos (abs_nonneg _) hA0.le) hw
            _ = A * (Λ n / Real.sqrt n) := by ring
      _ = A * ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, Λ n / Real.sqrt n := by rw [Finset.mul_sum]
      _ ≤ A * (2 * Real.log N + 4 * Real.log 4 + 16) :=
          mul_le_mul_of_nonneg_left (sum_nonprime_vonMangoldt_div_sqrt_le hN1) hA0.le
  have hsum : ∑ n ∈ Finset.Ioc 0 N, Λ n / Real.sqrt n * ((wcos ℓ 1 (Real.log n) /
      (windowD / ℓ) ^ 2 - wcos ℓ 0 (Real.log n)) * Real.cos (c * Real.log n)) =
      A * E.re + ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, g n := by
    rw [← hP, hsplit]
  rw [hsum] at key
  set Q := ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, g n
  set R := 2 * Real.log N + 4 * Real.log 4 + 16
  have hre := Complex.abs_re_le_norm E
  have h1 : -(A * E.re + Q) ≤ A * (‖E‖ + R) := by
    have hr : -E.re ≤ ‖E‖ := (neg_le_abs _).trans hre
    have hq : -Q ≤ A * R := (neg_le_abs _).trans hQ
    have := mul_le_mul_of_nonneg_left hr hA0.le
    linarith
  have h2 : -(1 / Real.pi) * (A * E.re + Q) ≤ 3 * ℓ * energy 0 * (‖E‖ + R) := by
    have e : 3 * ℓ * energy 0 * (‖E‖ + R) = 1 / Real.pi * (A * (‖E‖ + R)) := by
      rw [hA]; field_simp
    rw [e, neg_mul, ← mul_neg]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (Real.log c / 6 - K / (3 * energy 0)) * (3 * ℓ * energy 0) ≤
      (‖E‖ + R) * (3 * ℓ * energy 0) := by
    have e : (Real.log c / 6 - K / (3 * energy 0)) * (3 * ℓ * energy 0) =
        energy 0 / 2 * ℓ * Real.log c - K * ℓ := by field_simp; ring
    rw [e, mul_comm (‖E‖ + R)]
    linarith
  have h4 := le_of_mul_le_mul_right h3 (by positivity)
  linarith

/-! ## The measure of the gap set -/

theorem sum_norm_gapPoly_sq_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp (2 * ℓ)⌋₊, ‖gapPoly ℓ ⌊Real.exp (2 * ℓ)⌋₊ n‖ ^ 2 *
      (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤ 18 * ℓ ^ 2 := by
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨hN1, hlogN⟩ := log_floor_exp_le hℓ0.le
  set N := ⌊Real.exp (2 * ℓ)⌋₊
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖gapPoly ℓ N n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      Λ n ^ 2 / n := by
    intro n _
    rw [gapPoly_apply, Complex.norm_real, Real.norm_eq_abs,
      show (2 * (0 : ℝ) - 1) = -1 by norm_num, Real.rpow_neg_one, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _)
      (abs_gapCoeff_le hℓ0 N n) 2) (Nat.cast_nonneg _)
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, Λ n ^ 2 / n := Finset.sum_le_sum hterm
    _ ≤ Real.log N * (Real.log N + Real.log 4 + 4) := sum_sq_vonMangoldt_div_le hN1
    _ ≤ 2 * ℓ * (2 * ℓ + 7) := mul_le_mul hlogN (by linarith) (by positivity) (by positivity)
    _ ≤ 18 * ℓ ^ 2 := by nlinarith

/-- `8M(1 + log M) ≤ 2T` for `1 ≤ M ≤ T^{1/4}`, `log T ≥ 6`. -/
theorem eight_mul_one_add_log_le {M T : ℝ} (hM : 1 ≤ M) (hT : 0 < T)
    (hMT : M ≤ Real.exp (Real.log T / 4)) (hL : 6 ≤ Real.log T) :
    8 * M * (1 + Real.log M) ≤ 2 * T := by
  set L := Real.log T
  have hlogM : Real.log M ≤ L / 4 := by
    rw [← Real.log_exp (L / 4)]; exact Real.log_le_log (by linarith) hMT
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM
  have h1 : 1 + Real.log M ≤ Real.exp (L / 4) := by linarith [Real.add_one_le_exp (L / 4)]
  have h4 : 4 ≤ Real.exp (L / 2) := by linarith [Real.add_one_le_exp (L / 2)]
  have hTe : T = Real.exp (L / 4) * Real.exp (L / 4) * Real.exp (L / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, show L / 4 + L / 4 + L / 2 = L by ring,
      Real.exp_log hT]
  have hpos : 0 ≤ Real.exp (L / 4) * Real.exp (L / 4) := by positivity
  have h5 : 8 * M * (1 + Real.log M) ≤ 8 * (Real.exp (L / 4) * Real.exp (L / 4)) := by
    have := mul_le_mul hMT h1 (by linarith) (Real.exp_pos _).le
    linarith
  have h6 := mul_le_mul_of_nonneg_left h4 hpos
  rw [hTe]
  linarith

/-- **Gaps of length `η/log T` with `η ≥ 192Dm` have measure `≤ 4m!(10368D²)^m T/η^{2m}`**, with one
threshold `T₀` for all `m`. -/
theorem measureReal_zeroGap_le_of_large_unif (hRH : RiemannHypothesis) :
    ∃ T₀ : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ T h : ℝ, T₀ ≤ T → 0 < h → h ≤ 2 * windowD →
      192 * windowD * m ≤ h * Real.log T →
      volume.real ({t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)) ≤
        4 * m.factorial * (10368 * windowD ^ 2) ^ m * T / (h * Real.log T) ^ (2 * m) := by
  obtain ⟨K, hK⟩ := gap_norm_edPoly_large hRH
  refine ⟨max (max 2 windowD) (max (Real.exp (24 * |K|)) (Real.exp 6)),
    fun m hm T h hT hh hhD hη => ?_⟩
  have hD := one_le_windowD
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTD : windowD ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : 0 < T := by linarith
  have hLK : 24 * |K| ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
  have hL6 : 6 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
  set D := windowD with hDdef
  set L := Real.log T with hLdef
  have hDpos : 0 < D := by linarith
  set ℓ := 2 * D / h with hℓdef
  have hℓh : ℓ * h = 2 * D := by rw [hℓdef]; field_simp
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef, le_div_iff₀ hh]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hℓm : 96 * ℓ * m ≤ L := by
    have h1 : ℓ * (192 * D * m) ≤ ℓ * (h * L) := mul_le_mul_of_nonneg_left hη hℓ0.le
    have h2 : ℓ * (h * L) = 2 * D * L := by rw [← mul_assoc, hℓh]
    have h3 : 2 * D * (96 * ℓ * m) ≤ 2 * D * L := by
      have e : 2 * D * (96 * ℓ * m) = ℓ * (192 * D * m) := by ring
      linarith
    exact le_of_mul_le_mul_left h3 (by positivity)
  have hℓL : 96 * ℓ ≤ L := by
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 96 * ℓ)
    linarith
  obtain ⟨hN1, hlogN⟩ := log_floor_exp_le hℓ0.le
  set N := ⌊Real.exp (2 * ℓ)⌋₊ with hNdef
  set V := L / 12 with hVdef
  have hV : 0 < V := by positivity
  set S : Set ℝ := {τ | V ≤ ‖edPoly (gapPoly ℓ N) (Finset.Icc 1 N) (displacedLinePt 0 τ)‖}
  -- every gap point, shifted to the centre of its gap, is a large value
  have hsub : {t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T) ⊆
      (fun t => t + h / 2) ⁻¹' (S ∩ Ioc T (3 * T)) := by
    rintro t ⟨hgap, htT, ht2T⟩
    have ht0 : 0 ≤ t := by linarith
    have hdist := le_abs_im_sub_of_xiZeroCount_eq ht0 hh hgap
    have hDℓ : D / ℓ = h / 2 := by rw [hℓdef]; field_simp
    have hc2 : 2 ≤ t + h / 2 := by linarith
    have hXc : Real.exp (2 * ℓ) ≤ t + h / 2 := by
      calc Real.exp (2 * ℓ) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
        _ = T := Real.exp_log hT0
        _ ≤ t + h / 2 := by linarith
    have hlarge := hK ℓ (t + h / 2) hℓ1 hc2 hXc (fun ρ hρ => by rw [hDℓ]; exact hdist ρ hρ)
    have hlogc : L ≤ Real.log (t + h / 2) := Real.log_le_log hT0 (by linarith)
    have hKabs : K ≤ |K| := le_abs_self K
    refine ⟨?_, ?_, ?_⟩
    · show V ≤ _
      linarith
    · linarith
    · linarith
  have hfin : volume ((fun t => t + h / 2) ⁻¹' (S ∩ Ioc T (3 * T))) ≠ ⊤ := by
    rw [measure_preimage_add_right]
    exact ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne
  have hstep : volume.real ({t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)) ≤
      (volume.restrict (Ioc T (3 * T))).real S := by
    refine (measureReal_mono hsub hfin).trans_eq ?_
    rw [measureReal_restrict_apply' measurableSet_Ioc, measureReal_def, measureReal_def,
      measure_preimage_add_right]
  -- the moment hypothesis `8N^m(1 + log N^m) ≤ 2T`
  have hNm : 8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ)) ≤ 3 * T - T := by
    have hM1 : (1 : ℝ) ≤ ((N ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hN1
    have hMle : ((N ^ m : ℕ) : ℝ) ≤ Real.exp (L / 4) := by
      rw [Nat.cast_pow]
      calc (N : ℝ) ^ m ≤ Real.exp (2 * ℓ) ^ m :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.exp_pos _).le) m
        _ = Real.exp (m * (2 * ℓ)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by nlinarith)
    have := eight_mul_one_add_log_le hM1 hT0 hMle hL6
    linarith
  have hmom := WeilConeMoments.measureReal_large_primePoly_le_factorial
    (a := gapPoly ℓ N) gapPoly_prime gapPoly_le 0 hm (by linarith : T ≤ 3 * T) hV hNm
  refine hstep.trans (hmom.trans ?_)
  -- arithmetic
  set W := ∑ n ∈ Finset.Icc 1 N, ‖gapPoly ℓ N n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun n _ => by positivity
  have hWl : W ≤ 18 * ℓ ^ 2 := sum_norm_gapPoly_sq_le hℓ1
  have hkey : W * (h * L) ^ 2 ≤ 10368 * D ^ 2 * V ^ 2 := by
    have e : 10368 * D ^ 2 * V ^ 2 = 18 * (ℓ * h) ^ 2 * L ^ 2 := by rw [hℓh, hVdef]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hWl (by positivity : (0 : ℝ) ≤ (h * L) ^ 2)
    nlinarith
  have hηpos : 0 < h * L := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_mul, pow_mul]
  calc 2 * (3 * T - T) * ((m.factorial : ℝ) * W ^ m) * ((h * L) ^ 2) ^ m
      = 4 * T * m.factorial * (W * (h * L) ^ 2) ^ m := by rw [mul_pow]; ring
    _ ≤ 4 * T * m.factorial * (10368 * D ^ 2 * V ^ 2) ^ m := by gcongr
    _ = 4 * m.factorial * (10368 * D ^ 2) ^ m * T * (V ^ 2) ^ m := by rw [mul_pow]; ring

/-- **Gaps of length `η/log T` with `η ≥ 192Dm` have measure `O_m(T/η^{2m})`.** -/
theorem measureReal_zeroGap_le_of_large (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) :
    ∃ T₀ : ℝ, ∀ T h : ℝ, T₀ ≤ T → 0 < h → h ≤ 2 * windowD →
      192 * windowD * m ≤ h * Real.log T →
      volume.real ({t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)) ≤
        4 * m.factorial * (10368 * windowD ^ 2) ^ m * T / (h * Real.log T) ^ (2 * m) := by
  obtain ⟨T₀, hT₀⟩ := measureReal_zeroGap_le_of_large_unif hRH
  exact ⟨T₀, hT₀ m hm⟩

/-- **Large gaps between zeros are rare (RH).**  For every `k` there are `C ≥ 0` and `T₀` with
`|{t ∈ [T, 2T] : N_ξ(t + h) = N_ξ(t)}| ≤ C T/(1 + h log T)^k` for all `T ≥ T₀`, `h > 0`. -/
theorem riemannHypothesis_measureReal_zeroGap_le (hRH : RiemannHypothesis) (k : ℕ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T ≥ T₀, ∀ h > 0,
      volume.real ({t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)) ≤
        C * T / (1 + h * Real.log T) ^ k := by
  obtain ⟨T₁, hT₁⟩ := measureReal_zeroGap_le_of_large hRH (m := k + 1) (by omega)
  obtain ⟨CL, hCL, hLw⟩ := riemannHypothesis_eventually_xiZeroCount_window_ge hRH
  obtain ⟨t₀, ht₀⟩ := hLw 1
  have hD := one_le_windowD
  set D := windowD with hDdef
  set η₀ : ℝ := 192 * D * ((k + 1 : ℕ) : ℝ) with hη₀
  set C₂ : ℝ := 4 * (k + 1).factorial * (10368 * D ^ 2) ^ (k + 1) with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hη₀1 : 1 ≤ η₀ := by
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
    rw [hη₀]; nlinarith
  refine ⟨C₂ * 2 ^ k + (1 + η₀) ^ k,
    max (max T₁ t₀) (max 1 (Real.exp (Real.exp (CL / (2 * D))))), by positivity,
    fun T hT h hh => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTt₀ : t₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTe : Real.exp (Real.exp (CL / (2 * D))) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  set η := h * Real.log T with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hpos : 0 < (1 + η) ^ k := by positivity
  set G := {t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)
  by_cases hbig : 2 * D < h
  · -- Littlewood: every window of length `h` above `T` contains a zero
    have hempty : G = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun t ht => ?_
      obtain ⟨hgap, htT, -⟩ := ht
      have ht0 : 0 < t := by linarith
      have hlogt : Real.exp (CL / (2 * D)) ≤ Real.log t :=
        (Real.le_log_iff_exp_le ht0).mpr (hTe.trans htT)
      have hlogt0 : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos _) hlogt
      have hll : CL / (2 * D) ≤ Real.log (Real.log t) :=
        (Real.le_log_iff_exp_le hlogt0).mpr hlogt
      have hll0 : 0 < Real.log (Real.log t) :=
        lt_of_lt_of_le (by positivity) hll
      have hw : CL / Real.log (Real.log t) ≤ 2 * D := by
        rw [div_le_iff₀ hll0]
        rw [div_le_iff₀ (by positivity)] at hll
        linarith
      have h1 := ht₀ t (hTt₀.trans htT)
      have h2 := xiZeroCount_mono (show t + CL / Real.log (Real.log t) ≤ t + h by linarith)
      rw [hgap] at h2
      push_cast at h1
      linarith
    rw [hempty, measureReal_empty]
    positivity
  push Not at hbig
  have hGT : volume.real G ≤ T := by
    refine (measureReal_mono inter_subset_right measure_Icc_lt_top.ne).trans ?_
    rw [Real.volume_real_Icc_of_le (by linarith)]
    linarith
  by_cases hsmall : η₀ ≤ η
  · have hmain := hT₁ T h hTT₁ hh hbig hsmall
    refine hmain.trans ?_
    have hη1 : 1 ≤ η := hη₀1.trans hsmall
    rw [div_le_div_iff₀ (by positivity) hpos]
    have h1 : (1 + η) ^ k ≤ 2 ^ k * η ^ (2 * (k + 1)) := by
      calc (1 + η) ^ k ≤ (2 * η) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        _ = 2 ^ k * η ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * η ^ (2 * (k + 1)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hη1 (by omega)) (by positivity)
    have hT0 : 0 ≤ T := by linarith
    calc C₂ * T * (1 + η) ^ k ≤ C₂ * T * (2 ^ k * η ^ (2 * (k + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C₂ * 2 ^ k * T * η ^ (2 * (k + 1)) := by ring
      _ ≤ (C₂ * 2 ^ k + (1 + η₀) ^ k) * T * η ^ (2 * (k + 1)) := by
          gcongr; linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + η₀) k]
  · push Not at hsmall
    refine hGT.trans ?_
    rw [le_div_iff₀ hpos]
    have h1 : (1 + η) ^ k ≤ (1 + η₀) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have h2 : 0 ≤ C₂ * 2 ^ k := by positivity
    have hT0 : 0 ≤ T := by linarith
    nlinarith

/-- **Large gaps between zeros are exponentially rare (RH).**  There are `c > 0`, `C`, `T₀` with
`|{t ∈ [T, 2T] : N_ξ(t + h) = N_ξ(t)}| ≤ C T e^{−c h log T}` for all `T ≥ T₀`, `h > 0`.  Take
`m = ⌊h log T/(192D)⌋` in `measureReal_zeroGap_le_of_large_unif`: `m!(10368D²)^m/η^{2m} ≤
(54D/η)^m ≤ 2^{−m}`. -/
theorem riemannHypothesis_measureReal_zeroGap_le_exp (hRH : RiemannHypothesis) :
    ∃ c C T₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ T ≥ T₀, ∀ h > 0,
      volume.real ({t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)) ≤
        C * T * Real.exp (-(c * (h * Real.log T))) := by
  obtain ⟨T₁, hT₁⟩ := measureReal_zeroGap_le_of_large_unif hRH
  obtain ⟨CL, hCL, hLw⟩ := riemannHypothesis_eventually_xiZeroCount_window_ge hRH
  obtain ⟨t₀, ht₀⟩ := hLw 1
  have hD := one_le_windowD
  set D := windowD with hDdef
  have hD0 : 0 < D := by linarith
  set c : ℝ := Real.log 2 / (192 * D) with hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := by positivity
  refine ⟨c, 8, max (max T₁ t₀) (max 1 (Real.exp (Real.exp (CL / (2 * D))))), hc0, by norm_num,
    fun T hT h hh => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTt₀ : t₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTe : Real.exp (Real.exp (CL / (2 * D))) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  set η := h * Real.log T with hηdef
  have hη0 : 0 ≤ η := by positivity
  set G := {t : ℝ | xiZeroCount (t + h) = xiZeroCount t} ∩ Icc T (2 * T)
  have hT0 : 0 ≤ T := by linarith
  by_cases hbig : 2 * D < h
  · have hempty : G = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun t ht => ?_
      obtain ⟨hgap, htT, -⟩ := ht
      have ht0 : 0 < t := by linarith
      have hlogt : Real.exp (CL / (2 * D)) ≤ Real.log t :=
        (Real.le_log_iff_exp_le ht0).mpr (hTe.trans htT)
      have hlogt0 : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos _) hlogt
      have hll : CL / (2 * D) ≤ Real.log (Real.log t) :=
        (Real.le_log_iff_exp_le hlogt0).mpr hlogt
      have hll0 : 0 < Real.log (Real.log t) :=
        lt_of_lt_of_le (by positivity) hll
      have hw : CL / Real.log (Real.log t) ≤ 2 * D := by
        rw [div_le_iff₀ hll0]
        rw [div_le_iff₀ (by positivity)] at hll
        linarith
      have h1 := ht₀ t (hTt₀.trans htT)
      have h2 := xiZeroCount_mono (show t + CL / Real.log (Real.log t) ≤ t + h by linarith)
      rw [hgap] at h2
      push_cast at h1
      linarith
    rw [hempty, measureReal_empty]
    positivity
  push Not at hbig
  have hGT : volume.real G ≤ T := by
    refine (measureReal_mono inter_subset_right measure_Icc_lt_top.ne).trans ?_
    rw [Real.volume_real_Icc_of_le (by linarith)]
    linarith
  by_cases hsmall : 192 * D ≤ η
  · set m : ℕ := ⌊η / (192 * D)⌋₊ with hm
    have hq1 : 1 ≤ η / (192 * D) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hq1)
    have hmle : (m : ℝ) ≤ η / (192 * D) := Nat.floor_le (by positivity)
    have hmge : η / (192 * D) - 1 ≤ m := by
      have := Nat.lt_floor_add_one (η / (192 * D)); linarith
    have hη192 : 192 * D * m ≤ η := by
      rw [le_div_iff₀ (by positivity)] at hmle; linarith
    have hηpos : 0 < η := by linarith
    have hmain := hT₁ m hm1 T h hTT₁ hh hbig hη192
    refine hmain.trans ?_
    -- `m!(10368D²)^m/η^{2m} ≤ (1/2)^m`
    have hfact : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
    have hratio : 10368 * D ^ 2 * m / η ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 10368 * D ^ 2 * m ≤ 10368 * D ^ 2 * (η / (192 * D)) :=
        mul_le_mul_of_nonneg_left hmle (by positivity)
      have e : 10368 * D ^ 2 * (η / (192 * D)) = 54 * D * η := by field_simp; ring
      nlinarith
    have hpow : (m.factorial : ℝ) * (10368 * D ^ 2) ^ m / η ^ (2 * m) ≤ (1 / 2) ^ m := by
      rw [div_le_iff₀ (by positivity)]
      calc (m.factorial : ℝ) * (10368 * D ^ 2) ^ m ≤ (m : ℝ) ^ m * (10368 * D ^ 2) ^ m :=
            mul_le_mul_of_nonneg_right hfact (by positivity)
        _ = (10368 * D ^ 2 * m / η ^ 2) ^ m * η ^ (2 * m) := by
            rw [div_pow, pow_mul]; field_simp; rw [mul_pow]; ring
        _ ≤ (1 / 2) ^ m * η ^ (2 * m) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio m) (by positivity)
    have hhalf : ((1 : ℝ) / 2) ^ m ≤ 2 * Real.exp (-(c * η)) := by
      rw [one_div, inv_pow, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
        ← Real.exp_neg, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : c * η = Real.log 2 * (η / (192 * D)) := by rw [hc]; field_simp
      rw [this]
      nlinarith
    have e : 4 * (m.factorial : ℝ) * (10368 * D ^ 2) ^ m * T / η ^ (2 * m) =
        4 * T * ((m.factorial : ℝ) * (10368 * D ^ 2) ^ m / η ^ (2 * m)) := by ring
    rw [e]
    calc 4 * T * ((m.factorial : ℝ) * (10368 * D ^ 2) ^ m / η ^ (2 * m))
        ≤ 4 * T * (2 * Real.exp (-(c * η))) :=
          mul_le_mul_of_nonneg_left (hpow.trans hhalf) (by positivity)
      _ = 8 * T * Real.exp (-(c * η)) := by ring
  · push Not at hsmall
    refine hGT.trans ?_
    have hcη : c * η ≤ Real.log 2 := by
      rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hexp : 1 / 2 ≤ Real.exp (-(c * η)) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), Real.log_div one_ne_zero two_ne_zero,
        Real.log_one, zero_sub]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith

end

end RHTower.Littlewood
