import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheConePinsTheLocalDensity
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowReadsTheResidue
import GaloisForLFunctions.RHTower.ScaleSigmaSum
import GaloisForLFunctions.RHTower.SecondMoment

/-!
# The window reads the residue from above: the archimedean place against the density

`TheWindowReadsTheResidue` reads the pole weight from below with doubly exponential precision: the twisted-arc
family is blind, `Ξ`-divisible and carries a positive pole. This module reads it from above, by a different
mechanism with a different rate.

* **Smoothed Mertens law on every datum cone** (`smoothedMertens_mem_of_mem_datumCone`). Integrating the local law of
  `TheConePinsTheLocalDensity` against `e^{−a} da` on `[0, A]` gives, for `λ` in the cone of `(β, s)`, `β ≥ 0`,
  `A + 1 ≤ c`,

    `|Σ_{n ≥ 2} (λ(n)/n) h(log n − 2A) − 2βA| ≤ 6β + 2D_s/J²`,

  where `h(t) = J⁻² ∫_t^1 e^{u/2} k(u) du` is a smoothed step (`farStep`): one below `−1/6`, zero above `1/6`.
  The pole weight is the logarithmic density of the weights.
* **The archimedean ceiling with smoothed coefficients** (`smoothed_toeplitz_le`). The narrow pole-free resonator
  `Σ_m c_m g_w'(· − log m + log(2N)/2)` with `c_m = m^{−1/2} h(log m − log N)` is a window test, and on a pole-free
  test the datum energy at conductor `≤ 1` does not see the pole weight. The Weil–Toeplitz bound gives
  `2 Σ_m m⁻¹ Σ_n (λ(n)/n) h(log n + log m − log N) ≤ (log 2N + C₀)(1 + log 2N)`. The left side is a superposition of
  smoothed Mertens sums, so the density law applies term by term; the archimedean coefficient of `log` is what caps
  the density at one.
* **The residue from above** (`exists_le_one_add_div_of_datumCone`). There are `K, c₀` with
  `β ≤ 1 + K/c` on every nonempty cone of `(β, 0)` at a window `c ≥ c₀`, whatever the weights. With the reading from
  below, `1 − K′ e^{3c − (π/6)e^{2(c−13/12)}} ≤ β ≤ 1 + K/c` (`residue_window`).

The two readings are different mechanisms. From below, the zeros (`Ξ`-divisible blind tests with even multiplier)
read the residue spectrally, at a doubly exponential rate. From above, the archimedean place reads it through its
logarithmic coefficient `½ log(1 + ξ²)` against the density of the weights, at the rate `1/c` of a Chebyshev
inequality. Whether a blind `Ξ`-divisible family with negative pole exists (an odd-multiplier twisted arc), which
would make the upper reading doubly exponential too, is open.

What this does not say about `ζ`: nothing about zeros. The cone of `(β, 0)` for `β > 1` is eventually empty for every
weight system; at `β = 1` nonemptiness at every window is RH.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.OddSector _root_.RHTower.EvenSector
open _root_.RHTower.ResonatorProfile _root_.Zeta23

/-! ### The smoothed step -/

/-- The support radius `r₀ = 2 r_out ≤ 1/6` of the far kernel. -/
def kerRad : ℝ := 2 * (nodeBump 2).rOut

theorem kerRad_pos : 0 < kerRad := by unfold kerRad; linarith [(nodeBump 2).rOut_pos]

theorem kerRad_le : kerRad ≤ 1 / 6 := by unfold kerRad; linarith [nodeBump_rOut_le 2]

theorem two_mul_kerRad_lt_log_two : 2 * kerRad < Real.log 2 := by
  have := kerRad_le; have := Real.log_two_gt_d9; linarith

theorem farKernel_eq_zero_of_le {t : ℝ} (ht : kerRad ≤ |t|) : farKernel t = 0 := farKernel_eq_zero ht

/-- The smoothed step `h(t) = J⁻² ∫_t^1 e^{u/2} k(u) du`. -/
def farStep (t : ℝ) : ℝ := (∫ u in t..1, Real.exp (u / 2) * farKernel u) / farJ ^ 2

theorem continuous_stepIntegrand : Continuous fun u : ℝ => Real.exp (u / 2) * farKernel u :=
  (by fun_prop : Continuous fun u : ℝ => Real.exp (u / 2)).mul continuous_farKernel

theorem stepIntegrand_eq_zero {u : ℝ} (hu : kerRad ≤ |u|) : Real.exp (u / 2) * farKernel u = 0 := by
  rw [farKernel_eq_zero_of_le hu, mul_zero]

theorem integrable_stepIntegrand : Integrable fun u : ℝ => Real.exp (u / 2) * farKernel u :=
  continuous_stepIntegrand.integrable_of_hasCompactSupport hasCompactSupport_farKernel.mul_left

theorem integral_stepIntegrand : ∫ u, Real.exp (u / 2) * farKernel u = farJ ^ 2 := by
  rw [← farLaplace_zero]
  unfold farLaplace
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_comm]; congr 2; ring

theorem farStep_eq_zero {t : ℝ} (ht : kerRad ≤ t) : farStep t = 0 := by
  unfold farStep
  have hk := kerRad_le
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_,
    intervalIntegral.integral_zero, zero_div]
  have : kerRad ≤ u := by
    rcases le_total t 1 with h | h
    · rw [uIcc_of_le h] at hu; linarith [hu.1]
    · rw [uIcc_of_ge h] at hu; linarith [hu.1]
  exact stepIntegrand_eq_zero (this.trans (le_abs_self u))

theorem integral_step_eq_full {t : ℝ} (ht : t ≤ -kerRad) :
    ∫ u in t..1, Real.exp (u / 2) * farKernel u = farJ ^ 2 := by
  have hk := kerRad_le
  have hk0 := kerRad_pos
  rw [intervalIntegral.integral_of_le (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero
    fun u hu => ?_, integral_stepIntegrand]
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
  refine stepIntegrand_eq_zero ?_
  rcases hu with hu | hu
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem farStep_eq_one {t : ℝ} (ht : t ≤ -kerRad) : farStep t = 1 := by
  unfold farStep
  rw [integral_step_eq_full ht, div_self farJ_sq_pos.ne']

theorem farStep_nonneg (t : ℝ) : 0 ≤ farStep t := by
  rcases le_or_gt t 1 with h | h
  · unfold farStep
    refine div_nonneg (intervalIntegral.integral_nonneg h fun u _ => ?_) (sq_nonneg _)
    exact mul_nonneg (Real.exp_pos _).le (farKernel_nonneg u)
  · rw [farStep_eq_zero (by linarith [kerRad_le])]

theorem farStep_le_one (t : ℝ) : farStep t ≤ 1 := by
  rcases le_or_gt t 1 with h | h
  · unfold farStep
    rw [div_le_one farJ_sq_pos, intervalIntegral.integral_of_le h, ← integral_stepIntegrand]
    exact setIntegral_le_integral integrable_stepIntegrand
      (Eventually.of_forall fun u => mul_nonneg (Real.exp_pos _).le (farKernel_nonneg u))
  · rw [farStep_eq_zero (by linarith [kerRad_le])]; norm_num

/-! ### The local sums integrate to a smoothed Mertens sum -/

theorem exp_neg_half_log {n : ℕ} (hn : 1 ≤ n) : Real.exp (-Real.log n / 2) = 1 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hn0, one_div]

/-- `∫_0^A e^{−a} k(log n − 2a) da = ½ n^{−1/2} J² h(log n − 2A)` for `n ≥ 2`. -/
theorem integral_exp_neg_mul_farKernel {n : ℕ} (hn : 2 ≤ n) (A : ℝ) :
    ∫ a in (0 : ℝ)..A, Real.exp (-a) * farKernel (Real.log n - 2 * a) =
      1 / 2 * (1 / Real.sqrt n) * farJ ^ 2 * farStep (Real.log n - 2 * A) := by
  set L := Real.log n with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hk := two_mul_kerRad_lt_log_two
  have hk0 := kerRad_pos
  set g : ℝ → ℝ := fun x => Real.exp ((x - L) / 2) * farKernel x with hg
  have hgc : Continuous g := (by fun_prop : Continuous fun x : ℝ => Real.exp ((x - L) / 2)).mul
    continuous_farKernel
  have e1 : (fun a => Real.exp (-a) * farKernel (L - 2 * a)) = fun a => g (L - 2 * a) := by
    funext a; simp only [hg]; congr 2; ring
  rw [e1, intervalIntegral.integral_comp_sub_mul g (by norm_num : (2 : ℝ) ≠ 0) L, mul_zero,
    sub_zero]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgc.intervalIntegrable (L - 2 * A) L) (hgc.intervalIntegrable L 1)
  have hzero : ∫ x in L..1, g x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_,
      intervalIntegral.integral_zero]
    have : kerRad ≤ u := by
      rcases le_total L 1 with h | h
      · rw [uIcc_of_le h] at hu; linarith [hu.1]
      · rw [uIcc_of_ge h] at hu; linarith [hu.1]
    simp only [hg]
    rw [farKernel_eq_zero_of_le (this.trans (le_abs_self u)), mul_zero]
  have hfac : ∫ x in (L - 2 * A)..1, g x =
      Real.exp (-L / 2) * ∫ x in (L - 2 * A)..1, Real.exp (x / 2) * farKernel x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hg]
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have hstep : ∫ x in (L - 2 * A)..1, Real.exp (x / 2) * farKernel x =
      farJ ^ 2 * farStep (L - 2 * A) := by
    unfold farStep; field_simp [farJ_sq_pos.ne']
  rw [hzero, add_zero] at hsplit
  rw [hsplit, hfac, hstep, exp_neg_half_log (by omega), smul_eq_mul]
  ring

/-- On `[0, A]` the far sum is a finite sum over `[2, M]` once `2e^{2A} ≤ M`. -/
theorem farSum_eq_finset_sum (lam : ℕ → ℝ) {a A : ℝ} (ha : a ≤ A) {M : ℕ}
    (hM : 2 * Real.exp (2 * A) ≤ M) :
    farSum lam a = ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) := by
  unfold farSum
  rw [tsum_eq_sum (s := Finset.Icc 2 M) fun n hn => ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_Icc.mp hn).1]
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · rw [if_neg (by omega), zero_mul]
    · have hk := two_mul_kerRad_lt_log_two
      have hk0 := kerRad_pos
      have hpos : (0 : ℝ) < 2 * Real.exp (2 * A) := by positivity
      have hnr : 2 * Real.exp (2 * A) < n := lt_of_le_of_lt hM (by exact_mod_cast hn)
      have hlog : Real.log 2 + 2 * A < Real.log n := by
        have := Real.log_lt_log hpos hnr
        rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
      rw [farKernel_eq_zero_of_le (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]

theorem integral_exp_neg_interval (A : ℝ) : ∫ a in (0 : ℝ)..A, Real.exp (-a) = 1 - Real.exp (-A) := by
  rw [intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp, neg_zero,
    Real.exp_zero]

/-- **The smoothed Mertens law on every datum cone.** For `λ` in the cone of `(β, s)`, `β ≥ 0`,
`0 ≤ A ≤ c − 1` and `2e^{2A} ≤ M`, the smoothed sum `Σ_{2 ≤ n ≤ M} (λ(n)/n) h(log n − 2A)` lies within
`6β + 2D_s/J²` of `2βA`. -/
theorem smoothedMertens_mem_of_mem_datumCone {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    (hβ : 0 ≤ β) {A : ℝ} (hA : 0 ≤ A) (hAc : A + 1 ≤ c) {M : ℕ} (hM : 2 * Real.exp (2 * A) ≤ M) :
    2 * β * A - (4 * β + 2 * localDensityConst s / farJ ^ 2) ≤
        ∑ n ∈ Finset.Icc 2 M, lam n / n * farStep (Real.log n - 2 * A) ∧
      ∑ n ∈ Finset.Icc 2 M, lam n / n * farStep (Real.log n - 2 * A) ≤
        2 * β * A + (6 * β + 2 * localDensityConst s / farJ ^ 2) := by
  set D := localDensityConst s with hD
  have hD0 : 0 ≤ D := localDensityConst_nonneg s
  have hJ := farJ_sq_pos
  set F : ℝ → ℝ := fun a =>
    ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) with hF
  have hFc : Continuous F := continuous_finset_sum _ fun n _ =>
    continuous_const.mul (continuous_farKernel.comp (continuous_const.sub (continuous_mul_left 2)))
  have hcont : Continuous fun a => Real.exp (-a) * F a := (by fun_prop : Continuous fun a : ℝ =>
    Real.exp (-a)).mul hFc
  -- the integral of the local sums
  have hkey : ∫ a in (0 : ℝ)..A, Real.exp (-a) * F a =
      farJ ^ 2 / 2 * ∑ n ∈ Finset.Icc 2 M, lam n / n * farStep (Real.log n - 2 * A) := by
    have e : (fun a => Real.exp (-a) * F a) = fun a => ∑ n ∈ Finset.Icc 2 M,
        lam n / Real.sqrt n * (Real.exp (-a) * farKernel (Real.log n - 2 * a)) := by
      funext a; simp only [hF, Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
    rw [e, intervalIntegral.integral_finsetSum fun n _ =>
      ((continuous_const.mul ((by fun_prop : Continuous fun a : ℝ => Real.exp (-a)).mul
        (continuous_farKernel.comp (continuous_const.sub (continuous_mul_left 2))))).intervalIntegrable
        0 A), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul_farKernel hn2 A]
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    field_simp
    rw [← hsq]; ring
  -- pointwise bounds on `[0, A]`
  have hpt : ∀ a ∈ Icc (0 : ℝ) A,
      β * farJ ^ 2 - (2 * β * farJ ^ 2 + D) * Real.exp (-a) ≤ Real.exp (-a) * F a ∧
        Real.exp (-a) * F a ≤ β * farJ ^ 2 + (3 * β * farJ ^ 2 + D) * Real.exp (-a) := by
    intro a ha
    have hFa : F a = farSum lam a := (farSum_eq_finset_sum lam ha.2 hM).symm
    obtain ⟨l, u⟩ := farSum_mem_Icc_of_mem_datumCone h ha.1 (by linarith [ha.2])
    rw [exp_half_sub_sq] at l
    rw [exp_half_add_sq] at u
    rw [hFa]
    have he : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    have he0 := Real.exp_pos (-a)
    have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ha.1])
    have hbJ : 0 ≤ β * farJ ^ 2 := mul_nonneg hβ hJ.le
    have hsq : 0 ≤ β * farJ ^ 2 * (Real.exp (-a) * Real.exp (-a)) := by positivity
    have hsq' : β * farJ ^ 2 * (Real.exp (-a) * Real.exp (-a)) ≤ β * farJ ^ 2 * Real.exp (-a) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hbJ
    constructor
    · have := mul_le_mul_of_nonneg_left l he0.le
      nlinarith
    · have := mul_le_mul_of_nonneg_left u he0.le
      nlinarith
  have hexp := integral_exp_neg_interval A
  have hEA0 := Real.exp_pos (-A)
  have hEA1 : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hci : ∀ K : ℝ, IntervalIntegrable (fun a => K * Real.exp (-a)) volume 0 A := fun K =>
    ((by fun_prop : Continuous fun a : ℝ => K * Real.exp (-a))).intervalIntegrable 0 A
  have hlow := intervalIntegral.integral_mono_on hA
    ((intervalIntegrable_const).sub (hci (2 * β * farJ ^ 2 + D))) (hcont.intervalIntegrable 0 A)
    fun a ha => (hpt a ha).1
  have hup := intervalIntegral.integral_mono_on hA (hcont.intervalIntegrable 0 A)
    ((intervalIntegrable_const).add (hci (3 * β * farJ ^ 2 + D))) fun a ha => (hpt a ha).2
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hci _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hexp, hkey] at hlow
  rw [intervalIntegral.integral_add intervalIntegrable_const (hci _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hexp, hkey] at hup
  simp only [sub_zero, smul_eq_mul] at hlow hup
  set Σ' := ∑ n ∈ Finset.Icc 2 M, lam n / n * farStep (Real.log n - 2 * A) with hΣ
  have hK1 : 0 ≤ 2 * β * farJ ^ 2 + D := by positivity
  have hK2 : 0 ≤ 3 * β * farJ ^ 2 + D := by positivity
  have h1 : (2 * β * farJ ^ 2 + D) * (1 - Real.exp (-A)) ≤ 2 * β * farJ ^ 2 + D :=
    mul_le_of_le_one_right hK1 (by linarith)
  have h2 : (3 * β * farJ ^ 2 + D) * (1 - Real.exp (-A)) ≤ 3 * β * farJ ^ 2 + D :=
    mul_le_of_le_one_right hK2 (by linarith)
  have e3 : 2 * D / farJ ^ 2 * farJ ^ 2 = 2 * D := by field_simp
  constructor
  · have : (2 * β * A - (4 * β + 2 * D / farJ ^ 2)) * (farJ ^ 2 / 2) ≤ Σ' * (farJ ^ 2 / 2) := by
      have e : (2 * β * A - (4 * β + 2 * D / farJ ^ 2)) * (farJ ^ 2 / 2) =
          A * (β * farJ ^ 2) - (2 * β * farJ ^ 2 + D) := by field_simp; ring
      rw [e]; nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  · have : Σ' * (farJ ^ 2 / 2) ≤ (2 * β * A + (6 * β + 2 * D / farJ ^ 2)) * (farJ ^ 2 / 2) := by
      have e : (2 * β * A + (6 * β + 2 * D / farJ ^ 2)) * (farJ ^ 2 / 2) =
          A * (β * farJ ^ 2) + (3 * β * farJ ^ 2 + D) := by field_simp; ring
      rw [e]; nlinarith
    exact le_of_mul_le_mul_right this (by positivity)

/-! ### The archimedean ceiling with smoothed coefficients -/

/-- The smoothed Toeplitz coefficients `c_m = m^{−1/2} h(log m − log N)`. -/
def stepCoeff (N m : ℕ) : ℂ := ((1 / Real.sqrt m * farStep (Real.log m - Real.log N) : ℝ) : ℂ)

theorem stepCoeff_eq_zero {N m : ℕ} (hN : 1 ≤ N) (hm : 2 * N < m) : stepCoeff N m = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log 2 + Real.log N < Real.log m := by
    rw [← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_lt_log (by positivity) (by exact_mod_cast hm)
  have hk := two_mul_kerRad_lt_log_two
  have hk0 := kerRad_pos
  unfold stepCoeff
  rw [farStep_eq_zero (by linarith), mul_zero, Complex.ofReal_zero]

theorem norm_stepCoeff_sq_le {N m : ℕ} (hm : 1 ≤ m) : ‖stepCoeff N m‖ ^ 2 ≤ 1 / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold stepCoeff
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, div_pow, one_pow,
    Real.sq_sqrt hm0.le]
  have h0 := farStep_nonneg (Real.log m - Real.log N)
  have h1 := farStep_le_one (Real.log m - Real.log N)
  have : farStep (Real.log m - Real.log N) ^ 2 ≤ 1 := by nlinarith
  calc 1 / (m : ℝ) * farStep (Real.log m - Real.log N) ^ 2 ≤ 1 / m * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 / m := mul_one _

/-- The Toeplitz products of the smoothed coefficients: for `n ≥ 2`,
`Re Σ_m c(nm) c̄(m) = n^{−1/2} Σ_m m⁻¹ h(log n + log m − log N)`. -/
theorem re_sum_stepCoeff {N n : ℕ} (hn : 2 ≤ n) (S : Finset ℕ) (hS : ∀ m ∈ S, 1 ≤ m) :
    (∑ m ∈ S, stepCoeff N (n * m) * conj (stepCoeff N m)).re =
      1 / Real.sqrt n * ∑ m ∈ S, 1 / (m : ℝ) * farStep (Real.log n + Real.log m - Real.log N) := by
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 := hS m hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold stepCoeff
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  push_cast
  rw [Real.log_mul hn0.ne' hm0.ne', Real.sqrt_mul hn0.le]
  -- the second factor is one wherever the first is nonzero
  have hk := two_mul_kerRad_lt_log_two
  have hk0 := kerRad_pos
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  rcases le_or_gt kerRad (Real.log n + Real.log m - Real.log N) with h | h
  · rw [farStep_eq_zero h]; ring
  · rw [farStep_eq_one (t := Real.log m - Real.log N) (by linarith)]
    field_simp
    rw [hsm]

/-- On the cone of `(β, s)` at conductor `s ≤ 0`, the narrow pole-free resonator at level `L` with any
coefficients is nonnegative for the finite-atom symbol. -/
theorem integral_weilAtomSymbol_resonator_nonneg {β s c : ℝ} (hs : s ≤ 0) {lam : ℕ → ℝ}
    (h : lam ∈ datumCone β s c) {L : ℕ} (hLc : Real.log L / 2 + 1 / ((L : ℝ) + 1) / 4 ≤ c)
    (cf : ℕ → ℂ) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (profileResonator L cf (gR' (1 / ((L : ℝ) + 1)))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log L / 2 + 1 / ((L : ℝ) + 1) / 4))⌋₊
        (τ / (2 * Real.pi)) := by
  set w : ℝ := 1 / ((L : ℝ) + 1) with hw_def
  have hw : 0 < w := by positivity
  set R := profileResonator L cf (gR' w) with hR
  obtain ⟨hp1, hp2⟩ := paperFT_profileResonator_gR'_pole L cf hw
  have ha : 0 ≤ Real.log L / 2 + w / 4 := by
    have := Real.log_natCast_nonneg L
    positivity
  have hd : ContDiff ℝ 2 R := contDiff_profileResonator L cf (contDiff_gR' w 2)
  have hsupp : tsupport R ⊆ Icc (-(Real.log L / 2 + w / 4)) (Real.log L / 2 + w / 4) :=
    tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (h := fun v => ((gR' w v : ℝ) : ℂ))
      (fun v hv => by
        show ((gR' w v : ℝ) : ℂ) = 0
        rw [gR'_eq_zero hw hv, Complex.ofReal_zero]) hu
  have hRc : HasCompactSupport R :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport R) hsupp
  refine integral_weilAtomSymbol_nonneg_of_polar ha hd hsupp hp1 hp2 ?_
  have hE := h R hd (hsupp.trans (Icc_subset_Icc (by linarith) hLc))
  rw [datumEnergy_eq] at hE
  have hP : (weilPoleTerm (EF.weilTest R R)).re = 0 := by
    rw [weilPoleTerm_weilTest_eq hd.continuous hRc, show (-I / 2 : ℂ) = -(I / 2) by ring, hp1, hp2]
    simp
  have hm : 0 ≤ ∫ u, ‖R u‖ ^ 2 := integral_nonneg fun _ => by positivity
  rw [hP, mul_zero, add_zero] at hE
  nlinarith

/-- **The archimedean ceiling with smoothed coefficients.** On the cone of `(β, s)`, `s ≤ 0`, for `N ≥ 1` with
`½ log 2N + 1 ≤ c`:
`2 Σ_{m ≤ 2N} m⁻¹ Σ_{2 ≤ n ≤ 2N} (λ(n)/n) h(log n + log m − log N) ≤ (log 2N + C₀)(1 + log 2N)`. -/
theorem smoothed_toeplitz_le {β s c : ℝ} (hs : s ≤ 0) {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    {N : ℕ} (hN : 1 ≤ N) (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) :
    2 * ∑ m ∈ Finset.Icc 1 (2 * N), 1 / (m : ℝ) * ∑ n ∈ Finset.Icc 2 (2 * N),
        lam n / n * farStep (Real.log n + Real.log m - Real.log N) ≤
      (Real.log (2 * N : ℕ) + (Real.log 2 + 9 / 2 + oddProfileRatio / 2)) *
        (1 + Real.log (2 * N : ℕ)) := by
  set L : ℕ := 2 * N with hLdef
  have hL : 1 ≤ L := by omega
  have hL1 : (0 : ℝ) < L + 1 := by positivity
  set w : ℝ := 1 / ((L : ℝ) + 1) with hw_def
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw_def, div_le_one hL1]; have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith
  have hw4 : w / 4 ≤ 1 := by linarith
  have hc : ∀ m, L < m → stepCoeff N m = 0 := fun m hm => stepCoeff_eq_zero hN hm
  have hq0 : 0 < ∫ u, gR' w u ^ 2 :=
    lt_of_lt_of_le (div_pos integral_d3_sq_pos (by positivity)) (integral_gR'_sq_ge hw)
  have hK : w ^ 2 * ∫ u, deriv (gR' w) u ^ 2 ≤ oddProfileRatio * ∫ u, gR' w u ^ 2 := by
    rw [deriv_gR']; exact sq_mul_integral_gR''_le hw hw1
  have hW := integral_weilAtomSymbol_resonator_nonneg hs h (L := L) (by linarith) (stepCoeff N)
  have hb := weil_multiplicativeToeplitz_bound_of_profile hL (stepCoeff N) hc (contDiff_gR' w 3)
    (fun u hu => gR'_eq_zero hw hu) hq0 hK hW
  -- the left side
  have hlhs : ∑ n ∈ Finset.Icc 2 L, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 L, stepCoeff N (n * m) * conj (stepCoeff N m)).re =
      ∑ m ∈ Finset.Icc 1 L, 1 / (m : ℝ) * ∑ n ∈ Finset.Icc 2 L,
        lam n / n * farStep (Real.log n + Real.log m - Real.log N) := by
    rw [Finset.sum_congr rfl fun n hn => by
      rw [re_sum_stepCoeff (Finset.mem_Icc.mp hn).1 _ fun m hm => (Finset.mem_Icc.mp hm).1]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    field_simp
    rw [← hsq]; ring
  -- the right side
  have hrhs : ∑ m ∈ Finset.Icc 1 L, ‖stepCoeff N m‖ ^ 2 ≤ 1 + Real.log L :=
    (Finset.sum_le_sum fun m hm => norm_stepCoeff_sq_le (Finset.mem_Icc.mp hm).1).trans
      (RHTower.sum_Icc_inv_le_one_add_log L)
  have hC₀ : 0 ≤ Real.log L + (Real.log 2 + 9 / 2 + oddProfileRatio / 2) := by
    have h1 : 0 ≤ oddProfileRatio := by
      unfold oddProfileRatio
      exact div_nonneg (by positivity) integral_d3_sq_pos.le
    have h2 := Real.log_natCast_nonneg L
    have h3 := Real.log_two_gt_d9
    linarith
  rw [hlhs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hrhs hC₀)

/-! ### Floor against ceiling -/

/-- The smoothed Mertens floor inside the Toeplitz sum: each `m ≤ N` contributes at least
`β(log N − log m) − B`, and each `m > N` contributes zero. -/
theorem sum_floor_le_toeplitz {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) (hβ : 0 ≤ β)
    {N : ℕ} (hN : 1 ≤ N) (hNc : Real.log N / 2 + 1 ≤ c) :
    ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) *
        (β * (Real.log N - Real.log m) - (4 * β + 2 * localDensityConst s / farJ ^ 2)) ≤
      ∑ m ∈ Finset.Icc 1 (2 * N), 1 / (m : ℝ) * ∑ n ∈ Finset.Icc 2 (2 * N),
        lam n / n * farStep (Real.log n + Real.log m - Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk := two_mul_kerRad_lt_log_two
  have hk0 := kerRad_pos
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 (2 * N) := Finset.Icc_subset_Icc le_rfl (by omega)
  rw [← Finset.sum_subset hsub fun m hm hmN => ?_]
  · refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlm : Real.log m ≤ Real.log N := Real.log_le_log hm0 (by exact_mod_cast hmN)
    have hlm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    set A := (Real.log N - Real.log m) / 2 with hA
    have hA0 : 0 ≤ A := by rw [hA]; linarith
    have hAc : A + 1 ≤ c := by rw [hA]; linarith
    have hM : 2 * Real.exp (2 * A) ≤ ((2 * N : ℕ) : ℝ) := by
      rw [show 2 * A = Real.log N - Real.log m by rw [hA]; ring, Real.exp_sub,
        Real.exp_log hN0, Real.exp_log hm0]
      push_cast
      have : (N : ℝ) / m ≤ N := div_le_self hN0.le (by exact_mod_cast hm1)
      linarith
    obtain ⟨hlow, -⟩ := smoothedMertens_mem_of_mem_datumCone h hβ hA0 hAc hM
    have e : ∀ n : ℕ, Real.log n + Real.log m - Real.log N = Real.log n - 2 * A := fun n => by
      rw [hA]; ring
    simp_rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e2 : β * (Real.log N - Real.log m) = 2 * β * A := by rw [hA]; ring
    rw [e2]
    exact hlow
  · obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hmN' : N < m := by
      by_contra hcon; exact hmN (Finset.mem_Icc.mpr ⟨hm1, by omega⟩)
    have hlm : Real.log N < Real.log m := Real.log_lt_log hN0 (by exact_mod_cast hmN')
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun n hn => ?_)
    have hlog2 : Real.log 2 ≤ Real.log n :=
      Real.log_le_log two_pos (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    rw [farStep_eq_zero (by linarith), mul_zero]

/-- The arithmetic of the harmonic sums: `Σ_{m ≤ N} (log N − log m)/m ≥ (log N)²/2 − 1`. -/
theorem sum_log_sub_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ^ 2 / 2 - 1 ≤ ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) * (Real.log N - Real.log m) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH := RHTower.harmonic_Icc_ge_log N
  have hlog := RHTower.sum_log_div_le N hN
  have hl0 := Real.log_natCast_nonneg N
  have hle : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hN0 (by linarith)
  have e : ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) * (Real.log N - Real.log m) =
      Real.log N * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m -
        ∑ m ∈ Finset.Icc 1 N, Real.log m / (m : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  have : Real.log N * Real.log N ≤ Real.log N * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m :=
    mul_le_mul_of_nonneg_left (hle.trans hH) hl0
  nlinarith

/-- **Floor against ceiling.** On the cone of `(β, s)`, `s ≤ 0`, `β ≥ 0`, for `N ≥ 1` with
`½ log 2N + 1 ≤ c`, writing `ℓ = log N`, `B = 4β + 2D_s/J²`, `C₀ = log 2 + 9/2 + K/2`:
`β(ℓ² − 2) − 2B(1 + ℓ) ≤ (ℓ + log 2 + C₀)(1 + log 2 + ℓ)`. -/
theorem floor_le_ceiling {β s c : ℝ} (hs : s ≤ 0) {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) :
    β * (Real.log N ^ 2 - 2) - 2 * (4 * β + 2 * localDensityConst s / farJ ^ 2) * (1 + Real.log N) ≤
      (Real.log N + Real.log 2 + (Real.log 2 + 9 / 2 + oddProfileRatio / 2)) *
        (1 + Real.log 2 + Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : Real.log (2 * N : ℕ) = Real.log 2 + Real.log N := by
    push_cast; exact Real.log_mul (by norm_num) hN0.ne'
  have hNc' : Real.log N / 2 + 1 ≤ c := by
    have := Real.log_two_gt_d9; rw [hl2] at hNc; linarith
  have hT := smoothed_toeplitz_le hs h hN hNc
  have hF := sum_floor_le_toeplitz h hβ hN hNc'
  set B := 4 * β + 2 * localDensityConst s / farJ ^ 2 with hB
  have hB0 : 0 ≤ B := by
    have := localDensityConst_nonneg s; have := farJ_sq_pos; positivity
  have hS := sum_log_sub_div_ge hN
  have hHu : ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := RHTower.sum_Icc_inv_le_one_add_log N
  have e : ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) * (β * (Real.log N - Real.log m) - B) =
      β * ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) * (Real.log N - Real.log m) -
        B * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [e] at hF
  rw [hl2] at hT
  have h1 : β * (Real.log N ^ 2 / 2 - 1) ≤
      β * ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) * (Real.log N - Real.log m) :=
    mul_le_mul_of_nonneg_left hS hβ
  have h2 : B * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m ≤ B * (1 + Real.log N) :=
    mul_le_mul_of_nonneg_left hHu hB0
  nlinarith

/-! ### The residue from above -/

/-- **The window reads the residue from above.** There are `K > 0` and `c₀` such that every nonempty cone of the
datum `(β, 0)` at a window `c ≥ c₀` has `β ≤ 1 + K/c`, whatever the weights. -/
theorem exists_le_one_add_div_of_datumCone :
    ∃ K c₀ : ℝ, 0 < K ∧ ∀ c β : ℝ, c₀ ≤ c → (datumCone β 0 c).Nonempty → β ≤ 1 + K / c := by
  set C₀ : ℝ := Real.log 2 + 9 / 2 + oddProfileRatio / 2 with hC₀
  set b : ℝ := 2 * localDensityConst 0 / farJ ^ 2 with hb
  have hb0 : 0 ≤ b := by have := localDensityConst_nonneg 0; have := farJ_sq_pos; positivity
  have hr0 : 0 ≤ oddProfileRatio := by
    unfold oddProfileRatio; exact div_nonneg (by positivity) integral_d3_sq_pos.le
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hC0 : 0 ≤ C₀ := by rw [hC₀]; linarith
  set P : ℝ := 2 * Real.log 2 + C₀ + 2 + 2 * b + 8 with hP
  set Q : ℝ := (Real.log 2 + C₀) * (1 + Real.log 2) + 2 * b + 10 with hQ
  have hP0 : 0 ≤ P := by rw [hP]; linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; nlinarith
  refine ⟨4 * (P + Q) + 4, 12 + 2 * (P + Q), by positivity, fun c β hc hne => ?_⟩
  obtain ⟨lam, hlam⟩ := hne
  rcases le_or_gt β 0 with hβ | hβ
  · have : 0 < (4 * (P + Q) + 4) / c := div_pos (by positivity) (by linarith)
    linarith
  -- the level `N = ⌈e^{2c−3}⌉`
  set N : ℕ := ⌈Real.exp (2 * c - 3)⌉₊ with hNdef
  have hE1 : 1 ≤ Real.exp (2 * c - 3) := Real.one_le_exp (by linarith)
  have hNge : Real.exp (2 * c - 3) ≤ N := Nat.le_ceil _
  have hNle : (N : ℝ) < Real.exp (2 * c - 3) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN : 1 ≤ N := by exact_mod_cast (hE1.trans hNge)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlo : 2 * c - 3 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]; exact hNge
  have hhi : Real.log N ≤ 2 * c - 2 - Real.log 2 := by
    rw [Real.log_le_iff_le_exp hN0]
    have hsplit : Real.exp (2 * c - 2 - Real.log 2) = Real.exp (2 * c - 3) * (Real.exp 1 / 2) := by
      rw [show 2 * c - 2 - Real.log 2 = (2 * c - 3) + (1 - Real.log 2) by ring, Real.exp_add,
        Real.exp_sub, Real.exp_log two_pos]
    rw [hsplit]
    have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    nlinarith
  have hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c := by
    have : Real.log (2 * N : ℕ) = Real.log 2 + Real.log N := by
      push_cast; exact Real.log_mul (by norm_num) hN0.ne'
    rw [this]; linarith
  have hmain := floor_le_ceiling le_rfl hlam hβ.le hN hNc
  rw [← hC₀, ← hb] at hmain
  set ℓ := Real.log N with hℓ
  have hℓ0 : 2 * (P + Q) + 21 ≤ ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  -- `β ℓ² ≤ ℓ² + (P + 8β) ℓ + Q + 10β`, hence `β ≤ 1 + 4(P + Q + 1)/ℓ`
  have hineq : β * (ℓ ^ 2 - 8 * ℓ - 10) ≤ ℓ ^ 2 + P * ℓ + Q := by
    rw [hP, hQ]; nlinarith
  have hden : ℓ ^ 2 / 2 ≤ ℓ ^ 2 - 8 * ℓ - 10 := by nlinarith
  have hβle : β ≤ 1 + 2 * (P + Q + 8) / ℓ := by
    have hpos : 0 < ℓ ^ 2 - 8 * ℓ - 10 := by nlinarith
    have h1 : β ≤ (ℓ ^ 2 + P * ℓ + Q) / (ℓ ^ 2 - 8 * ℓ - 10) := by
      rw [le_div_iff₀ hpos]; exact hineq
    have h2 : (ℓ ^ 2 + P * ℓ + Q) / (ℓ ^ 2 - 8 * ℓ - 10) ≤ 1 + 2 * (P + Q + 8) / ℓ := by
      rw [div_le_iff₀ hpos]
      have e : (1 + 2 * (P + Q + 8) / ℓ) * (ℓ ^ 2 - 8 * ℓ - 10) =
          ℓ ^ 2 - 8 * ℓ - 10 + 2 * (P + Q + 8) * (ℓ - 8 - 10 / ℓ) := by
        field_simp; ring
      rw [e]
      have h10 : 10 / ℓ ≤ 10 := by rw [div_le_iff₀ (by linarith)]; nlinarith
      nlinarith
    linarith
  have hℓc : c ≤ ℓ := by linarith
  have hfin : 2 * (P + Q + 8) / ℓ ≤ (4 * (P + Q) + 4) / c := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

/-- **The window reads the residue on both sides.** From a finite window on, every nonempty cone of `(β, 0)` has
`1 − K′ e^{3c − (π/6) e^{2(c−13/12)}} ≤ β ≤ 1 + K/c`. -/
theorem residue_window :
    ∃ K K' c₀ : ℝ, 0 < K ∧ 0 < K' ∧ ∀ c β : ℝ, c₀ ≤ c → (datumCone β 0 c).Nonempty →
      1 - K' * marginCeiling c ≤ β ∧ β ≤ 1 + K / c := by
  obtain ⟨K', c₁, hK', hlow⟩ := exists_one_sub_le_of_datumCone
  obtain ⟨K, c₂, hK, hup⟩ := exists_le_one_add_div_of_datumCone
  exact ⟨K, K', max c₁ c₂, hK, hK', fun c β hc hne =>
    ⟨hlow c β ((le_max_left _ _).trans hc) hne, hup c β ((le_max_right _ _).trans hc) hne⟩⟩

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
