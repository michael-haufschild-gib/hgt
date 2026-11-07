import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheConeHasNoLongGaps
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheConeHasPositiveSupportDensity

/-!
# The cone obeys the prime number theorem with a power saving

For a weight system `λ` write `ψ_λ(X) = Σ_{2 ≤ n ≤ X} λ(n)`.

* **Smoothed Chebyshev law at every resolution** (`smoothedChebyshev_le`). Integrating the
  short-interval law of `TheConeHasNoLongGaps` against `e^a da` on `[0, A]` gives, on the cone of `(β, s)`,
  `|Σ_n λ(n) H_j(log n − 2A) − βe^{2A}| ≤ |β| + (6|β| + 2D_{j,s}/J_j²) e^A`, where `H_j` is the smoothed step of
  resolution `r_j` built from `e^{−u/2} k_j(u)` (`jStep`).
* **Sharp against smooth** (`abs_chebyshev_sub_smooth_le`). The two differ only on `|log(n/X)| < 2r_j`, a primitive
  set; Cauchy–Schwarz and the second-moment law of `TheConeHasPositiveSupportDensity` bound the difference by
  `√((8r_jX + 1) e^{2r_j} X) · (log N + C_s)`.
* **Power saving** (`exists_abs_chebyshev_sub_le_of_mem_windowCone`). Balancing the resolution, `r ≍ X^{−1/3}`:
  every point of `𝒜(c)` has `|ψ_λ(X) − X| ≤ C X^{5/6} log X` for `X₀ ≤ X ≤ e^{2c−3}`.

So positivity of Weil's form on `[−c, c]` alone gives every weight system the prime number theorem with exponent
`5/6` across the whole box. The local law has square-root precision at each fixed resolution; the loss to `5/6`
is the price of the sharp cutoff, paid with the only absolute control the cone provides in short intervals, the
second moment. For `Λ` under RH the exponent is `½`.

What this does not say about `ζ`: `Λ` is a point of the cone only under RH; the law is uniform in `c` only through
the cone, which is empty off RH.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.OddSector _root_.RHTower.EvenSector
open _root_.RHTower.WeilMeanSquare _root_.Zeta23

/-! ### The Laplace value of the kernel -/

theorem continuous_jKernel (j : ℕ) : Continuous (jKernel j) := by
  have hc : Continuous fun u => (nodeBump j u : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_nodeBump j)
  have hcs : HasCompactSupport fun u => (nodeBump j u : ℂ) :=
    (nodeBump j).hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ 2 fun u => (nodeBump j u : ℂ) := contDiff_ofReal_comp (nodeBump j).contDiff
  have hw := (EF.weilTest_contDiff h2 hc hcs).continuous
  have e : jKernel j = fun u => (EF.weilTest (fun u => (nodeBump j u : ℂ))
      (fun u => (nodeBump j u : ℂ)) u).re := by
    funext u; rw [weilTest_ofReal_eq, Complex.ofReal_re]; rfl
  rw [e]
  exact Complex.continuous_re.comp hw

theorem hasCompactSupport_jKernel (j : ℕ) : HasCompactSupport (jKernel j) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * (nodeBump j).rOut)) fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    exact jKernel_eq_zero j hx.le

/-- `∫ k_j(u) e^{−u/2} du = J_j²`: the transform of an autocorrelation at `i/2`. -/
theorem integral_jKernel_mul_exp : ∀ j : ℕ, ∫ u, jKernel j u * Real.exp (-u / 2) = jJ j ^ 2 := by
  intro j
  have hc : Continuous fun u => (nodeBump j u : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_nodeBump j)
  have hcs : HasCompactSupport fun u => (nodeBump j u : ℂ) :=
    (nodeBump j).hasCompactSupport.comp_left Complex.ofReal_zero
  have hk : EF.weilTest (fun u => (nodeBump j u : ℂ)) (fun u => (nodeBump j u : ℂ)) =
      fun u => (jKernel j u : ℂ) := by
    funext u; rw [weilTest_ofReal_eq]; rfl
  have h1 := EF.paperFT_weilTest hc hc hcs hcs (Complex.I / 2)
  rw [hk, conj_I_div_two, paperFT_ofRealFun_I_div_two, paperFT_ofRealFun_I_div_two,
    paperFT_ofRealFun_neg_I_div_two, Complex.conj_ofReal] at h1
  have hJ' : ∫ u, nodeBump j u * Real.exp (u / 2) = jJ j := by
    unfold jJ
    rw [← integral_neg_eq_self (fun u => nodeBump j u * Real.exp (u / 2))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show nodeBump j (-u) * Real.exp (-u / 2) = nodeBump j u * Real.exp (-u / 2)
    rw [nodeBump_neg']
  rw [hJ'] at h1
  have h3 : ∫ u, jKernel j u * Real.exp (-u / 2) = jJ j * jJ j := by exact_mod_cast h1
  rw [h3, sq]

theorem jJ_pos (j : ℕ) : 0 < jJ j := lt_of_lt_of_le (by have := nodeScale_pos j; positivity) (jJ_ge j)

theorem jJ_sq_pos (j : ℕ) : 0 < jJ j ^ 2 := pow_pos (jJ_pos j) 2

/-! ### The smoothed step of resolution `r_j` -/

/-- `H_j(t) = J_j⁻² ∫_t^1 e^{−u/2} k_j(u) du`: one below `−2r_j`, zero above `2r_j`. -/
def jStep (j : ℕ) (t : ℝ) : ℝ := (∫ u in t..1, Real.exp (-u / 2) * jKernel j u) / jJ j ^ 2

theorem jStepIntegrand_eq_zero (j : ℕ) {u : ℝ} (hu : 2 * (nodeBump j).rOut ≤ |u|) :
    Real.exp (-u / 2) * jKernel j u = 0 := by rw [jKernel_eq_zero j hu, mul_zero]

theorem continuous_jStepIntegrand (j : ℕ) : Continuous fun u : ℝ => Real.exp (-u / 2) * jKernel j u :=
  (by fun_prop : Continuous fun u : ℝ => Real.exp (-u / 2)).mul (continuous_jKernel j)

theorem integrable_jStepIntegrand (j : ℕ) : Integrable fun u : ℝ => Real.exp (-u / 2) * jKernel j u :=
  (continuous_jStepIntegrand j).integrable_of_hasCompactSupport (hasCompactSupport_jKernel j).mul_left

theorem rOut_le_sixth (j : ℕ) : 2 * (nodeBump j).rOut ≤ 1 / 6 := by linarith [nodeBump_rOut_le j]

theorem jStep_eq_zero (j : ℕ) {t : ℝ} (ht : 2 * (nodeBump j).rOut ≤ t) : jStep j t = 0 := by
  unfold jStep
  have hk := rOut_le_sixth j
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_,
    intervalIntegral.integral_zero, zero_div]
  have : 2 * (nodeBump j).rOut ≤ u := by
    rcases le_total t 1 with h | h
    · rw [uIcc_of_le h] at hu; linarith [hu.1]
    · rw [uIcc_of_ge h] at hu; linarith [hu.1]
  exact jStepIntegrand_eq_zero j (this.trans (le_abs_self u))

theorem jStep_eq_one (j : ℕ) {t : ℝ} (ht : t ≤ -(2 * (nodeBump j).rOut)) : jStep j t = 1 := by
  unfold jStep
  have hk := rOut_le_sixth j
  have hk0 := (nodeBump j).rOut_pos
  have hfull : ∫ u in t..1, Real.exp (-u / 2) * jKernel j u = jJ j ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero
      fun u hu => ?_, ← integral_jKernel_mul_exp j]
    · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only; ring
    · rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
      refine jStepIntegrand_eq_zero j ?_
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  rw [hfull, div_self (jJ_sq_pos j).ne']

theorem jStep_nonneg (j : ℕ) (t : ℝ) : 0 ≤ jStep j t := by
  rcases le_or_gt t 1 with h | h
  · unfold jStep
    refine div_nonneg (intervalIntegral.integral_nonneg h fun u _ => ?_) (sq_nonneg _)
    exact mul_nonneg (Real.exp_pos _).le (jKernel_nonneg j u)
  · rw [jStep_eq_zero j (by linarith [rOut_le_sixth j])]

theorem jStep_le_one (j : ℕ) (t : ℝ) : jStep j t ≤ 1 := by
  rcases le_or_gt t 1 with h | h
  · unfold jStep
    rw [div_le_one (jJ_sq_pos j), intervalIntegral.integral_of_le h, ← integral_jKernel_mul_exp j]
    calc ∫ u in Ioc t 1, Real.exp (-u / 2) * jKernel j u
        ≤ ∫ u, Real.exp (-u / 2) * jKernel j u :=
          setIntegral_le_integral (integrable_jStepIntegrand j)
            (Eventually.of_forall fun u => mul_nonneg (Real.exp_pos _).le (jKernel_nonneg j u))
      _ = ∫ u, jKernel j u * Real.exp (-u / 2) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_); simp only; ring
  · rw [jStep_eq_zero j (by linarith [rOut_le_sixth j])]; norm_num

/-! ### The smoothed Chebyshev law -/

/-- `∫_0^A e^{a} k_j(log n − 2a) da = ½ √n J_j² H_j(log n − 2A)` for `n ≥ 2`. -/
theorem integral_exp_mul_jKernel (j : ℕ) {n : ℕ} (hn : 2 ≤ n) (A : ℝ) :
    ∫ a in (0 : ℝ)..A, Real.exp a * jKernel j (Real.log n - 2 * a) =
      1 / 2 * Real.sqrt n * jJ j ^ 2 * jStep j (Real.log n - 2 * A) := by
  set L := Real.log n with hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hk := rOut_lt j
  have hk6 := rOut_le_sixth j
  have hk0 := (nodeBump j).rOut_pos
  set g : ℝ → ℝ := fun x => Real.exp ((L - x) / 2) * jKernel j x with hg
  have hgc : Continuous g := (by fun_prop : Continuous fun x : ℝ => Real.exp ((L - x) / 2)).mul
    (continuous_jKernel j)
  have e1 : (fun a => Real.exp a * jKernel j (L - 2 * a)) = fun a => g (L - 2 * a) := by
    funext a; simp only [hg]; congr 2; ring
  rw [e1, intervalIntegral.integral_comp_sub_mul g (by norm_num : (2 : ℝ) ≠ 0) L, mul_zero,
    sub_zero]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgc.intervalIntegrable (μ := volume) (L - 2 * A) L) (hgc.intervalIntegrable (μ := volume) L 1)
  have hzero : ∫ x in L..1, g x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_,
      intervalIntegral.integral_zero]
    have : 2 * (nodeBump j).rOut ≤ u := by
      rcases le_total L 1 with h | h
      · rw [uIcc_of_le h] at hu; linarith [hu.1]
      · rw [uIcc_of_ge h] at hu; linarith [hu.1]
    simp only [hg]
    rw [jKernel_eq_zero j (this.trans (le_abs_self u)), mul_zero]
  have hfac : ∫ x in (L - 2 * A)..1, g x =
      Real.exp (L / 2) * ∫ x in (L - 2 * A)..1, Real.exp (-x / 2) * jKernel j x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hg]
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have hstep : ∫ x in (L - 2 * A)..1, Real.exp (-x / 2) * jKernel j x =
      jJ j ^ 2 * jStep j (L - 2 * A) := by
    unfold jStep
    rw [mul_div_assoc', mul_div_right_comm, div_self (jJ_sq_pos j).ne', one_mul]
  have hsq : Real.exp (L / 2) = Real.sqrt n := by rw [hL, Real.exp_half, Real.exp_log hn0]
  rw [hzero, add_zero] at hsplit
  rw [hsplit, hfac, hstep, hsq, smul_eq_mul]
  ring

/-- On `[0, A]` the local sum is a finite sum over `[2, M]` once `2e^{2A} ≤ M`. -/
theorem jSum_eq_finset_sum (j : ℕ) (lam : ℕ → ℝ) {a A : ℝ} (ha : a ≤ A) {M : ℕ}
    (hM : 2 * Real.exp (2 * A) ≤ M) :
    jSum j lam a = ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * jKernel j (Real.log n - 2 * a) := by
  unfold jSum
  rw [tsum_eq_sum (s := Finset.Icc 2 M) fun n hn => ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_Icc.mp hn).1]
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · rw [if_neg (by omega), zero_mul]
    · have hk := rOut_lt j
      have hk0 := (nodeBump j).rOut_pos
      have hpos : (0 : ℝ) < 2 * Real.exp (2 * A) := by positivity
      have hnr : 2 * Real.exp (2 * A) < n := lt_of_le_of_lt hM (by exact_mod_cast hn)
      have hlog : Real.log 2 + 2 * A < Real.log n := by
        have := Real.log_lt_log hpos hnr
        rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
      rw [jKernel_eq_zero j (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]

/-- **The smoothed Chebyshev law at resolution `r_j`.** On the cone of `(β, s)`, for `0 ≤ A ≤ c − 1` and
`2e^{2A} ≤ M`, `|Σ_{2 ≤ n ≤ M} λ(n) H_j(log n − 2A) − βe^{2A}| ≤ |β| + (6|β| + 2D_{j,s}/J_j²)e^A`. -/
theorem smoothedChebyshev_le {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) (j : ℕ)
    {A : ℝ} (hA : 0 ≤ A) (hAc : A + 1 ≤ c) {M : ℕ} (hM : 2 * Real.exp (2 * A) ≤ M) :
    |∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - 2 * A) - β * Real.exp (2 * A)| ≤
      |β| + (6 * |β| + 2 * jConst j s / jJ j ^ 2) * Real.exp A := by
  set D := jConst j s with hD
  have hD0 : 0 ≤ D := jConst_nonneg j s
  have hJ := jJ_sq_pos j
  set F : ℝ → ℝ := fun a =>
    ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * jKernel j (Real.log n - 2 * a) with hF
  have hlk : ∀ n : ℕ, Continuous fun a : ℝ => jKernel j (Real.log n - 2 * a) := fun n =>
    (continuous_jKernel j).comp (continuous_const.sub (continuous_const_mul 2))
  have hFc : Continuous F := continuous_finsetSum _ fun n _ => continuous_const.mul (hlk n)
  have hcont : Continuous fun a => Real.exp a * F a := Real.continuous_exp.mul hFc
  have hkey : ∫ a in (0 : ℝ)..A, Real.exp a * F a =
      jJ j ^ 2 / 2 * ∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - 2 * A) := by
    have e : (fun a => Real.exp a * F a) = fun a => ∑ n ∈ Finset.Icc 2 M,
        lam n / Real.sqrt n * (Real.exp a * jKernel j (Real.log n - 2 * a)) := by
      funext a; simp only [hF, Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
    have hint : ∀ n ∈ Finset.Icc 2 M, IntervalIntegrable
        (fun a => lam n / Real.sqrt n * (Real.exp a * jKernel j (Real.log n - 2 * a))) volume 0 A :=
      fun n _ => (continuous_const.mul (Real.continuous_exp.mul (hlk n))).intervalIntegrable 0 A
    rw [e, intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_jKernel j hn2 A]
    field_simp
  -- pointwise bounds
  set E := 3 * |β| * jJ j ^ 2 + D with hE
  have hpt : ∀ a ∈ Icc (0 : ℝ) A,
      β * jJ j ^ 2 * Real.exp (2 * a) - E * Real.exp a ≤ Real.exp a * F a ∧
        Real.exp a * F a ≤ β * jJ j ^ 2 * Real.exp (2 * a) + E * Real.exp a := by
    intro a ha
    have hFa : F a = jSum j lam a := (jSum_eq_finset_sum j lam ha.2 hM).symm
    have hl := abs_jSum_sub_le_of_mem_datumCone h j ha.1 (by linarith [ha.2])
    rw [← hFa] at hl
    have he := Real.exp_pos a
    have e2 : Real.exp (2 * a) = Real.exp a * Real.exp a := by rw [← Real.exp_add]; ring_nf
    obtain ⟨l, u⟩ := abs_le.mp hl
    rw [e2]
    constructor
    · have := mul_le_mul_of_nonneg_left l he.le
      nlinarith
    · have := mul_le_mul_of_nonneg_left u he.le
      nlinarith
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hci : ∀ K κ : ℝ, IntervalIntegrable (fun a => K * Real.exp (κ * a)) volume 0 A := fun K κ =>
    ((by fun_prop : Continuous fun a : ℝ => K * Real.exp (κ * a))).intervalIntegrable 0 A
  have i1 : ∫ a in (0 : ℝ)..A, Real.exp a = Real.exp A - 1 := by
    rw [integral_exp, Real.exp_zero]
  have i2 : ∫ a in (0 : ℝ)..A, Real.exp (2 * a) = (Real.exp (2 * A) - 1) / 2 := by
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := A) (fun x => Real.exp x)
      (by norm_num : (2 : ℝ) ≠ 0)
    rw [this, integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]; ring
  have hlow := intervalIntegral.integral_mono_on hA
    (((hci (β * jJ j ^ 2) 2)).sub (hci E 1)) (hcont.intervalIntegrable 0 A) fun a ha => by
      simpa using (hpt a ha).1
  have hup := intervalIntegral.integral_mono_on hA (hcont.intervalIntegrable 0 A)
    ((hci (β * jJ j ^ 2) 2).add (hci E 1)) fun a ha => by simpa using (hpt a ha).2
  rw [intervalIntegral.integral_sub (hci _ _) (hci _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hkey] at hlow
  rw [intervalIntegral.integral_add (hci _ _) (hci _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hkey] at hup
  simp only [one_mul] at hlow hup
  rw [i1, i2] at hlow hup
  set T := ∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - 2 * A) with hT
  have hJne : jJ j ≠ 0 := (jJ_pos j).ne'
  have hEA : 1 ≤ Real.exp A := Real.one_le_exp hA
  -- divide by `J²/2`
  have hT1 : β * (Real.exp (2 * A) - 1) - 2 * E / jJ j ^ 2 * (Real.exp A - 1) ≤ T := by
    have : (β * (Real.exp (2 * A) - 1) - 2 * E / jJ j ^ 2 * (Real.exp A - 1)) * (jJ j ^ 2 / 2) ≤
        T * (jJ j ^ 2 / 2) := by
      have e : (β * (Real.exp (2 * A) - 1) - 2 * E / jJ j ^ 2 * (Real.exp A - 1)) * (jJ j ^ 2 / 2) =
          β * jJ j ^ 2 * ((Real.exp (2 * A) - 1) / 2) - E * (Real.exp A - 1) := by
        field_simp
      rw [e]; linarith
    exact le_of_mul_le_mul_right this (by positivity)
  have hT2 : T ≤ β * (Real.exp (2 * A) - 1) + 2 * E / jJ j ^ 2 * (Real.exp A - 1) := by
    have : T * (jJ j ^ 2 / 2) ≤
        (β * (Real.exp (2 * A) - 1) + 2 * E / jJ j ^ 2 * (Real.exp A - 1)) * (jJ j ^ 2 / 2) := by
      have e : (β * (Real.exp (2 * A) - 1) + 2 * E / jJ j ^ 2 * (Real.exp A - 1)) * (jJ j ^ 2 / 2) =
          β * jJ j ^ 2 * ((Real.exp (2 * A) - 1) / 2) + E * (Real.exp A - 1) := by
        field_simp
      rw [e]; linarith
    exact le_of_mul_le_mul_right this (by positivity)
  have hEJ : 2 * E / jJ j ^ 2 = 6 * |β| + 2 * D / jJ j ^ 2 := by
    rw [hE]; field_simp; ring
  rw [hEJ] at hT1 hT2
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 6 * |β| + 2 * D / jJ j ^ 2 := ⟨_, rfl⟩
  rw [← hK] at hT1 hT2 ⊢
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hb1 := le_abs_self β
  have hb2 := neg_abs_le β
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Sharp against smooth -/

/-- The Chebyshev function of a weight system, `ψ_λ(X) = Σ_{2 ≤ n ≤ X} λ(n)`. -/
def chebyshevOf (lam : ℕ → ℝ) (X : ℝ) : ℝ := ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, lam n

/-- The boundary layer `|log n − log X| < 2r_j` inside `[2, M]`. -/
def jLayer (j : ℕ) (X : ℝ) (M : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n => |Real.log n - Real.log X| < 2 * (nodeBump j).rOut

theorem isPrimitiveSet_jLayer (j : ℕ) (X : ℝ) (M : ℕ) : IsPrimitiveSet (jLayer j X M) := by
  intro m hm m' hm' k hk heq
  rw [jLayer, Finset.mem_filter, Finset.mem_Icc] at hm hm'
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast (show 0 < m' by omega)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (2 : ℝ) * m' ≤ m := by rw [heq]; push_cast; nlinarith
  have hlog : Real.log 2 + Real.log m' ≤ Real.log m := by
    rw [← Real.log_mul (by norm_num) hm0.ne']
    exact Real.log_le_log (by positivity) hk2
  have h1 := abs_lt.mp hm.2
  have h2 := abs_lt.mp hm'.2
  have hk := nodeBump_rOut_le j
  have hl2 := Real.log_two_gt_d9
  linarith [h1.2, h2.1]

/-- The boundary layer has at most `X(e^{2r} − e^{−2r}) + 1` elements. -/
theorem card_jLayer_le (j : ℕ) {X : ℝ} (hX : 0 < X) (M : ℕ) :
    ((jLayer j X M).card : ℝ) ≤ X * (Real.exp (2 * (nodeBump j).rOut) -
      Real.exp (-(2 * (nodeBump j).rOut))) + 1 := by
  set r := 2 * (nodeBump j).rOut with hr
  set lo := X * Real.exp (-r) with hlo
  set hi := X * Real.exp r with hhi
  have hlo0 : 0 < lo := by positivity
  have hsub : jLayer j X M ⊆ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
    intro n hn
    rw [jLayer, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn2, -⟩, hlog⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    obtain ⟨h1, h2⟩ := abs_lt.mp hlog
    rw [Finset.mem_Icc]
    constructor
    · refine Nat.ceil_le.mpr ?_
      rw [hlo, ← Real.exp_log hX, ← Real.exp_add, ← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by linarith)
    · refine Nat.le_floor ?_
      rw [hhi, ← Real.exp_log hX, ← Real.exp_add, ← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by linarith)
  calc ((jLayer j X M).card : ℝ) ≤ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ hi - lo + 1 := by
        rw [Nat.card_Icc]
        rcases le_or_gt ⌈lo⌉₊ (⌊hi⌋₊ + 1) with hle | hgt
        · rw [Nat.cast_sub hle]; push_cast
          have h1 : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le (by positivity)
          have h2 : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
          linarith
        · rw [Nat.sub_eq_zero_of_le hgt.le]; push_cast
          have : lo ≤ hi := by
            rw [hlo, hhi]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [(nodeBump j).rOut_pos]))
              hX.le
          linarith
    _ = _ := by rw [hhi, hlo]; ring

/-- **Sharp against smooth.** The Chebyshev function and the smoothed sum differ by at most the absolute mass of
the boundary layer. -/
theorem abs_chebyshev_sub_smooth_le (j : ℕ) (lam : ℕ → ℝ) {X : ℝ} (hX : 1 ≤ X) {M : ℕ}
    (hM : X ≤ M) :
    |chebyshevOf lam X - ∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - Real.log X)| ≤
      ∑ n ∈ jLayer j X M, |lam n| := by
  have hX0 : 0 < X := by linarith
  have hfl : ⌊X⌋₊ ≤ M := Nat.floor_le_of_le hM
  have hsplit : chebyshevOf lam X =
      ∑ n ∈ Finset.Icc 2 M, lam n * (if (n : ℝ) ≤ X then 1 else 0) := by
    unfold chebyshevOf
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hfl) fun n hn hnX => ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have : (n : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (Finset.mem_Icc.mp hn).2
      rw [if_pos this, mul_one]
    · have : ¬ (n : ℝ) ≤ X := fun h => hnX (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
        Nat.le_floor h⟩)
      rw [if_neg this, mul_zero]
  rw [hsplit, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [jLayer, Finset.sum_filter]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
  rw [← mul_sub, abs_mul]
  have h0 := jStep_nonneg j (Real.log n - Real.log X)
  have h1 := jStep_le_one j (Real.log n - Real.log X)
  by_cases hin : |Real.log n - Real.log X| < 2 * (nodeBump j).rOut
  · rw [if_pos hin]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [if_neg hin]
    rw [not_lt] at hin
    by_cases hle : (n : ℝ) ≤ X
    · have hlog : Real.log n ≤ Real.log X := Real.log_le_log hn0 hle
      rw [abs_of_nonpos (by linarith)] at hin
      rw [if_pos hle, jStep_eq_one j (by linarith)]
      simp
    · have hlog : Real.log X < Real.log n := Real.log_lt_log hX0 (by push Not at hle; exact hle)
      rw [abs_of_pos (by linarith)] at hin
      rw [if_neg hle, jStep_eq_zero j (by linarith)]
      simp

/-! ### The power saving -/

theorem exp_sub_exp_neg_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 6) : Real.exp t - Real.exp (-t) ≤ 4 * t := by
  have h1 : Real.exp (2 * t) - 1 ≤ 2 * t * Real.exp (2 * t) := by
    have := Real.add_one_le_exp (-(2 * t))
    have h2 : Real.exp (2 * t) * Real.exp (-(2 * t)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (2 * t)]
  have h3 : Real.exp (2 * t) ≤ 2 := by
    have : Real.exp (2 * t) ≤ Real.exp (1 / 3) := Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (1 / 3) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have h5 : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      by_contra hcon
      push Not at hcon
      have h6 : (2 : ℝ) ^ 3 < Real.exp (1 / 3) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      norm_num at h6
      linarith
    linarith
  have e : Real.exp t - Real.exp (-t) = Real.exp (-t) * (Real.exp (2 * t) - 1) := by
    rw [mul_sub, ← Real.exp_add, mul_one]; ring_nf
  have h6 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h7 : 0 ≤ Real.exp (2 * t) - 1 := by linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * t)]
  rw [e]
  calc Real.exp (-t) * (Real.exp (2 * t) - 1) ≤ 1 * (Real.exp (2 * t) - 1) :=
        mul_le_mul_of_nonneg_right h6 h7
    _ ≤ 2 * t * 2 := by nlinarith
    _ = 4 * t := by ring

/-- The layer count at resolution `x ≥ u²/2` for `X = u⁶`: at most `9u⁴` integers. -/
theorem card_jLayer_le_nine (j : ℕ) {X u : ℝ} (hX0 : 0 < X) (hu1 : 1 ≤ u) (hu6 : u ^ 6 = X)
    (hxge : u ^ 2 / 2 ≤ nodeScale j) (M : ℕ) : ((jLayer j X M).card : ℝ) ≤ 9 * u ^ 4 := by
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < nodeScale j := nodeScale_pos j
  have hx3 : (3 : ℝ) ≤ nodeScale j := by unfold nodeScale; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hr : 2 * (nodeBump j).rOut = 1 / (2 * nodeScale j) := by
    rw [nodeBump_rOut]
    show 2 * (1 / (4 * nodeScale j)) = 1 / (2 * nodeScale j)
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcard := card_jLayer_le j hX0 M
  rw [hr] at hcard
  have hr6 : 1 / (2 * nodeScale j) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1 := exp_sub_exp_neg_le (t := 1 / (2 * nodeScale j)) (by positivity) hr6
  have h4 : 4 * (1 / (2 * nodeScale j)) ≤ 4 / u ^ 2 := by
    rw [show 4 * (1 / (2 * nodeScale j)) = 2 / nodeScale j by ring,
      div_le_div_iff₀ hx0 (by positivity)]
    linarith
  have h2 : X * (4 * (1 / (2 * nodeScale j))) ≤ 4 * u ^ 4 := by
    calc X * (4 * (1 / (2 * nodeScale j))) ≤ u ^ 6 * (4 / u ^ 2) := by
          rw [← hu6]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4 * u ^ 4 := by field_simp
  have h3 : 1 ≤ u ^ 4 := one_le_pow₀ hu1
  have h5 := mul_le_mul_of_nonneg_left h1 hX0.le
  linarith

/-- Cauchy–Schwarz on the layer: `#P ≤ 9u⁴`, `Σ_P λ²/n ≤ B²`, `P ⊆ [2, 2u⁶]` give `Σ_P |λ| ≤ 5u⁵B`. -/
theorem sum_abs_layer_le {P : Finset ℕ} {lam : ℕ → ℝ} {u B : ℝ} (hu0 : 0 < u) (hB : 0 ≤ B)
    (hcard : (P.card : ℝ) ≤ 9 * u ^ 4) (hsq : ∑ n ∈ P, lam n ^ 2 / n ≤ B ^ 2)
    (hP : ∀ n ∈ P, 1 ≤ n ∧ (n : ℝ) ≤ 2 * u ^ 6) :
    ∑ n ∈ P, |lam n| ≤ 5 * u ^ 5 * B := by
  have hsq2 : ∑ n ∈ P, lam n ^ 2 ≤ 2 * u ^ 6 * ∑ n ∈ P, lam n ^ 2 / n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := hP n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [mul_div_assoc', le_div_iff₀ hn0]
    have := mul_le_mul_of_nonneg_left hn2 (sq_nonneg (lam n))
    linarith
  have hCS : (∑ n ∈ P, |lam n|) ^ 2 ≤ (P.card : ℝ) * ∑ n ∈ P, lam n ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℝ)) (fun n => |lam n|)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at this
    exact this
  have h1 : (∑ n ∈ P, |lam n|) ^ 2 ≤ (5 * u ^ 5 * B) ^ 2 := by
    calc (∑ n ∈ P, |lam n|) ^ 2 ≤ (P.card : ℝ) * ∑ n ∈ P, lam n ^ 2 := hCS
      _ ≤ (9 * u ^ 4) * (2 * u ^ 6 * B ^ 2) :=
          mul_le_mul hcard (hsq2.trans (mul_le_mul_of_nonneg_left hsq (by positivity)))
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = 18 * u ^ 10 * B ^ 2 := by ring
      _ ≤ (5 * u ^ 5 * B) ^ 2 := by nlinarith [pow_pos hu0 10, sq_nonneg B]
  exact (abs_le_of_sq_le_sq' h1 (by positivity)).2

/-- The archimedean constant at resolution `x = nodeScale j ≤ u² ≤ X`, `log X ≥ 1`:
`2D_{j,0}/J_j² ≤ (512/π) G u² log X`. -/
theorem two_jConst_div_le (j : ℕ) {X u G : ℝ} (hlogX : 1 ≤ Real.log X) (hxle : nodeScale j ≤ u ^ 2)
    (hu26 : u ^ 2 ≤ X)
    (hG : G = |gammaLogConst| * |bumpMassConst| + |bumpMassConst| + |bumpLogConst|) :
    2 * jConst j 0 / jJ j ^ 2 ≤ 512 / Real.pi * G * u ^ 2 * Real.log X := by
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = nodeScale j := ⟨_, rfl⟩
  have hJ := jJ_ge j
  rw [← hxdef] at hJ
  have hx0' : 0 < x := hxdef ▸ nodeScale_pos j
  have hxle' : x ≤ u ^ 2 := hxdef ▸ hxle
  have hx1' : 1 ≤ x := hxdef ▸ one_le_nodeScale j
  have hJ2 : 1 / (64 * x ^ 2) ≤ jJ j ^ 2 := by
    have h0 : 0 ≤ 1 / (8 * x) := by positivity
    calc 1 / (64 * x ^ 2) = (1 / (8 * x)) ^ 2 := by field_simp; ring
      _ ≤ _ := pow_le_pow_left₀ h0 hJ 2
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = (gammaLogConst + Real.log x) * bumpMassConst + bumpLogConst :=
    ⟨_, rfl⟩
  have hY : Y ≤ G * Real.log X := by
    have hlogx : Real.log x ≤ Real.log X := Real.log_le_log hx0' (hxle'.trans hu26)
    have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1'
    have hb0 := abs_nonneg bumpMassConst
    have e1 : (gammaLogConst + Real.log x) * bumpMassConst ≤
        |gammaLogConst| * |bumpMassConst| + Real.log X * |bumpMassConst| := by
      calc _ ≤ |(gammaLogConst + Real.log x) * bumpMassConst| := le_abs_self _
        _ = |gammaLogConst + Real.log x| * |bumpMassConst| := abs_mul _ _
        _ ≤ (|gammaLogConst| + Real.log X) * |bumpMassConst| := by
            refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) hb0
            rw [abs_of_nonneg hlogx0]; linarith
        _ = _ := by ring
    have e2 : bumpLogConst ≤ |bumpLogConst| := le_abs_self _
    have e3 : |gammaLogConst| * |bumpMassConst| + |bumpLogConst| ≤
        (|gammaLogConst| * |bumpMassConst| + |bumpLogConst|) * Real.log X :=
      le_mul_of_one_le_right (by positivity) hlogX
    rw [hYdef, hG]; nlinarith
  have hDval : jConst j 0 = 1 / (4 * Real.pi) * (16 / x * Y) := by
    rw [hYdef, hxdef]; simp only [jConst, jArchMass, abs_zero, mul_zero, zero_mul, add_zero]
  have hpi := Real.pi_pos
  have hval : 2 * jConst j 0 = 8 / (Real.pi * x) * Y := by rw [hDval]; field_simp; ring
  rw [hval, div_le_iff₀ (jJ_sq_pos j)]
  calc 8 / (Real.pi * x) * Y ≤ 8 / (Real.pi * x) * (G * Real.log X) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = 512 / Real.pi * G * x * Real.log X * (1 / (64 * x ^ 2)) := by field_simp; ring
    _ ≤ 512 / Real.pi * G * u ^ 2 * Real.log X * jJ j ^ 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxle'
          (by positivity)) (by linarith)) hJ2 (by positivity) (by positivity)

/-- The arithmetic of the power saving. -/
theorem power_saving_arith {u L B C₀ g : ℝ} (hu1 : 1 ≤ u) (hL : 1 ≤ L) (hC : 0 ≤ C₀)
    (hB : B ≤ 2 * L + C₀) :
    1 + (6 + g * u ^ 2 * L) * u ^ 3 + 5 * u ^ 5 * B ≤ (17 + g + 5 * C₀) * u ^ 5 * L := by
  have hu35 : u ^ 3 ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have hu05 : 1 ≤ u ^ 5 := one_le_pow₀ hu1
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u ^ 5 * L := ⟨_, rfl⟩
  have hv1 : 1 ≤ v := by rw [hv]; nlinarith
  have h2 : u ^ 3 ≤ v := by rw [hv]; nlinarith
  have h3 : 5 * u ^ 5 * B ≤ 5 * u ^ 5 * (2 * L + C₀) := mul_le_mul_of_nonneg_left hB (by positivity)
  have h4 : u ^ 5 * C₀ ≤ C₀ * v := by
    have h := mul_le_mul_of_nonneg_left hL (mul_nonneg (by positivity : (0 : ℝ) ≤ u ^ 5) hC)
    rw [hv]; linarith
  have e1 : (6 + g * u ^ 2 * L) * u ^ 3 = 6 * u ^ 3 + g * v := by rw [hv]; ring
  have e2 : 5 * u ^ 5 * (2 * L + C₀) = 10 * v + 5 * (u ^ 5 * C₀) := by rw [hv]; ring
  have e3 : (17 + g + 5 * C₀) * u ^ 5 * L = 17 * v + g * v + 5 * (C₀ * v) := by rw [hv]; ring
  rw [e1, e3]
  linarith only [hv1, h2, h3, h4, e2]

/-- **The prime number theorem on the cone, with exponent `5/6`.** There are `C, X₀` such that every point of
`𝒜(c)` has `|ψ_λ(X) − X| ≤ C X^{5/6} log X` for `X₀ ≤ X ≤ e^{2c−3}`. -/
theorem exists_abs_chebyshev_sub_le_of_mem_windowCone :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ c : ℝ, ∀ lam ∈ windowCone c, ∀ X : ℝ, X₀ ≤ X →
      X ≤ Real.exp (2 * c - 3) →
        |chebyshevOf lam X - X| ≤ C * X ^ ((5 : ℝ) / 6) * Real.log X := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = |gammaLogConst| * |bumpMassConst| + |bumpMassConst| + |bumpLogConst| :=
    ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = coneToeplitzConst 0 := ⟨_, rfl⟩
  have hC0 : 0 < C₀ := hC₀ ▸ coneToeplitzConst_pos 0
  refine ⟨17 + 512 / Real.pi * G + 5 * C₀, 125, by positivity, fun c lam hlam X hX hXc => ?_⟩
  have hlam' := mem_datumCone_one_zero_of_mem_windowCone hlam
  have hX0 : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9; linarith
  -- `u = X^{1/6}`
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = X ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu6 : u ^ 6 = X := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hu5 : X ^ ((5 : ℝ) / 6) = u ^ 5 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hu3 : Real.sqrt X = u ^ 3 := by
    rw [Real.sqrt_eq_rpow, hu, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hu1 : 1 ≤ u := by
    by_contra hcon; push Not at hcon
    have : u ^ 6 < 1 := pow_lt_one₀ hu0.le hcon (by norm_num)
    linarith
  have hu25 : 5 ≤ u ^ 2 := by
    by_contra hcon; push Not at hcon
    have : (u ^ 2) ^ 3 < 5 ^ 3 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
    have e : (u ^ 2) ^ 3 = u ^ 6 := by ring
    rw [e] at this; norm_num at this; linarith
  have hu26 : u ^ 2 ≤ X := by rw [← hu6]; exact pow_le_pow_right₀ hu1 (by norm_num)
  -- the resolution `x = 2j + 3 ≈ u²`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊(u ^ 2 - 3) / 2⌋₊ := ⟨_, rfl⟩
  have hjle : (j : ℝ) ≤ (u ^ 2 - 3) / 2 := by rw [hj]; exact Nat.floor_le (by linarith)
  have hjgt : (u ^ 2 - 3) / 2 < j + 1 := by rw [hj]; exact Nat.lt_floor_add_one _
  have hxle : nodeScale j ≤ u ^ 2 := by unfold nodeScale; linarith
  have hxge : u ^ 2 / 2 ≤ nodeScale j := by unfold nodeScale; linarith
  -- the window
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.log X / 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hlogXc : Real.log X ≤ 2 * c - 3 := (Real.log_le_iff_le_exp hX0).mpr hXc
  have hAc : A + 1 ≤ c := by rw [hA]; linarith
  have h2A : 2 * A = Real.log X := by rw [hA]; ring
  have heA : Real.exp A = Real.sqrt X := by rw [hA, Real.exp_half, Real.exp_log hX0]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈2 * X⌉₊ := ⟨_, rfl⟩
  have hMge : 2 * X ≤ M := by rw [hM]; exact Nat.le_ceil _
  have hMlt : (M : ℝ) < 2 * X + 1 := by rw [hM]; exact Nat.ceil_lt_add_one (by positivity)
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : Real.log M ≤ Real.log X + 1 := by
    have h1 : (M : ℝ) ≤ X * Real.exp 1 := by
      have he := Real.exp_one_gt_d9
      nlinarith
    calc Real.log M ≤ Real.log (X * Real.exp 1) := Real.log_le_log hM0 h1
      _ = Real.log X + 1 := by rw [Real.log_mul hX0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hMc : Real.log M / 2 + 1 ≤ c := by linarith
  -- the smoothed law
  have hsm := smoothedChebyshev_le hlam' j hA0 hAc (M := M)
    (by rw [h2A, Real.exp_log hX0]; exact hMge)
  rw [h2A, Real.exp_log hX0, abs_one, heA, hu3] at hsm
  simp only [one_mul, mul_one] at hsm
  have hD := two_jConst_div_le j hlogX hxle hu26 hG
  -- the boundary layer
  have hlay := abs_chebyshev_sub_smooth_le j lam (X := X) (by linarith) (M := M) (by linarith)
  have hcard := card_jLayer_le_nine j hX0 hu1 hu6 hxge M
  have hQ := sum_sq_div_le_of_primitive hlam' hM1 hMc (Finset.filter_subset _ _)
    (isPrimitiveSet_jLayer j X M)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Real.log M + coneToeplitzConst 0 := ⟨_, rfl⟩
  rw [← hB] at hQ
  have hB0 : 0 ≤ B := by
    have := Real.log_natCast_nonneg M; have := coneToeplitzConst_pos 0; rw [hB]; linarith
  have hPmem : ∀ n ∈ jLayer j X M, 1 ≤ n ∧ (n : ℝ) ≤ 2 * u ^ 6 := by
    intro n hn
    rw [jLayer, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn2, -⟩, hlog⟩ := hn
    refine ⟨by omega, ?_⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 : Real.log n < Real.log X + 1 / 6 := by
      have := (abs_lt.mp hlog).2; linarith [rOut_le_sixth j]
    have h2 : (n : ℝ) < X * Real.exp (1 / 6) := by
      rw [← Real.exp_log hn0, ← Real.exp_log hX0, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr h1
    have h3 : Real.exp (1 / 6) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have h5 : Real.exp (1 / 6) ^ 6 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      by_contra hcon
      push Not at hcon
      have h6 : (2 : ℝ) ^ 6 < Real.exp (1 / 6) ^ 6 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      norm_num at h6
      linarith
    have h4 : X * Real.exp (1 / 6) ≤ X * 2 := mul_le_mul_of_nonneg_left h3 hX0.le
    rw [hu6]; linarith
  have hlayer := sum_abs_layer_le hu0 hB0 hcard hQ hPmem
  have hBle : B ≤ 2 * Real.log X + C₀ := by rw [hB, ← hC₀]; linarith
  -- assembly
  have hsm' : |∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - Real.log X) - X| ≤
      1 + (6 + 512 / Real.pi * G * u ^ 2 * Real.log X) * u ^ 3 := by
    refine hsm.trans ?_
    have : 6 + 2 * jConst j 0 / jJ j ^ 2 ≤ 6 + 512 / Real.pi * G * u ^ 2 * Real.log X := by
      linarith only [hD]
    have h := mul_le_mul_of_nonneg_right this (pow_nonneg hu0.le 3)
    linarith only [h]
  rw [hu5]
  have hfinal := power_saving_arith (g := 512 / Real.pi * G) hu1 hlogX hC0.le hBle
  calc |chebyshevOf lam X - X|
      ≤ |chebyshevOf lam X - ∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - Real.log X)| +
        |∑ n ∈ Finset.Icc 2 M, lam n * jStep j (Real.log n - Real.log X) - X| := abs_sub_le _ _ _
    _ ≤ 5 * u ^ 5 * B + (1 + (6 + 512 / Real.pi * G * u ^ 2 * Real.log X) * u ^ 3) :=
        add_le_add (hlay.trans hlayer) hsm'
    _ ≤ _ := by linarith only [hfinal]

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
