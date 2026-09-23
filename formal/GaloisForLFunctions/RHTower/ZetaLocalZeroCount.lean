import GaloisForLFunctions.PNTPlus.ZetaBounds
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# Local zero count: `N(t+1) − N(t) ≪ log t`

Jensen's inequality for `ζ` on the disc of radius `1.95` around `2 + it` (which avoids the pole and
needs no Gamma factor), with the Euler–Maclaurin bound `‖ζ(σ+it)‖ ≤ 3/2 + 1/‖1−s‖ + 2|t|/σ` on
`0 < σ ≤ 2` (Zeta23 at `N = 1`) and the trivial bounds `1/3 ≤ ‖ζ(s)‖ ≤ 2` for `Re s ≥ 2`, bounds the
number of zeros of `ζ` (with multiplicity) in the disc of radius `1.85` by `20 log(180|t|)`; the disc
contains every zero with `½ ≤ β` and `|γ − t| ≤ 1`.  Multiplicities of `ζ` and `ξ` agree in the
strip, and the reflection `ρ ↦ 1 − ρ` moves the zeros with `β < ½` to the window at `−t`, so the
number of zero copies with ordinate in `[t−1, t+1]` is at most `40 log(180|t|)` for `|t| ≥ 4`.
-/

open Complex Set Metric

namespace RHTower

noncomputable section

/-! ## The Euler–Maclaurin strip bound at `N = 1` -/

theorem norm_riemannZeta_le_strip {σ t : ℝ} (hσ : σ ∈ Set.Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ 3 / 2 + 1 / ‖1 - ((σ : ℂ) + t * I)‖ + 2 * |t| / σ := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht0 this
  have hs0 : (σ : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht0 this
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp [hσ.1]
  rw [← Zeta0EqZeta one_pos hre hs1, riemannZeta0_apply]
  have hI := ZetaBnd_aux1 1 le_rfl hσ ht
  simp_rw [div_cpow_eq_cpow_neg] at hI
  simp only [Nat.cast_one, Real.rpow_neg (zero_le_one' ℝ), Real.one_rpow, inv_one, mul_one] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
    Complex.zero_cpow hs0, Complex.one_cpow, div_zero, zero_add, div_one]
  set X : ℂ := ((σ : ℂ) + t * I) * ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) *
    (x : ℂ) ^ (-(((σ : ℂ) + t * I) + 1)) with hX
  have h1 : ‖(1 : ℂ) + (-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2 + X)‖
      ≤ 1 + 1 / ‖1 - ((σ : ℂ) + t * I)‖ + 1 / 2 + ‖X‖ := by
    calc ‖(1 : ℂ) + (-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2 + X)‖
        ≤ ‖(1 : ℂ)‖ + ‖-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2 + X‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + (‖-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2‖ + ‖X‖) := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + ((‖-1 / (1 - ((σ : ℂ) + t * I))‖ + ‖(-1 / 2 : ℂ)‖) + ‖X‖) := by
          gcongr; exact norm_add_le _ _
      _ = 1 + 1 / ‖1 - ((σ : ℂ) + t * I)‖ + 1 / 2 + ‖X‖ := by
          rw [norm_one, norm_div, norm_neg, norm_one, norm_div, norm_neg, norm_one]
          norm_num
          ring
  refine h1.trans ?_
  have hXle : ‖X‖ ≤ 2 * |t| / σ := hI
  linarith

/-! ## Trivial bounds for `Re s ≥ 2` -/

theorem norm_LSeries_term_one_le {s : ℂ} (hs : 2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term 1 s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, Pi.one_apply, norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by norm_cast
      _ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs

theorem summable_one_div_nat_sq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
  hasSum_zeta_two.summable

theorem norm_riemannZeta_le_two {s : ℂ} (hs : 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 2 := by
  rw [← LSeries_one_eq_riemannZeta (by linarith)]
  unfold LSeries
  have hsum : Summable fun n : ℕ => ‖LSeries.term 1 s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_LSeries_term_one_le hs)
      summable_one_div_nat_sq
  calc ‖∑' n, LSeries.term 1 s n‖ ≤ ∑' n, ‖LSeries.term 1 s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
        hsum.tsum_le_tsum (norm_LSeries_term_one_le hs) summable_one_div_nat_sq
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 2 := by
        have := Real.pi_lt_d2
        have := Real.pi_pos
        nlinarith

/-- The tail `Σ_{n ≥ 2} n^{−2} = π²/6 − 1`. -/
theorem hasSum_one_div_nat_sq_tail :
    HasSum (fun n : ℕ => if n ≤ 1 then (0 : ℝ) else 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h1 : HasSum (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) 1 := by
    simpa using hasSum_ite_eq (1 : ℕ) (1 : ℝ)
  have h := hasSum_zeta_two.sub h1
  have hf : (fun n : ℕ => if n ≤ 1 then (0 : ℝ) else 1 / (n : ℝ) ^ 2)
      = fun n : ℕ => 1 / (n : ℝ) ^ 2 - if n = 1 then (1 : ℝ) else 0 := by
    funext n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have h1' : n ≠ 1 := by omega
      have h2 : ¬ n ≤ 1 := by omega
      simp [h1', h2]
  rw [hf]
  exact h

theorem norm_riemannZeta_ge_third {s : ℂ} (hs : 2 ≤ s.re) : 1 / 3 ≤ ‖riemannZeta s‖ := by
  rw [← LSeries_one_eq_riemannZeta (by linarith)]
  unfold LSeries
  have hsum : Summable fun n : ℕ => LSeries.term 1 s n :=
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_LSeries_term_one_le hs)
      summable_one_div_nat_sq).of_norm
  have hδ : Summable fun n : ℕ => if n = 1 then (1 : ℂ) else 0 :=
    (hasSum_ite_eq (1 : ℕ) (1 : ℂ)).summable
  have hterm1 : LSeries.term 1 s 1 = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero, Pi.one_apply, Nat.cast_one, Complex.one_cpow, div_one]
  have hsplit : (∑' n, LSeries.term 1 s n) - 1
      = ∑' n, (LSeries.term 1 s n - if n = 1 then (1 : ℂ) else 0) := by
    rw [hsum.tsum_sub hδ, (hasSum_ite_eq (1 : ℕ) (1 : ℂ)).tsum_eq]
  have hbound : ∀ n : ℕ, ‖LSeries.term 1 s n - if n = 1 then (1 : ℂ) else 0‖
      ≤ if n ≤ 1 then (0 : ℝ) else 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [LSeries.term_zero]
      · rw [hterm1]; simp
    · have h1' : n ≠ 1 := by omega
      have h2 : ¬ n ≤ 1 := by omega
      simp only [h1', if_false, sub_zero, h2]
      exact norm_LSeries_term_one_le hs n
  have hsum2 : Summable fun n : ℕ => ‖LSeries.term 1 s n - if n = 1 then (1 : ℂ) else 0‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hasSum_one_div_nat_sq_tail.summable
  have hdiff : ‖(∑' n, LSeries.term 1 s n) - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    rw [hsplit]
    calc ‖∑' n, (LSeries.term 1 s n - if n = 1 then (1 : ℂ) else 0)‖
        ≤ ∑' n, ‖LSeries.term 1 s n - if n = 1 then (1 : ℂ) else 0‖ := norm_tsum_le_tsum_norm hsum2
      _ ≤ ∑' n : ℕ, (if n ≤ 1 then (0 : ℝ) else 1 / (n : ℝ) ^ 2) :=
          hsum2.tsum_le_tsum hbound hasSum_one_div_nat_sq_tail.summable
      _ = Real.pi ^ 2 / 6 - 1 := hasSum_one_div_nat_sq_tail.tsum_eq
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  have := norm_sub_norm_le (1 : ℂ) (∑' n, LSeries.term 1 s n)
  rw [norm_one, norm_sub_rev] at this
  linarith

/-! ## Jensen on the disc around `2 + it` -/

theorem log_ratio_ge_twentieth : (1 / 20 : ℝ) ≤ Real.log (1.95 / 1.85) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_bound (x := (1 / 20 : ℝ))
    (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one, Nat.succ_eq_add_one, Nat.factorial_two,
    Nat.cast_ofNat] at h
  rw [abs_le] at h
  norm_num at h ⊢
  linarith [h.2]

theorem analyticOnNhd_riemannZeta_disc {t : ℝ} (ht : 4 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + t * I) |1.95|) := by
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  refine (hd.analyticOnNhd isOpen_ne).mono ?_
  intro z hz
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num)] at hz
  have him := Complex.abs_im_le_norm (z - ((2 : ℂ) + t * I))
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at him
  norm_num at him
  have hbound : |z.im - t| ≤ 1.95 := him.trans hz
  intro h1
  rw [h1] at hbound
  simp only [Complex.one_im, zero_sub, abs_neg] at hbound
  linarith

theorem norm_riemannZeta_le_sphere {t : ℝ} (ht : 4 ≤ |t|) {z : ℂ}
    (hz : z ∈ sphere ((2 : ℂ) + t * I) |1.95|) : ‖riemannZeta z‖ ≤ 60 * |t| := by
  rw [mem_sphere_iff_norm, abs_of_pos (by norm_num)] at hz
  have hre := Complex.abs_re_le_norm (z - ((2 : ℂ) + t * I))
  have him := Complex.abs_im_le_norm (z - ((2 : ℂ) + t * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at hre him
  rw [hz] at hre him
  norm_num at hre him
  have hre' := abs_le.mp hre
  have him' := abs_le.mp him
  have hτ : 2 ≤ |z.im| := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h] at ht
      rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_neg h] at ht
      rw [abs_of_neg (by linarith)]; linarith
  have hτt : |z.im| ≤ |t| + 1.95 := by
    calc |z.im| = |t + (z.im - t)| := by ring_nf
      _ ≤ |t| + |z.im - t| := abs_add_le _ _
      _ ≤ |t| + 1.95 := by linarith
  rcases le_or_gt z.re 2 with hσ | hσ
  · have hσ0 : 0 < z.re := by linarith
    have h := norm_riemannZeta_le_strip (σ := z.re) (t := z.im) ⟨hσ0, hσ⟩ hτ
    rw [Complex.re_add_im] at h
    have h1 : 1 / ‖1 - z‖ ≤ 1 / 2 := by
      have : 2 ≤ ‖1 - z‖ := by
        have := Complex.abs_im_le_norm (1 - z)
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
        linarith
      exact one_div_le_one_div_of_le (by norm_num) this
    have h2 : 2 * |z.im| / z.re ≤ 40 * (|t| + 1.95) := by
      rw [div_le_iff₀ hσ0]
      calc 2 * |z.im| ≤ 2 * (|t| + 1.95) := by linarith
        _ = 40 * (|t| + 1.95) * 0.05 := by ring
        _ ≤ 40 * (|t| + 1.95) * z.re := by gcongr; linarith
    linarith
  · have := norm_riemannZeta_le_two (s := z) (by linarith)
    linarith

/-- **Jensen for `ζ` on the disc.**  The number of zeros of `ζ` in the closed disc of radius `1.85`
around `2 + it`, counted with multiplicity, is at most `20 log(180|t|)` for `|t| ≥ 4`. -/
theorem zeta_disc_zeroCount_le {t : ℝ} (ht : 4 ≤ |t|) :
    ((∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|)) u : ℤ) : ℝ)
      ≤ 20 * Real.log (180 * |t|) := by
  have hM : (1 : ℝ) ≤ 60 * |t| := by linarith
  have h := GaloisForLFunctions.HTGeometry.sum_divisor_le_of_bounds (c := (2 : ℂ) + t * I)
    (r := 1.85) (R := 1.95) (M := 60 * |t|) (m := 1 / 3) (f := riemannZeta)
    (by norm_num) (by norm_num) hM (by norm_num) (analyticOnNhd_riemannZeta_disc ht)
    (norm_riemannZeta_ge_third (by simp)) (fun z hz => norm_riemannZeta_le_sphere ht hz)
  refine h.trans ?_
  have hlog := log_ratio_ge_twentieth
  have hlogpos : 0 < Real.log (1.95 / 1.85) := by linarith
  rw [div_le_iff₀ hlogpos]
  have hnum : Real.log (60 * |t| / (1 / 3)) = Real.log (180 * |t|) := by
    congr 1; ring
  rw [hnum]
  have h180 : 0 ≤ Real.log (180 * |t|) := Real.log_nonneg (by linarith)
  nlinarith

/-! ## Multiplicities of `ζ` and `ξ` agree in the strip -/

/-- The unit factor `u(z) = z(z−1)/2 · Γ_ℝ(z)`, so that `ξ = u · ζ` on `Re z > 0`, `z ≠ 0, 1`. -/
def xiUnit (z : ℂ) : ℂ := z * (z - 1) / 2 * Gammaℝ z

theorem xi_eq_xiUnit_mul_zeta {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (hre : 0 < z.re) :
    xi z = xiUnit z * riemannZeta z := by
  have hΓ : Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0]
  unfold xiUnit
  field_simp

theorem analyticAt_xiUnit {z : ℂ} (hre : 0 < z.re) : AnalyticAt ℂ xiUnit z := by
  have hΓ : AnalyticAt ℂ Gammaℝ z := by
    have hd : DifferentiableOn ℂ Gammaℝ {w : ℂ | 0 < w.re} := fun w hw =>
      (hasDerivAt_Gammaℝ_of_re_pos hw).differentiableAt.differentiableWithinAt
    exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)
  have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) z := by fun_prop
  exact hpoly.mul hΓ

theorem xiUnit_ne_zero {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (hre : 0 < z.re) : xiUnit z ≠ 0 := by
  unfold xiUnit
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero)
    (Complex.Gammaℝ_ne_zero_of_re_pos hre)

theorem analyticAt_riemannZeta_of_ne_one_zetaLocalZeroCount {z : ℂ} (h1 : z ≠ 1) : AnalyticAt ℂ riemannZeta z := by
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw =>
    (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds h1)

/-- On `Re z > 0`, `z ≠ 1`, the meromorphic orders of `ξ` and `ζ` agree. -/
theorem meromorphicOrderAt_xi_eq_zeta {z : ℂ} (hre : 0 < z.re) (h1 : z ≠ 1) :
    meromorphicOrderAt xi z = meromorphicOrderAt riemannZeta z := by
  have h0 : z ≠ 0 := by rintro rfl; simp at hre
  have hVopen : IsOpen {w : ℂ | 0 < w.re ∧ w ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hzV : z ∈ {w : ℂ | 0 < w.re ∧ w ≠ 1} := ⟨hre, h1⟩
  have heq : xi =ᶠ[nhdsWithin z {z}ᶜ] (xiUnit * riemannZeta) := by
    refine Filter.EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds
    refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds hzV) fun w hw => ?_
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    exact xi_eq_xiUnit_mul_zeta hw0 hw.2 hw.1
  rw [meromorphicOrderAt_congr heq,
    meromorphicOrderAt_mul (analyticAt_xiUnit hre).meromorphicAt
      (analyticAt_riemannZeta_of_ne_one_zetaLocalZeroCount h1).meromorphicAt,
    (analyticAt_xiUnit hre).meromorphicOrderAt_eq,
    ((analyticAt_xiUnit hre).analyticOrderAt_eq_zero).mpr (xiUnit_ne_zero h0 h1 hre)]
  simp

theorem re_pos_of_mem_disc {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ closedBall ((2 : ℂ) + t * I) |1.85|) :
    0 < ρ.re ∧ |ρ.im - t| ≤ 1.85 := by
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num)] at hρ
  have hre := Complex.abs_re_le_norm (ρ - ((2 : ℂ) + t * I))
  have him := Complex.abs_im_le_norm (ρ - ((2 : ℂ) + t * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at hre him
  norm_num at hre him
  have := abs_le.mp (hre.trans hρ)
  exact ⟨by linarith, him.trans hρ⟩

theorem ne_one_of_mem_disc {t : ℝ} (ht : 4 ≤ |t|) {ρ : ℂ}
    (hρ : ρ ∈ closedBall ((2 : ℂ) + t * I) |1.85|) : ρ ≠ 1 := by
  intro h
  have := (re_pos_of_mem_disc hρ).2
  rw [h] at this
  simp only [Complex.one_im, zero_sub, abs_neg] at this
  linarith

theorem xi_meromorphicOn_univ : MeromorphicOn xi Set.univ :=
  (xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn

/-- The divisor of `ξ` on `ℂ` and the divisor of `ζ` on the disc agree at points of the disc. -/
theorem divisor_xi_eq_divisor_zeta_disc {t : ℝ} (ht : 4 ≤ |t|) {ρ : ℂ}
    (hρ : ρ ∈ closedBall ((2 : ℂ) + t * I) |1.85|) :
    (MeromorphicOn.divisor xi Set.univ) ρ
      = (MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|)) ρ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|) :=
    (analyticOnNhd_riemannZeta_disc ht).mono
      (closedBall_subset_closedBall (by rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]; norm_num))
  rw [MeromorphicOn.divisor_apply xi_meromorphicOn_univ (Set.mem_univ ρ),
    MeromorphicOn.divisor_apply hana.meromorphicOn hρ,
    meromorphicOrderAt_xi_eq_zeta (re_pos_of_mem_disc hρ).1 (ne_one_of_mem_disc ht hρ)]

theorem divisor_zeta_disc_nonneg {t : ℝ} (ht : 4 ≤ |t|) (ρ : ℂ) :
    0 ≤ (MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|)) ρ := by
  by_cases hρ : ρ ∈ closedBall ((2 : ℂ) + t * I) |1.85|
  · have hana : AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|) :=
      (analyticOnNhd_riemannZeta_disc ht).mono
        (closedBall_subset_closedBall (by rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]; norm_num))
    rw [MeromorphicOn.divisor_apply hana.meromorphicOn hρ, (hana ρ hρ).meromorphicOrderAt_eq]
    rw [WithTop.untop₀_nonneg]
    cases h : analyticOrderAt riemannZeta ρ with
    | top => simp
    | coe n => simp
  · have := (MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|)).supportWithinDomain
    have h0 : (MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|)) ρ = 0 := by
      by_contra hne
      exact hρ (this hne)
    rw [h0]

/-! ## Counting zero copies -/

/-- A finite set of zero copies whose base points lie in the disc has at most as many elements
as the disc zero count of `ζ`. -/
theorem card_le_disc_zeroCount {t : ℝ} (ht : 4 ≤ |t|) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, ((q.1 : ℂ)) ∈ closedBall ((2 : ℂ) + t * I) |1.85|) :
    (F.card : ℝ) ≤
      ((∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|)) u : ℤ) : ℝ) := by
  classical
  set D := MeromorphicOn.divisor riemannZeta (closedBall ((2 : ℂ) + t * I) |1.85|) with hD
  set T : Finset ℂ := F.image (fun q : XiZeroCopy => (q.1 : ℂ)) with hT
  have hmaps : Set.MapsTo (fun q : XiZeroCopy => (q.1 : ℂ)) (F : Set XiZeroCopy) (T : Set ℂ) :=
    fun q hq => Finset.mem_image_of_mem _ hq
  have hfiber : ∀ ρ ∈ T, ((F.filter fun q : XiZeroCopy => (q.1 : ℂ) = ρ).card : ℤ) ≤ D ρ := by
    intro ρ hρT
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hρT
    have hDρ : D (q₀.1 : ℂ) = (MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ) :=
      (divisor_xi_eq_divisor_zeta_disc ht (hF q₀ hq₀)).symm
    rw [hDρ]
    have hcard : (F.filter fun q : XiZeroCopy => (q.1 : ℂ) = (q₀.1 : ℂ)).card
        ≤ ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)).toNat := by
      refine (Finset.card_le_card_of_injOn (fun q : XiZeroCopy => (q.2 : ℕ))
        (t := Finset.range (((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)).toNat)) ?_ ?_).trans
        (by rw [Finset.card_range])
      · intro q hq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
        rw [Finset.coe_range, Set.mem_Iio]
        have h := q.2.isLt
        exact lt_of_lt_of_eq h (by rw [hq.2])
      · intro q hq q' hq' hqq'
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
        have h1 : q.1 = q'.1 := Subtype.ext (hq.2.trans hq'.2.symm)
        exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).mpr hqq')
    have hnn : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ) := by
      rw [← hDρ]; exact divisor_zeta_disc_nonneg ht _
    calc ((F.filter fun q : XiZeroCopy => (q.1 : ℂ) = (q₀.1 : ℂ)).card : ℤ)
        ≤ (((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)).toNat : ℤ) := by exact_mod_cast hcard
      _ = (MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ) := Int.toNat_of_nonneg hnn
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  set S : Finset ℂ := hfin.toFinset with hS
  have hsupp : Function.support (fun u => D u) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [hS, Set.Finite.coe_toFinset]
    exact hu
  have hfinsum : (∑ᶠ u, D u) = ∑ u ∈ S, D u := finsum_eq_sum_of_support_subset _ hsupp
  have hTle : (∑ ρ ∈ T, D ρ) ≤ ∑ ρ ∈ S, D ρ := by
    calc (∑ ρ ∈ T, D ρ) ≤ ∑ ρ ∈ T ∪ S, D ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            (fun ρ _ _ => divisor_zeta_disc_nonneg ht ρ)
      _ = ∑ ρ ∈ S, D ρ := by
          symm
          refine Finset.sum_subset Finset.subset_union_right fun ρ _ hρS => ?_
          by_contra hne
          exact hρS (by rw [hS, Set.Finite.mem_toFinset]; exact hne)
  have hcardT : (F.card : ℤ) ≤ ∑ ρ ∈ T, D ρ := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    exact Finset.sum_le_sum hfiber
  have : (F.card : ℤ) ≤ ∑ᶠ u, D u := by rw [hfinsum]; exact hcardT.trans hTle
  exact_mod_cast this

theorem mem_disc_of_window {t : ℝ} {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re) (hre1 : ρ.re < 1)
    (him : |ρ.im - t| ≤ 1) : ρ ∈ closedBall ((2 : ℂ) + t * I) |1.85| := by
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num)]
  have hsq : ‖ρ - ((2 : ℂ) + t * I)‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
    norm_num
    ring
  have h1 : (ρ.re - 2) ^ 2 ≤ (3 / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hre) (by linarith : (0:ℝ) ≤ 7 / 2 - ρ.re)]
  have h2 : (ρ.im - t) ^ 2 ≤ 1 := by
    have := abs_le.mp him
    nlinarith
  have hle : ‖ρ - ((2 : ℂ) + t * I)‖ ^ 2 ≤ (1.85 : ℝ) ^ 2 := by
    rw [hsq]; norm_num at h1 ⊢; linarith
  nlinarith [hle, norm_nonneg (ρ - ((2 : ℂ) + t * I)), sq_nonneg (‖ρ - ((2 : ℂ) + t * I)‖ - 1.85)]

/-- Copies with real part `≥ ½` and ordinate within `1` of `t`. -/
theorem card_le_of_window_re_ge_half {t : ℝ} (ht : 4 ≤ |t|) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, 1 / 2 ≤ (q.1 : ℂ).re ∧ |(q.1 : ℂ).im - t| ≤ 1) :
    (F.card : ℝ) ≤ 20 * Real.log (180 * |t|) := by
  refine (card_le_disc_zeroCount ht F fun q hq => ?_).trans (zeta_disc_zeroCount_le ht)
  exact mem_disc_of_window (hF q hq).1 (xiZeroCopy_re_lt_one q) (hF q hq).2

/-- **The local zero count.**  For `|t| ≥ 4`, at most `40 log(180|t|)` zero copies have ordinate
within `1` of `t`. -/
theorem card_le_of_ordinates_in_window {t : ℝ} (ht : 4 ≤ |t|) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ 1) :
    (F.card : ℝ) ≤ 40 * Real.log (180 * |t|) := by
  classical
  set F₁ := F.filter (fun q : XiZeroCopy => 1 / 2 ≤ (q.1 : ℂ).re) with hF₁
  set F₂ := F.filter (fun q : XiZeroCopy => ¬ (1 / 2 ≤ (q.1 : ℂ).re)) with hF₂
  have hcard : F.card = F₁.card + F₂.card := (Finset.card_filter_add_card_filter_not _).symm
  have h1 : (F₁.card : ℝ) ≤ 20 * Real.log (180 * |t|) := by
    refine card_le_of_window_re_ge_half ht F₁ fun q hq => ?_
    rw [hF₁, Finset.mem_filter] at hq
    exact ⟨hq.2, hF q hq.1⟩
  have h2 : (F₂.card : ℝ) ≤ 20 * Real.log (180 * |t|) := by
    have ht' : 4 ≤ |-t| := by rwa [abs_neg]
    have := card_le_of_window_re_ge_half (t := -t) ht' (F₂.image xiZeroCopyReflectEquiv) (by
      intro q' hq'
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
      rw [hF₂, Finset.mem_filter] at hq
      have hval := xiZeroCopy_reflect_val q
      have hre : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
        rw [hval]; simp
      have him : ((xiZeroCopyReflectEquiv q).1 : ℂ).im = -(q.1 : ℂ).im := by
        rw [hval]; simp
      refine ⟨?_, ?_⟩
      · rw [hre]; push Not at hq; linarith [hq.2]
      · rw [him]
        have := hF q hq.1
        rw [show -(q.1 : ℂ).im - -t = -((q.1 : ℂ).im - t) by ring, abs_neg]
        exact this)
    rw [Finset.card_image_of_injective _ xiZeroCopyReflectEquiv.injective, abs_neg] at this
    exact this
  have : (F.card : ℝ) = F₁.card + F₂.card := by rw [hcard]; push_cast; ring
  linarith

end

end RHTower
