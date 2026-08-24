import GaloisForLFunctions.HTGeometry.EisensteinSeriesDiskNaturalBoundary
import GaloisForLFunctions.HTGeometry.HardyDiskMultiplier
import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgeMeanSquare
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone

/-!
# Finite bounded Hardy jets with a natural boundary

Repeated zero-constant primitives of the disk Eisenstein series `E₂ - 1` give, at every prescribed
finite jet depth, an explicit holomorphic and differentially algebraic function whose observed jet
lies in `H^∞(𝔻)` while every unit-circle point blocks analytic continuation.  This module formalizes
the exact factorial-ratio series, derivative ladder, divisor-sum convergence, shifted Chazy
annihilator, and continuation obstruction.
-/

open UpperHalfPlane hiding I
open Real Complex Filter Topology Set Metric ArithmeticFunction MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient-normalized `s`-fold primitive term of `E₂ - 1`. -/
def hardyPrimitiveTerm (s n : ℕ) (q : ℂ) : ℂ :=
  (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
      ((n + 1).ascFactorial s : ℂ) * q ^ (n + s)

/-- The `s`-fold primitive of `E₂ - 1`, with every integration constant zero. -/
def hardyPrimitiveJet (s : ℕ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, hardyPrimitiveTerm s n q

theorem hasDerivAt_hardyPrimitiveTerm_succ (s n : ℕ) (q : ℂ) :
    HasDerivAt (hardyPrimitiveTerm (s + 1) n) (hardyPrimitiveTerm s n q) q := by
  have ha : ((n + 1).ascFactorial s : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.ascFactorial_pos n s))
  have hb : ((n + 1).ascFactorial (s + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.ascFactorial_pos n (s + 1)))
  have hpow := (hasDerivAt_pow (n + (s + 1)) q).const_mul
    ((-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
      ((n + 1).ascFactorial (s + 1) : ℂ))
  have hexp : n + (s + 1) - 1 = n + s := by omega
  have hvalue :
      (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
          ((n + 1).ascFactorial (s + 1) : ℂ) *
            ((n + (s + 1) : ℕ) * q ^ (n + (s + 1) - 1)) =
        hardyPrimitiveTerm s n q := by
    rw [hexp, hardyPrimitiveTerm, Nat.ascFactorial_succ]
    push_cast
    have hfac : (n : ℂ) + 1 + (s : ℂ) = (n : ℂ) + ((s : ℂ) + 1) := by ring
    have hfac_ne : (n : ℂ) + ((s : ℂ) + 1) ≠ 0 := by
      have hn : n + (s + 1) ≠ 0 := by omega
      exact_mod_cast hn
    rw [hfac]
    field_simp [ha, hfac_ne]
  change HasDerivAt
    (fun y => (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
      ((n + 1).ascFactorial (s + 1) : ℂ) * y ^ (n + (s + 1)))
    (hardyPrimitiveTerm s n q) q
  exact hpow.congr_deriv hvalue

private theorem summable_hardyPrimitiveMajorant {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => 24 * (n : ℝ) ^ 2 * ρ ^ n) := by
  have hgeom : Summable (fun n : ℕ => (n : ℝ) ^ 2 * ρ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by simpa [Real.norm_eq_abs, abs_of_nonneg hρ0])
  simpa only [mul_assoc] using hgeom.mul_left 24

private theorem norm_hardyPrimitiveTerm_le {s n : ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {q : ℂ} (hq : ‖q‖ ≤ ρ) :
    ‖hardyPrimitiveTerm s n q‖ ≤ 24 * (n : ℝ) ^ 2 * ρ ^ n := by
  have hasc : 1 ≤ (n + 1).ascFactorial s := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.ascFactorial_pos n s))
  have hsigma : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  have hqpow : ‖q‖ ^ (n + s) ≤ ρ ^ n := by
    calc
      ‖q‖ ^ (n + s) ≤ ρ ^ (n + s) := pow_le_pow_left₀ (norm_nonneg q) hq _
      _ ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1 (Nat.le_add_right n s)
  rw [hardyPrimitiveTerm, norm_mul, norm_div, norm_mul, norm_pow]
  norm_num only [norm_neg, Complex.norm_ofNat, Complex.norm_natCast]
  have hden : (1 : ℝ) ≤ ((n + 1).ascFactorial s : ℝ) := by exact_mod_cast hasc
  calc
    24 * ↑((ArithmeticFunction.sigma 1) n) /
          ↑((n + 1).ascFactorial s) * ‖q‖ ^ (n + s)
        ≤ 24 * ↑((ArithmeticFunction.sigma 1) n) * ‖q‖ ^ (n + s) := by
          gcongr
          exact div_le_self (by positivity) hden
    _ ≤ 24 * (n : ℝ) ^ 2 * ρ ^ n := by gcongr

theorem hasDerivAt_hardyPrimitiveJet_succ (s : ℕ) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) 1) :
    HasDerivAt (hardyPrimitiveJet (s + 1)) (hardyPrimitiveJet s q) q := by
  set ρ : ℝ := (‖q‖ + 1) / 2 with hρ
  have hq1 : ‖q‖ < 1 := by simpa [mem_ball] using hq
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hqρ : ‖q‖ < ρ := by rw [hρ]; linarith
  let u : ℕ → ℝ := fun n => 24 * (n : ℝ) ^ 2 * ρ ^ n
  have hu : Summable u := summable_hardyPrimitiveMajorant hρ0.le hρ1
  have hterm : ∀ n : ℕ, ∀ y ∈ ball (0 : ℂ) ρ,
      HasDerivAt (hardyPrimitiveTerm (s + 1) n) (hardyPrimitiveTerm s n y) y := by
    intro n y _
    exact hasDerivAt_hardyPrimitiveTerm_succ s n y
  have hbound : ∀ n : ℕ, ∀ y ∈ ball (0 : ℂ) ρ,
      ‖hardyPrimitiveTerm s n y‖ ≤ u n := by
    intro n y hy
    apply norm_hardyPrimitiveTerm_le hρ0.le hρ1.le
    have hyn : ‖y‖ < ρ := by simpa [mem_ball] using hy
    exact hyn.le
  have hzero : Summable (fun n : ℕ => hardyPrimitiveTerm (s + 1) n 0) := by
    apply summable_zero.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [hardyPrimitiveTerm]
    · simp [hardyPrimitiveTerm, hn]
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hterm hbound
      (by simpa using hρ0) hzero (by simpa [mem_ball] using hqρ)

theorem e2Disk_zero : e2Disk 0 = 1 := by
  rw [e2Disk, UpperHalfPlane.cuspFunction_apply_zero one_pos
    (e2Disk_analyticOnNhd 0 (by simp)) Bottcher.E2_periodic_comp_ramanujan]
  exact Bottcher.eisensteinSeries_E2_tendsto_one_atImInfty.limUnder_eq

theorem hardyPrimitiveJet_zero_eq :
    EqOn (hardyPrimitiveJet 0) (fun q => e2Disk q - 1) (ball (0 : ℂ) 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · subst q
    have hz : (fun n : ℕ => hardyPrimitiveTerm 0 n 0) = 0 := by
      funext n
      cases n with
      | zero => simp [hardyPrimitiveTerm]
      | succ n => simp [hardyPrimitiveTerm]
    rw [hardyPrimitiveJet, hz]
    change (∑' _ : ℕ, (0 : ℂ)) = e2Disk 0 - 1
    simp [e2Disk_zero]
  have hqnorm : ‖q‖ < 1 := by simpa [mem_ball] using hq
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, invQParam_one_im_pos hq0 hqnorm⟩
  have hqp : Function.Periodic.qParam 1 τ = q := qParam_one_invQParam_one hq0
  have hs := EisensteinSeries.hasSum_qExpansion_E2 τ
  have hs1 : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have hsub := hs.sub hs1
  have hterms : (fun n : ℕ =>
      (if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℂ)) •
          Complex.exp (2 * Real.pi * I * (τ : ℂ)) ^ n -
        (if n = 0 then 1 else 0)) =
      (fun n => hardyPrimitiveTerm 0 n q) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [hardyPrimitiveTerm]
    · rw [if_neg hn, if_neg hn, sub_zero]
      simp only [smul_eq_mul, hardyPrimitiveTerm, Nat.ascFactorial_zero,
        Nat.cast_one, div_one]
      rw [← hqp]
      simp [Function.Periodic.qParam]
  have hsum : HasSum (fun n => hardyPrimitiveTerm 0 n q)
      (EisensteinSeries.E2 τ - 1) := by
    rw [← hterms]
    exact hsub
  rw [hardyPrimitiveJet, hsum.tsum_eq, ← e2Disk_qParam τ, hqp]

theorem hardyPrimitiveJet_analyticOnNhd (s : ℕ) :
    AnalyticOnNhd ℂ (hardyPrimitiveJet s) (ball (0 : ℂ) 1) := by
  cases s with
  | zero =>
      exact AnalyticOnNhd.congr isOpen_ball
        (e2Disk_analyticOnNhd.sub analyticOnNhd_const)
        (fun q hq => (hardyPrimitiveJet_zero_eq hq).symm)
  | succ s =>
      have hd : DifferentiableOn ℂ (hardyPrimitiveJet (s + 1)) (ball (0 : ℂ) 1) := by
        intro q hq
        exact (hasDerivAt_hardyPrimitiveJet_succ s hq).differentiableAt.differentiableWithinAt
      exact hd.analyticOnNhd isOpen_ball

theorem deriv_hardyPrimitiveJet_succ (s : ℕ) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) 1) :
    deriv (hardyPrimitiveJet (s + 1)) q = hardyPrimitiveJet s q :=
  (hasDerivAt_hardyPrimitiveJet_succ s hq).deriv

/-- Every derivative consumes exactly one primitive level. -/
theorem iteratedDeriv_hardyPrimitiveJet_eq (s j : ℕ) (hj : j ≤ s) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) 1) :
    iteratedDeriv j (hardyPrimitiveJet s) q = hardyPrimitiveJet (s - j) q := by
  induction j generalizing q with
  | zero => simp
  | succ j ih =>
      have hj' : j ≤ s := by omega
      have hlocal : iteratedDeriv j (hardyPrimitiveJet s) =ᶠ[𝓝 q]
          hardyPrimitiveJet (s - j) := by
        filter_upwards [isOpen_ball.mem_nhds hq] with z hz
        exact ih hj' hz
      rw [iteratedDeriv_succ, hlocal.deriv_eq]
      have hsub : s - j = (s - (j + 1)) + 1 := by omega
      rw [hsub]
      exact deriv_hardyPrimitiveJet_succ (s - (j + 1)) hq

/-- The `m`-th derivative is exactly `E₂ - 1`. -/
theorem iteratedDeriv_hardyPrimitiveJet_self (m : ℕ) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) 1) :
    iteratedDeriv m (hardyPrimitiveJet m) q = e2Disk q - 1 := by
  rw [iteratedDeriv_hardyPrimitiveJet_eq m m le_rfl hq]
  simpa using hardyPrimitiveJet_zero_eq hq

/-- Rising-factorial coefficients are exactly the factorial ratios in the paper formula. -/
theorem hardyPrimitiveTerm_eq_factorialRatio (s n : ℕ) (q : ℂ) :
    hardyPrimitiveTerm s n q =
      (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) * (n.factorial : ℂ) /
        ((n + s).factorial : ℂ) * q ^ (n + s) := by
  have ha : ((n + 1).ascFactorial s : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.ascFactorial_pos n s))
  have hf : ((n + s).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + s)
  have hfac : (n.factorial : ℂ) * ((n + 1).ascFactorial s : ℂ) =
      ((n + s).factorial : ℂ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n s
  unfold hardyPrimitiveTerm
  field_simp [ha, hf]
  linear_combination
    ((ArithmeticFunction.sigma 1 n : ℂ) * q ^ (n + s)) * hfac

private theorem sigma_one_le_mul_card_divisors (n : ℕ) :
    ArithmeticFunction.sigma 1 n ≤ n * n.divisors.card := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.sigma_apply]
    calc
      ∑ d ∈ n.divisors, d ^ 1 ≤ ∑ _d ∈ n.divisors, n := by
        apply Finset.sum_le_sum
        intro d hd
        simp only [pow_one]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1
      _ = n * n.divisors.card := by simp [Nat.mul_comm]

private theorem pow_le_ascFactorial (n s : ℕ) :
    n ^ s ≤ (n + 1).ascFactorial s := by
  rw [Nat.ascFactorial_eq_prod_range]
  calc
    n ^ s = ∏ _i ∈ Finset.range s, n := by simp
    _ ≤ ∏ i ∈ Finset.range s, (n + 1 + i) := by
      apply Finset.prod_le_prod
      · intro _ _
        exact Nat.zero_le _
      · intro i _
        omega

/-- Absolute coefficient summability starts exactly after three integrations. -/
theorem summable_norm_hardyPrimitiveCoefficient {s : ℕ} (hs : 3 ≤ s) :
    Summable (fun n : ℕ =>
      ‖(-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
        ((n + 1).ascFactorial s : ℂ)‖) := by
  let beta : ℝ := (s : ℝ) - 1
  have hbeta : 1 < beta := by
    dsimp [beta]
    have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hbase : Summable (fun n : ℕ =>
      24 * (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)) := by
    simpa only [mul_assoc] using
      (RHTower.Sieve.summable_card_divisors_mul_rpow hbeta).mul_left 24
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbase
  rcases eq_or_ne n 0 with rfl | hn
  · simp [beta]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hsig := sigma_one_le_mul_card_divisors n
    have hasc := pow_le_ascFactorial n s
    have hdenpos : (0 : ℝ) < ((n + 1).ascFactorial s : ℝ) := by
      exact_mod_cast Nat.ascFactorial_pos n s
    rw [norm_div, norm_mul, norm_neg, Complex.norm_ofNat,
      Complex.norm_natCast, Complex.norm_natCast]
    have hfrac :
        (ArithmeticFunction.sigma 1 n : ℝ) /
            ((n + 1).ascFactorial s : ℝ) ≤
          ((n : ℝ) * n.divisors.card) / (n : ℝ) ^ s := by
      apply (div_le_div_iff₀ hdenpos (pow_pos hnpos s)).2
      have hsigR : (ArithmeticFunction.sigma 1 n : ℝ) ≤
          (n : ℝ) * n.divisors.card := by exact_mod_cast hsig
      have hascR : (n : ℝ) ^ s ≤ ((n + 1).ascFactorial s : ℝ) := by
        exact_mod_cast hasc
      nlinarith [mul_le_mul hsigR hascR (by positivity) (by positivity)]
    calc
      24 * ↑((ArithmeticFunction.sigma 1) n) / ↑((n + 1).ascFactorial s)
          = 24 * (↑((ArithmeticFunction.sigma 1) n) /
              ↑((n + 1).ascFactorial s)) := by ring
      _ ≤ 24 * (((n : ℝ) * n.divisors.card) / (n : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 24 * n.divisors.card * (n : ℝ) ^ (-beta) := by
        have hbeta_eq : beta = (s : ℝ) - 1 := rfl
        rw [Real.rpow_neg hnpos.le, hbeta_eq]
        rw [Real.rpow_sub hnpos  (s : ℝ) 1, Real.rpow_natCast, Real.rpow_one]
        field_simp

/-- Exact absolutely convergent divisor-sum series in card equation `(9)`. -/
theorem sigmaOne_LSeriesHasSum {w : ℂ} (hw : 2 < w.re) :
    LSeriesHasSum (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ)) w
      (riemannZeta w * riemannZeta (w - 1)) := by
  let Z : ArithmeticFunction ℂ := (ArithmeticFunction.zeta : ArithmeticFunction ℂ)
  let P : ArithmeticFunction ℂ :=
    ((ArithmeticFunction.pow 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
  have hz : LSeriesHasSum (fun n => Z n) w (riemannZeta w) := by
    dsimp [Z]
    exact ArithmeticFunction.LSeriesHasSum_zeta (by linarith)
  have hzshift : LSeriesHasSum (1 : ℕ → ℂ) (w - 1) (riemannZeta (w - 1)) := by
    have h := ArithmeticFunction.LSeriesHasSum_zeta (s := w - 1) (by
      rw [Complex.sub_re]
      norm_num
      linarith)
    exact (LSeriesHasSum_congr (w - 1) (riemannZeta (w - 1)) (fun {n} hn => by
      simp [ArithmeticFunction.zeta_apply, hn])).mp h
  have hpow : LSeriesHasSum (fun n : ℕ => (n : ℂ) ^ (1 : ℂ)) w
      (riemannZeta (w - 1)) := by
    exact hzshift.congr_fun fun n => RHTower.term_cpow_eq 1 w n
  have hp : LSeriesHasSum (fun n => P n) w (riemannZeta (w - 1)) := by
    refine hpow.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      simp [P, ArithmeticFunction.pow_apply]
  have hmul := ArithmeticFunction.LSeriesHasSum_mul hz hp
  have hconv : Z * P =
      ((ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    dsimp [Z, P]
    rw [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.zeta_mul_pow_eq_sigma]
  rw [hconv] at hmul
  exact hmul

/-- Classical divisor-sum identity in card equation `(9)`, on exact absolute-convergence
half-plane. -/
theorem sigmaOne_LSeries_eq_riemannZeta_mul {w : ℂ} (hw : 2 < w.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ)) w =
      riemannZeta w * riemannZeta (w - 1) :=
  (sigmaOne_LSeriesHasSum hw).LSeries_eq

theorem sigmaOne_LSeriesSummable {w : ℂ} (hw : 2 < w.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ)) w :=
  (sigmaOne_LSeriesHasSum hw).LSeriesSummable

/-- Every primitive level `s ≥ 3` is a literal bounded analytic disk multiplier, hence lies in
`H^∞(𝔻)`. -/
def hardyPrimitiveDiskMultiplier (s : ℕ) (hs : 3 ≤ s) : DiskMultiplier where
  fn := hardyPrimitiveJet s
  diff := (hardyPrimitiveJet_analyticOnNhd s).differentiableOn
  bd := ∑' n : ℕ, ‖(-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
    ((n + 1).ascFactorial s : ℂ)‖
  bd_nonneg := tsum_nonneg fun _ => norm_nonneg _
  bd_le := by
    intro q hq
    have hcoeff := summable_norm_hardyPrimitiveCoefficient hs
    have hqnorm : ‖q‖ < 1 := by simpa [mem_ball] using hq
    have hterm : Summable (fun n : ℕ => ‖hardyPrimitiveTerm s n q‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hcoeff
      rw [hardyPrimitiveTerm, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ (norm_nonneg q) hqnorm.le)
    calc
      ‖hardyPrimitiveJet s q‖ ≤ ∑' n : ℕ, ‖hardyPrimitiveTerm s n q‖ := by
        exact norm_tsum_le_tsum_norm hterm
      _ ≤ ∑' n : ℕ, ‖(-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) /
          ((n + 1).ascFactorial s : ℂ)‖ := by
        exact Summable.tsum_le_tsum (fun n => by
            rw [hardyPrimitiveTerm, norm_mul, norm_pow]
            exact mul_le_of_le_one_right (by positivity)
              (pow_le_one₀ (norm_nonneg q) hqnorm.le)) hterm hcoeff

/-- Every observed derivative through level `r` is represented by a bounded analytic disk
multiplier when primitive depth is `r + 3`. -/
theorem exists_diskMultiplier_iteratedDeriv_hardyPrimitiveJet
    (r j : ℕ) (hj : j ≤ r) :
    ∃ φ : DiskMultiplier,
      EqOn φ.fn (iteratedDeriv j (hardyPrimitiveJet (r + 3))) (ball (0 : ℂ) 1) := by
  have hlevel : 3 ≤ r + 3 - j := by omega
  refine ⟨hardyPrimitiveDiskMultiplier (r + 3 - j) hlevel, ?_⟩
  intro q hq
  exact (iteratedDeriv_hardyPrimitiveJet_eq (r + 3) j (by omega) hq).symm

/-- Derivatives above primitive depth are corresponding positive-order derivatives of `E₂`; the
subtracted constant disappears after first derivative. -/
theorem iteratedDeriv_hardyPrimitiveJet_add (m k : ℕ) (hk : 1 ≤ k) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) 1) :
    iteratedDeriv (m + k) (hardyPrimitiveJet m) q = iteratedDeriv k e2Disk q := by
  induction k generalizing q with
  | zero => omega
  | succ k ih =>
      rcases eq_or_ne k 0 with rfl | hk0
      · have hlocal : iteratedDeriv m (hardyPrimitiveJet m) =ᶠ[𝓝 q]
            (fun z => e2Disk z - 1) := by
          filter_upwards [isOpen_ball.mem_nhds hq] with z hz
          exact iteratedDeriv_hardyPrimitiveJet_self m hz
        have he2 := (e2Disk_analyticOnNhd q hq).differentiableAt.hasDerivAt.sub_const 1
        rw [iteratedDeriv_succ, hlocal.deriv_eq]
        rw [he2.deriv, iteratedDeriv_succ]
        rfl
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hlocal : iteratedDeriv (m + k) (hardyPrimitiveJet m) =ᶠ[𝓝 q]
            iteratedDeriv k e2Disk := by
          filter_upwards [isOpen_ball.mem_nhds hq] with z hz
          exact ih hk1 hz
        have he2 := hasDerivAt_iteratedDeriv_of_analyticOnNhd
          e2Disk_analyticOnNhd k hq
        rw [show m + (k + 1) = (m + k) + 1 by omega,
          iteratedDeriv_succ, hlocal.deriv_eq, iteratedDeriv_succ]

/-- Analytic continuation is stable under every finite iterated derivative. -/
theorem continuesAcross_iteratedDeriv {f : ℂ → ℂ} {ζ : ℂ} (n : ℕ)
    (h : Bottcher.ContinuesAcross f ζ) :
    Bottcher.ContinuesAcross (iteratedDeriv n f) ζ := by
  obtain ⟨U, hUo, hζU, G, hGd, hGeq⟩ := h
  have hGa : AnalyticOnNhd ℂ G U := hGd.analyticOnNhd hUo
  refine ⟨U, hUo, hζU, iteratedDeriv n G, ?_, ?_⟩
  · intro z hz
    exact (hasDerivAt_iteratedDeriv_of_analyticOnNhd hGa n hz).differentiableAt
      |>.differentiableWithinAt
  · intro z hz
    have heq : G =ᶠ[𝓝 z] f := by
      filter_upwards [(hUo.inter isOpen_ball).mem_nhds hz] with w hw
      exact hGeq hw
    exact heq.iteratedDeriv_eq n

/-- Continuation depends only on values on open unit disk. -/
theorem continuesAcross_congr_disk {f g : ℂ → ℂ} {ζ : ℂ}
    (hfg : EqOn f g (ball (0 : ℂ) 1))
    (h : Bottcher.ContinuesAcross f ζ) : Bottcher.ContinuesAcross g ζ := by
  obtain ⟨U, hUo, hζU, G, hGd, hGeq⟩ := h
  exact ⟨U, hUo, hζU, G, hGd, fun z hz => (hGeq hz).trans (hfg hz.2)⟩

theorem continuesAcross_add_const {f : ℂ → ℂ} {ζ c : ℂ}
    (h : Bottcher.ContinuesAcross f ζ) :
    Bottcher.ContinuesAcross (fun z => f z + c) ζ := by
  obtain ⟨U, hUo, hζU, G, hGd, hGeq⟩ := h
  refine ⟨U, hUo, hζU, fun z => G z + c, hGd.add_const c, ?_⟩
  intro z hz
  change G z + c = f z + c
  rw [hGeq hz]

/-- Every finite primitive retains pointwise unit-circle natural boundary. -/
theorem hardyPrimitiveJet_naturalBoundary (m : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ¬ Bottcher.ContinuesAcross (hardyPrimitiveJet m) ζ := by
  intro hcont
  have hm := continuesAcross_iteratedDeriv m hcont
  have hmEq : EqOn (iteratedDeriv m (hardyPrimitiveJet m))
      (fun q => e2Disk q - 1) (ball (0 : ℂ) 1) := by
    intro q hq
    exact iteratedDeriv_hardyPrimitiveJet_self m hq
  have hsub := continuesAcross_congr_disk hmEq hm
  have he2 := continuesAcross_add_const (c := (1 : ℂ)) hsub
  apply e2Disk_naturalBoundary hζ
  exact continuesAcross_congr_disk (fun q _ => by simp) he2

/-- Chazy polynomial after direct substitution `E₂ = F_m⁽ᵐ⁾ + 1`. -/
def hardyPrimitiveChazyPolynomial (m : ℕ) : MvPolynomial (Fin (m + 5)) ℂ :=
  let x := X (0 : Fin (m + 5))
  let y0 := X (⟨m + 1, by omega⟩ : Fin (m + 5)) + 1
  let y1 := X (⟨m + 2, by omega⟩ : Fin (m + 5))
  let y2 := X (⟨m + 3, by omega⟩ : Fin (m + 5))
  let y3 := X (⟨m + 4, by omega⟩ : Fin (m + 5))
  2 * (x * y1 + 3 * x ^ 2 * y2 + x ^ 3 * y3) -
    2 * y0 * (x * y1 + x ^ 2 * y2) + 3 * (x * y1) ^ 2

theorem hardyPrimitiveChazyPolynomial_ne_zero (m : ℕ) :
    hardyPrimitiveChazyPolynomial m ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin (m + 5) => (1 : ℂ))) h
  norm_num [hardyPrimitiveChazyPolynomial] at he

theorem hardyPrimitiveChazyPolynomial_eval (m : ℕ) (f : ℂ → ℂ) (q : ℂ) :
    MvPolynomial.eval
      (Fin.cons q (fun j : Fin (m + 4) => iteratedDeriv (j : ℕ) f q))
        (hardyPrimitiveChazyPolynomial m) =
      2 * (q * iteratedDeriv (m + 1) f q +
          3 * q ^ 2 * iteratedDeriv (m + 2) f q +
          q ^ 3 * iteratedDeriv (m + 3) f q) -
        2 * (iteratedDeriv m f q + 1) *
          (q * iteratedDeriv (m + 1) f q +
            q ^ 2 * iteratedDeriv (m + 2) f q) +
          3 * (q * iteratedDeriv (m + 1) f q) ^ 2 := by
  simp only [hardyPrimitiveChazyPolynomial, map_sub, map_add, map_mul, map_pow,
    map_ofNat, eval_X]
  simp [Fin.cons]

/-- Every finite primitive satisfies explicit nonzero ADE of order at most `m + 3`. -/
theorem hardyPrimitiveJet_differentiallyAlgebraicOn (m : ℕ) :
    DifferentiallyAlgebraicOn (hardyPrimitiveJet m) (ball (0 : ℂ) 1) := by
  refine ⟨m + 3, hardyPrimitiveChazyPolynomial m,
    hardyPrimitiveChazyPolynomial_ne_zero m, ?_⟩
  intro q hq
  rw [hardyPrimitiveChazyPolynomial_eval,
    iteratedDeriv_hardyPrimitiveJet_self m hq,
    iteratedDeriv_hardyPrimitiveJet_add m 1 (by omega) hq,
    iteratedDeriv_hardyPrimitiveJet_add m 2 (by omega) hq,
    iteratedDeriv_hardyPrimitiveJet_add m 3 (by omega) hq]
  have h2 := eulerDeriv_two_eq e2Disk_analyticOnNhd hq
  have h3 := eulerDeriv_three_eq e2Disk_analyticOnNhd isOpen_ball hq
  have hc := e2DiskChazyDefect_eq_zero hq
  unfold e2DiskChazyDefect at hc
  rw [h2, h3] at hc
  have h1 : eulerDeriv e2Disk q = q * iteratedDeriv 1 e2Disk q := by
    simp [eulerDeriv, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1] at hc
  simpa only [sub_add_cancel, Pi.zero_apply] using hc

/-- Exact paper formula `(5)` with factorial-ratio coefficients. -/
theorem hardyPrimitiveJet_eq_factorialRatioSeries (m : ℕ) (q : ℂ) :
    hardyPrimitiveJet m q =
      ∑' n : ℕ, (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
        (n.factorial : ℂ) / ((n + m).factorial : ℂ) * q ^ (n + m) := by
  unfold hardyPrimitiveJet
  exact tsum_congr fun n => hardyPrimitiveTerm_eq_factorialRatio m n q

/-- Exact derivative-series formula `(8)`. -/
theorem iteratedDeriv_hardyPrimitiveJet_eq_factorialRatioSeries
    (m j : ℕ) (hj : j ≤ m) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) :
    iteratedDeriv j (hardyPrimitiveJet m) q =
      ∑' n : ℕ, (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
        (n.factorial : ℂ) / ((n + (m - j)).factorial : ℂ) *
          q ^ (n + (m - j)) := by
  rw [iteratedDeriv_hardyPrimitiveJet_eq m j hj hq]
  exact hardyPrimitiveJet_eq_factorialRatioSeries (m - j) q

/-- Finite Hardy-jet natural-boundary saturation law.  At every prescribed finite depth `r`, the
explicit `(r+3)`-fold primitive is holomorphic and DA on disk, all observed derivatives are
`H^∞` disk multipliers, and every unit-circle point blocks analytic continuation. -/
theorem finiteHardyJet_da_naturalBoundary_saturation (r : ℕ) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball (0 : ℂ) 1) ∧
      DifferentiallyAlgebraicOn F (ball (0 : ℂ) 1) ∧
      (∀ j ≤ r, ∃ φ : DiskMultiplier,
        EqOn φ.fn (iteratedDeriv j F) (ball (0 : ℂ) 1)) ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → ¬ Bottcher.ContinuesAcross F ζ := by
  refine ⟨hardyPrimitiveJet (r + 3), hardyPrimitiveJet_analyticOnNhd (r + 3),
    hardyPrimitiveJet_differentiallyAlgebraicOn (r + 3), ?_, ?_⟩
  · intro j hj
    exact exists_diskMultiplier_iteratedDeriv_hardyPrimitiveJet r j hj
  · intro ζ hζ
    exact hardyPrimitiveJet_naturalBoundary (r + 3) hζ

end

end GaloisForLFunctions.HTGeometry
