import GaloisForLFunctions.RHTower.EulerFisherCurvature
import Mathlib

open Complex Filter

namespace RHTower

noncomputable section

/-- The Gamma–Meixner time-`θ` prime weight `w_θ(p) = cosh (2 log p) ^ (-θ/2)`. -/
def meixnerPrimeWeight (θ : ℝ) (n : ℕ) : ℝ := (Real.cosh (2 * Real.log n)) ^ (-θ / 2)

theorem meixnerPrimeWeight_pos (θ : ℝ) (n : ℕ) : 0 < meixnerPrimeWeight θ n :=
  Real.rpow_pos_of_pos (Real.cosh_pos _) _

theorem cosh_two_log_ge {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ 2) / 2 ≤ Real.cosh (2 * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
    rw [mul_comm, ← Real.rpow_def_of_pos hn0]
    exact_mod_cast Real.rpow_natCast (n : ℝ) 2
  have hpos : 0 < Real.exp (-(2 * Real.log n)) := Real.exp_pos _
  rw [Real.cosh_eq, hexp]
  linarith

theorem meixnerPrimeWeight_le (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (hn : 1 ≤ n) :
    meixnerPrimeWeight θ n ≤ 2 ^ (θ / 2) * (n : ℝ) ^ (-θ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcosh := cosh_two_log_ge hn
  have hbase : (0 : ℝ) < (n : ℝ) ^ 2 / 2 := by positivity
  have hmono : (Real.cosh (2 * Real.log n)) ^ (-θ / 2) ≤ ((n : ℝ) ^ 2 / 2) ^ (-θ / 2) :=
    Real.rpow_le_rpow_of_nonpos hbase hcosh (by linarith)
  refine hmono.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by norm_num)]
  rw [← Real.rpow_natCast ((n : ℝ)) 2, ← Real.rpow_mul hn0.le]
  rw [show ((2 : ℕ) : ℝ) * (-θ / 2) = -θ by push_cast; ring]
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    show (-(-θ / 2)) = θ / 2 by ring, mul_comm]

theorem sqrt_meixnerPrimeWeight (θ : ℝ) (n : ℕ) :
    Real.sqrt (meixnerPrimeWeight θ n) = meixnerPrimeWeight (θ / 2) n := by
  rw [meixnerPrimeWeight, meixnerPrimeWeight, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Real.cosh_pos _).le]
  congr 1
  ring

/-- The prime-supported Dirichlet coefficients of a prime coefficient vector. -/
def primeLaplaceCoeff (θ : ℝ) (a : Nat.Primes → ℂ) (n : ℕ) : ℂ :=
  if h : n.Prime then a ⟨n, h⟩ * (Real.sqrt (meixnerPrimeWeight θ n) : ℂ) else 0

@[simp]
theorem primeLaplaceCoeff_zero (θ : ℝ) (a : Nat.Primes → ℂ) : primeLaplaceCoeff θ a 0 = 0 := by
  simp [primeLaplaceCoeff, Nat.not_prime_zero]

theorem primeLaplaceCoeff_prime (θ : ℝ) (a : Nat.Primes → ℂ) (p : Nat.Primes) :
    primeLaplaceCoeff θ a (p : ℕ) = a p * (Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) : ℂ) := by
  rw [primeLaplaceCoeff, dif_pos p.2]
  congr 2

theorem norm_primeLaplaceCoeff_le (θ : ℝ) (hθ : 0 ≤ θ) (a : Nat.Primes → ℂ) (n : ℕ) :
    ‖primeLaplaceCoeff θ a n‖ ≤
      (if h : n.Prime then ‖a ⟨n, h⟩‖ * (2 ^ (θ / 4) * (n : ℝ) ^ (-θ / 2)) else 0) := by
  rw [primeLaplaceCoeff]
  by_cases h : n.Prime
  · rw [dif_pos h, dif_pos h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), sqrt_meixnerPrimeWeight]
    have hbound := meixnerPrimeWeight_le (θ / 2) (by linarith) (n := n) h.one_lt.le
    have hb : 2 ^ (θ / 2 / 2) * (n : ℝ) ^ (-(θ / 2)) = 2 ^ (θ / 4) * (n : ℝ) ^ (-θ / 2) := by
      rw [show θ / 2 / 2 = θ / 4 by ring, show -(θ / 2) = -θ / 2 by ring]
    rw [hb] at hbound
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  · simp [h]

theorem norm_term_primeLaplaceCoeff_eq_zero {θ : ℝ} {a : Nat.Primes → ℂ} {s : ℂ} {n : ℕ}
    (hn : ¬ n.Prime) : ‖LSeries.term (primeLaplaceCoeff θ a) s n‖ = 0 := by
  have hc : primeLaplaceCoeff θ a n = 0 := by
    rw [primeLaplaceCoeff, dif_neg hn]
  rcases eq_or_ne n 0 with h0 | h0
  · simp [LSeries.term, h0]
  · simp [LSeries.term, h0, hc]

/-- **Absolute convergence of the weighted prime–Laplace transform.**  Cauchy–Schwarz against the
square-summable coefficient vector places the abscissa at `(1 - θ)/2`. -/
theorem lSeriesSummable_primeLaplaceCoeff {θ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) {s : ℂ} (hs : (1 - θ) / 2 < s.re) :
    LSeriesSummable (primeLaplaceCoeff θ a) s := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun p q h => Subtype.ext h
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun p : Nat.Primes => (p : ℕ)) →
      ‖LSeries.term (primeLaplaceCoeff θ a) s n‖ = 0 := by
    intro n hn
    refine norm_term_primeLaplaceCoeff_eq_zero (θ := θ) (a := a) (s := s) fun hprime => ?_
    exact hn ⟨⟨n, hprime⟩, rfl⟩
  have hpow : Summable fun n : ℕ => (n : ℝ) ^ (-θ - 2 * s.re) := by
    have hgt : 1 < θ + 2 * s.re := by linarith
    have := Real.summable_nat_rpow.mpr (show -θ - 2 * s.re < -1 by linarith)
    exact this
  have hpowsub : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-θ - 2 * s.re) :=
    hpow.subtype _
  have hmaj : Summable fun p : Nat.Primes =>
      2 ^ (θ / 4) / 2 * (‖a p‖ ^ 2 + ((p : ℕ) : ℝ) ^ (-θ - 2 * s.re)) :=
    (ha.add hpowsub).mul_left _
  have hsub : Summable fun p : Nat.Primes => ‖LSeries.term (primeLaplaceCoeff θ a) s (p : ℕ)‖ := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hmaj
    have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.2.one_lt.le.trans' (by norm_num)
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hne : ((p : ℕ) : ℕ) ≠ 0 := p.2.ne_zero
    rw [LSeries.norm_term_eq, if_neg hne]
    have hcoeff := norm_primeLaplaceCoeff_le θ hθ a (p : ℕ)
    rw [dif_pos p.2] at hcoeff
    have hpow' : ((p : ℕ) : ℝ) ^ s.re ≠ 0 := by positivity
    have hdiv : ‖primeLaplaceCoeff θ a (p : ℕ)‖ / ((p : ℕ) : ℝ) ^ s.re
        ≤ ‖a ⟨(p : ℕ), p.2⟩‖ * (2 ^ (θ / 4) * ((p : ℕ) : ℝ) ^ (-θ / 2)) / ((p : ℕ) : ℝ) ^ s.re := by
      apply div_le_div_of_nonneg_right hcoeff
      positivity
    refine hdiv.trans ?_
    have hcast : a ⟨(p : ℕ), p.2⟩ = a p := by congr 1
    rw [hcast]
    have hsplit : ‖a p‖ * (2 ^ (θ / 4) * ((p : ℕ) : ℝ) ^ (-θ / 2)) / ((p : ℕ) : ℝ) ^ s.re
        = 2 ^ (θ / 4) * (‖a p‖ * ((p : ℕ) : ℝ) ^ (-θ / 2 - s.re)) := by
      rw [Real.rpow_sub hp0]
      field_simp
    rw [hsplit]
    have hamgm : ‖a p‖ * ((p : ℕ) : ℝ) ^ (-θ / 2 - s.re)
        ≤ (‖a p‖ ^ 2 + ((p : ℕ) : ℝ) ^ (-θ - 2 * s.re)) / 2 := by
      have hsq : (((p : ℕ) : ℝ) ^ (-θ / 2 - s.re)) ^ 2 = ((p : ℕ) : ℝ) ^ (-θ - 2 * s.re) := by
        rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-θ / 2 - s.re)) 2, ← Real.rpow_mul hp0.le]
        congr 1
        push_cast
        ring
      nlinarith [sq_nonneg (‖a p‖ - ((p : ℕ) : ℝ) ^ (-θ / 2 - s.re)), hsq]
    have h2 : (0 : ℝ) < 2 ^ (θ / 4) := by positivity
    calc 2 ^ (θ / 4) * (‖a p‖ * ((p : ℕ) : ℝ) ^ (-θ / 2 - s.re))
        ≤ 2 ^ (θ / 4) * ((‖a p‖ ^ 2 + ((p : ℕ) : ℝ) ^ (-θ - 2 * s.re)) / 2) :=
          mul_le_mul_of_nonneg_left hamgm h2.le
      _ = 2 ^ (θ / 4) / 2 * (‖a p‖ ^ 2 + ((p : ℕ) : ℝ) ^ (-θ - 2 * s.re)) := by ring
  have hnorm : Summable fun n : ℕ => ‖LSeries.term (primeLaplaceCoeff θ a) s n‖ :=
    (hinj.summable_iff hzero).mp hsub
  exact hnorm.of_norm

open LSeries in
theorem abscissaOfAbsConv_primeLaplaceCoeff_le {θ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) :
    abscissaOfAbsConv (primeLaplaceCoeff θ a) ≤ (((1 - θ) / 2 : ℝ) : EReal) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact lSeriesSummable_primeLaplaceCoeff hθ ha (by simpa using hy)

/-- **Joint faithfulness of the finite jet clocks.**  If every raw derivative of the weighted
prime–Laplace transform vanishes at one base point of the convergence half plane, the prime
coefficient vector is zero. -/
theorem eq_zero_of_forall_iteratedDeriv_eq_zero {θ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) {x₀ : ℝ} (hx₀ : (1 - θ) / 2 < x₀)
    (h : ∀ j : ℕ, iteratedDeriv j (LSeries (primeLaplaceCoeff θ a)) (x₀ : ℂ) = 0) :
    a = 0 := by
  classical
  set f := primeLaplaceCoeff θ a with hf
  set U : Set ℂ := {s : ℂ | LSeries.abscissaOfAbsConv f < (s.re : EReal)} with hU
  have habs : LSeries.abscissaOfAbsConv f ≤ (((1 - θ) / 2 : ℝ) : EReal) :=
    abscissaOfAbsConv_primeLaplaceCoeff_le hθ ha
  have hmem : ∀ y : ℝ, (1 - θ) / 2 < y → ((y : ℂ)) ∈ U := by
    intro y hy
    have : LSeries.abscissaOfAbsConv f < ((y : ℝ) : EReal) :=
      lt_of_le_of_lt habs (by exact_mod_cast hy)
    simpa [hU] using this
  have hx₀mem : ((x₀ : ℂ)) ∈ U := hmem x₀ hx₀
  have hana : AnalyticOnNhd ℂ (LSeries f) U := LSeries_analyticOnNhd f
  have hanaAt : AnalyticAt ℂ (LSeries f) (x₀ : ℂ) := hana _ hx₀mem
  have horder : analyticOrderAt (LSeries f) (x₀ : ℂ) = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanaAt).mpr fun i _ => h i
  have hev : ∀ᶠ z in nhds ((x₀ : ℂ)), LSeries f z = 0 := analyticOrderAt_eq_top.mp horder
  set V : Set ℂ := {s : ℂ | (1 - θ) / 2 < s.re} with hV
  have hVU : V ⊆ U := by
    intro s hs
    have : LSeries.abscissaOfAbsConv f < ((s.re : ℝ) : EReal) :=
      lt_of_le_of_lt habs (by exact_mod_cast hs)
    simpa [hU] using this
  have hconvV : Convex ℝ V := convex_halfSpace_re_gt ((1 - θ) / 2)
  have hx₀V : ((x₀ : ℂ)) ∈ V := by simpa [hV] using hx₀
  have hzero : Set.EqOn (LSeries f) 0 V :=
    (hana.mono hVU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconvV.isPreconnected hx₀V hev
  have hatTop : (fun x : ℝ => LSeries f (x : ℂ)) =ᶠ[Filter.atTop] 0 := by
    filter_upwards [Filter.eventually_gt_atTop ((1 - θ) / 2)] with y hy
    exact hzero (by simpa [hV] using hy)
  have hcoeff : ∀ n : ℕ, n ≠ 0 → f n = 0 := by
    rcases LSeries_eventually_eq_zero_iff'.mp hatTop with hzeroc | htop
    · exact hzeroc
    · exact absurd htop (by
        intro hcon
        rw [hcon] at habs
        exact absurd habs (by simp))
  funext p
  have hp := hcoeff (p : ℕ) p.2.ne_zero
  rw [hf, primeLaplaceCoeff_prime] at hp
  have hw : Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (meixnerPrimeWeight_pos θ _))
  have hwc : ((Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hw
  simpa [hwc] using mul_eq_zero.mp hp

theorem logMul_iterate (j : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    (LSeries.logMul^[j] f) n = (Real.log n : ℂ) ^ j * f n := by
  induction j generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (LSeries.logMul f)]
    simp [LSeries.logMul, pow_succ]
    ring

/-- **The raw jet coordinates of the weighted prime–Laplace transform.**  The `j`-th derivative at
a point of the convergence half plane is the prime series with the extra factor `(-log p)^j`. -/
theorem iteratedDeriv_primeLaplace_eq {θ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) {s : ℂ} (hs : (1 - θ) / 2 < s.re) (j : ℕ) :
    iteratedDeriv j (LSeries (primeLaplaceCoeff θ a)) s
      = LSeries (fun n : ℕ => (-(Real.log n : ℂ)) ^ j * primeLaplaceCoeff θ a n) s := by
  have habs : LSeries.abscissaOfAbsConv (primeLaplaceCoeff θ a) < (s.re : EReal) :=
    lt_of_le_of_lt (abscissaOfAbsConv_primeLaplaceCoeff_le hθ ha) (by exact_mod_cast hs)
  rw [LSeries_iteratedDeriv j habs]
  rw [← LSeries_smul]
  congr 1
  funext n
  simp only [Pi.smul_apply, smul_eq_mul, logMul_iterate]
  rw [neg_pow]
  ring

/-- The factorial-metric norm square of the jet column of one prime. -/
def primeJetColumnFactorialNormSq (θ x₀ : ℝ) (N : ℕ) (p : Nat.Primes) : ℝ :=
  meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) *
    ∑ j ∈ Finset.range N, (Real.log ((p : ℕ) : ℝ)) ^ (2 * j) / (j.factorial : ℝ)

theorem sum_range_log_pow_div_factorial_le (N : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range N, x ^ (2 * j) / (j.factorial : ℝ) ≤ (N : ℝ) * (1 + |x| ^ (2 * N)) := by
  have hterm : ∀ j ∈ Finset.range N, x ^ (2 * j) / (j.factorial : ℝ) ≤ 1 + |x| ^ (2 * N) := by
    intro j hj
    have hjN : j ≤ N := (Finset.mem_range.mp hj).le
    have hfac : (1 : ℝ) ≤ (j.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hnn0 : (0 : ℝ) ≤ x ^ (2 * j) := by
      rw [pow_mul]
      positivity
    have habs : x ^ (2 * j) = |x| ^ (2 * j) := by
      rw [← abs_pow, abs_of_nonneg hnn0]
    have hpow : x ^ (2 * j) ≤ 1 + |x| ^ (2 * N) := by
      rcases le_or_gt |x| 1 with hx | hx
      · have hle : |x| ^ (2 * j) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
        have hnn : (0 : ℝ) ≤ |x| ^ (2 * N) := by positivity
        rw [habs]
        linarith
      · have hle : |x| ^ (2 * j) ≤ |x| ^ (2 * N) := pow_le_pow_right₀ hx.le (by omega)
        rw [habs]
        linarith
    have hdiv : x ^ (2 * j) / (j.factorial : ℝ) ≤ x ^ (2 * j) := div_le_self hnn0 hfac
    linarith
  calc ∑ j ∈ Finset.range N, x ^ (2 * j) / (j.factorial : ℝ)
      ≤ ∑ _j ∈ Finset.range N, (1 + |x| ^ (2 * N)) := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (1 + |x| ^ (2 * N)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Every finite jet clock receives the prime source Hilbert–Schmidtly.**  The sum over the
primes of the factorial-metric column norms is finite. -/
theorem summable_primeJetColumnFactorialNormSq {θ x₀ : ℝ} (hθ : 0 ≤ θ)
    (hx : (1 - θ) / 2 < x₀) (N : ℕ) :
    Summable (primeJetColumnFactorialNormSq θ x₀ N) := by
  have hβ : 1 < θ + 2 * x₀ := by linarith
  have hlog : Summable fun n : ℕ => |Real.log (n : ℝ)| ^ (2 * N) * (n : ℝ) ^ (-(θ + 2 * x₀)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg (2 * N) (θ + 2 * x₀) hβ
  have hlogp : Summable fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| ^ (2 * N) * (((p : ℕ) : ℝ)) ^ (-(θ + 2 * x₀)) :=
    hlog.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  have hpow : Summable fun n : ℕ => (n : ℝ) ^ (-(θ + 2 * x₀)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hpowp : Summable fun p : Nat.Primes => (((p : ℕ) : ℝ)) ^ (-(θ + 2 * x₀)) :=
    hpow.subtype _
  have hmaj : Summable fun p : Nat.Primes =>
      2 ^ (θ / 2) * (N : ℝ) *
        ((((p : ℕ) : ℝ)) ^ (-(θ + 2 * x₀)) +
          |Real.log ((p : ℕ) : ℝ)| ^ (2 * N) * (((p : ℕ) : ℝ)) ^ (-(θ + 2 * x₀))) :=
    ((hpowp.add hlogp)).mul_left _
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
  · refine mul_nonneg (mul_nonneg (meixnerPrimeWeight_pos θ _).le (by positivity)) ?_
    refine Finset.sum_nonneg fun j _ => ?_
    have hnn : (0 : ℝ) ≤ (Real.log ((p : ℕ) : ℝ)) ^ (2 * j) := by
      rw [pow_mul]
      positivity
    positivity
  · have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.2.one_lt.le.trans' (by norm_num)
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hw := meixnerPrimeWeight_le θ hθ (n := (p : ℕ)) hp1
    have hsum := sum_range_log_pow_div_factorial_le N (Real.log ((p : ℕ) : ℝ))
    have hsumnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range N,
        (Real.log ((p : ℕ) : ℝ)) ^ (2 * j) / (j.factorial : ℝ) := by
      refine Finset.sum_nonneg fun j _ => ?_
      have hnn : (0 : ℝ) ≤ (Real.log ((p : ℕ) : ℝ)) ^ (2 * j) := by
        rw [pow_mul]
        positivity
      positivity
    have hrpow : ((p : ℕ) : ℝ) ^ (-θ) * ((p : ℕ) : ℝ) ^ (-2 * x₀)
        = ((p : ℕ) : ℝ) ^ (-(θ + 2 * x₀)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    calc primeJetColumnFactorialNormSq θ x₀ N p
        ≤ (2 ^ (θ / 2) * ((p : ℕ) : ℝ) ^ (-θ)) * ((p : ℕ) : ℝ) ^ (-2 * x₀) *
            ((N : ℝ) * (1 + |Real.log ((p : ℕ) : ℝ)| ^ (2 * N))) := by
          rw [primeJetColumnFactorialNormSq]
          have h1 : meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀)
              ≤ 2 ^ (θ / 2) * ((p : ℕ) : ℝ) ^ (-θ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) := by
            have hnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-2 * x₀) := by positivity
            exact mul_le_mul_of_nonneg_right hw hnn
          have hnn2 : (0 : ℝ) ≤ 2 ^ (θ / 2) * ((p : ℕ) : ℝ) ^ (-θ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) := by
            positivity
          have hnn3 : (0 : ℝ) ≤ meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) := by
            have := (meixnerPrimeWeight_pos θ (p : ℕ)).le
            positivity
          calc meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) *
                ∑ j ∈ Finset.range N, (Real.log ((p : ℕ) : ℝ)) ^ (2 * j) / (j.factorial : ℝ)
              ≤ meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) *
                ((N : ℝ) * (1 + |Real.log ((p : ℕ) : ℝ)| ^ (2 * N))) :=
                mul_le_mul_of_nonneg_left hsum hnn3
            _ ≤ 2 ^ (θ / 2) * ((p : ℕ) : ℝ) ^ (-θ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) *
                ((N : ℝ) * (1 + |Real.log ((p : ℕ) : ℝ)| ^ (2 * N))) := by
                refine mul_le_mul_of_nonneg_right h1 ?_
                have : (0 : ℝ) ≤ |Real.log ((p : ℕ) : ℝ)| ^ (2 * N) := by positivity
                positivity
      _ = 2 ^ (θ / 2) * (N : ℝ) *
            (((p : ℕ) : ℝ) ^ (-(θ + 2 * x₀)) +
              |Real.log ((p : ℕ) : ℝ)| ^ (2 * N) * ((p : ℕ) : ℝ) ^ (-(θ + 2 * x₀))) := by
          rw [← hrpow]
          ring

/-- The factorial (Fock) metric norm square of the full coherent jet column of one prime. -/
def primeFockColumnNormSq (θ x₀ : ℝ) (p : Nat.Primes) : ℝ :=
  meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀) *
    Real.exp ((Real.log ((p : ℕ) : ℝ)) ^ 2)

/-- **The exact coherent-jet column norm.**  Summing the factorial-weighted raw jet coordinates of
one prime gives the Gaussian factor `exp ((log p)²)`. -/
theorem tsum_primeJetColumn_eq_primeFockColumnNormSq (θ x₀ : ℝ) (p : Nat.Primes) :
    (meixnerPrimeWeight θ (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x₀)) *
        ∑' j : ℕ, (Real.log ((p : ℕ) : ℝ)) ^ (2 * j) / (j.factorial : ℝ)
      = primeFockColumnNormSq θ x₀ p := by
  have hpow : ∀ j : ℕ, (Real.log ((p : ℕ) : ℝ)) ^ (2 * j)
      = ((Real.log ((p : ℕ) : ℝ)) ^ 2) ^ j := by
    intro j
    rw [pow_mul]
  rw [primeFockColumnNormSq]
  congr 1
  simp only [hpow]
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem meixnerPrimeWeight_ge (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ)) ^ (-θ) ≤ meixnerPrimeWeight θ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcosh : Real.cosh (2 * Real.log n) ≤ (n : ℝ) ^ 2 := by
    have hexp : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
      rw [mul_comm, ← Real.rpow_def_of_pos hn0]
      exact_mod_cast Real.rpow_natCast (n : ℝ) 2
    have hle : Real.exp (-(2 * Real.log n)) ≤ Real.exp (2 * Real.log n) := by
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      linarith
    rw [Real.cosh_eq, hexp] at *
    linarith
  have hpos : (0 : ℝ) < Real.cosh (2 * Real.log n) := Real.cosh_pos _
  have hmono : ((n : ℝ) ^ 2) ^ (-θ / 2) ≤ (Real.cosh (2 * Real.log n)) ^ (-θ / 2) :=
    Real.rpow_le_rpow_of_nonpos hpos hcosh (by linarith)
  refine le_trans (le_of_eq ?_) hmono
  rw [← Real.rpow_natCast ((n : ℝ)) 2, ← Real.rpow_mul hn0.le]
  congr 1
  push_cast
  ring

/-- **The factorial Fock colimit is unbounded.**  No constant bounds the coherent-jet column
norms, so the infinite jet observation is not a bounded operator for any positive shape. -/
theorem not_bddAbove_primeFockColumnNormSq {θ x₀ : ℝ} (hθ : 0 ≤ θ) :
    ¬ ∃ C : ℝ, ∀ p : Nat.Primes, primeFockColumnNormSq θ x₀ p ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨q, hqle, hq⟩ :=
    Nat.exists_infinite_primes (max (Nat.ceil (Real.exp (θ + 2 * x₀ + 1))) (Nat.ceil C) + 1)
  set p : Nat.Primes := ⟨q, hq⟩ with hp
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := hq.pos
    exact_mod_cast this
  have hq1 : (1 : ℕ) ≤ q := hq.one_lt.le.trans' (by norm_num)
  have hlogq : θ + 2 * x₀ + 1 ≤ Real.log (q : ℝ) := by
    have hexple : Real.exp (θ + 2 * x₀ + 1) ≤ (q : ℝ) := by
      have h1 : Real.exp (θ + 2 * x₀ + 1) ≤ (Nat.ceil (Real.exp (θ + 2 * x₀ + 1)) : ℝ) :=
        Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp (θ + 2 * x₀ + 1)) : ℕ) : ℝ) ≤ (q : ℝ) := by
        have : (Nat.ceil (Real.exp (θ + 2 * x₀ + 1)) : ℕ) ≤ q := le_trans (le_trans (le_max_left _ _)
          (Nat.le_succ _)) hqle
        exact_mod_cast this
      linarith
    have := Real.log_le_log (Real.exp_pos _) hexple
    rwa [Real.log_exp] at this
  have hCq : C + 1 ≤ (q : ℝ) := by
    have h1 : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil C : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
      have hnat : (Nat.ceil C : ℕ) + 1 ≤ q :=
        le_trans (Nat.succ_le_succ (le_max_right _ _)) hqle
      exact_mod_cast hnat
    linarith
  have hlower : (q : ℝ) ≤ primeFockColumnNormSq θ x₀ p := by
    have hw : ((q : ℝ)) ^ (-θ) ≤ meixnerPrimeWeight θ q := meixnerPrimeWeight_ge θ hθ hq1
    have hexp : Real.exp (Real.log (q : ℝ))
        ≤ Real.exp ((Real.log (q : ℝ)) ^ 2 - (θ + 2 * x₀) * Real.log (q : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hlogq, Real.log_natCast_nonneg q]
    have hsplit : ((q : ℝ)) ^ (-θ) * ((q : ℝ)) ^ (-2 * x₀)
        = Real.exp (-(θ + 2 * x₀) * Real.log (q : ℝ)) := by
      rw [← Real.rpow_add hq0, Real.rpow_def_of_pos hq0]
      congr 1
      ring
    have hpos2 : (0 : ℝ) < ((q : ℝ)) ^ (-2 * x₀) := by positivity
    calc (q : ℝ) = Real.exp (Real.log (q : ℝ)) := (Real.exp_log hq0).symm
      _ ≤ Real.exp ((Real.log (q : ℝ)) ^ 2 - (θ + 2 * x₀) * Real.log (q : ℝ)) := hexp
      _ = Real.exp (-(θ + 2 * x₀) * Real.log (q : ℝ)) * Real.exp ((Real.log (q : ℝ)) ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ = (((q : ℝ)) ^ (-θ) * ((q : ℝ)) ^ (-2 * x₀)) * Real.exp ((Real.log (q : ℝ)) ^ 2) := by
          rw [hsplit]
      _ ≤ (meixnerPrimeWeight θ q * ((q : ℝ)) ^ (-2 * x₀)) * Real.exp ((Real.log (q : ℝ)) ^ 2) := by
          have hnn : (0 : ℝ) ≤ Real.exp ((Real.log (q : ℝ)) ^ 2) := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hw hpos2.le) hnn
      _ = primeFockColumnNormSq θ x₀ p := by
          rw [primeFockColumnNormSq, hp]
  have := hC p
  linarith

/-! ### The unit source translation and its Gamma clock shadow -/

/-- The prime source translation `(S a) p = p⁻¹ a p`. -/
def primeSourceShift (a : Nat.Primes → ℂ) : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ)⁻¹ * a p

theorem summable_primeSourceShift {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) :
    Summable fun p : Nat.Primes => ‖primeSourceShift a p‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) ha
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hnorm : ‖primeSourceShift a p‖ = ((p : ℕ) : ℝ)⁻¹ * ‖a p‖ := by
    rw [primeSourceShift, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hnorm, mul_pow]
  have hinv : (((p : ℕ) : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have : ((p : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hp1
    nlinarith [inv_nonneg.mpr hp0.le]
  nlinarith [sq_nonneg ‖a p‖, norm_nonneg (a p)]

theorem primeLaplaceCoeff_primeSourceShift (θ : ℝ) (a : Nat.Primes → ℂ) (n : ℕ) :
    primeLaplaceCoeff θ (primeSourceShift a) n = ((n : ℂ))⁻¹ * primeLaplaceCoeff θ a n := by
  rw [primeLaplaceCoeff, primeLaplaceCoeff]
  by_cases h : n.Prime
  · rw [dif_pos h, dif_pos h, primeSourceShift]
    ring
  · rw [dif_neg h, dif_neg h, mul_zero]

/-- **Unit translation of the transform.**  Multiplying the prime coefficients by `p⁻¹` translates
the weighted prime–Laplace transform by one. -/
theorem lSeries_primeSourceShift (θ : ℝ) (a : Nat.Primes → ℂ) (s : ℂ) :
    LSeries (primeLaplaceCoeff θ (primeSourceShift a)) s
      = LSeries (primeLaplaceCoeff θ a) (s + 1) := by
  rw [LSeries, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      primeLaplaceCoeff_primeSourceShift, Complex.cpow_add _ _ hn0, Complex.cpow_one]
    field_simp

/-- The raw derivative jet of the weighted prime–Laplace transform at the base point. -/
def primeLaplaceJet (θ x₀ : ℝ) (a : Nat.Primes → ℂ) (j : ℕ) : ℂ :=
  iteratedDeriv j (LSeries (primeLaplaceCoeff θ a)) (x₀ : ℂ)

theorem primeLaplaceJet_primeSourceShift (θ x₀ : ℝ) (a : Nat.Primes → ℂ) (j : ℕ) :
    primeLaplaceJet θ x₀ (primeSourceShift a) j
      = iteratedDeriv j (LSeries (primeLaplaceCoeff θ a)) ((x₀ : ℂ) + 1) := by
  have hfun : LSeries (primeLaplaceCoeff θ (primeSourceShift a))
      = fun s : ℂ => LSeries (primeLaplaceCoeff θ a) (s + 1) := by
    funext s
    exact lSeries_primeSourceShift θ a s
  rw [primeLaplaceJet, hfun, iteratedDeriv_comp_add_const]

/-- The Gamma clock shadow of unit translation on the first `N` raw derivatives. -/
def gammaClockShadowSum (N : ℕ) (y : ℕ → ℂ) (i : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N - i), y (i + k) / (k.factorial : ℂ)

/-- The source-to-clock descent anomaly of the prime translation. -/
def primeLaplaceDescentAnomaly (θ x₀ : ℝ) (N : ℕ) (a : Nat.Primes → ℂ) (i : ℕ) : ℂ :=
  gammaClockShadowSum N (primeLaplaceJet θ x₀ a) i
    - primeLaplaceJet θ x₀ (primeSourceShift a) i

/-- **Taylor descent of the raw jets.**  On a base point at distance more than one from the
abscissa, the shifted jet is the convergent sum of the higher jets with factorial weights. -/
theorem hasSum_taylor_primeLaplaceJet {θ x₀ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) (hx₀ : (1 - θ) / 2 + 1 < x₀) (i : ℕ) :
    HasSum (fun k : ℕ => primeLaplaceJet θ x₀ a (i + k) / (k.factorial : ℂ))
      (primeLaplaceJet θ x₀ (primeSourceShift a) i) := by
  classical
  set f := primeLaplaceCoeff θ a with hf
  set F := LSeries f with hF
  set U : Set ℂ := {s : ℂ | (1 - θ) / 2 < s.re} with hU
  have habs : LSeries.abscissaOfAbsConv f ≤ (((1 - θ) / 2 : ℝ) : EReal) :=
    abscissaOfAbsConv_primeLaplaceCoeff_le hθ ha
  have hUsub : U ⊆ {s : ℂ | LSeries.abscissaOfAbsConv f < (s.re : EReal)} := by
    intro s hs
    exact lt_of_le_of_lt habs (by exact_mod_cast hs)
  have hana : AnalyticOnNhd ℂ F U := (LSeries_analyticOnNhd f).mono hUsub
  have hanaG : AnalyticOnNhd ℂ (iteratedDeriv i F) U := by
    have hiterate : ∀ j : ℕ, AnalyticOnNhd ℂ (deriv^[j] F) U := by
      intro j
      induction j with
      | zero => simpa using hana
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih.deriv
    have := hiterate i
    simpa [iteratedDeriv_eq_iterate] using this
  set r : ℝ := x₀ - (1 - θ) / 2 with hr
  have hr1 : 1 < r := by simp [hr]; linarith
  have hball : Metric.ball ((x₀ : ℂ)) r ⊆ U := by
    intro z hz
    have hdist : ‖z - (x₀ : ℂ)‖ < r := by
      rw [← Complex.dist_eq]
      exact hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ))
      simpa using this
    have : |z.re - x₀| < r := lt_of_le_of_lt hre hdist
    have h2 := (abs_lt.mp this).1
    simp only [hU, Set.mem_setOf_eq]
    simp only [hr] at h2
    linarith
  have hdiff : DifferentiableOn ℂ (iteratedDeriv i F) (Metric.ball ((x₀ : ℂ)) r) :=
    ((hanaG.mono hball).differentiableOn)
  have hz : ((x₀ : ℂ) + 1) ∈ Metric.ball ((x₀ : ℂ)) r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simpa using hr1
  have htaylor := Complex.hasSum_taylorSeries_on_ball hdiff hz
  have hiter : ∀ k : ℕ, iteratedDeriv k (iteratedDeriv i F) (x₀ : ℂ)
      = primeLaplaceJet θ x₀ a (i + k) := by
    intro k
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
      primeLaplaceJet, iteratedDeriv_eq_iterate, hF, hf, Nat.add_comm k i]
  have hval : iteratedDeriv i F ((x₀ : ℂ) + 1) = primeLaplaceJet θ x₀ (primeSourceShift a) i := by
    rw [primeLaplaceJet_primeSourceShift, hF, hf]
  rw [hval] at htaylor
  refine htaylor.congr_fun fun k => ?_
  rw [hiter k]
  simp [div_eq_inv_mul]

/-- **The exact descent anomaly.**  The finite Gamma clock shadow of the prime translation differs
from the translated jet exactly by the omitted Taylor tail. -/
theorem primeLaplaceDescentAnomaly_eq {θ x₀ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) (hx₀ : (1 - θ) / 2 + 1 < x₀) (N i : ℕ) :
    primeLaplaceDescentAnomaly θ x₀ N a i
      = (∑ k ∈ Finset.range (N - i), primeLaplaceJet θ x₀ a (i + k) / (k.factorial : ℂ))
        - ∑' k : ℕ, primeLaplaceJet θ x₀ a (i + k) / (k.factorial : ℂ) := by
  rw [primeLaplaceDescentAnomaly, gammaClockShadowSum,
    (hasSum_taylor_primeLaplaceJet hθ ha hx₀ i).tsum_eq]

/-- The anomaly is exactly minus the omitted factorial tail. -/
theorem primeLaplaceDescentAnomaly_eq_neg_tail {θ x₀ : ℝ} (hθ : 0 ≤ θ) {a : Nat.Primes → ℂ}
    (ha : Summable fun p : Nat.Primes => ‖a p‖ ^ 2) (hx₀ : (1 - θ) / 2 + 1 < x₀) (N i : ℕ) :
    primeLaplaceDescentAnomaly θ x₀ N a i
      = -∑' k : ℕ, primeLaplaceJet θ x₀ a (i + (k + (N - i)))
          / (((k + (N - i)).factorial : ℕ) : ℂ) := by
  have hsum := hasSum_taylor_primeLaplaceJet hθ ha hx₀ i
  have hsplit := hsum.summable.sum_add_tsum_nat_add (N - i)
  rw [primeLaplaceDescentAnomaly_eq hθ ha hx₀ N i, ← hsplit]
  ring

/-- **Adjacent-resolution Bianchi law.**  Refining the resolution by one changes the descent
anomaly exactly by the newly exposed derivative with the Gamma factorial weight. -/
theorem primeLaplaceDescentAnomaly_bianchi (θ x₀ : ℝ) (a : Nat.Primes → ℂ) {N i : ℕ}
    (hi : i ≤ N) :
    primeLaplaceDescentAnomaly θ x₀ (N + 1) a i - primeLaplaceDescentAnomaly θ x₀ N a i
      = primeLaplaceJet θ x₀ a N / (((N - i).factorial : ℕ) : ℂ) := by
  have hcard : N + 1 - i = (N - i) + 1 := by omega
  have hadd : i + (N - i) = N := by omega
  rw [primeLaplaceDescentAnomaly, primeLaplaceDescentAnomaly, gammaClockShadowSum,
    gammaClockShadowSum, hcard, Finset.sum_range_succ, hadd]
  ring

/-! ### The reflected time-one Euler seam -/

/-- The weighted prime logarithmic transform `M_θ (w) = ∑_p w_θ(p) (log p) p^{-w}`. -/
def primeSeamTransform (θ : ℝ) (w : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (meixnerPrimeWeight θ (p : ℕ) : ℂ) * (Real.log ((p : ℕ) : ℝ) : ℂ)
    * ((p : ℕ) : ℂ) ^ (-w)

/-- The reflected time-one Euler coefficient vector `c_ρ(p) = √w_θ(p) (log p) p^{-ρ}`. -/
def reflectedEulerVector (θ : ℝ) (ρ : ℂ) (p : Nat.Primes) : ℂ :=
  (Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) : ℂ) * (Real.log ((p : ℕ) : ℝ) : ℂ)
    * ((p : ℕ) : ℂ) ^ (-ρ)

theorem summable_reflectedEulerVector {θ : ℝ} (hθ : 0 ≤ θ) {ρ : ℂ}
    (hρ : (1 - θ) / 2 < ρ.re) :
    Summable fun p : Nat.Primes => ‖reflectedEulerVector θ ρ p‖ ^ 2 := by
  have hβ : 1 < θ + 2 * ρ.re := by linarith
  have hlog : Summable fun n : ℕ => |Real.log (n : ℝ)| ^ 2 * (n : ℝ) ^ (-(θ + 2 * ρ.re)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg 2 (θ + 2 * ρ.re) hβ
  have hlogp : Summable fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| ^ 2 * (((p : ℕ) : ℝ)) ^ (-(θ + 2 * ρ.re)) :=
    hlog.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hlogp.mul_left (2 ^ (θ / 2)))
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.2.one_le
  have hnorm : ‖reflectedEulerVector θ ρ p‖
      = Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) * |Real.log ((p : ℕ) : ℝ)|
        * ((p : ℕ) : ℝ) ^ (-ρ.re) := by
    rw [reflectedEulerVector, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Complex.norm_natCast_cpow_of_pos p.2.pos]
    congr 2
  rw [hnorm]
  have hsq : (Real.sqrt (meixnerPrimeWeight θ (p : ℕ))) ^ 2 = meixnerPrimeWeight θ (p : ℕ) :=
    Real.sq_sqrt (meixnerPrimeWeight_pos θ _).le
  have hw := meixnerPrimeWeight_le θ hθ (n := (p : ℕ)) hp1
  have hrpow : (((p : ℕ) : ℝ) ^ (-ρ.re)) ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * ρ.re)) := by
    rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-ρ.re)) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hsplit : ((p : ℕ) : ℝ) ^ (-θ) * ((p : ℕ) : ℝ) ^ (-(2 * ρ.re))
      = ((p : ℕ) : ℝ) ^ (-(θ + 2 * ρ.re)) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  calc (Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) * |Real.log ((p : ℕ) : ℝ)|
        * ((p : ℕ) : ℝ) ^ (-ρ.re)) ^ 2
      = meixnerPrimeWeight θ (p : ℕ) * |Real.log ((p : ℕ) : ℝ)| ^ 2
        * ((p : ℕ) : ℝ) ^ (-(2 * ρ.re)) := by
        rw [mul_pow, mul_pow, hsq, hrpow]
    _ ≤ (2 ^ (θ / 2) * ((p : ℕ) : ℝ) ^ (-θ)) * |Real.log ((p : ℕ) : ℝ)| ^ 2
        * ((p : ℕ) : ℝ) ^ (-(2 * ρ.re)) := by
        have hnn : (0 : ℝ) ≤ |Real.log ((p : ℕ) : ℝ)| ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * ρ.re)) := by
          positivity
        nlinarith [hw, hnn, (meixnerPrimeWeight_pos θ (p : ℕ)).le,
          sq_nonneg |Real.log ((p : ℕ) : ℝ)|, Real.rpow_pos_of_pos hp0 (-(2 * ρ.re))]
    _ = 2 ^ (θ / 2) * (|Real.log ((p : ℕ) : ℝ)| ^ 2 * ((p : ℕ) : ℝ) ^ (-(θ + 2 * ρ.re))) := by
        rw [← hsplit]
        ring

/-- **The reflected Euler seam is a translate of the weighted prime logarithmic transform.** -/
theorem lSeries_reflectedEulerVector (θ : ℝ) (ρ : ℂ) (z : ℂ) :
    LSeries (primeLaplaceCoeff θ (reflectedEulerVector θ ρ)) z = primeSeamTransform θ (z + ρ) := by
  classical
  have hterm : ∀ p : Nat.Primes,
      LSeries.term (primeLaplaceCoeff θ (reflectedEulerVector θ ρ)) z (p : ℕ)
        = (meixnerPrimeWeight θ (p : ℕ) : ℂ) * (Real.log ((p : ℕ) : ℝ) : ℂ)
          * ((p : ℕ) : ℂ) ^ (-(z + ρ)) := by
    intro p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
    rw [LSeries.term_of_ne_zero p.2.ne_zero, primeLaplaceCoeff_prime, reflectedEulerVector]
    have hsq : ((Real.sqrt (meixnerPrimeWeight θ (p : ℕ)) : ℝ) : ℂ) ^ 2
        = (meixnerPrimeWeight θ (p : ℕ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (meixnerPrimeWeight_pos θ _).le]
    have hcpow : ((p : ℕ) : ℂ) ^ (-(z + ρ)) = ((p : ℕ) : ℂ) ^ (-ρ) / ((p : ℕ) : ℂ) ^ z := by
      rw [show -(z + ρ) = -ρ - z by ring, Complex.cpow_sub _ _ hp0]
    rw [hcpow]
    field_simp
    rw [hsq]
    ring
  have hsupp : Function.support (LSeries.term (primeLaplaceCoeff θ (reflectedEulerVector θ ρ)) z)
      ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_contra hmem
    have hnp : ¬ n.Prime := fun hp => hmem ⟨⟨n, hp⟩, rfl⟩
    apply hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero h0, primeLaplaceCoeff, dif_neg hnp, zero_div]
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun p q h => Subtype.ext h
  rw [LSeries, primeSeamTransform, ← hinj.tsum_eq hsupp]
  exact tsum_congr hterm

end

end RHTower
