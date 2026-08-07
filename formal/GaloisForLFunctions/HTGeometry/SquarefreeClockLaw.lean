import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# Dirichlet clocks and the squarefree clock

A nonnegative arithmetic weight with convergent Dirichlet series defines a clock law on the half
line: its points are the logarithms of the integers and its weights are the normalized Dirichlet
coefficients.  Its Laplace transform is the ratio of Dirichlet totals at shifted abscissae and its
mean is the ratio of the logarithmically weighted total to the plain one.

The squarefree weight — the square of the Möbius function — is such a weight past the abscissa one,
and its clock is the ground clock of the critical transport statement.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Dirichlet total of an arithmetic weight at an abscissa. -/
def dirichletTotal (f : ℕ → ℝ) (σ : ℝ) : ℝ := ∑' n : ℕ, f n * (n : ℝ) ^ (-σ)

/-- The normalized clock weight of a nonnegative arithmetic weight. -/
def dirichletClockWeight (f : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  f n * (n : ℝ) ^ (-σ) / dirichletTotal f σ

/-- The clock law of a nonnegative arithmetic weight. -/
def dirichletClockLaw (f : ℕ → ℝ) (σ : ℝ) : Measure ℝ := logClockLaw (dirichletClockWeight f σ)

variable {f : ℕ → ℝ} {σ : ℝ}

theorem dirichletClockWeight_nonneg (hf : ∀ n, 0 ≤ f n) (hpos : 0 < dirichletTotal f σ) (n : ℕ) :
    0 ≤ dirichletClockWeight f σ n :=
  div_nonneg (mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hpos.le

theorem dirichletClockWeight_zero (hf0 : f 0 = 0) : dirichletClockWeight f σ 0 = 0 := by
  simp [dirichletClockWeight, hf0]

theorem tsum_dirichletClockWeight (hpos : 0 < dirichletTotal f σ) :
    ∑' n : ℕ, dirichletClockWeight f σ n = 1 := by
  simp only [dirichletClockWeight]
  rw [tsum_div_const]
  exact div_self (ne_of_gt hpos)

theorem isProbabilityMeasure_dirichletClockLaw (hf : ∀ n, 0 ≤ f n)
    (hpos : 0 < dirichletTotal f σ) : IsProbabilityMeasure (dirichletClockLaw f σ) :=
  isProbabilityMeasure_logClockLaw (dirichletClockWeight_nonneg hf hpos)
    (tsum_dirichletClockWeight hpos)

theorem dirichletClockLaw_Iio_zero (f : ℕ → ℝ) (σ : ℝ) : dirichletClockLaw f σ (Iio 0) = 0 :=
  logClockLaw_Iio_zero _

/-- **The Laplace transform of a Dirichlet clock is the ratio of shifted Dirichlet totals.** -/
theorem integral_exp_neg_dirichletClockLaw (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (hpos : 0 < dirichletTotal f σ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(dirichletClockLaw f σ))
      = dirichletTotal f (σ + u) / dirichletTotal f σ := by
  rw [dirichletClockLaw, integral_exp_neg_logClockLaw (dirichletClockWeight_nonneg hf hpos)
    (dirichletClockWeight_zero hf0) (tsum_dirichletClockWeight hpos) hu]
  rw [dirichletTotal, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [dirichletClockWeight, div_mul_eq_mul_div]
  by_cases hn : n = 0
  · subst hn
    simp [hf0]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [show -(σ + u) = -σ + -u by ring, Real.rpow_add hnpos]
    ring

/-- A Dirichlet clock whose logarithmic series converges has a finite mean. -/
theorem integrable_id_dirichletClockLaw (hf : ∀ n, 0 ≤ f n) (hpos : 0 < dirichletTotal f σ)
    (hlog : Summable fun n : ℕ => (Real.log n * f n) * (n : ℝ) ^ (-σ)) :
    Integrable (id : ℝ → ℝ) (dirichletClockLaw f σ) := by
  refine integrable_weightedPointLaw _ _ (fun n => ENNReal.ofReal_ne_top) ?_
  refine (hlog.div_const (dirichletTotal f σ)).congr fun n => ?_
  rw [ENNReal.toReal_ofReal (dirichletClockWeight_nonneg hf hpos n)]
  simp only [dirichletClockWeight, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg n)]
  ring

/-- **The mean of a Dirichlet clock is the ratio of the logarithmic total to the plain total.** -/
theorem integral_id_dirichletClockLaw (hf : ∀ n, 0 ≤ f n) (hpos : 0 < dirichletTotal f σ)
    (hlog : Summable fun n : ℕ => (Real.log n * f n) * (n : ℝ) ^ (-σ)) :
    (∫ y, y ∂(dirichletClockLaw f σ))
      = (∑' n : ℕ, (Real.log n * f n) * (n : ℝ) ^ (-σ)) / dirichletTotal f σ := by
  rw [dirichletClockLaw, integral_id_logClockLaw (dirichletClockWeight_nonneg hf hpos)
    (integrable_id_dirichletClockLaw hf hpos hlog)]
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  simp only [dirichletClockWeight]
  ring

/-- The squarefree weight: the square of the Möbius function. -/
def squarefreeWeight (n : ℕ) : ℝ := ((moebius n : ℤ) : ℝ) ^ 2

theorem squarefreeWeight_nonneg (n : ℕ) : 0 ≤ squarefreeWeight n := sq_nonneg _

@[simp] theorem squarefreeWeight_zero : squarefreeWeight 0 = 0 := by
  simp [squarefreeWeight]

theorem squarefreeWeight_le_one (n : ℕ) : squarefreeWeight n ≤ 1 := by
  rcases moebius_eq_or n with h | h | h <;> rw [squarefreeWeight, h] <;> norm_num

theorem squarefreeWeight_of_squarefree {n : ℕ} (h : Squarefree n) : squarefreeWeight n = 1 := by
  rw [squarefreeWeight]
  exact_mod_cast moebius_sq_eq_one_of_squarefree h

theorem squarefreeWeight_of_not_squarefree {n : ℕ} (h : ¬ Squarefree n) :
    squarefreeWeight n = 0 := by
  rw [squarefreeWeight, moebius_eq_zero_of_not_squarefree h]
  norm_num

/-- The squarefree weight is the indicator of the squarefree integers. -/
theorem squarefreeWeight_eq_indicator (n : ℕ) :
    squarefreeWeight n = if Squarefree n then 1 else 0 := by
  by_cases h : Squarefree n
  · rw [if_pos h, squarefreeWeight_of_squarefree h]
  · rw [if_neg h, squarefreeWeight_of_not_squarefree h]

theorem norm_squarefreeWeight_le_one (n : ℕ) : ‖((squarefreeWeight n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (squarefreeWeight_nonneg n)]
  exact squarefreeWeight_le_one n

theorem lseriesSummable_squarefreeWeight {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => ((squarefreeWeight n : ℝ) : ℂ)) (s : ℂ) :=
  LSeriesSummable_of_bounded_of_one_lt_real (m := 1) (fun n _ => norm_squarefreeWeight_le_one n) hs

theorem abscissa_squarefreeWeight_lt {σ : ℝ} (hσ : 1 < σ) :
    LSeries.abscissaOfAbsConv (fun n => ((squarefreeWeight n : ℝ) : ℂ)) < ((σ : ℂ)).re := by
  have hmid : (1 : ℝ) < (1 + σ) / 2 := by linarith
  refine lt_of_le_of_lt (lseriesSummable_squarefreeWeight hmid).abscissaOfAbsConv_le ?_
  simp only [Complex.ofReal_re]
  exact_mod_cast by linarith

theorem summable_squarefreeWeight_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => squarefreeWeight n * (n : ℝ) ^ (-σ) :=
  summable_real_of_lseriesSummable (by simp) (lseriesSummable_squarefreeWeight hσ)

theorem dirichletTotal_squarefreeWeight_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < dirichletTotal squarefreeWeight σ := by
  have hsummable := summable_squarefreeWeight_rpow hσ
  refine lt_of_lt_of_le ?_ (hsummable.le_tsum 1 fun n _ =>
    mul_nonneg (squarefreeWeight_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  norm_num [squarefreeWeight, moebius_apply_one]

theorem summable_squarefreeWeight_logMul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (Real.log n * squarefreeWeight n) * (n : ℝ) ^ (-σ) := by
  have hlog := LSeriesSummable_logMul_of_lt_re (abscissa_squarefreeWeight_lt hσ)
  have hcoef : (LSeries.logMul fun n => ((squarefreeWeight n : ℝ) : ℂ))
      = fun n : ℕ => ((Real.log n * squarefreeWeight n : ℝ) : ℂ) := by
    funext n
    have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [LSeries.logMul, hlogn, ← Complex.ofReal_mul]
  rw [hcoef] at hlog
  exact summable_real_of_lseriesSummable (by simp) hlog

/-- The critical squarefree clock: the ground clock of the transport statement. -/
def squarefreeClockLaw (σ : ℝ) : Measure ℝ := dirichletClockLaw squarefreeWeight σ

theorem isProbabilityMeasure_squarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (squarefreeClockLaw σ) :=
  isProbabilityMeasure_dirichletClockLaw squarefreeWeight_nonneg
    (dirichletTotal_squarefreeWeight_pos hσ)

theorem squarefreeClockLaw_Iio_zero (σ : ℝ) : squarefreeClockLaw σ (Iio 0) = 0 :=
  dirichletClockLaw_Iio_zero _ _

/-- **The Laplace transform of the squarefree clock is the ratio of squarefree Dirichlet
totals.** -/
theorem integral_exp_neg_squarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(squarefreeClockLaw σ))
      = dirichletTotal squarefreeWeight (σ + u) / dirichletTotal squarefreeWeight σ :=
  integral_exp_neg_dirichletClockLaw squarefreeWeight_nonneg (by simp)
    (dirichletTotal_squarefreeWeight_pos hσ) hu

/-- **The mean of the squarefree clock.** -/
theorem integral_id_squarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) :
    (∫ y, y ∂(squarefreeClockLaw σ))
      = (∑' n : ℕ, (Real.log n * squarefreeWeight n) * (n : ℝ) ^ (-σ))
        / dirichletTotal squarefreeWeight σ :=
  integral_id_dirichletClockLaw squarefreeWeight_nonneg
    (dirichletTotal_squarefreeWeight_pos hσ) (summable_squarefreeWeight_logMul_rpow hσ)

theorem integrable_id_squarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) :
    Integrable (id : ℝ → ℝ) (squarefreeClockLaw σ) :=
  integrable_id_dirichletClockLaw squarefreeWeight_nonneg
    (dirichletTotal_squarefreeWeight_pos hσ) (summable_squarefreeWeight_logMul_rpow hσ)

/-- The weight supported on squares which reads a given weight at the square root. -/
def squareSupportedWeight (f : ℕ → ℝ) (n : ℕ) : ℝ := if n = (Nat.sqrt n) ^ 2 then f (Nat.sqrt n) else 0

@[simp] theorem squareSupportedWeight_sq (f : ℕ → ℝ) (d : ℕ) : squareSupportedWeight f (d ^ 2) = f d := by
  rw [squareSupportedWeight, Nat.sqrt_eq' d, if_pos rfl]

theorem squareSupportedWeight_eq_zero_of_notMem_range {f : ℕ → ℝ} {n : ℕ}
    (hn : n ∉ Set.range fun d : ℕ => d ^ 2) : squareSupportedWeight f n = 0 := by
  rw [squareSupportedWeight, if_neg]
  intro hsq
  exact hn ⟨Nat.sqrt n, hsq.symm⟩

/-- **Square substitution for a real Dirichlet series.**  A weight supported on the squares has the
Dirichlet series of its square root at twice the abscissa. -/
theorem tsum_squareSupportedWeight (f : ℕ → ℝ) (σ : ℝ) :
    (∑' n : ℕ, squareSupportedWeight f n * (n : ℝ) ^ (-σ))
      = ∑' d : ℕ, f d * (d : ℝ) ^ (-(2 * σ)) := by
  have hinj : Function.Injective fun d : ℕ => d ^ 2 :=
    Nat.pow_left_injective (by norm_num)
  have hsupp : Function.support (fun n : ℕ => squareSupportedWeight f n * (n : ℝ) ^ (-σ))
      ⊆ Set.range fun d : ℕ => d ^ 2 := by
    intro n hn
    by_contra hcon
    refine hn ?_
    show squareSupportedWeight f n * (n : ℝ) ^ (-σ) = 0
    rw [squareSupportedWeight_eq_zero_of_notMem_range hcon, zero_mul]
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun d => ?_
  rw [squareSupportedWeight_sq]
  by_cases hd : d = 0
  · subst hd
    rcases eq_or_ne σ 0 with hσ | hσ
    · subst hσ
      norm_num
    · have hc1 : (((0 ^ 2 : ℕ) : ℝ)) = (0 : ℝ) := by norm_num
      have hc2 : (((0 : ℕ) : ℝ)) = (0 : ℝ) := by norm_num
      rw [hc1, hc2, Real.zero_rpow (neg_ne_zero.mpr hσ),
        Real.zero_rpow (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hσ))]
  · have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hcast : (((d ^ 2 : ℕ) : ℝ)) = (d : ℝ) ^ (2 : ℕ) := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (d : ℝ) 2, ← Real.rpow_mul hdpos.le]
    congr 2
    push_cast
    ring

/-- The largest integer whose square divides `n`. -/
def sqDivisorPart (n : ℕ) : ℕ :=
  (n.factorization.mapRange (· / 2) (by simp)).prod (· ^ ·)

theorem mapRange_half_le (n : ℕ) :
    n.factorization.mapRange (· / 2) (by simp) ≤ n.factorization := by
  rw [Finsupp.le_def]
  intro p
  rw [Finsupp.mapRange_apply]
  exact Nat.div_le_self _ 2

theorem factorization_sqDivisorPart (n : ℕ) :
    (sqDivisorPart n).factorization = n.factorization.mapRange (· / 2) (by simp) :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (mapRange_half_le n)

theorem sqDivisorPart_dvd (n : ℕ) : sqDivisorPart n ∣ n :=
  Nat.prod_pow_dvd_of_le_factorization (mapRange_half_le n)

theorem sqDivisorPart_ne_zero (n : ℕ) : sqDivisorPart n ≠ 0 := by
  refine Finsupp.prod_ne_zero_iff.mpr fun p hp => ?_
  refine pow_ne_zero _ ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors
    (Finsupp.support_mono (mapRange_half_le n) hp)
  exact hprime.ne_zero

/-- **A square divides an integer exactly when its root divides the square part.** -/
theorem sq_dvd_iff_dvd_sqDivisorPart {n d : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    d ^ 2 ∣ n ↔ d ∣ sqDivisorPart n := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) hn,
    ← Nat.factorization_le_iff_dvd hd (sqDivisorPart_ne_zero n),
    factorization_sqDivisorPart, Nat.factorization_pow, Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h p
    have hp := h p
    rw [Finsupp.smul_apply, smul_eq_mul] at hp
    rw [Finsupp.mapRange_apply]
    omega
  · intro h p
    have hp := h p
    rw [Finsupp.mapRange_apply] at hp
    rw [Finsupp.smul_apply, smul_eq_mul]
    omega

/-- **The square part is trivial exactly for squarefree integers.** -/
theorem sqDivisorPart_eq_one_iff {n : ℕ} (hn : n ≠ 0) :
    sqDivisorPart n = 1 ↔ Squarefree n := by
  rw [Nat.squarefree_iff_factorization_le_one hn]
  constructor
  · intro h1 p
    have hfac := congrArg (fun m : ℕ => m.factorization p) h1
    simp only [factorization_sqDivisorPart, Finsupp.mapRange_apply,
      Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply] at hfac
    omega
  · intro hle
    have hzero : n.factorization.mapRange (· / 2) (by simp) = 0 := by
      ext p
      rw [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
      have := hle p
      omega
    rw [sqDivisorPart, hzero, Finsupp.prod_zero_index]

/-- The Möbius sum over the divisors of an integer. -/
theorem sum_moebius_divisors (N : ℕ) :
    ∑ d ∈ N.divisors, moebius d = if N = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f N) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

theorem filter_sq_dvd_eq_divisors_sqDivisorPart {n : ℕ} (hn : n ≠ 0) :
    n.divisors.filter (fun d => d ^ 2 ∣ n) = (sqDivisorPart n).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdn, -⟩, hsq⟩
    refine ⟨(sq_dvd_iff_dvd_sqDivisorPart ?_ hn).mp hsq, sqDivisorPart_ne_zero n⟩
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd hdn) hn
  · rintro ⟨hd, -⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hd) (sqDivisorPart_ne_zero n)
    exact ⟨⟨hd.trans (sqDivisorPart_dvd n), hn⟩, (sq_dvd_iff_dvd_sqDivisorPart hd0 hn).mpr hd⟩

/-- **The squarefree indicator is the Möbius sum over square divisors.**  This is the convolution
identity behind the squarefree Dirichlet series. -/
theorem sum_moebius_sq_dvd {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), moebius d = moebius n ^ 2 := by
  rw [filter_sq_dvd_eq_divisors_sqDivisorPart hn, sum_moebius_divisors]
  simp only [sqDivisorPart_eq_one_iff hn]
  by_cases hsf : Squarefree n
  · rw [if_pos hsf, moebius_sq_eq_one_of_squarefree hsf]
  · rw [if_neg hsf, moebius_eq_zero_of_not_squarefree hsf]
    ring

/-- The Möbius function read at square roots, supported on the squares. -/
def sqrtMoebius (n : ℕ) : ℤ := if n = (Nat.sqrt n) ^ 2 then moebius (Nat.sqrt n) else 0

@[simp] theorem sqrtMoebius_sq (d : ℕ) : sqrtMoebius (d ^ 2) = moebius d := by
  rw [sqrtMoebius, Nat.sqrt_eq' d, if_pos rfl]

theorem sqrtMoebius_eq_zero_of_not_sq {a : ℕ} (h : a ≠ (Nat.sqrt a) ^ 2) :
    sqrtMoebius a = 0 := by
  rw [sqrtMoebius, if_neg h]

/-- **The squarefree indicator is the divisor sum of the square-root Möbius weight.**  This is the
Dirichlet convolution identity `μ² = sqrtMoebius ⋆ 1`. -/
theorem sum_divisors_sqrtMoebius {n : ℕ} (hn : n ≠ 0) :
    ∑ a ∈ n.divisors, sqrtMoebius a = moebius n ^ 2 := by
  classical
  have hsub : (sqDivisorPart n).divisors.image (fun d => d ^ 2) ⊆ n.divisors := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    rw [Nat.mem_divisors] at hd ⊢
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hd.1) (sqDivisorPart_ne_zero n)
    exact ⟨(sq_dvd_iff_dvd_sqDivisorPart hd0 hn).mpr hd.1, hn⟩
  have hzero : ∀ a ∈ n.divisors, a ∉ (sqDivisorPart n).divisors.image (fun d => d ^ 2) →
      sqrtMoebius a = 0 := by
    intro a ha hnot
    by_contra hne
    have hsq : a = (Nat.sqrt a) ^ 2 := by
      by_contra hcon
      exact hne (sqrtMoebius_eq_zero_of_not_sq hcon)
    rw [Nat.mem_divisors] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd ha.1)
    have hs0 : Nat.sqrt a ≠ 0 := by
      rintro h0
      rw [h0] at hsq
      simp only [pow_two, mul_zero] at hsq
      exact ha0 hsq
    have hdvd : Nat.sqrt a ∣ sqDivisorPart n :=
      (sq_dvd_iff_dvd_sqDivisorPart hs0 hn).mp (by rw [← hsq]; exact ha.1)
    exact hnot (Finset.mem_image.mpr
      ⟨Nat.sqrt a, Nat.mem_divisors.mpr ⟨hdvd, sqDivisorPart_ne_zero n⟩, hsq.symm⟩)
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_image fun x _ y _ h => Nat.pow_left_injective (by norm_num) h]
  simp only [sqrtMoebius_sq]
  rw [sum_moebius_divisors]
  simp only [sqDivisorPart_eq_one_iff hn]
  by_cases hsf : Squarefree n
  · rw [if_pos hsf, moebius_sq_eq_one_of_squarefree hsf]
  · rw [if_neg hsf, moebius_eq_zero_of_not_squarefree hsf]
    ring

theorem sqrtMoebius_real (n : ℕ) :
    ((sqrtMoebius n : ℤ) : ℝ) = squareSupportedWeight (fun d => ((moebius d : ℤ) : ℝ)) n := by
  rw [sqrtMoebius, squareSupportedWeight]
  by_cases h : n = (Nat.sqrt n) ^ 2
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    norm_num

theorem norm_sqrtMoebius_le_one (n : ℕ) : ‖((sqrtMoebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [sqrtMoebius]
  by_cases h : n = (Nat.sqrt n) ^ 2
  · rw [if_pos h]
    rcases moebius_eq_or (Nat.sqrt n) with hm | hm | hm <;> rw [hm] <;> norm_num
  · rw [if_neg h]
    norm_num

/-- **The squarefree Dirichlet series is the ratio of zeta values.** -/
theorem ofReal_dirichletTotal_squarefreeWeight_eq {σ : ℝ} (hσ : 1 < σ) :
    ((dirichletTotal squarefreeWeight σ : ℝ) : ℂ)
      = riemannZeta (σ : ℂ) / riemannZeta (2 * (σ : ℂ)) := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hsum1 : LSeriesSummable (fun n : ℕ => ((sqrtMoebius n : ℤ) : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_real (m := 1) (fun n _ => norm_sqrtMoebius_le_one n) hσ
  have hsum2 : LSeriesSummable (1 : ℕ → ℂ) (σ : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_real (m := 1) (fun n _ => by simp) hσ
  have hconv : LSeries.convolution (fun n : ℕ => ((sqrtMoebius n : ℤ) : ℂ)) (1 : ℕ → ℂ)
      = fun n : ℕ => (((moebius n : ℤ) : ℂ)) ^ 2 := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [LSeries.convolution_def]
      rw [Nat.sum_divisorsAntidiagonal
        (f := fun a b => ((sqrtMoebius a : ℤ) : ℂ) * (1 : ℕ → ℂ) b)]
      simp only [Pi.one_apply, mul_one]
      have := congrArg (fun z : ℤ => (z : ℂ)) (sum_divisors_sqrtMoebius hn)
      push_cast at this
      exact this
  have hprod := LSeries_convolution' hsum1 hsum2
  rw [hconv] at hprod
  have hLHS : LSeries (fun n : ℕ => (((moebius n : ℤ) : ℂ)) ^ 2) (σ : ℂ)
      = ((dirichletTotal squarefreeWeight σ : ℝ) : ℂ) := by
    rw [dirichletTotal, ofReal_tsum_eq_lseries (f := squarefreeWeight) (by simp)]
    refine congrArg (fun g => LSeries g (σ : ℂ)) ?_
    funext n
    rw [squarefreeWeight]
    push_cast
    ring
  have hfactor1 : LSeries (fun n : ℕ => ((sqrtMoebius n : ℤ) : ℂ)) (σ : ℂ)
      = 1 / riemannZeta (2 * (σ : ℂ)) := by
    have hcoef : (fun n : ℕ => ((sqrtMoebius n : ℤ) : ℂ))
        = fun n : ℕ => (((sqrtMoebius n : ℤ) : ℝ) : ℂ) := by
      funext n
      push_cast
      ring
    rw [hcoef, ← ofReal_tsum_eq_lseries (f := fun n => ((sqrtMoebius n : ℤ) : ℝ))
      (by simp [sqrtMoebius])]
    have hcongr : (∑' n : ℕ, ((sqrtMoebius n : ℤ) : ℝ) * (n : ℝ) ^ (-σ))
        = ∑' d : ℕ, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(2 * σ)) := by
      rw [← tsum_squareSupportedWeight (fun d => ((moebius d : ℤ) : ℝ)) σ]
      exact tsum_congr fun n => by rw [sqrtMoebius_real]
    rw [hcongr]
    have h2 : (1 : ℝ) < 2 * σ := by linarith
    have := ofReal_tsum_moebius_eq h2
    rw [this]
    push_cast
    ring_nf
  have hfactor2 : LSeries (1 : ℕ → ℂ) (σ : ℂ) = riemannZeta (σ : ℂ) :=
    LSeries_one_eq_riemannZeta hre
  rw [hLHS, hfactor1, hfactor2] at hprod
  rw [hprod]
  ring

/-! ### The ground clock and the prime current are distinct at every finite scale -/

/-- The squarefree clock has a positive atom at the origin: the trivial divisor. -/
theorem squarefreeClockLaw_singleton_zero (σ : ℝ) :
    squarefreeClockLaw σ {(0 : ℝ)}
      = ENNReal.ofReal (1 / dirichletTotal squarefreeWeight σ) := by
  rw [squarefreeClockLaw, dirichletClockLaw,
    logClockLaw_singleton_zero (dirichletClockWeight_zero (by simp))]
  congr 1
  have hone : squarefreeWeight 1 = 1 := by
    rw [squarefreeWeight, moebius_apply_one]
    norm_num
  rw [dirichletClockWeight, hone]
  norm_num

/-- **The two critical clocks are distinct at every finite scale.**  The ground clock charges the
trivial divisor; the prime current does not.  Their agreement is therefore asymptotic only, which is
what makes the fixed-current orientation a genuine selection inside the critical metric class. -/
theorem squarefreeClockLaw_ne_eulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    squarefreeClockLaw σ ≠ eulerClockLaw σ := by
  intro hcon
  have hsq : squarefreeClockLaw σ {(0 : ℝ)}
      = ENNReal.ofReal (1 / dirichletTotal squarefreeWeight σ) :=
    squarefreeClockLaw_singleton_zero σ
  have heuler : eulerClockLaw σ {(0 : ℝ)} = 0 := by
    rw [eulerClockLaw, logClockLaw_singleton_zero (by simp [eulerClockWeight])]
    simp [eulerClockWeight]
  have hpos : 0 < 1 / dirichletTotal squarefreeWeight σ :=
    div_pos one_pos (dirichletTotal_squarefreeWeight_pos hσ)
  rw [hcon, heuler] at hsq
  exact absurd hsq.symm (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))

end

end GaloisForLFunctions.HTGeometry
