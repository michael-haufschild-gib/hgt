import GaloisForLFunctions.HTGeometry.SqrtStretchedZeroFree
import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm
import GaloisForLFunctions.HTGeometry.ModulusDeterminesNewtonData

/-!
# An uncountable HT family with one magnitude profile and pairwise distinct divisors

Varying only the phase of the constant term of the square-root stretched-exponential series keeps
every coefficient magnitude, hence every Newton datum, and keeps hypertranscendence.  Two members
with the same zero divisor would have an entire nonvanishing quotient; since they differ by a
nonzero constant, that forces one of them to be zero-free, hence constant by the order-zero
rigidity — contradicting its nonzero linear coefficient.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000

/-- The card's family: only the phase of the constant term varies. -/
def phaseFamily (t : ℝ) : ℂ → ℂ :=
  GaloisForLFunctions.sqrtStretchedPhaseFunction (fun n => if n = 0 then t else 0)

theorem hypertranscendental_phaseFamily (t : ℝ) :
    GaloisForLFunctions.Hypertranscendental (phaseFamily t) :=
  GaloisForLFunctions.hypertranscendental_sqrtStretchedPhaseFunction _

theorem coeff_taylorPS_phaseFamily (t : ℝ) (n : ℕ) :
    PowerSeries.coeff n (GaloisForLFunctions.taylorPS (phaseFamily t))
      = (Real.exp (-Real.exp (Real.sqrt n)) : ℂ) *
        Complex.exp (Complex.I * ((if n = 0 then t else 0 : ℝ) : ℂ)) := by
  rw [phaseFamily, GaloisForLFunctions.sqrtStretchedPhaseFunction,
    GaloisForLFunctions.taylorPS_stretchedExponentialPhaseFunction (by norm_num) (by norm_num)
      (by norm_num), GaloisForLFunctions.stretchedExponentialPhaseCoeff,
    GaloisForLFunctions.stretchedExp_oneHalf_eq_exp_sqrt]
  norm_num

theorem norm_coeff_taylorPS_phaseFamily (t : ℝ) (n : ℕ) :
    ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS (phaseFamily t))‖
      = Real.exp (-Real.exp (Real.sqrt n)) := by
  rw [coeff_taylorPS_phaseFamily, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  simp

theorem contDiff_phaseFamily (t : ℝ) : ContDiff ℂ (⊤ : ℕ∞) (phaseFamily t) :=
  GaloisForLFunctions.contDiff_stretchedExponentialPhaseFunction (by norm_num) (by norm_num)
    (by norm_num) _

theorem differentiable_phaseFamily (t : ℝ) : Differentiable ℂ (phaseFamily t) :=
  (contDiff_phaseFamily t).differentiable (by simp)

theorem analyticOnNhd_phaseFamily (t : ℝ) :
    AnalyticOnNhd ℂ (phaseFamily t) Set.univ :=
  (differentiable_phaseFamily t).differentiableOn.analyticOnNhd isOpen_univ

/-- The value at the origin is the constant coefficient. -/
theorem phaseFamily_zero (t : ℝ) :
    phaseFamily t 0 = (Real.exp (-1 : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by
  have h := coeff_taylorPS_phaseFamily t 0
  rw [GaloisForLFunctions.coeff_taylorPS] at h
  simpa using h

theorem phaseFamily_zero_ne_zero (t : ℝ) : phaseFamily t 0 ≠ 0 := by
  rw [phaseFamily_zero]
  exact mul_ne_zero (by simp) (Complex.exp_ne_zero _)

theorem deriv_phaseFamily_zero_ne_zero (t : ℝ) : deriv (phaseFamily t) 0 ≠ 0 := by
  have h := coeff_taylorPS_phaseFamily t 1
  rw [GaloisForLFunctions.coeff_taylorPS] at h
  intro hzero
  have h1 : iteratedDeriv 1 (phaseFamily t) 0 = 0 := by
    rw [iteratedDeriv_one]
    exact hzero
  rw [h1] at h
  have hne : ((Real.exp (-Real.exp (Real.sqrt 1)) : ℂ) *
      Complex.exp (Complex.I * ((0 : ℝ) : ℂ))) ≠ 0 :=
    mul_ne_zero (by simp) (Complex.exp_ne_zero _)
  refine hne ?_
  have h2 : (0 : ℂ) = (Real.exp (-Real.exp (Real.sqrt 1)) : ℂ) *
      Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) := by
    simpa using h
  exact h2.symm

/-- Order zero, in the form required by the rigidity theorem. -/
theorem phaseFamily_growth (t : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖phaseFamily t z‖ ≤ Real.exp (C + ε * ‖z‖) :=
  sqrtStretched_norm_le_exp _ hε

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000

theorem summable_phaseFamily_terms (t : ℝ) (z : ℂ) :
    Summable (fun n : ℕ => (Real.exp (-Real.exp (Real.sqrt n)) : ℂ) *
      Complex.exp (Complex.I * ((if n = 0 then t else 0 : ℝ) : ℂ)) * z ^ n) := by
  refine Summable.of_norm ?_
  have hnorm : ∀ n : ℕ,
      ‖(Real.exp (-Real.exp (Real.sqrt n)) : ℂ) *
        Complex.exp (Complex.I * ((if n = 0 then t else 0 : ℝ) : ℂ)) * z ^ n‖
      = Real.exp (-Real.exp (Real.sqrt n)) * ‖z‖ ^ n := by
    intro n
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    simp
  exact (summable_sqrtStretched_term (norm_nonneg z)).congr fun n => (hnorm n).symm

/-- Two members of the family differ by the constant phase difference of the constant term. -/
theorem phaseFamily_sub (t s : ℝ) (z : ℂ) :
    phaseFamily t z - phaseFamily s z
      = (Real.exp (-1 : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (t : ℂ)) - Complex.exp (Complex.I * (s : ℂ))) := by
  rw [phaseFamily, phaseFamily, GaloisForLFunctions.sqrtStretchedPhaseFunction_eq_tsum,
    GaloisForLFunctions.sqrtStretchedPhaseFunction_eq_tsum,
    ← Summable.tsum_sub (summable_phaseFamily_terms t z) (summable_phaseFamily_terms s z)]
  rw [tsum_eq_single 0 ?_]
  · norm_num
    ring
  · intro n hn
    simp [if_neg hn]

theorem analyticOrderAt_phaseFamily_ne_top (t : ℝ) (z : ℂ) :
    analyticOrderAt (phaseFamily t) z ≠ ⊤ := by
  intro hcon
  rw [analyticOrderAt_eq_top] at hcon
  have hall := (analyticOnNhd_phaseFamily t).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) hcon
  have h0 := hall (Set.mem_univ (0 : ℂ))
  simp only [Pi.zero_apply] at h0
  exact phaseFamily_zero_ne_zero t h0

/-- **Distinct constant-term phases give distinct zero divisors.** -/
theorem exists_analyticOrderAt_ne {t s : ℝ}
    (hts : Complex.exp (Complex.I * (t : ℂ)) ≠ Complex.exp (Complex.I * (s : ℂ))) :
    ∃ z : ℂ, analyticOrderAt (phaseFamily t) z ≠ analyticOrderAt (phaseFamily s) z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨Q, hQd, hQne, hQeq⟩ :=
    GaloisForLFunctions.EntireQuotient.exists_entire_nonvanishing_quotient
      (analyticOnNhd_phaseFamily t) (analyticOnNhd_phaseFamily s)
      (analyticOrderAt_phaseFamily_ne_top t) hcon (phaseFamily_zero_ne_zero s)
  set c : ℂ := (Real.exp (-1 : ℝ) : ℂ) *
    (Complex.exp (Complex.I * (t : ℂ)) - Complex.exp (Complex.I * (s : ℂ))) with hc
  have hcne : c ≠ 0 := by
    refine mul_ne_zero (by simp) ?_
    exact sub_ne_zero.mpr hts
  have hprod : ∀ z : ℂ, (Q z - 1) * phaseFamily s z = c := by
    intro z
    have h1 := phaseFamily_sub t s z
    have h2 := hQeq z
    rw [h2] at h1
    rw [hc]
    linear_combination h1
  have hsne : ∀ z : ℂ, phaseFamily s z ≠ 0 := by
    intro z hz
    have := hprod z
    rw [hz, mul_zero] at this
    exact hcne this.symm
  have hconst := const_of_ne_zero_of_subexponential (differentiable_phaseFamily s) hsne
    (phaseFamily_growth s)
  have hfun : phaseFamily s = fun _ : ℂ => phaseFamily s 0 := funext hconst
  have hderiv : deriv (phaseFamily s) 0 = 0 := by
    rw [hfun]
    simp
  exact deriv_phaseFamily_zero_ne_zero s hderiv

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000

theorem exp_I_inj_on_Ico {t s : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hne : t ≠ s) :
    Complex.exp (Complex.I * (t : ℂ)) ≠ Complex.exp (Complex.I * (s : ℂ)) := by
  intro heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hreal : (t : ℂ) = (s : ℂ) + (n : ℂ) * (2 * Real.pi) := by
    have hn' : Complex.I * (t : ℂ) = Complex.I * ((s : ℂ) + (n : ℂ) * (2 * Real.pi)) := by
      rw [hn]
      ring
    exact mul_left_cancel₀ hI hn'
  have hrr : t = s + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re hreal
    simpa using this
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlt : |t - s| < 2 * Real.pi := by
    rcases ht with ⟨ht0, ht1⟩
    rcases hs with ⟨hs0, hs1⟩
    rw [abs_lt]
    constructor <;> linarith
  have hn0 : n = 0 := by
    by_contra hn0
    have hge : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hn0)
      exact_mod_cast this
    have : |t - s| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [show t - s = (n : ℝ) * (2 * Real.pi) by linarith [hrr], abs_mul,
        abs_of_pos hpi]
    nlinarith [hlt, hge, hpi]
  rw [hn0] at hrr
  simp at hrr
  exact hne hrr

theorem not_countable_Ico_two_pi : ¬ (Set.Ico (0 : ℝ) (2 * Real.pi)).Countable := by
  intro hc
  have h := Cardinal.mk_Ico_real (show (0 : ℝ) < 2 * Real.pi by positivity)
  have hle := hc.le_aleph0
  rw [h] at hle
  exact absurd hle (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **Card 16, Theorem 3.**  An uncountable family of hypertranscendental entire functions with
identical Taylor magnitudes — hence identical Newton geometry — and pairwise distinct zero
divisors. -/
theorem uncountable_HT_family_with_distinct_divisors :
    ¬ (Set.Ico (0 : ℝ) (2 * Real.pi)).Countable
      ∧ (∀ t : ℝ, GaloisForLFunctions.Hypertranscendental (phaseFamily t))
      ∧ (∀ t : ℝ, ∀ n : ℕ,
          ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS (phaseFamily t))‖
            = Real.exp (-Real.exp (Real.sqrt n)))
      ∧ (∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), t ≠ s →
          ∃ z : ℂ, analyticOrderAt (phaseFamily t) z ≠ analyticOrderAt (phaseFamily s) z) :=
  ⟨not_countable_Ico_two_pi, hypertranscendental_phaseFamily, norm_coeff_taylorPS_phaseFamily,
    fun _t ht _s hs hne => exists_analyticOrderAt_ne (exp_I_inj_on_Ico ht hs hne)⟩

/-- The family has order zero and, having equal Taylor magnitudes, identical Newton data. -/
theorem phaseFamily_order_zero_and_newton (t s : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
        ‖phaseFamily t z‖ ≤ Real.exp (C + ε * ‖z‖))
      ∧ (∀ r : ℝ, maxTerm (fun n => PowerSeries.coeff n
            (GaloisForLFunctions.taylorPS (phaseFamily t))) r
          = maxTerm (fun n => PowerSeries.coeff n
            (GaloisForLFunctions.taylorPS (phaseFamily s))) r)
      ∧ (∀ r : ℝ, centralIndex (fun n => PowerSeries.coeff n
            (GaloisForLFunctions.taylorPS (phaseFamily t))) r
          = centralIndex (fun n => PowerSeries.coeff n
            (GaloisForLFunctions.taylorPS (phaseFamily s))) r)
      ∧ (∀ u : ℝ, logNewtonEnvelope (fun n => PowerSeries.coeff n
            (GaloisForLFunctions.taylorPS (phaseFamily t))) u
          = logNewtonEnvelope (fun n => PowerSeries.coeff n
            (GaloisForLFunctions.taylorPS (phaseFamily s))) u) := by
  have hmod : ∀ n : ℕ,
      ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS (phaseFamily t))‖
        = ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS (phaseFamily s))‖ := by
    intro n
    rw [norm_coeff_taylorPS_phaseFamily, norm_coeff_taylorPS_phaseFamily]
  obtain ⟨h1, -, h3, h4⟩ := newton_data_congr hmod
  exact ⟨fun ε hε => phaseFamily_growth t ε hε, h1, h3, h4⟩

end

end GaloisForLFunctions.HTGeometry
