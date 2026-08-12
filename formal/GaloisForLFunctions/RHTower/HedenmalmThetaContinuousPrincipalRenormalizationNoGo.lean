import GaloisForLFunctions.RHTower.HedenmalmThetaPrincipalClassTrichotomy

/-!
# Continuous principal-renormalization no-go for Route P

Allow the diagonal harmonic counterterm coefficient to depend on radial grade.  If every grade is
to become summable modulo an arbitrary grade-dependent summable tail, the principal-class
trichotomy forces coefficient zero at neutral grade and coefficient minus one at every nonneutral
grade.  This is discontinuous at the critical wall.

Hence no continuous—therefore no analytic—diagonal functional calculus can universally remove
Route P harmonic escape.  A surviving pre-divisor producer must be singular at the wall or mix
source channels before diagonal fibre evaluation.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Universal admission forces the principal coefficient to be zero at the wall. -/
theorem principalCoefficient_eq_zero_at_wall_of_universalAdmission
    (c : ℝ → ℝ) (r : ℝ → Nat.Primes → ℝ)
    (hr : ∀ t, Summable (r t))
    (hadmit : ∀ t,
      Summable (thetaPrimeFixedPrincipalCorrection (c t) t (r t))) :
    c 0 = 0 := by
  have hclass :=
    (summable_thetaPrimeFixedPrincipalCorrection_iff
      (c 0) 0 (r 0) (hr 0)).mp (hadmit 0)
  simpa using hclass

/-- Universal admission forces coefficient minus one at every punctured grade. -/
theorem principalCoefficient_eq_neg_one_off_wall_of_universalAdmission
    (c : ℝ → ℝ) (r : ℝ → Nat.Primes → ℝ)
    (hr : ∀ t, Summable (r t))
    (hadmit : ∀ t,
      Summable (thetaPrimeFixedPrincipalCorrection (c t) t (r t)))
    {t : ℝ} (ht : t ≠ 0) :
    c t = -1 := by
  have hclass :=
    (summable_thetaPrimeFixedPrincipalCorrection_iff
      (c t) t (r t) (hr t)).mp (hadmit t)
  simpa [ht] using hclass

/-- **Wall-jump no-go.** No grade-continuous diagonal principal coefficient, even with arbitrary
summable grade-dependent tails, can make every radial sector summable. -/
theorem no_continuous_principalCoefficient_universalAdmission
    (c : ℝ → ℝ) (r : ℝ → Nat.Primes → ℝ)
    (hc : ContinuousAt c 0) (hr : ∀ t, Summable (r t)) :
    ¬ ∀ t, Summable (thetaPrimeFixedPrincipalCorrection (c t) t (r t)) := by
  intro hadmit
  have hc0 : c 0 = 0 :=
    principalCoefficient_eq_zero_at_wall_of_universalAdmission c r hr hadmit
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht_ne : ∀ n, t n ≠ 0 := by
    intro n
    exact one_div_ne_zero (by positivity)
  have hvalues : ∀ n, c (t n) = -1 := by
    intro n
    exact principalCoefficient_eq_neg_one_off_wall_of_universalAdmission
      c r hr hadmit (ht_ne n)
  have htend : Filter.Tendsto t Filter.atTop (nhds 0) := by
    simpa [t] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htoZero : Filter.Tendsto (fun n => c (t n)) Filter.atTop (nhds 0) := by
    have hcomp := hc.tendsto.comp htend
    rwa [hc0] at hcomp
  have htoNegOne :
      Filter.Tendsto (fun n => c (t n)) Filter.atTop (nhds (-1 : ℝ)) := by
    simpa only [hvalues] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (-1 : ℝ)) Filter.atTop (nhds (-1 : ℝ)))
  have hzeroNegOne : (0 : ℝ) = -1 :=
    tendsto_nhds_unique htoZero htoNegOne
  norm_num at hzeroNegOne

/-- Global continuity is in particular excluded. -/
theorem no_continuous_principalCoefficient_universalAdmission_global
    (c : ℝ → ℝ) (r : ℝ → Nat.Primes → ℝ)
    (hc : Continuous c) (hr : ∀ t, Summable (r t)) :
    ¬ ∀ t, Summable (thetaPrimeFixedPrincipalCorrection (c t) t (r t)) :=
  no_continuous_principalCoefficient_universalAdmission c r hc.continuousAt hr

end

end RHTower.HedenmalmThetaSource
