import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceCurrent

/-!
# Spatial mass of the complete PW-B same-source forcing

The actual positive-ray pairing is an everywhere absolutely convergent Dirichlet
series. Its first nonzero coefficient is a strictly negative, finite source mass.
This survives spatial integration and gives a quantitative scaled L1 gap.
No spectral parameter identification or Riemann hypothesis is asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

/-- Actual integrated operator difference for one complete arithmetic atom. -/
def pwGammaSameSourceMassAtom (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceAtom z n (h,x))-
    pwGammaMobiusReflectedCurrentAtom z n x

theorem pwGammaSameSourceMassAtom_eq (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    pwGammaSameSourceMassAtom z n x =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ) :=
  pwGammaMobiusSameSourceAtom_defect_eq z n hx

theorem pwGammaSameSourceMassAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaSameSourceMassAtom z n) (Ioi 0) :=
  (pwGammaMobiusSameSourceAtom_integrable z n).integral_prod_right.sub
    (pwGammaMobiusReflectedCurrentAtom_integrable z n)

theorem pwGammaSameSourceMassAtom_norm_integral_le (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaSameSourceMassAtom z n x‖) ≤
      (∫ p, ‖pwGammaMobiusSameSourceAtom z n p‖
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))+
      ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusReflectedCurrentAtom z n x‖ := by
  have hA := pwGammaMobiusSameSourceAtom_integrable z n
  have hB := pwGammaMobiusReflectedCurrentAtom_integrable z n
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), (∫ h in Ioi (0 : ℝ), ‖pwGammaMobiusSameSourceAtom z n (h,x)‖)+
        ‖pwGammaMobiusReflectedCurrentAtom z n x‖ := by
      apply integral_mono_ae (pwGammaSameSourceMassAtom_integrable z n).norm
        (hA.integral_norm_prod_right.add hB.norm)
      filter_upwards with x
      change ‖(∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceAtom z n (h,x))-
        pwGammaMobiusReflectedCurrentAtom z n x‖ ≤
        (∫ h in Ioi (0 : ℝ), ‖pwGammaMobiusSameSourceAtom z n (h,x)‖)+
          ‖pwGammaMobiusReflectedCurrentAtom z n x‖
      exact (norm_sub_le _ _).trans (add_le_add
        (norm_integral_le_integral_norm (fun h : ℝ => pwGammaMobiusSameSourceAtom z n (h,x))) le_rfl)
    _ = _ := by
      rw [integral_add hA.integral_norm_prod_right hB.norm, ← integral_prod_symm _ hA.norm]

theorem pwGammaSameSourceMassAtom_norm_integrals_summable (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaSameSourceMassAtom z n x‖) :=
  ((pwGammaMobiusSameSourceAtom_norm_integrals_summable z).add
    (pwGammaMobiusReflectedCurrentAtom_norm_integrals_summable z)).of_nonneg_of_le
      (fun _n => integral_nonneg (fun _x => norm_nonneg _))
      (pwGammaSameSourceMassAtom_norm_integral_le z)

private theorem pwGammaSameSourceMass_coefficient_zero (x : ℝ) :
    pwGammaSameSourceDefectCoefficient x 0 = 0 := by
  simp [pwGammaSameSourceDefectCoefficient, pwGammaSameSourceDefectWeight_zero]

private theorem pwGammaSameSourceMass_coefficient_one (x : ℝ) :
    pwGammaSameSourceDefectCoefficient x 1 = 0 := by
  simp [pwGammaSameSourceDefectCoefficient, pwGammaSameSourceDefectWeight_one]

theorem pwGammaSameSourceDefectCoefficient_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => pwGammaSameSourceDefectCoefficient x n) (Ioi 0) := by
  apply IntegrableOn.congr_fun (pwGammaSameSourceMassAtom_integrable 0 n) _ measurableSet_Ioi
  intro x hx
  rw [pwGammaSameSourceMassAtom_eq 0 n hx]
  simp [pwGammaSameSourceDefectCoefficient]

private theorem pwGammaSameSourceMass_term_eq (z : ℂ) (x : ℝ) (n : ℕ) :
    LSeries.term (pwGammaSameSourceDefectCoefficient x) z n =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaSameSourceDefectWeight_zero]
  rw [LSeries.term_def₀ (pwGammaSameSourceMass_coefficient_zero x),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne' : (n : ℂ) ≠ 0),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ n)]
  rw [mul_comm (Real.log (n : ℝ) : ℂ) (-z)]
  dsimp [pwGammaSameSourceDefectCoefficient]
  ring

theorem pwGammaSameSourceMassAtom_eq_term (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    pwGammaSameSourceMassAtom z n x = LSeries.term (pwGammaSameSourceDefectCoefficient x) z n := by
  rw [pwGammaSameSourceMassAtom_eq z n hx, pwGammaSameSourceMass_term_eq]

/-- Coefficients of the literal spatially paired same-source forcing. -/
def pwGammaSameSourceMassCoefficient (n : ℕ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), pwGammaSameSourceDefectCoefficient x n

theorem pwGammaSameSourceMassCoefficient_zero : pwGammaSameSourceMassCoefficient 0 = 0 := by
  simp [pwGammaSameSourceMassCoefficient, pwGammaSameSourceMass_coefficient_zero]

theorem pwGammaSameSourceMassCoefficient_one : pwGammaSameSourceMassCoefficient 1 = 0 := by
  simp [pwGammaSameSourceMassCoefficient, pwGammaSameSourceMass_coefficient_one]

theorem pwGammaSameSourceMassAtom_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), pwGammaSameSourceMassAtom z n x) =
      LSeries.term pwGammaSameSourceMassCoefficient z n := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaSameSourceMassAtom_eq_term z n hx)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero, integral_zero]
  simp only [LSeries.term_of_ne_zero hn.ne', integral_div, pwGammaSameSourceMassCoefficient]

theorem pwGammaSameSourceMassCoefficient_LSeriesSummable (z : ℂ) :
    LSeriesSummable pwGammaSameSourceMassCoefficient z := by
  have hs := (hasSum_integral_of_summable_integral_norm
    (pwGammaSameSourceMassAtom_integrable z) (pwGammaSameSourceMassAtom_norm_integrals_summable z)).summable
  change Summable (fun n => LSeries.term pwGammaSameSourceMassCoefficient z n)
  simpa only [pwGammaSameSourceMassAtom_integral] using hs

/-- The unchanged complete positive-ray spatial pairing. -/
def pwGammaMobiusSameSourceMass (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), pwGammaMobiusSameSourceDefect z x

theorem pwGammaMobiusSameSourceMass_eq_LSeries (z : ℂ) :
    pwGammaMobiusSameSourceMass z = LSeries pwGammaSameSourceMassCoefficient z := by
  have he : ∀ x : ℝ, x ∈ Ioi 0 → pwGammaMobiusSameSourceDefect z x =
      ∑' n, pwGammaSameSourceMassAtom z n x := by
    intro x hx
    rw [pwGammaMobiusSameSourceDefect_eq_tsum z hx]
    exact tsum_congr (fun n => (pwGammaSameSourceMassAtom_eq z n hx).symm)
  rw [pwGammaMobiusSameSourceMass, setIntegral_congr_fun measurableSet_Ioi he,
    ← integral_tsum_of_summable_integral_norm (pwGammaSameSourceMassAtom_integrable z)
      (pwGammaSameSourceMassAtom_norm_integrals_summable z)]
  simp only [pwGammaSameSourceMassAtom_integral, LSeries]

theorem pwGammaMobiusSameSourceMass_eq_difference (z : ℂ) :
    pwGammaMobiusSameSourceMass z =
      (∫ x in Ioi (0 : ℝ), pwGammaMobiusSameSourceCurrent z x)-
        ∫ x in Ioi (0 : ℝ), pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x := by
  change (∫ x in Ioi (0 : ℝ), pwGammaMobiusSameSourceCurrent z x-
    pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x) = _
  exact integral_sub (pwGammaMobiusSameSourceCurrent_integrable z) (pwGammaMobiusTiltCurrent_reflection_integrable z)

theorem pwGammaMobiusSameSourceMass_eq_joint_integral (z : ℂ) :
    pwGammaMobiusSameSourceMass z =
      ∫ p, pwGammaMobiusSameSourceResponse z p.2 p.1-pwGammaMobiusReflectedFrullaniResponse z p.2 p.1
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integral_prod_symm _ (pwGammaMobiusSameSourceDefect_response_joint_integrable z)]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => (pwGammaMobiusSameSourceDefect_response_integral z hx).symm)

/-- Positive original source profile of the prime-two forcing coefficient. -/
def pwGammaSameSourcePrimeProfile (x : ℝ) : ℝ :=
  ‖pwGammaRaySource x‖*pwGammaSameSourceDefectWeight 2 x

theorem pwGammaSameSourcePrimeProfile_pos {x : ℝ} (hx : 0 < x) :
    0 < pwGammaSameSourcePrimeProfile x :=
  mul_pos (norm_pos_iff.mpr (pwGammaRaySource_ne_zero x))
    (pwGammaSameSourceDefectWeight_pos one_lt_two hx)

theorem pwGammaSameSourceDefectCoefficient_two {x : ℝ} (hx : 0 < x) :
    pwGammaSameSourceDefectCoefficient x 2 = -(pwGammaSameSourcePrimeProfile x : ℂ) := by
  rw [pwGammaSameSourceDefectCoefficient, moebius_apply_prime Nat.prime_two,
    pwGammaSameSourcePrimeProfile, pwGammaRaySource_eq hx, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  push_cast
  ring

theorem pwGammaSameSourcePrimeProfile_integrable :
    IntegrableOn pwGammaSameSourcePrimeProfile (Ioi 0) := by
  apply IntegrableOn.congr_fun (pwGammaSameSourceDefectCoefficient_integrable 2).neg.re _ measurableSet_Ioi
  intro x hx
  change (-pwGammaSameSourceDefectCoefficient x 2).re = pwGammaSameSourcePrimeProfile x
  rw [pwGammaSameSourceDefectCoefficient_two hx, neg_neg, Complex.ofReal_re]

/-- The finite strictly positive leading spatial mass; no numerical evaluation is used. -/
def pwGammaSameSourcePrimeMass : ℝ :=
  ∫ x in Ioi (0 : ℝ), pwGammaSameSourcePrimeProfile x

theorem pwGammaSameSourcePrimeMass_pos : 0 < pwGammaSameSourcePrimeMass := by
  have hp : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] pwGammaSameSourcePrimeProfile := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (pwGammaSameSourcePrimeProfile_pos hx).le
  rw [pwGammaSameSourcePrimeMass, setIntegral_pos_iff_support_of_nonneg_ae hp
    pwGammaSameSourcePrimeProfile_integrable]
  have hs : Function.support pwGammaSameSourcePrimeProfile ∩ Ioi (0 : ℝ) = Ioi 0 := by
    apply inter_eq_right.mpr
    intro x hx
    exact (pwGammaSameSourcePrimeProfile_pos hx).ne'
  rw [hs]
  simp

theorem pwGammaSameSourceMassCoefficient_two :
    pwGammaSameSourceMassCoefficient 2 = -(pwGammaSameSourcePrimeMass : ℂ) := by
  rw [pwGammaSameSourceMassCoefficient,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaSameSourceDefectCoefficient_two hx),
    integral_neg, integral_complex_ofReal]
  rfl

theorem pwGammaMobiusSameSourceMass_leading_limit :
    Tendsto (fun r : ℝ => (2 : ℂ)^(r : ℂ)*pwGammaMobiusSameSourceMass r) atTop
      (𝓝 (-(pwGammaSameSourcePrimeMass : ℂ))) := by
  have ha : LSeries.abscissaOfAbsConv pwGammaSameSourceMassCoefficient < ⊤ :=
    (pwGammaSameSourceMassCoefficient_LSeriesSummable 0).abscissaOfAbsConv_le.trans_lt (by simp)
  have hhead : ∀ m : ℕ, m ≤ 1 → pwGammaSameSourceMassCoefficient m = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact pwGammaSameSourceMassCoefficient_zero
    · have hm1 : m = 1 := by omega
      rw [hm1]
      exact pwGammaSameSourceMassCoefficient_one
  have ht := LSeries.tendsto_cpow_mul_atTop hhead ha
  simpa only [pwGammaMobiusSameSourceMass_eq_LSeries, Nat.cast_one, one_add_one_eq_two,
    pwGammaSameSourceMassCoefficient_two] using ht

theorem pwGammaMobiusSameSourceMass_eventually_ne_zero :
    ∀ᶠ r : ℝ in atTop, pwGammaMobiusSameSourceMass r ≠ 0 := by
  have hc : -(pwGammaSameSourcePrimeMass : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr pwGammaSameSourcePrimeMass_pos.ne')
  filter_upwards [pwGammaMobiusSameSourceMass_leading_limit.eventually_ne hc] with r hr
  exact fun hh => hr (by rw [hh, mul_zero])

theorem pwGammaMobiusSameSourceMass_not_identically_zero :
    ¬ ∀ z : ℂ, pwGammaMobiusSameSourceMass z = 0 := by
  intro hz
  obtain ⟨r, hr⟩ := pwGammaMobiusSameSourceMass_eventually_ne_zero.exists
  exact hr (hz r)

theorem pwGammaMobiusSameSourceCurrent_not_universal_integral_balance :
    ¬ ∀ z : ℂ, (∫ x in Ioi (0 : ℝ), pwGammaMobiusSameSourceCurrent z x) =
      ∫ x in Ioi (0 : ℝ), pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x := by
  intro hz
  apply pwGammaMobiusSameSourceMass_not_identically_zero
  intro z
  rw [pwGammaMobiusSameSourceMass_eq_difference, hz z, sub_self]

theorem pwGammaMobiusSameSourceMass_norm_le (z : ℂ) :
    ‖pwGammaMobiusSameSourceMass z‖ ≤
      ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusSameSourceDefect z x‖ :=
  norm_integral_le_integral_norm _

theorem pwGammaMobiusSameSourceMass_scaled_norm_limit :
    Tendsto (fun r : ℝ => ‖(2 : ℂ)^(r : ℂ)*pwGammaMobiusSameSourceMass r‖) atTop
      (𝓝 pwGammaSameSourcePrimeMass) := by
  simpa only [norm_neg, Complex.norm_real, Real.norm_of_nonneg pwGammaSameSourcePrimeMass_pos.le] using
    pwGammaMobiusSameSourceMass_leading_limit.norm

theorem pwGammaMobiusSameSourceDefect_scaled_norm_gap :
    ∀ᶠ r : ℝ in atTop, pwGammaSameSourcePrimeMass/2 <
      ∫ x in Ioi (0 : ℝ), ‖(2 : ℂ)^(r : ℂ)*pwGammaMobiusSameSourceDefect r x‖ := by
  have hh : pwGammaSameSourcePrimeMass/2 < pwGammaSameSourcePrimeMass := by
    linarith [pwGammaSameSourcePrimeMass_pos]
  filter_upwards [pwGammaMobiusSameSourceMass_scaled_norm_limit.eventually_const_lt hh] with r hr
  apply hr.trans_le
  have hi := norm_integral_le_integral_norm
    (fun x : ℝ => (2 : ℂ)^(r : ℂ)*pwGammaMobiusSameSourceDefect r x)
      (μ := volume.restrict (Ioi (0 : ℝ)))
  simpa only [integral_const_mul, pwGammaMobiusSameSourceMass] using hi

/-- Closed complete spatial forcing and its positive leading mass, with no spectral premise. -/
theorem pwGammaMobiusSameSourceMass_closed :
    (∀ z : ℂ, LSeriesSummable pwGammaSameSourceMassCoefficient z ∧
      pwGammaMobiusSameSourceMass z = LSeries pwGammaSameSourceMassCoefficient z) ∧
    0 < pwGammaSameSourcePrimeMass ∧
    Tendsto (fun r : ℝ => (2 : ℂ)^(r : ℂ)*pwGammaMobiusSameSourceMass r) atTop
      (𝓝 (-(pwGammaSameSourcePrimeMass : ℂ))) ∧
    (∀ᶠ r : ℝ in atTop, pwGammaMobiusSameSourceMass r ≠ 0) ∧
    ¬ (∀ z : ℂ, pwGammaMobiusSameSourceMass z = 0) :=
  ⟨fun z => ⟨pwGammaSameSourceMassCoefficient_LSeriesSummable z, pwGammaMobiusSameSourceMass_eq_LSeries z⟩,
    pwGammaSameSourcePrimeMass_pos, pwGammaMobiusSameSourceMass_leading_limit,
    pwGammaMobiusSameSourceMass_eventually_ne_zero, pwGammaMobiusSameSourceMass_not_identically_zero⟩

end
end RHTower
