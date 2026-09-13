import GaloisForLFunctions.RHTower.DQPTEtaDeriv
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# Paired eta roots and exact pole cancellation

The absolutely convergent paired eta series has a simple zero at
`1 + 2πi / log 2`, where zeta is nonzero. It therefore has no analytic square root
on the strict right critical half-plane.

Its entire elementary correction `C` satisfies `etaPair = C * zetaPoleUnit`
throughout the positive half-plane, including the cancelled pole. This separates
the auxiliary divisor from the original zeta divisor.

The entire family `J_h(s) = dslope exp 0 (-h(s-1))` satisfies `J_0 = 1` and
`J_h(1) = 1`. Both `J_h → 1` and `J_h * zetaPoleUnit → zetaPoleUnit`
hold locally uniformly as `h → 0`. At `h = log 2`, the latter source is exactly
`etaPair / log 2`. These are identities and continuation limits for the source,
not constructions of roots of the limiting pole unit.
-/

open Complex Filter Set Topology Metric
noncomputable section
namespace RHTower

/-- A nonreal zero introduced by the dyadic pairing factor. -/
def pairedEtaAuxiliaryPoint : ℂ :=
  1 + ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I

/-- The elementary multiplier relating the paired series to zeta. -/
def pairedEtaFilter (s : ℂ) : ℂ := 1 - (2 : ℂ) ^ (1 - s)

/-- The entire pairing factor after its zero at one is divided out. -/
def pairedEtaPoleCorrection : ℂ → ℂ := dslope pairedEtaFilter 1

theorem pairedEtaAuxiliaryPoint_re : pairedEtaAuxiliaryPoint.re = 1 := by
  simp only [pairedEtaAuxiliaryPoint, Complex.add_re, Complex.one_re,
    Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]

theorem pairedEtaAuxiliaryPoint_ne_one : pairedEtaAuxiliaryPoint ≠ 1 := by
  intro h
  have hi := congrArg Complex.im h
  have hp : 0 < 2 * Real.pi / Real.log 2 :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by norm_num))
  simp only [pairedEtaAuxiliaryPoint, Complex.add_im, Complex.one_im,
    Complex.mul_I_im, Complex.ofReal_re, zero_add] at hi
  linarith

theorem pairedEtaFilter_zero : pairedEtaFilter pairedEtaAuxiliaryPoint = 0 := by
  have hl : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have he : Complex.log (2 : ℂ) * (1 - pairedEtaAuxiliaryPoint) =
      (-1 : ℤ) * (2 * Real.pi * I) := by
    have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_ofNat] using
        (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [hlog]
    simp only [pairedEtaAuxiliaryPoint, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Int.cast_neg, Int.cast_one]
    field_simp
    ring
  rw [pairedEtaFilter, sub_eq_zero, Complex.cpow_def_of_ne_zero (by norm_num), he]
  exact (Complex.exp_eq_one_iff.mpr ⟨-1, rfl⟩).symm

theorem hasDerivAt_pairedEtaFilter (s : ℂ) :
    HasDerivAt pairedEtaFilter
      ((2 : ℂ) ^ (1 - s) * Complex.log 2) s := by
  have h := (((hasDerivAt_id s).const_sub 1).const_cpow
    (c := (2 : ℂ)) (Or.inl (by norm_num))).const_sub 1
  unfold pairedEtaFilter
  simpa only [id_eq, mul_neg, mul_one, neg_neg] using h

theorem analyticAt_pairedEtaFilter (s : ℂ) : AnalyticAt ℂ pairedEtaFilter s := by
  apply Differentiable.analyticAt
  exact fun z => (hasDerivAt_pairedEtaFilter z).differentiableAt

theorem analyticAt_pairedEtaPoleCorrection (s : ℂ) :
    AnalyticAt ℂ pairedEtaPoleCorrection s :=
  analyticAt_dslope_of_analyticAt (analyticAt_pairedEtaFilter 1)
    (analyticAt_pairedEtaFilter s)

theorem pairedEtaPoleCorrection_one : pairedEtaPoleCorrection 1 = Complex.log 2 := by
  rw [pairedEtaPoleCorrection, dslope_same, (hasDerivAt_pairedEtaFilter 1).deriv]
  simp

theorem pairedEtaPoleCorrection_mul_sub_one (s : ℂ) :
    pairedEtaPoleCorrection s * (s - 1) = pairedEtaFilter s := by
  have h := sub_smul_dslope pairedEtaFilter (1 : ℂ) s
  simpa [pairedEtaPoleCorrection, pairedEtaFilter, smul_eq_mul, mul_comm] using h

theorem analyticOnNhd_etaPair_posHalf :
    AnalyticOnNhd ℂ etaPair {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (DQPT.hasDerivAt_etaPair hs).differentiableAt.differentiableWithinAt

/-- Exact factorization, with the removable value at one retained. -/
theorem etaPair_eq_poleCorrection_mul_zetaPoleUnit {s : ℂ} (hs : 0 < s.re) :
    etaPair s = pairedEtaPoleCorrection s * zetaPoleUnit s := by
  have hright : AnalyticOnNhd ℂ
      (fun s => pairedEtaPoleCorrection s * zetaPoleUnit s) {s : ℂ | 0 < s.re} := by
    intro z _
    exact (analyticAt_pairedEtaPoleCorrection z).mul (differentiable_zetaPoleUnit.analyticAt z)
  have heq : etaPair =ᶠ[𝓝 (2 : ℂ)]
      (fun s => pairedEtaPoleCorrection s * zetaPoleUnit s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with z hz
    have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
    rw [etaPair_eq z (by linarith) hz1, zetaPoleUnit_of_ne hz1,
      ← mul_assoc, pairedEtaPoleCorrection_mul_sub_one]
    rfl
  exact analyticOnNhd_etaPair_posHalf.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
    (show (2 : ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) heq hs

theorem etaPair_one_eq_log_two : etaPair 1 = Complex.log 2 := by
  rw [etaPair_eq_poleCorrection_mul_zetaPoleUnit (by norm_num),
    pairedEtaPoleCorrection_one, zetaPoleUnit_one, mul_one]

theorem etaPair_auxiliary_zero : etaPair pairedEtaAuxiliaryPoint = 0 := by
  rw [etaPair_eq _ (by rw [pairedEtaAuxiliaryPoint_re]; norm_num)
    pairedEtaAuxiliaryPoint_ne_one]
  change pairedEtaFilter pairedEtaAuxiliaryPoint * _ = 0
  rw [pairedEtaFilter_zero, zero_mul]

theorem hasDerivAt_etaPair_auxiliary :
    HasDerivAt etaPair (Complex.log 2 * riemannZeta pairedEtaAuxiliaryPoint)
      pairedEtaAuxiliaryPoint := by
  have heq : etaPair =ᶠ[𝓝 pairedEtaAuxiliaryPoint]
      (fun s => pairedEtaFilter s * riemannZeta s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show pairedEtaAuxiliaryPoint ∈ {s : ℂ | 0 < s.re} by
        rw [mem_setOf_eq, pairedEtaAuxiliaryPoint_re]; norm_num),
      isOpen_ne.mem_nhds pairedEtaAuxiliaryPoint_ne_one] with s hs hs1
    exact etaPair_eq s hs hs1
  have hf : (2 : ℂ) ^ (1 - pairedEtaAuxiliaryPoint) = 1 :=
    (sub_eq_zero.mp pairedEtaFilter_zero).symm
  have h := (hasDerivAt_pairedEtaFilter pairedEtaAuxiliaryPoint).mul
    (differentiableAt_riemannZeta pairedEtaAuxiliaryPoint_ne_one).hasDerivAt
  simp only [hf, one_mul, pairedEtaFilter_zero, zero_mul, add_zero] at h
  exact h.congr_of_eventuallyEq heq

theorem deriv_etaPair_auxiliary_ne_zero : deriv etaPair pairedEtaAuxiliaryPoint ≠ 0 := by
  rw [hasDerivAt_etaPair_auxiliary.deriv]
  apply mul_ne_zero
  · have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_ofNat] using
        (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [hlog]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [pairedEtaAuxiliaryPoint_re])

/-- The actual paired eta series has no global analytic square root on `rightHalf`. -/
theorem not_exists_analytic_etaPair_squareRoot_rightHalf :
    ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalf ∧
      ∀ s ∈ rightHalf, g s ^ 2 = etaPair s := by
  rintro ⟨g, hg, hsq⟩
  have hp : pairedEtaAuxiliaryPoint ∈ rightHalf := by
    rw [mem_rightHalf, pairedEtaAuxiliaryPoint_re]; norm_num
  have hg0 : g pairedEtaAuxiliaryPoint = 0 :=
    (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp (by rw [hsq _ hp, etaPair_auxiliary_zero])
  have heq : (fun s => g s ^ 2) =ᶠ[𝓝 pairedEtaAuxiliaryPoint] etaPair := by
    filter_upwards [isOpen_rightHalf.mem_nhds hp] with s hs
    exact hsq s hs
  have h := (hg _ hp).differentiableAt.hasDerivAt.pow 2
  have hd := (h.congr_of_eventuallyEq heq.symm).deriv
  apply deriv_etaPair_auxiliary_ne_zero
  simpa [hg0] using hd

/-- The entire normalized exponential divided difference at dilation time `h`. -/
def poleDilationCorrection (h : ℝ) (s : ℂ) : ℂ :=
  dslope Complex.exp 0 (-(h : ℂ) * (s - 1))

/-- The genuine zeta pole unit with its normalized dilation correction. -/
def poleDilationSource (h : ℝ) (s : ℂ) : ℂ :=
  poleDilationCorrection h s * zetaPoleUnit s

theorem analyticAt_poleDilationCorrection (h : ℝ) (s : ℂ) :
    AnalyticAt ℂ (poleDilationCorrection h) s := by
  exact (analyticAt_dslope_of_analyticAt (show AnalyticAt ℂ Complex.exp 0 by fun_prop)
    (show AnalyticAt ℂ Complex.exp _ by fun_prop)).comp
    (show AnalyticAt ℂ (fun z : ℂ => -(h : ℂ) * (z - 1)) s by
      fun_prop)

theorem poleDilationCorrection_zero (s : ℂ) : poleDilationCorrection 0 s = 1 := by
  simp [poleDilationCorrection, dslope_same, Complex.deriv_exp]

theorem poleDilationCorrection_one (h : ℝ) : poleDilationCorrection h 1 = 1 := by
  simp [poleDilationCorrection, dslope_same, Complex.deriv_exp]

theorem poleDilationSource_one (h : ℝ) : poleDilationSource h 1 = 1 := by
  rw [poleDilationSource, poleDilationCorrection_one, zetaPoleUnit_one, mul_one]

theorem analyticAt_poleDilationSource (h : ℝ) (s : ℂ) :
    AnalyticAt ℂ (poleDilationSource h) s :=
  (analyticAt_poleDilationCorrection h s).mul (differentiable_zetaPoleUnit.analyticAt s)

theorem poleDilationCorrection_exact (h : ℝ) (s : ℂ) :
    (h : ℂ) * (s - 1) * poleDilationCorrection h s =
      1 - Complex.exp (-(h : ℂ) * (s - 1)) := by
  have hd := sub_smul_dslope Complex.exp (0 : ℂ) (-(h : ℂ) * (s - 1))
  simp only [sub_zero, Complex.exp_zero, smul_eq_mul] at hd
  change _ * dslope Complex.exp 0 (-(h : ℂ) * (s - 1)) = _
  linear_combination -hd

theorem continuous_poleDilationCorrection :
    Continuous (fun p : ℝ × ℂ => poleDilationCorrection p.1 p.2) := by
  have hc : Continuous (dslope Complex.exp 0) := continuous_iff_continuousAt.mpr fun z =>
    (analyticAt_dslope_of_analyticAt (show AnalyticAt ℂ Complex.exp 0 by fun_prop)
      (show AnalyticAt ℂ Complex.exp z by fun_prop)).continuousAt
  exact hc.comp (by fun_prop)

/-- The dilation correction tends locally uniformly to the unit as the dilation vanishes. -/
theorem tendstoLocallyUniformly_poleDilationCorrection :
    TendstoLocallyUniformly poleDilationCorrection (fun _ => 1) (𝓝 (0 : ℝ)) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro s
  have h := continuous_poleDilationCorrection.continuousAt (x := ((0 : ℝ), s))
  rw [ContinuousAt, poleDilationCorrection_zero, nhds_prod_eq] at h
  exact (tendsto_const_nhds.prodMk_nhds h).mono_right (nhds_le_uniformity (1 : ℂ))

/-- Removing the dilation recovers the actual pole unit locally uniformly. -/
theorem tendstoLocallyUniformly_poleDilationSource :
    TendstoLocallyUniformly poleDilationSource zetaPoleUnit (𝓝 (0 : ℝ)) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro s
  have hc : Continuous (fun p : ℝ × ℂ => poleDilationSource p.1 p.2) :=
    continuous_poleDilationCorrection.mul (differentiable_zetaPoleUnit.continuous.comp continuous_snd)
  have h := hc.continuousAt (x := ((0 : ℝ), s))
  simp only [ContinuousAt, poleDilationSource, poleDilationCorrection_zero,
    one_mul, nhds_prod_eq] at h
  have hu : Tendsto (fun p : ℝ × ℂ => zetaPoleUnit p.2)
      (𝓝 (0 : ℝ) ×ˢ 𝓝 s) (𝓝 (zetaPoleUnit s)) :=
    differentiable_zetaPoleUnit.continuous.continuousAt.tendsto.comp tendsto_snd
  exact (hu.prodMk_nhds h).mono_right (nhds_le_uniformity (zetaPoleUnit s))

theorem poleDilationCorrection_log_two (s : ℂ) :
    (Real.log 2 : ℂ) * poleDilationCorrection (Real.log 2) s =
      pairedEtaPoleCorrection s := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  by_cases hs : s = 1
  · subst s
    rw [poleDilationCorrection_one, mul_one, pairedEtaPoleCorrection_one, hlog]
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs)
  have hpow : (2 : ℂ) ^ (1 - s) =
      Complex.exp (-(Real.log 2 : ℂ) * (s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog]
    congr 1
    ring
  calc
    (s - 1) * ((Real.log 2 : ℂ) * poleDilationCorrection (Real.log 2) s) =
        (Real.log 2 : ℂ) * (s - 1) * poleDilationCorrection (Real.log 2) s := by ring
    _ = pairedEtaFilter s := by rw [poleDilationCorrection_exact, pairedEtaFilter, hpow]
    _ = (s - 1) * pairedEtaPoleCorrection s := by
      rw [mul_comm, pairedEtaPoleCorrection_mul_sub_one]

/-- Dyadic pairing is exactly one member of the normalized entire source family. -/
theorem poleDilationSource_log_two {s : ℂ} (hs : 0 < s.re) :
    poleDilationSource (Real.log 2) s = etaPair s / (Real.log 2 : ℂ) := by
  have hl : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  apply (eq_div_iff hl).mpr
  rw [poleDilationSource, etaPair_eq_poleCorrection_mul_zetaPoleUnit hs,
    ← poleDilationCorrection_log_two]
  ring

theorem analyticOrderAt_etaPair_auxiliary :
    analyticOrderAt etaPair pairedEtaAuxiliaryPoint = 1 := by
  apply (analyticOnNhd_etaPair_posHalf _
    (by rw [mem_setOf_eq, pairedEtaAuxiliaryPoint_re]; norm_num)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact etaPair_auxiliary_zero
  · exact deriv_etaPair_auxiliary_ne_zero

end RHTower

