import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletionLanding
import GaloisForLFunctions.RHTower.BurnolGammaSteinMoments
import GaloisForLFunctions.HTGeometry.GaussianMellinMoments

/-!
# The prime-two collar symbol, its Gamma sewing and its reflection

On the positive half-plane the causal dyadic expansion `1/(2^w - 1) = ∑_{n ≥ 1} 2^{-nw}` turns the
rational completion multiplier `C₂(w) = w²(w-1)/(2(2^w-1))` into a summable ladder of translated
symbols.  Sewing the archimedean factor gives the physical multiplier `M₂ = C₂ Γ_ℝ`, whose
logarithmic kernel is the Fourier transform of `γ(u) = 2 e^{-u/2} e^{-π e^{-2u}}`:

`∫_ℝ γ(u) e^{-itu} du = Γ_ℝ(1/2 + it)`.

The physical multiplier carries the raw Burnol source `H(w) = (2^w-1) ζ(w)/w` to `ξ`, and it does so
on first divided vectors as well.  On the critical line the reflected orientation `M₂(1-w)` is the
complex conjugate of `M₂(w)`, which is exactly the statement that the logarithmic kernel is real and
its reflection is the reflected kernel.
-/

open Complex Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## Positive real bases -/

theorem burnolPosRealCpow_natMul {a : ℝ} (ha : 0 < a) (w : ℂ) (n : ℕ) :
    (((a : ℝ) : ℂ) ^ w) ^ n = ((a : ℝ) : ℂ) ^ ((n : ℂ) * w) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  rw [Complex.cpow_def_of_ne_zero hane, Complex.cpow_def_of_ne_zero hane,
    ← Complex.exp_nat_mul]
  congr 1
  ring

theorem burnolPosRealCpow_conj {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ((a : ℝ) : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ (((a : ℝ) : ℂ) ^ w) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hlog : Complex.log ((a : ℝ) : ℂ) = ((Real.log a : ℝ) : ℂ) :=
    Complex.ofReal_log ha.le ▸ rfl
  rw [Complex.cpow_def_of_ne_zero hane, Complex.cpow_def_of_ne_zero hane, ← Complex.exp_conj,
    hlog, map_mul, Complex.conj_ofReal]

/-! ## The causal dyadic symbol ladder -/

/-- **The causal dyadic expansion of the rational completion.** -/
theorem hasSum_burnolXiCompletionMultiplier {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun n : ℕ => 1 / 2 * w ^ 2 * (w - 1) * (2 : ℂ) ^ (-(((n : ℂ) + 1) * w)))
      (burnolXiCompletionMultiplier w) := by
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hne : (2 : ℂ) ^ w ≠ 0 := by
    rw [← htwo]
    exact Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h
      rw [h, Complex.zero_re] at hw
      linarith) |>.mpr (by norm_num)
  have hsub : (2 : ℂ) ^ w - 1 ≠ 0 := two_cpow_sub_one_ne_zero hw
  have hnorm : ‖(2 : ℂ) ^ (-w)‖ < 1 := by
    rw [← htwo, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), Complex.neg_re,
      show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hbase : HasSum (fun n : ℕ => ((2 : ℂ) ^ (-w)) ^ n) ((1 - (2 : ℂ) ^ (-w))⁻¹) :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hscaled := hbase.mul_left (1 / 2 * w ^ 2 * (w - 1) * (2 : ℂ) ^ (-w))
  have hfun : (fun n : ℕ => 1 / 2 * w ^ 2 * (w - 1) * (2 : ℂ) ^ (-w) * ((2 : ℂ) ^ (-w)) ^ n) =
      fun n : ℕ => 1 / 2 * w ^ 2 * (w - 1) * (2 : ℂ) ^ (-(((n : ℂ) + 1) * w)) := by
    funext n
    rw [← htwo, burnolPosRealCpow_natMul (by norm_num : (0 : ℝ) < 2), mul_assoc,
      ← Complex.cpow_add _ _ (by rw [htwo]; norm_num : ((2 : ℝ) : ℂ) ≠ 0)]
    congr 2
    ring
  have hval : 1 / 2 * w ^ 2 * (w - 1) * (2 : ℂ) ^ (-w) * (1 - (2 : ℂ) ^ (-w))⁻¹ =
      burnolXiCompletionMultiplier w := by
    rw [burnolXiCompletionMultiplier, Complex.cpow_neg]
    field_simp
  rw [hfun, hval] at hscaled
  exact hscaled

/-! ## The Gamma-sewn physical multiplier -/

/-- The raw (uncompleted) Mellin transform of the fixed prime-two Burnol source. -/
def burnolFixedAtomRawMellin (w : ℂ) : ℂ := ((2 : ℂ) ^ w - 1) * (riemannZeta w / w)

/-- The Gamma-sewn physical completion multiplier `M₂ = C₂ Γ_ℝ`. -/
def burnolPhysicalCollarMultiplier (w : ℂ) : ℂ :=
  burnolXiCompletionMultiplier w * Complex.Gammaℝ w

theorem burnolFixedAtomCompletedMellin_eq_gammaR_mul_raw {w : ℂ} (hw0 : 0 < w.re)
    (hw1 : w.re < 1) :
    burnolFixedAtomCompletedMellin w = Complex.Gammaℝ w * burnolFixedAtomRawMellin w := by
  rw [burnolFixedAtomCompletedMellin_eq hw0 hw1, burnolFixedAtomRawMellin]
  ring

/-- **The physical multiplier carries the raw source to `ξ`.** -/
theorem burnolPhysicalCollarMultiplier_mul_rawMellin {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolPhysicalCollarMultiplier w * burnolFixedAtomRawMellin w = xi w := by
  rw [burnolPhysicalCollarMultiplier,
    show burnolXiCompletionMultiplier w * Complex.Gammaℝ w * burnolFixedAtomRawMellin w =
      burnolXiCompletionMultiplier w * (Complex.Gammaℝ w * burnolFixedAtomRawMellin w) by ring,
    ← burnolFixedAtomCompletedMellin_eq_gammaR_mul_raw hw0 hw1,
    burnolXiCompletionMultiplier_mul_fixedAtomMellin hw0 hw1]

theorem burnolFixedAtomRawMellin_eq_zero_of_xi_eq_zero {rho : ℂ} (hrho0 : 0 < rho.re)
    (hrho1 : rho.re < 1) (hxi : xi rho = 0) : burnolFixedAtomRawMellin rho = 0 := by
  have hM : burnolPhysicalCollarMultiplier rho ≠ 0 := by
    rw [burnolPhysicalCollarMultiplier]
    exact mul_ne_zero (burnolXiCompletionMultiplier_ne_zero hrho0 hrho1)
      (Complex.Gammaℝ_ne_zero_of_re_pos hrho0)
  have hfac := burnolPhysicalCollarMultiplier_mul_rawMellin hrho0 hrho1
  rw [hxi] at hfac
  exact (mul_eq_zero.mp hfac).resolve_left hM

theorem differentiableAt_burnolFixedAtomRawMellin {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    DifferentiableAt ℂ burnolFixedAtomRawMellin w := by
  have hwne0 : w ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hw0; linarith
  have hwne1 : w ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hw1; linarith
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) w :=
    differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  unfold burnolFixedAtomRawMellin
  exact (hpow.sub (differentiableAt_const (c := (1 : ℂ)))).mul
    ((differentiableAt_riemannZeta hwne1).div differentiableAt_id hwne0)

theorem differentiableAt_burnolPhysicalCollarMultiplier {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    DifferentiableAt ℂ burnolPhysicalCollarMultiplier w := by
  unfold burnolPhysicalCollarMultiplier
  exact (differentiableAt_burnolXiCompletionMultiplier hw0 hw1).mul
    (Gammaℝ_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hw0)).differentiableAt

/-- **The raw-source-to-Xi operator landing on first divided vectors.** -/
theorem burnolPhysicalCollarMultiplier_mul_dslope_rawMellin {rho s : ℂ}
    (hrho0 : 0 < rho.re) (hrho1 : rho.re < 1) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hxi : xi rho = 0) :
    burnolPhysicalCollarMultiplier s * dslope burnolFixedAtomRawMellin rho s =
      dslope xi rho s := by
  have hH : burnolFixedAtomRawMellin rho = 0 :=
    burnolFixedAtomRawMellin_eq_zero_of_xi_eq_zero hrho0 hrho1 hxi
  rcases eq_or_ne s rho with rfl | hsr
  · rw [dslope_same, dslope_same]
    have hlocal :
        (fun z => burnolPhysicalCollarMultiplier z * burnolFixedAtomRawMellin z) =ᶠ[𝓝 s] xi := by
      have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
      exact burnolPhysicalCollarMultiplier_mul_rawMellin hz.1 hz.2
    rw [← hlocal.deriv_eq,
      deriv_fun_mul (differentiableAt_burnolPhysicalCollarMultiplier hrho0 hrho1)
        (differentiableAt_burnolFixedAtomRawMellin hrho0 hrho1), hH, mul_zero, zero_add]
  · rw [dslope_of_ne _ hsr, dslope_of_ne _ hsr, slope_def_field, slope_def_field, hH, hxi,
      sub_zero, sub_zero, ← burnolPhysicalCollarMultiplier_mul_rawMellin hs0 hs1]
    field_simp [sub_ne_zero.mpr hsr]

/-! ## Reflection on the critical line -/

theorem burnolGammaR_conj (w : ℂ) :
    Complex.Gammaℝ (starRingEnd ℂ w) = starRingEnd ℂ (Complex.Gammaℝ w) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · rw [show ((π : ℂ)) = ((Real.pi : ℝ) : ℂ) by norm_num,
      ← burnolPosRealCpow_conj Real.pi_pos]
    congr 1
    rw [map_div₀, map_neg, map_ofNat]
  · rw [show (starRingEnd ℂ) w / 2 = (starRingEnd ℂ) (w / 2) by rw [map_div₀, map_ofNat],
      Complex.Gamma_conj]

theorem burnolXiCompletionMultiplier_conj (w : ℂ) :
    burnolXiCompletionMultiplier (starRingEnd ℂ w) =
      starRingEnd ℂ (burnolXiCompletionMultiplier w) := by
  rw [burnolXiCompletionMultiplier, burnolXiCompletionMultiplier, map_div₀, map_mul, map_mul,
    map_pow, map_sub, map_one, map_ofNat, map_sub, map_one]
  congr 2
  rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num,
    ← burnolPosRealCpow_conj (by norm_num : (0 : ℝ) < 2)]

/-- **The reflected orientation is the conjugate on the critical line.**  Equivalently, the
logarithmic kernel of `M₂` is real and `M₂^∨` has the reflected kernel `u ↦ κ₂(-u)`. -/
theorem burnolPhysicalCollarMultiplier_reflection {w : ℂ} (hw : w.re = 1 / 2) :
    burnolPhysicalCollarMultiplier (1 - w) =
      starRingEnd ℂ (burnolPhysicalCollarMultiplier w) := by
  have hconj : (1 : ℂ) - w = starRingEnd ℂ w := by
    apply Complex.ext
    · simp [Complex.sub_re, hw]
      norm_num
    · simp [Complex.sub_im]
  rw [hconj, burnolPhysicalCollarMultiplier, burnolPhysicalCollarMultiplier,
    burnolXiCompletionMultiplier_conj, burnolGammaR_conj, map_mul]

/-! ## The archimedean collar kernel is the Gamma factor -/

theorem range_burnolNegExp : Set.range (fun u : ℝ => Real.exp (-u)) = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨u, rfl⟩
    exact Real.exp_pos _
  · intro hr
    refine ⟨-Real.log r, ?_⟩
    show Real.exp (-(-Real.log r)) = r
    rw [neg_neg, Real.exp_log hr]

theorem integral_burnolNegExpSubstitution (F : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), F r) = ∫ u : ℝ, Real.exp (-u) • F (Real.exp (-u)) := by
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-u)) Set.univ u := by
    intro u _
    have h : HasDerivAt (fun v : ℝ => Real.exp (-v)) (Real.exp (-u) * (-1)) u :=
      ((hasDerivAt_id u).neg).exp
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => Real.exp (-u)) Set.univ := by
    intro u _ v _ huv
    have := Real.exp_eq_exp.mp huv
    linarith
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => Real.exp (-u)) (f' := fun u : ℝ => -Real.exp (-u))
    (s := Set.univ) MeasurableSet.univ hderiv hinj F
  rw [Set.image_univ, range_burnolNegExp, MeasureTheory.setIntegral_univ] at hcov
  rw [hcov]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with u
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]

theorem burnolNegExp_cpow (u : ℝ) (s : ℂ) :
    (((Real.exp (-u) : ℝ)) : ℂ) ^ s = Complex.exp (s * ((-u : ℝ) : ℂ)) := by
  have hne : (((Real.exp (-u) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have hlog : Complex.log (((Real.exp (-u) : ℝ)) : ℂ) = ((-u : ℝ) : ℂ) := by
    rw [show (((Real.exp (-u) : ℝ)) : ℂ) = Complex.exp (((-u : ℝ) : ℂ)) by
      rw [← Complex.ofReal_exp]]
    exact Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  ring_nf

/-- The Fourier transform of the archimedean collar density. -/
def burnolCollarGammaFourier (t : ℝ) : ℂ :=
  ∫ u : ℝ, ((burnolCollarGamma u : ℝ) : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))

/-- **The archimedean collar density has Fourier transform `Γ_ℝ(1/2 + it)`.** -/
theorem burnolCollarGammaFourier_eq (t : ℝ) :
    burnolCollarGammaFourier t = Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ)) := by
  set s : ℂ := 1 / 2 + Complex.I * (t : ℂ) with hs
  have hsre : s.re = 1 / 2 := by
    rw [hs]
    simp [Complex.add_re, Complex.mul_re]
  have hspos : 0 < s.re := by rw [hsre]; norm_num
  have hmel := GaloisForLFunctions.HTGeometry.mellin_gaussianKernel (z := s) hspos
  rw [mellin, integral_burnolNegExpSubstitution] at hmel
  have hpoint : ∀ u : ℝ,
      Real.exp (-u) • ((((Real.exp (-u) : ℝ)) : ℂ) ^ (s - 1) •
          GaloisForLFunctions.HTGeometry.gaussianKernel (Real.exp (-u))) =
        ((burnolCollarGamma u : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))) / 2 := by
    intro u
    have hx : (((Real.exp (-u) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
    have hmul : (((Real.exp (-u) : ℝ)) : ℂ) * (((Real.exp (-u) : ℝ)) : ℂ) ^ (s - 1) =
        (((Real.exp (-u) : ℝ)) : ℂ) ^ s := by
      nth_rewrite 1 [← Complex.cpow_one (((Real.exp (-u) : ℝ)) : ℂ)]
      rw [← Complex.cpow_add _ _ hx]
      congr 1
      ring
    have hgk : GaloisForLFunctions.HTGeometry.gaussianKernel (Real.exp (-u)) =
        ((Real.exp (-(π * Real.exp (-2 * u))) : ℝ) : ℂ) := by
      rw [GaloisForLFunctions.HTGeometry.gaussianKernel]
      congr 2
      rw [← Real.exp_nat_mul]
      ring_nf
    have hcpow : (((Real.exp (-u) : ℝ)) : ℂ) ^ s =
        ((Real.exp (-u / 2) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))) := by
      rw [burnolNegExp_cpow, hs]
      rw [show ((1 : ℂ) / 2 + Complex.I * (t : ℂ)) * ((-u : ℝ) : ℂ) =
          ((-u / 2 : ℝ) : ℂ) + -(Complex.I * (t : ℂ) * (u : ℂ)) by push_cast; ring,
        Complex.exp_add, ← Complex.ofReal_exp]
    rw [smul_eq_mul, Complex.real_smul, ← mul_assoc, hmul, hgk, hcpow,
      burnolCollarGamma_apply]
    push_cast
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)] at hmel
  have hdiv : (∫ u : ℝ, ((burnolCollarGamma u : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))) / 2) =
      burnolCollarGammaFourier t / 2 := by
    rw [burnolCollarGammaFourier, ← MeasureTheory.integral_div]
  rw [hdiv] at hmel
  field_simp at hmel
  linear_combination hmel

end RHTower
