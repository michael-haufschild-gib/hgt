import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

/-!
# Fixed Taylor moduli and hypertranscendence do not select real-rootedness
-/

namespace GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

local instance fmDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance fmRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance fmDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance fmRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance fmDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

/-! ## Hölder's theorem for reciprocal-Gamma translates -/

/-- The shifted reciprocal-Gamma function is entire. -/
theorem analyticOnNhd_reciprocalGammaTranslate (x : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => reciprocalGammaEntire (z + x)) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp
    (differentiable_id.add (differentiable_const x))

/-- Its global meromorphic realization is the reciprocal-Gamma orbit element of charge `-1`. -/
theorem analyticMeroElement_reciprocalGammaTranslate (x : ℂ) :
    analyticMeroElement (fun z : ℂ => reciprocalGammaEntire (z + x))
        (analyticOnNhd_reciprocalGammaTranslate x)
      = gammaOrbitProductMero (fun _ : Fin 1 => x) (fun _ => (-1 : ℤ)) := by
  rw [gammaOrbitProductMero, Fin.prod_univ_one, gammaShiftMero, zpow_neg, zpow_one, inv_inv,
    analyticMeroElement]
  congr 1

/-- **Every reciprocal-Gamma translate is hypertranscendental.**  Hölder's theorem in the
orbit-charge form: a single reciprocal-Gamma factor carries charge `-1 ≠ 0`. -/
theorem hypertranscendental_reciprocalGammaTranslate (x : ℂ) :
    Hypertranscendental (fun z : ℂ => reciprocalGammaEntire (z + x)) := by
  intro hDA
  have hDAover := differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
    (analyticOnNhd_reciprocalGammaTranslate x) hDA
  rw [analyticMeroElement_reciprocalGammaTranslate x] at hDAover
  exact hypertranscendentalOver_gammaOrbitProductMero (fun _ : Fin 1 => x) (fun _ => (-1 : ℤ)) 0
    (by decide) (fun c hc => absurd (Subsingleton.elim c 0) hc) hDAover

theorem hypertranscendental_reciprocalGammaEntire :
    Hypertranscendental reciprocalGammaEntire := by
  have h := hypertranscendental_reciprocalGammaTranslate 0
  simpa using h

/-! ## A full-support base point -/

/-- **A hypertranscendental function has no identically vanishing derivative.**  The jet variable
`Yₙ` is itself a nonzero differential polynomial, so `f⁽ⁿ⁾ ≡ 0` is already an algebraic
differential equation. -/
theorem exists_iteratedDeriv_ne_zero_of_hypertranscendental {f : ℂ → ℂ}
    (hf : Hypertranscendental f) (n : ℕ) : ∃ z : ℂ, iteratedDeriv n f z ≠ 0 := by
  by_contra hcon
  refine hf ⟨n, MvPolynomial.X (Fin.succ (Fin.last n)), MvPolynomial.X_ne_zero _, fun z => ?_⟩
  rw [MvPolynomial.eval_X, Fin.cons_succ]
  simpa using not_not.mp (not_exists.mp hcon z)

/-- Every iterated derivative of the entire reciprocal Gamma function is entire. -/
theorem analyticOnNhd_iteratedDeriv_reciprocalGammaEntire (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n reciprocalGammaEntire) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact (contDiff_iteratedDeriv n (contDiff_reciprocalGammaEntire.of_le le_top)).differentiable
    (by simp)

theorem not_countable_Ioi_zero : ¬ (Set.Ioi (0 : ℝ)).Countable := by
  intro h
  have h0 : MeasureTheory.volume (Set.Ioi (0 : ℝ)) = 0 := h.measure_zero _
  rw [Real.volume_Ioi] at h0
  simp at h0

/-- **A positive real base at which every reciprocal-Gamma derivative is nonzero.**  Each
derivative is a nonzero entire function by hypertranscendence, so its real zero set is countable;
the countable union cannot exhaust `(0,∞)`. -/
theorem exists_pos_base_all_iteratedDeriv_ne_zero :
    ∃ x : ℝ, 0 < x ∧ ∀ n : ℕ, iteratedDeriv n reciprocalGammaEntire ((x : ℝ) : ℂ) ≠ 0 := by
  classical
  set B : Set ℝ := {t : ℝ | ∃ n : ℕ, iteratedDeriv n reciprocalGammaEntire ((t : ℝ) : ℂ) = 0}
    with hBdef
  have hBcount : B.Countable := by
    have hunion : B = ⋃ n : ℕ,
        {t : ℝ | iteratedDeriv n reciprocalGammaEntire ((t : ℝ) : ℂ) = 0} := by
      ext t
      simp [hBdef]
    rw [hunion]
    refine Set.countable_iUnion (fun n => ?_)
    have hcz : {z : ℂ | iteratedDeriv n reciprocalGammaEntire z = 0}.Countable :=
      _root_.HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd
        (analyticOnNhd_iteratedDeriv_reciprocalGammaEntire n)
        (exists_iteratedDeriv_ne_zero_of_hypertranscendental
          hypertranscendental_reciprocalGammaEntire n)
    exact hcz.preimage Complex.ofReal_injective
  have hnsub : ¬ (Set.Ioi (0 : ℝ) ⊆ B) := by
    intro hsub
    exact not_countable_Ioi_zero (hBcount.mono hsub)
  obtain ⟨x, hxpos, hxB⟩ := Set.not_subset.mp hnsub
  refine ⟨x, hxpos, fun n hn => hxB ?_⟩
  exact ⟨n, hn⟩

/-- The chosen full-support base point. -/
def fmBase : ℝ := exists_pos_base_all_iteratedDeriv_ne_zero.choose

theorem fmBase_pos : 0 < fmBase :=
  exists_pos_base_all_iteratedDeriv_ne_zero.choose_spec.1

theorem iteratedDeriv_reciprocalGammaEntire_fmBase_ne_zero (n : ℕ) :
    iteratedDeriv n reciprocalGammaEntire ((fmBase : ℝ) : ℂ) ≠ 0 :=
  exists_pos_base_all_iteratedDeriv_ne_zero.choose_spec.2 n

/-! ## The all-real-divisor carrier -/

/-- The real-rooted hypertranscendental carrier `z ↦ 1/Γ(z + x₀)`. -/
def realCarrier (z : ℂ) : ℂ := reciprocalGammaEntire (z + (fmBase : ℂ))

theorem contDiff_realCarrier : ContDiff ℂ (⊤ : ℕ∞) realCarrier :=
  (contDiff_reciprocalGammaEntire.of_le le_top).comp
    (contDiff_id.add (contDiff_const : ContDiff ℂ (⊤ : ℕ∞) fun _ : ℂ => (fmBase : ℂ)))

theorem hypertranscendental_realCarrier : Hypertranscendental realCarrier :=
  hypertranscendental_reciprocalGammaTranslate (fmBase : ℂ)

/-- The divisor of the carrier is the negative real progression `−x₀ − m`. -/
theorem realCarrier_eq_zero_iff (z : ℂ) :
    realCarrier z = 0 ↔ ∃ m : ℕ, z = -(fmBase : ℂ) - (m : ℂ) := by
  rw [realCarrier, reciprocalGammaEntire, inv_eq_zero, Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linear_combination hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; ring⟩

/-- **Every zero of the carrier is real.** -/
theorem im_eq_zero_of_realCarrier_eq_zero {z : ℂ} (hz : realCarrier z = 0) : z.im = 0 := by
  obtain ⟨m, hm⟩ := (realCarrier_eq_zero_iff z).mp hz
  rw [hm]
  simp

/-- The carrier has infinitely many zeros, so real-rootedness is not vacuous. -/
theorem infinite_zeros_realCarrier : {z : ℂ | realCarrier z = 0}.Infinite := by
  have hinj : Function.Injective (fun m : ℕ => -(fmBase : ℂ) - (m : ℂ)) := by
    intro a b hab
    simp only [sub_right_inj] at hab
    exact_mod_cast hab
  have hsub : Set.range (fun m : ℕ => -(fmBase : ℂ) - (m : ℂ)) ⊆ {z : ℂ | realCarrier z = 0} := by
    rintro z ⟨m, rfl⟩
    exact (realCarrier_eq_zero_iff _).mpr ⟨m, rfl⟩
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)

/-- **Full support.**  Every Taylor coefficient of the carrier is nonzero. -/
theorem coeff_taylorPS_realCarrier_ne_zero (n : ℕ) :
    PowerSeries.coeff n (taylorPS realCarrier) ≠ 0 := by
  rw [coeff_taylorPS]
  refine div_ne_zero ?_ ?_
  · have hshift : iteratedDeriv n realCarrier
        = fun t : ℂ => iteratedDeriv n reciprocalGammaEntire (t + (fmBase : ℂ)) :=
      iteratedDeriv_comp_add_const n reciprocalGammaEntire (fmBase : ℂ)
    rw [hshift]
    simpa using iteratedDeriv_reciprocalGammaEntire_fmBase_ne_zero n
  · exact_mod_cast Nat.factorial_ne_zero n

end

end GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness

namespace GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

/-- The constant Taylor coefficient of the carrier is the positive real `1/Γ(x₀)`. -/
def fmConst : ℝ := (Real.Gamma fmBase)⁻¹

theorem fmConst_pos : 0 < fmConst := inv_pos.mpr (Real.Gamma_pos_of_pos fmBase_pos)

theorem realCarrier_zero_eq : realCarrier 0 = (fmConst : ℂ) := by
  rw [realCarrier, zero_add, reciprocalGammaEntire, Complex.Gamma_ofReal, fmConst,
    Complex.ofReal_inv]

theorem realCarrier_neg_base : realCarrier (-(fmBase : ℂ)) = 0 := by
  rw [realCarrier]
  simp [reciprocalGammaEntire]

/-- The base zero `−x₀` is simple with derivative `1`. -/
theorem hasDerivAt_realCarrier_neg_base :
    HasDerivAt realCarrier 1 (-(fmBase : ℂ)) := by
  have hE : HasDerivAt reciprocalGammaEntire 1 (-(fmBase : ℂ) + (fmBase : ℂ)) := by
    have h := hasDerivAt_oneDivGamma_neg_nat 0
    simp only [Nat.cast_zero, neg_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul] at h
    have hz : -(fmBase : ℂ) + (fmBase : ℂ) = 0 := by ring
    rw [hz]
    exact h
  exact HasDerivAt.comp_add_const _ _ hE

theorem hasStrictDerivAt_realCarrier_neg_base :
    HasStrictDerivAt realCarrier 1 (-(fmBase : ℂ)) := by
  have hstrict := (contDiff_realCarrier.contDiffAt (x := -(fmBase : ℂ))).hasStrictDerivAt
    (by simp)
  rwa [hasDerivAt_realCarrier_neg_base.deriv] at hstrict

/-- The unit phase factor. -/
def phaseUnit (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem norm_phaseUnit (t : ℝ) : ‖phaseUnit t‖ = 1 := by
  rw [phaseUnit]
  exact Complex.norm_exp_ofReal_mul_I t

theorem phaseUnit_zero : phaseUnit 0 = 1 := by simp [phaseUnit]

/-- The companion carrier: the same function with only the constant Taylor coefficient rotated. -/
def phaseCarrier (t : ℝ) (z : ℂ) : ℂ :=
  realCarrier z + (phaseUnit t - 1) * realCarrier 0

theorem phaseCarrier_zero_eq (t : ℝ) :
    phaseCarrier t 0 = phaseUnit t * realCarrier 0 := by
  rw [phaseCarrier]; ring

theorem iteratedDeriv_succ_phaseCarrier (t : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (phaseCarrier t) = iteratedDeriv (n + 1) realCarrier := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  congr 1
  funext z
  exact deriv_add_const _

/-- **Identical Taylor moduli.**  The phase companion has exactly the coefficient magnitudes of
the carrier. -/
theorem norm_coeff_phaseCarrier (t : ℝ) (n : ℕ) :
    ‖PowerSeries.coeff n (taylorPS (phaseCarrier t))‖
      = ‖PowerSeries.coeff n (taylorPS realCarrier)‖ := by
  cases n with
  | zero =>
      rw [coeff_taylorPS, coeff_taylorPS, iteratedDeriv_zero, iteratedDeriv_zero,
        phaseCarrier_zero_eq]
      simp [norm_phaseUnit]
  | succ n =>
      rw [coeff_taylorPS, coeff_taylorPS, iteratedDeriv_succ_phaseCarrier]

/-- **The phase companion is hypertranscendental.**  It differs from the carrier by a constant,
and adding a polynomial never changes differential algebraicity. -/
theorem hypertranscendental_phaseCarrier (t : ℝ) : Hypertranscendental (phaseCarrier t) := by
  have hpoly : phaseCarrier t
      = fun z : ℂ => realCarrier z
        + Polynomial.eval z (Polynomial.C ((phaseUnit t - 1) * realCarrier 0)) := by
    funext z
    simp [phaseCarrier]
  rw [hpoly]
  exact (hypertranscendental_add_polynomial_iff contDiff_realCarrier _).mpr
    hypertranscendental_realCarrier

theorem contDiff_phaseCarrier (t : ℝ) : ContDiff ℂ (⊤ : ℕ∞) (phaseCarrier t) :=
  contDiff_realCarrier.add contDiff_const

end

end GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness


namespace GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

/-- The imaginary part of a differentiable complex path is differentiable. -/
theorem hasDerivAt_im_of_hasDerivAt {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (h : HasDerivAt g g' x) :
    HasDerivAt (fun t => (g t).im) g'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/-- **Transverse motion of a simple zero.**  If `ρ` is a simple real zero of `f` and a real
one-parameter family of constants `w` leaves the origin with velocity `v` transverse to the real
axis after division by `f'(ρ)`, then for some parameter the equation `f z = w t` has a solution
off the real axis.  This is the analytic inverse function theorem plus a first-order slope
argument; no zero count and no Rouché step is needed. -/
theorem exists_perturbed_zero_off_axis {f : ℂ → ℂ} {ρ c v : ℂ} {w : ℝ → ℂ}
    (hf : HasStrictDerivAt f c ρ) (hc : c ≠ 0) (hfρ : f ρ = 0) (hρ : ρ.im = 0)
    (hw0 : w 0 = 0) (hwd : HasDerivAt w v 0) (hv : (v * c⁻¹).im ≠ 0) :
    ∃ t : ℝ, ∃ z : ℂ, f z = w t ∧ z.im ≠ 0 := by
  classical
  have hψ0 : HasStrictDerivAt.localInverse f c ρ hf hc 0 = ρ := by
    have hleft := (hf.eventually_left_inverse hc).self_of_nhds
    rwa [hfρ] at hleft
  have hψderiv : HasStrictDerivAt (HasStrictDerivAt.localInverse f c ρ hf hc) c⁻¹ 0 := by
    have h := hf.to_localInverse hc
    rwa [hfρ] at h
  have hright : ∀ᶠ y in 𝓝 (0 : ℂ), f (HasStrictDerivAt.localInverse f c ρ hf hc y) = y := by
    have h := hf.eventually_right_inverse hc
    rwa [hfρ] at h
  have hat : HasDerivAt (HasStrictDerivAt.localInverse f c ρ hf hc) c⁻¹ (w 0) := by
    rw [hw0]; exact hψderiv.hasDerivAt
  have hρderiv : HasDerivAt
      (fun t : ℝ => HasStrictDerivAt.localInverse f c ρ hf hc (w t)) (v * c⁻¹) 0 :=
    HasDerivAt.scomp (0 : ℝ) hat hwd
  have huderiv : HasDerivAt
      (fun t : ℝ => (HasStrictDerivAt.localInverse f c ρ hf hc (w t)).im) (v * c⁻¹).im 0 :=
    hasDerivAt_im_of_hasDerivAt hρderiv
  have hu0 : (HasStrictDerivAt.localInverse f c ρ hf hc (w 0)).im = 0 := by
    rw [hw0, hψ0]; exact hρ
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      slope (fun t : ℝ => (HasStrictDerivAt.localInverse f c ρ hf hc (w t)).im) 0 t ≠ 0 :=
    (hasDerivAt_iff_tendsto_slope.mp huderiv).eventually_ne hv
  have hcont : Filter.Tendsto w (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [← hw0]; exact hwd.continuousAt
  have hrighteq : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      f (HasStrictDerivAt.localInverse f c ρ hf hc (w t)) = w t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont.eventually hright)
  obtain ⟨t, hslt, hrt⟩ := (hne.and hrighteq).exists
  refine ⟨t, HasStrictDerivAt.localInverse f c ρ hf hc (w t), hrt, ?_⟩
  intro him
  apply hslt
  rw [slope_def_field]
  simp [him, hu0]

/-- **A nonreal zero appears under a phase rotation of the constant coefficient alone.** -/
theorem exists_phase_nonreal_zero : ∃ t : ℝ, ∃ z : ℂ, phaseCarrier t z = 0 ∧ z.im ≠ 0 := by
  have hstrict := hasStrictDerivAt_realCarrier_neg_base
  have h1 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ) * Complex.I) Complex.I 0 := by
    have h := h1.mul_const Complex.I
    rwa [one_mul] at h
  have h3 : HasDerivAt phaseUnit Complex.I 0 := by
    have h := h2.cexp
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at h
    exact h
  have hwd : HasDerivAt (fun t : ℝ => -((phaseUnit t - 1) * realCarrier 0))
      (-(Complex.I * realCarrier 0)) 0 := ((h3.sub_const 1).mul_const (realCarrier 0)).neg
  have hv : ((-(Complex.I * realCarrier 0)) * (1 : ℂ)⁻¹).im ≠ 0 := by
    have h : ((-(Complex.I * realCarrier 0)) * (1 : ℂ)⁻¹).im = -fmConst := by
      rw [realCarrier_zero_eq]; simp
    rw [h]
    exact neg_ne_zero.mpr fmConst_pos.ne'
  have hw0 : (fun t : ℝ => -((phaseUnit t - 1) * realCarrier 0)) 0 = 0 := by
    simp [phaseUnit_zero]
  obtain ⟨t, z, hz, him⟩ := exists_perturbed_zero_off_axis hstrict one_ne_zero
    realCarrier_neg_base (by simp) hw0 hwd hv
  refine ⟨t, z, ?_, him⟩
  rw [phaseCarrier, hz]
  ring

end

end GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness

namespace GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

/-- The phase parameter realizing a nonreal zero. -/
def fmPhase : ℝ := exists_phase_nonreal_zero.choose

/-- The phase companion of the carrier. -/
def phaseCompanion : ℂ → ℂ := phaseCarrier fmPhase

theorem exists_nonreal_zero_phaseCompanion : ∃ z : ℂ, phaseCompanion z = 0 ∧ z.im ≠ 0 :=
  exists_phase_nonreal_zero.choose_spec

/-- **Fixed Taylor moduli together with hypertranscendence do not select real-rootedness.**

There is one full-support Taylor-modulus profile carrying both a hypertranscendental entire
function whose whole (infinite) divisor is real and a hypertranscendental entire function with a
nonreal zero. -/
theorem fixedModulus_hypertranscendence_real_rootedness_nonselection :
    ∃ f g : ℂ → ℂ,
      ContDiff ℂ (⊤ : ℕ∞) f ∧ ContDiff ℂ (⊤ : ℕ∞) g ∧
      Hypertranscendental f ∧ Hypertranscendental g ∧
      (∀ n : ℕ, ‖PowerSeries.coeff n (taylorPS f)‖
        = ‖PowerSeries.coeff n (taylorPS g)‖) ∧
      (∀ n : ℕ, PowerSeries.coeff n (taylorPS f) ≠ 0) ∧
      (∀ z : ℂ, f z = 0 → z.im = 0) ∧
      {z : ℂ | f z = 0}.Infinite ∧
      (∃ z : ℂ, g z = 0 ∧ z.im ≠ 0) := by
  refine ⟨realCarrier, phaseCompanion, contDiff_realCarrier, contDiff_phaseCarrier _,
    hypertranscendental_realCarrier, hypertranscendental_phaseCarrier _, ?_,
    coeff_taylorPS_realCarrier_ne_zero, fun z hz => im_eq_zero_of_realCarrier_eq_zero hz,
    infinite_zeros_realCarrier, exists_nonreal_zero_phaseCompanion⟩
  intro n
  exact (norm_coeff_phaseCarrier fmPhase n).symm

/-- **Phase form.**  Both functions are recovered from one positive full-support modulus profile by
two phase sequences. -/
theorem exists_common_modulus_profile_phases :
    ∃ (r : ℕ → ℝ) (θ φ : ℕ → ℝ) (f g : ℂ → ℂ),
      (∀ n : ℕ, 0 < r n) ∧
      (∀ n : ℕ, PowerSeries.coeff n (taylorPS f)
        = (r n : ℂ) * Complex.exp ((θ n : ℂ) * Complex.I)) ∧
      (∀ n : ℕ, PowerSeries.coeff n (taylorPS g)
        = (r n : ℂ) * Complex.exp ((φ n : ℂ) * Complex.I)) ∧
      Hypertranscendental f ∧ Hypertranscendental g ∧
      (∀ z : ℂ, f z = 0 → z.im = 0) ∧
      {z : ℂ | f z = 0}.Infinite ∧
      (∃ z : ℂ, g z = 0 ∧ z.im ≠ 0) := by
  refine ⟨fun n => ‖PowerSeries.coeff n (taylorPS realCarrier)‖,
    fun n => (PowerSeries.coeff n (taylorPS realCarrier)).arg,
    fun n => (PowerSeries.coeff n (taylorPS phaseCompanion)).arg,
    realCarrier, phaseCompanion, ?_, ?_, ?_,
    hypertranscendental_realCarrier, hypertranscendental_phaseCarrier _,
    fun z hz => im_eq_zero_of_realCarrier_eq_zero hz,
    infinite_zeros_realCarrier, exists_nonreal_zero_phaseCompanion⟩
  · intro n
    exact norm_pos_iff.mpr (coeff_taylorPS_realCarrier_ne_zero n)
  · intro n
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  · intro n
    have hnorm : ‖PowerSeries.coeff n (taylorPS phaseCompanion)‖
        = ‖PowerSeries.coeff n (taylorPS realCarrier)‖ := norm_coeff_phaseCarrier fmPhase n
    simp only [← hnorm]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm

/-- **No selector factoring through the Taylor-modulus profile can imply real-rootedness.**
Whatever invariant `Φ` of the modulus profile one forms — Newton polygon, maximum-term function,
order, type, support — it takes the same value on a real-rooted hypertranscendental function and on
a hypertranscendental function with a nonreal zero. -/
theorem modulusProfile_selector_blind {α : Type*} (Φ : (ℕ → ℝ) → α) :
    ∃ f g : ℂ → ℂ,
      Hypertranscendental f ∧ Hypertranscendental g ∧
      Φ (fun n => ‖PowerSeries.coeff n (taylorPS f)‖)
        = Φ (fun n => ‖PowerSeries.coeff n (taylorPS g)‖) ∧
      (∀ z : ℂ, f z = 0 → z.im = 0) ∧
      {z : ℂ | f z = 0}.Infinite ∧
      (∃ z : ℂ, g z = 0 ∧ z.im ≠ 0) := by
  refine ⟨realCarrier, phaseCompanion, hypertranscendental_realCarrier,
    hypertranscendental_phaseCarrier _, ?_,
    fun z hz => im_eq_zero_of_realCarrier_eq_zero hz,
    infinite_zeros_realCarrier, exists_nonreal_zero_phaseCompanion⟩
  congr 1
  funext n
  exact (norm_coeff_phaseCarrier fmPhase n).symm

end

end GaloisForLFunctions.HTGeometry.FixedModulusRealRootedness
