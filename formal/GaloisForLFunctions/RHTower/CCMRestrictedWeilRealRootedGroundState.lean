import GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
import GaloisForLFunctions.RHTower.FreeLagTraceCertificateObstruction
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundState
import GaloisForLFunctions.RHTower.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# Real-rooted polar ground states of the restricted Weil form

For a positive aperture `a`, a vector `u` of the CCM form domain has a time function `f_u`
supported in `[-a, a]` (`timeRep`) whose Fourier–Laplace transform
`f̂_u(w) = ∫ e^{-2πiwx} f_u(x) dx` is entire.  The polar constraints say `f̂_u(w_{±1/2}) = 0` with
`w_s = is/(2π)` (`isPolarConstrained_iff`), and on polar vectors the restricted Weil quadratic
form is `Q(u) = ∫ S_a(ξ) |f̂_u(ξ)|² dξ`, where `S_a` is the archimedean symbol minus the prime atoms
`n ≤ e^{2a}` (`source_eq_integral`).  A polar ground state is a polar vector with
`Q(u) = μ_a ‖J u‖²`, `μ_a` the polar ground energy.

**Theorem** (`exists_realRooted_polarGround`).  At every aperture some nonzero polar ground state
has a transform whose zeros other than `w_{±1/2}` are all real.  No simplicity of the ground level
is assumed.

**Proof.**
* Division (`exists_div`): if `f̂_u(w₀) = 0`, then `f̂_u(w)/(w − w₀)` is the transform of a
  form-domain vector `v`; its time function is supported in `[-a, a]`, and its frequency function
  is dominated by `|f̂_u|` at distance `≥ 1` from `Re w₀` and is bounded near `Re w₀`.
* Splitting (`isPolarGround_div`): on `ℝ`,
  `|f̂_u|² = |f̂_u + i Im w₀ · f̂_v|² + (Im w₀)² |f̂_v|²`.  Both pieces are polar vectors, so `Q`
  and `‖J ·‖²` split additively and minimality makes both pieces ground states; hence so is `v`.
* Finite multiplicity (`finiteDimensional_groundSubmodule`): the ground states form a closed
  subspace, since the excess `Q − μ_a ‖J ·‖²` is a nonnegative quadratic form on polar vectors.  On
  this subspace `‖u‖² ≤ (μ_a + ‖R‖) ‖J u‖²`, so the compact embedding `J` is antilipschitz and the
  closed unit ball is compact.
* Chain: if every nonzero ground state had a non-real zero off `w_{±1/2}`, iterated division would
  give ground states with transforms `f̂₀(ξ)/∏_{l<k}(ξ − z_l)` for every `k`.  These are linearly
  independent because their pole orders differ, which contradicts finite dimension.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct

namespace RHTower.CCMRealRootedGround

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision

variable (a : SuzukiPositiveAperture)

/-- The time function of a form-domain vector, extended by zero off the aperture. -/
def timeRep (u : CCMArchimedeanFormDomain a) : ℝ → ℂ :=
  (centralInterval a.1).indicator
    (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ)

theorem supportedIn_timeRep (u : CCMArchimedeanFormDomain a) : SupportedIn a.1 (timeRep a u) :=
  fun _ hx => indicator_of_notMem hx _

theorem coeFn_eq_timeRep (u : CCMArchimedeanFormDomain a) :
    (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] timeRep a u := by
  have hfix := indicatorCutoff_ccmArchimedeanFormEmbedding a u
  have hae := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
    (ccmArchimedeanFormEmbedding a u)
  rw [hfix] at hae
  exact hae

theorem integrable_timeRep (u : CCMArchimedeanFormDomain a) : Integrable (timeRep a u) := by
  have hmem : MemLp (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) :
      ℝ → ℂ) 2 (volume.restrict (centralInterval a.1)) := (Lp.memLp _).restrict _
  haveI : IsFiniteMeasure (volume.restrict (centralInterval a.1)) := by
    rw [centralInterval]
    exact isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  exact IntegrableOn.integrable_indicator (hmem.integrable (by norm_num))
    (measurableSet_centralInterval a.1)

/-- The frequency function is the Fourier–Laplace transform of the time function on `ℝ`. -/
theorem freq_ae (u : CCMArchimedeanFormDomain a) :
    ((u.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => unitaryLaplace (timeRep a u) ξ := by
  set f : SoninL2 := ((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2)
  have hfint : Integrable (f : ℝ → ℂ) :=
    (integrable_timeRep a u).congr (coeFn_eq_timeRep a u).symm
  have h1 : ((u.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) =ᵐ[volume]
      (ccmArchimedeanWeightedToL2 u.1 : ℝ → ℂ) := (ccmArchimedeanWeightedToL2_coeFn u.1).symm
  have h2 : ccmArchimedeanWeightedToL2 u.1 = fourierUnitary f :=
    (fourierUnitary_ccmArchimedeanFourierToTime u.1).symm
  have h3 := l2_fourier_coeFn_eq_l1_fourier_of_integrable f hfint
  have h4 : (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hfint).toLp f) : ℝ → ℂ) =
      FourierTransform.fourier (f : ℝ → ℂ) := Real.fourierTransform_toLp _
  rw [h2] at h1
  refine h1.trans (h3.trans ?_)
  rw [h4]
  refine Eventually.of_forall fun ξ => ?_
  rw [Real.fourier_congr_ae (coeFn_eq_timeRep a u)]
  exact (unitaryLaplace_ofReal _ ξ).symm

/-- The polar evaluation point `w_s = i s/(2π)`, where `e^{-2πi w_s x} = e^{s x}`. -/
def polarPoint (s : ℝ) : ℂ := I * s / (2 * Real.pi)

theorem inner_polar_eq (u : CCMArchimedeanFormDomain a) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s) (ccmArchimedeanFormToAperture a u) =
      unitaryLaplace (timeRep a u) (polarPoint s) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def, unitaryLaplace]
  refine integral_congr_ae ?_
  have hp : ((ccmPolarApertureVector a s : suzukiApertureHilbert a) : SoninL2) =
      ccmPolarL2Vector a s := rfl
  rw [hp]
  filter_upwards [ccmPolarL2Vector_coeFn a s, coeFn_eq_timeRep a u] with x hpx hfx
  rw [hpx, hfx, RCLike.inner_apply]
  have hexp : cexp (-(2 * Real.pi * I * polarPoint s * x)) = cexp (s * x) := by
    congr 1
    unfold polarPoint
    field_simp
    rw [I_sq]; ring
  rw [hexp]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, ccmPolarProfile, timeRep, indicator_of_mem hx]
    rw [Complex.conj_ofReal, Complex.ofReal_exp]
    push_cast
    ring
  · rw [indicator_of_notMem hx, timeRep, indicator_of_notMem hx]
    simp

/-- Both polar constraints say that the transform vanishes at `w_{±1/2}`. -/
theorem isPolarConstrained_iff (u : CCMArchimedeanFormDomain a) :
    IsPolarConstrained a u ↔ unitaryLaplace (timeRep a u) (polarPoint (1 / 2)) = 0 ∧
      unitaryLaplace (timeRep a u) (polarPoint (-1 / 2)) = 0 := by
  unfold IsPolarConstrained
  rw [inner_polar_eq, inner_polar_eq]

/-- The level-`a` symbol: the archimedean symbol minus the atoms `n ≤ e^{2a}`. -/
def levelSymbol (ξ : ℝ) : ℝ :=
  weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (Nat.floor (Real.exp (2 * a.1))) ξ

theorem source_eq_integral (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    ccmRestrictedWeilSourceQuadratic a u =
      ∫ ξ : ℝ, levelSymbol a ξ * ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2 := by
  rw [← ccmRestrictedWeilSourceQuadraticWith_eq a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    le_rfl (fun n _ _ => rfl) u, ccmRestrictedWeilSourceQuadraticWith_eq_integral_symbol a _ _ u hu]
  refine integral_congr_ae ?_
  filter_upwards [freq_ae a u] with ξ hξ
  rw [hξ]
  rfl

theorem integral_norm_sq_eq (u : CCMArchimedeanFormDomain a) :
    ∫ ξ : ℝ, ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2 = ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [← integral_norm_sq_ccmFormDomain a u]
  refine integral_congr_ae ?_
  filter_upwards [freq_ae a u] with ξ hξ
  rw [hξ]

/-- A continuous function dominated by a form-domain function plus a bounded bump is in the
form domain. -/
theorem memLp_formMeasure_of_bound {G F : ℝ → ℂ} (hG : Continuous G)
    (hF : MemLp F 2 ccmArchimedeanFormMeasure) (x₀ C : ℝ)
    (hbound : ∀ ξ, ‖G ξ‖ ≤ ‖F ξ‖ + (Icc (x₀ - 1) (x₀ + 1)).indicator (fun _ => C) ξ) :
    MemLp G 2 ccmArchimedeanFormMeasure := by
  have hfin : ccmArchimedeanFormMeasure (Icc (x₀ - 1) (x₀ + 1)) ≠ ⊤ := by
    rw [ccmArchimedeanFormMeasure, withDensity_apply _ measurableSet_Icc]
    refine (setLIntegral_lt_top_of_isCompact ?_ isCompact_Icc ?_).ne
    · exact measure_Icc_lt_top.ne
    · refine continuous_real_toNNReal.comp ?_
      unfold ccmArchimedeanFormWeight
      exact continuous_const.add (continuous_const.mul ((continuous_gammaHardyPhaseRate.comp
        (continuous_const.mul continuous_abs)).sub continuous_const))
  have hind : MemLp ((Icc (x₀ - 1) (x₀ + 1)).indicator fun _ => C) 2
      ccmArchimedeanFormMeasure := memLp_indicator_const 2 measurableSet_Icc C (Or.inr hfin)
  refine (hF.norm.add hind).of_le hG.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  refine (hbound ξ).trans (le_trans (le_abs_self _) ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, le_refl]

/-- **Division inside the form domain.**  If the transform of a form-domain vector vanishes at
`w₀`, some form-domain vector has transform `f̂(w)/(w − w₀)`. -/
theorem exists_div (u : CCMArchimedeanFormDomain a) {w₀ : ℂ}
    (hz : unitaryLaplace (timeRep a u) w₀ = 0) :
    ∃ v : CCMArchimedeanFormDomain a, ∀ w : ℂ, w ≠ w₀ →
      unitaryLaplace (timeRep a v) w = unitaryLaplace (timeRep a u) w / (w - w₀) := by
  set F := timeRep a u with hFdef
  have hFi := integrable_timeRep a u
  have hFs := supportedIn_timeRep a u
  set g := divLaplace a.1 F w₀ with hgdef
  have hgL := memLp_divLaplace a.2.le hFi hFs hz
  have hgi := integrable_divLaplace a.2.le hFi hFs hz
  have hgs := supportedIn_divLaplace a.2.le hFs hz
  set gL : SoninL2 := hgL.toLp g with hgLdef
  set G : ℝ → ℂ := fun ξ => unitaryLaplace g ξ with hGdef
  have hGcont : Continuous G := continuous_unitaryLaplace_ofReal hgi
  have hGmem : MemLp G 2 ccmArchimedeanFormMeasure := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := w₀.re - 1) (b := w₀.re + 1)).exists_bound_of_continuousOn
      hGcont.continuousOn
    have hu2 : MemLp (fun ξ : ℝ => unitaryLaplace F ξ) 2 ccmArchimedeanFormMeasure :=
      (Lp.memLp (u.1 : CCMArchimedeanFourierL2)).ae_eq
        (ccmArchimedeanFormMeasure_absolutelyContinuous_volume.ae_le (freq_ae a u))
    refine memLp_formMeasure_of_bound hGcont hu2 w₀.re C fun ξ => ?_
    by_cases hξ : ξ ∈ Icc (w₀.re - 1) (w₀.re + 1)
    · rw [indicator_of_mem hξ]
      exact (hC ξ hξ).trans (le_add_of_nonneg_left (norm_nonneg _))
    · rw [indicator_of_notMem hξ, add_zero]
      have h1 : 1 ≤ |ξ - w₀.re| := by
        simp only [mem_Icc, not_and_or, not_le] at hξ
        rcases hξ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have h2 : |ξ - w₀.re| ≤ ‖(ξ : ℂ) - w₀‖ := by
        have := Complex.abs_re_le_norm ((ξ : ℂ) - w₀)
        simpa using this
      have hne : (ξ : ℂ) ≠ w₀ := by
        intro h
        rw [h, sub_self, norm_zero] at h2
        linarith
      simp only [G]
      rw [unitaryLaplace_divLaplace a.2.le hFi hFs hz hne, norm_div]
      exact div_le_self (norm_nonneg _) (h1.trans h2)
  set V : CCMArchimedeanFourierL2 := hGmem.toLp G with hVdef
  have hvolV : (V : ℝ → ℂ) =ᵐ[volume] G :=
    (Measure.absolutelyContinuous_of_le volume_le_ccmArchimedeanFormMeasure).ae_le
      hGmem.coeFn_toLp
  have hgLi : Integrable (gL : ℝ → ℂ) := hgi.congr hgL.coeFn_toLp.symm
  have hWV : ccmArchimedeanWeightedToL2 V = fourierUnitary gL := by
    apply Lp.ext
    have h3 := l2_fourier_coeFn_eq_l1_fourier_of_integrable gL hgLi
    have h4 : (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hgLi).toLp gL) :
        ℝ → ℂ) = FourierTransform.fourier (gL : ℝ → ℂ) := Real.fourierTransform_toLp _
    refine (ccmArchimedeanWeightedToL2_coeFn V).trans (hvolV.trans ?_)
    refine EventuallyEq.symm (h3.trans ?_)
    rw [h4]
    refine Eventually.of_forall fun ξ => ?_
    rw [Real.fourier_congr_ae hgL.coeFn_toLp, ← unitaryLaplace_ofReal]
  have htime : ccmArchimedeanFourierToTime V = gL := by
    change fourierUnitary.symm (ccmArchimedeanWeightedToL2 V) = gL
    rw [hWV, LinearIsometryEquiv.symm_apply_apply]
  have hcut :
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) gL = gL := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) gL,
      hgL.coeFn_toLp] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h2, hgs x hx]
  have hker : V ∈ CCMArchimedeanFormDomain a := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1))
      (ccmArchimedeanFourierToTime V) = 0
    rw [htime, sub_apply, one_apply_eq_self, hcut, sub_self]
  refine ⟨⟨V, hker⟩, fun w hw => ?_⟩
  have hJ : ((ccmArchimedeanFormToAperture a ⟨V, hker⟩ : suzukiApertureHilbert a) : SoninL2) =
      gL := htime
  have hrep : timeRep a ⟨V, hker⟩ =ᵐ[volume] g := by
    refine (coeFn_eq_timeRep a ⟨V, hker⟩).symm.trans ?_
    rw [hJ]
    exact hgL.coeFn_toLp
  have hval : unitaryLaplace (timeRep a ⟨V, hker⟩) w = unitaryLaplace g w :=
    integral_congr_ae (hrep.mono fun x hx => by simp only [hx])
  rw [hval]
  exact unitaryLaplace_divLaplace a.2.le hFi hFs hz hw

theorem timeRep_add_smul_ae (u v : CCMArchimedeanFormDomain a) (c : ℂ) :
    timeRep a (u + c • v) =ᵐ[volume] fun x => timeRep a u x + c * timeRep a v x := by
  have hJ : ((ccmArchimedeanFormToAperture a (u + c • v) : suzukiApertureHilbert a) : SoninL2) =
      ((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) +
        c • ((ccmArchimedeanFormToAperture a v : suzukiApertureHilbert a) : SoninL2) := by
    rw [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
  have h1 := coeFn_eq_timeRep a (u + c • v)
  rw [hJ] at h1
  filter_upwards [h1, Lp.coeFn_add (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) :
      SoninL2)) (c • ((ccmArchimedeanFormToAperture a v : suzukiApertureHilbert a) : SoninL2)),
    Lp.coeFn_smul c (((ccmArchimedeanFormToAperture a v : suzukiApertureHilbert a) : SoninL2)),
    coeFn_eq_timeRep a u, coeFn_eq_timeRep a v] with x h1 h2 h3 h4 h5
  rw [← h1, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul, h4, h5]

theorem unitaryLaplace_timeRep_add_smul (u v : CCMArchimedeanFormDomain a) (c w : ℂ) :
    unitaryLaplace (timeRep a (u + c • v)) w =
      unitaryLaplace (timeRep a u) w + c * unitaryLaplace (timeRep a v) w := by
  have h : unitaryLaplace (timeRep a (u + c • v)) w =
      unitaryLaplace (fun x => timeRep a u x + c * timeRep a v x) w :=
    integral_congr_ae ((timeRep_add_smul_ae a u v c).mono fun x hx => by simp only [hx])
  rw [h, unitaryLaplace_add_mul (integrable_timeRep a u) (supportedIn_timeRep a u)
    (integrable_timeRep a v) (supportedIn_timeRep a v)]

theorem unitaryLaplace_timeRep_zero (w : ℂ) : unitaryLaplace (timeRep a 0) w = 0 := by
  have hz : timeRep a 0 =ᵐ[volume] (0 : ℝ → ℂ) := by
    refine (coeFn_eq_timeRep a 0).symm.trans ?_
    rw [map_zero, Submodule.coe_zero]
    exact Lp.coeFn_zero ℂ 2 volume
  rw [unitaryLaplace, integral_congr_ae (g := fun _ => (0 : ℂ)) (hz.mono fun x hx => by
    simp only [hx, Pi.zero_apply, mul_zero])]
  exact integral_zero ℝ ℂ

theorem unitaryLaplace_timeRep_smul (v : CCMArchimedeanFormDomain a) (c w : ℂ) :
    unitaryLaplace (timeRep a (c • v)) w = c * unitaryLaplace (timeRep a v) w := by
  have h := unitaryLaplace_timeRep_add_smul a 0 v c w
  rw [zero_add] at h
  rw [h, unitaryLaplace_timeRep_zero, zero_add]

theorem integrable_levelSymbol_mul (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => levelSymbol a ξ * ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2) := by
  have hW : Integrable (fun ξ : ℝ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    simpa [archimedeanWeilSymbol] using integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1
  have hC : Integrable (fun ξ : ℝ => ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    refine integrable_finsetSum _ fun n _ => ?_
    refine ((integrable_cos_mul_norm_sq_ccmFormDomain a u (Real.log n)).const_mul
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) * 2)).congr
        (Eventually.of_forall fun ξ => ?_)
    simp only
    ring
  refine (hW.sub hC).congr ?_
  filter_upwards [freq_ae a u] with ξ hξ
  simp only [Pi.sub_apply, levelSymbol, weilAtomSymbol, sub_mul, Finset.sum_mul, hξ]

theorem integrable_norm_sq_unitaryLaplace (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2) :=
  (integrable_norm_sq_ccmFormDomain a u).congr ((freq_ae a u).mono fun ξ hξ => by simp only [hξ])

/-- A polar ground state: pole-vanishing with Rayleigh value the polar ground energy. -/
def IsPolarGround (u : CCMArchimedeanFormDomain a) : Prop :=
  IsPolarConstrained a u ∧ ccmRestrictedWeilSourceQuadratic a u =
    ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2

theorem polarGroundEnergy_mul_le (v : CCMArchimedeanFormDomain a) (hv : IsPolarConstrained a v) :
    ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a v := by
  by_cases hJ : ccmArchimedeanFormToAperture a v = 0
  · have hv0 : v = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hJ, map_zero])
    rw [hJ, norm_zero, hv0]
    have hq : ccmRestrictedWeilSourceQuadratic a 0 = 0 := by
      have hpol0 : IsPolarConstrained a 0 := by
        unfold IsPolarConstrained
        simp only [map_zero, inner_zero_right, and_self]
      rw [source_eq_integral a 0 hpol0]
      simp only [unitaryLaplace_timeRep_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, integral_zero]
    rw [hq]; simp
  · have hpos : 0 < ‖ccmArchimedeanFormToAperture a v‖ ^ 2 := by
      have := norm_pos_iff.mpr hJ; positivity
    have hmem : ccmRestrictedWeilSourceQuadratic a v / ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ∈
        polarRayleighSet a := ⟨v, hv, hJ, rfl⟩
    have hle := csInf_le ⟨_, ccmRestrictedWeilGroundEnergy_mem_lowerBounds a⟩ hmem
    rw [le_div_iff₀ hpos] at hle
    exact hle

/-- **Polar ground states are closed under division by non-real zeros.** -/
theorem isPolarGround_div {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) {w₀ : ℂ}
    (him : w₀.im ≠ 0) (hp : w₀ ≠ polarPoint (1 / 2)) (hm : w₀ ≠ polarPoint (-1 / 2))
    {v : CCMArchimedeanFormDomain a}
    (hv : ∀ w : ℂ, w ≠ w₀ →
      unitaryLaplace (timeRep a v) w = unitaryLaplace (timeRep a u) w / (w - w₀)) :
    IsPolarGround a v := by
  obtain ⟨hpolu, hQ⟩ := hu
  have hpol := (isPolarConstrained_iff a u).mp hpolu
  set μ := ccmRestrictedWeilPolarGroundEnergy a with hμ
  have hvp : unitaryLaplace (timeRep a v) (polarPoint (1 / 2)) = 0 := by
    rw [hv _ (Ne.symm hp), hpol.1, zero_div]
  have hvm : unitaryLaplace (timeRep a v) (polarPoint (-1 / 2)) = 0 := by
    rw [hv _ (Ne.symm hm), hpol.2, zero_div]
  have hvpol : IsPolarConstrained a v := (isPolarConstrained_iff a v).mpr ⟨hvp, hvm⟩
  set c : ℂ := I * w₀.im with hc
  set h₁ := u + c • v with hh₁
  set h₂ := (w₀.im : ℂ) • v with hh₂
  have hT₁ : ∀ w, unitaryLaplace (timeRep a h₁) w =
      unitaryLaplace (timeRep a u) w + c * unitaryLaplace (timeRep a v) w :=
    unitaryLaplace_timeRep_add_smul a u v c
  have hT₂ : ∀ w, unitaryLaplace (timeRep a h₂) w =
      (w₀.im : ℂ) * unitaryLaplace (timeRep a v) w := unitaryLaplace_timeRep_smul a v _
  have hpol₁ : IsPolarConstrained a h₁ := by
    rw [isPolarConstrained_iff, hT₁, hT₁, hpol.1, hpol.2, hvp, hvm]
    simp
  have hpol₂ : IsPolarConstrained a h₂ := by
    rw [isPolarConstrained_iff, hT₂, hT₂, hvp, hvm]
    simp
  have hG : ∀ ξ : ℝ, unitaryLaplace (timeRep a v) ξ =
      unitaryLaplace (timeRep a u) ξ / ((ξ : ℂ) - w₀) := fun ξ =>
    hv ξ (ne_of_im_ne_zero ξ him)
  have hsplit : ∀ ξ : ℝ, ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2 =
      ‖unitaryLaplace (timeRep a h₁) ξ‖ ^ 2 + ‖unitaryLaplace (timeRep a h₂) ξ‖ ^ 2 := by
    intro ξ
    rw [hT₁, hT₂, hG]
    exact sq_norm_split _ ξ him
  have hNsum : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 =
      ‖ccmArchimedeanFormToAperture a h₁‖ ^ 2 + ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 := by
    rw [← integral_norm_sq_eq, ← integral_norm_sq_eq, ← integral_norm_sq_eq,
      ← integral_add (integrable_norm_sq_unitaryLaplace a h₁)
        (integrable_norm_sq_unitaryLaplace a h₂)]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  have hQsum : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilSourceQuadratic a h₁ + ccmRestrictedWeilSourceQuadratic a h₂ := by
    rw [source_eq_integral a u hpolu, source_eq_integral a h₁ hpol₁,
      source_eq_integral a h₂ hpol₂, ← integral_add (integrable_levelSymbol_mul a h₁)
        (integrable_levelSymbol_mul a h₂)]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by simp only [hsplit ξ, mul_add])
  have hl₁ := polarGroundEnergy_mul_le a h₁ hpol₁
  have hl₂ := polarGroundEnergy_mul_le a h₂ hpol₂
  have heq₂ : ccmRestrictedWeilSourceQuadratic a h₂ =
      μ * ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 := by
    rw [hQsum, hNsum, mul_add] at hQ
    linarith
  have hy2 : (0 : ℝ) < w₀.im ^ 2 := by positivity
  have hscale : ∀ ξ : ℝ, ‖unitaryLaplace (timeRep a h₂) ξ‖ ^ 2 =
      w₀.im ^ 2 * ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2 := fun ξ => by
    rw [hT₂, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hQ₂ : ccmRestrictedWeilSourceQuadratic a h₂ =
      w₀.im ^ 2 * ccmRestrictedWeilSourceQuadratic a v := by
    rw [source_eq_integral a h₂ hpol₂, source_eq_integral a v hvpol, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by
      simp only [hscale ξ]; ring)
  have hN₂ : ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 =
      w₀.im ^ 2 * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 := by
    rw [← integral_norm_sq_eq, ← integral_norm_sq_eq, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hscale)
  refine ⟨hvpol, ?_⟩
  rw [hQ₂, hN₂] at heq₂
  have h' : w₀.im ^ 2 * ccmRestrictedWeilSourceQuadratic a v =
      w₀.im ^ 2 * (μ * ‖ccmArchimedeanFormToAperture a v‖ ^ 2) := by
    rw [heq₂]; ring
  exact mul_left_cancel₀ hy2.ne' h'


theorem isPolarGround_smul {v : CCMArchimedeanFormDomain a} (hv : IsPolarGround a v) (c : ℂ) :
    IsPolarGround a (c • v) := by
  obtain ⟨hpol, hQ⟩ := hv
  have hp := (isPolarConstrained_iff a v).mp hpol
  have hpol' : IsPolarConstrained a (c • v) := by
    rw [isPolarConstrained_iff, unitaryLaplace_timeRep_smul, unitaryLaplace_timeRep_smul,
      hp.1, hp.2]
    simp
  refine ⟨hpol', ?_⟩
  rw [source_eq_integral a _ hpol', map_smul, norm_smul]
  have h : (fun ξ : ℝ => levelSymbol a ξ * ‖unitaryLaplace (timeRep a (c • v)) ξ‖ ^ 2) =
      fun ξ => ‖c‖ ^ 2 * (levelSymbol a ξ * ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2) := by
    funext ξ
    rw [unitaryLaplace_timeRep_smul, norm_mul]
    ring
  rw [h, integral_const_mul, ← source_eq_integral a v hpol, hQ]
  ring

/-- `q(v) = Q(v) − μ‖Jv‖²` in integral form, for polar `v`. -/
theorem source_sub_eq_integral (v : CCMArchimedeanFormDomain a) (hv : IsPolarConstrained a v) :
    ccmRestrictedWeilSourceQuadratic a v -
        ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 =
      ∫ ξ : ℝ, (levelSymbol a ξ - ccmRestrictedWeilPolarGroundEnergy a) *
        ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2 := by
  rw [source_eq_integral a v hv, ← integral_norm_sq_eq, ← integral_const_mul,
    ← integral_sub (integrable_levelSymbol_mul a v)
      ((integrable_norm_sq_unitaryLaplace a v).const_mul _)]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by simp only; ring)

theorem integrable_excess (v : CCMArchimedeanFormDomain a) :
    Integrable fun ξ : ℝ => (levelSymbol a ξ - ccmRestrictedWeilPolarGroundEnergy a) *
        ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2 :=
  ((integrable_levelSymbol_mul a v).sub ((integrable_norm_sq_unitaryLaplace a v).const_mul
    (ccmRestrictedWeilPolarGroundEnergy a))).congr
    (Eventually.of_forall fun ξ => by simp only [Pi.sub_apply]; ring)

theorem isPolarGround_add {v w : CCMArchimedeanFormDomain a} (hv : IsPolarGround a v)
    (hw : IsPolarGround a w) : IsPolarGround a (v + w) := by
  set μ := ccmRestrictedWeilPolarGroundEnergy a
  have hpv := (isPolarConstrained_iff a v).mp hv.1
  have hpw := (isPolarConstrained_iff a w).mp hw.1
  have hadd : ∀ c : ℂ, IsPolarConstrained a (v + c • w) := fun c => by
    rw [isPolarConstrained_iff, unitaryLaplace_timeRep_add_smul, unitaryLaplace_timeRep_add_smul,
      hpv.1, hpv.2, hpw.1, hpw.2]
    simp
  have hq : ∀ x : CCMArchimedeanFormDomain a, IsPolarConstrained a x →
      0 ≤ ccmRestrictedWeilSourceQuadratic a x - μ * ‖ccmArchimedeanFormToAperture a x‖ ^ 2 :=
    fun x hx => sub_nonneg.mpr (polarGroundEnergy_mul_le a x hx)
  have hzv : ∫ ξ : ℝ, (levelSymbol a ξ - μ) * ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2 = 0 := by
    rw [← source_sub_eq_integral a v hv.1, hv.2, sub_self]
  have hzw : ∫ ξ : ℝ, (levelSymbol a ξ - μ) * ‖unitaryLaplace (timeRep a w) ξ‖ ^ 2 = 0 := by
    rw [← source_sub_eq_integral a w hw.1, hw.2, sub_self]
  have hpar : (∫ ξ : ℝ, (levelSymbol a ξ - μ) *
        ‖unitaryLaplace (timeRep a (v + (1 : ℂ) • w)) ξ‖ ^ 2) +
      (∫ ξ : ℝ, (levelSymbol a ξ - μ) * ‖unitaryLaplace (timeRep a (v + (-1 : ℂ) • w)) ξ‖ ^ 2) =
      2 * (∫ ξ : ℝ, (levelSymbol a ξ - μ) * ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2) +
        2 * ∫ ξ : ℝ, (levelSymbol a ξ - μ) * ‖unitaryLaplace (timeRep a w) ξ‖ ^ 2 := by
    rw [← integral_add (integrable_excess a _) (integrable_excess a _), ← integral_const_mul,
      ← integral_const_mul, ← integral_add ((integrable_excess a v).const_mul 2)
        ((integrable_excess a w).const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [unitaryLaplace_timeRep_add_smul]
    have key : ‖unitaryLaplace (timeRep a v) ξ + 1 * unitaryLaplace (timeRep a w) ξ‖ ^ 2 +
        ‖unitaryLaplace (timeRep a v) ξ + -1 * unitaryLaplace (timeRep a w) ξ‖ ^ 2 =
        2 * ‖unitaryLaplace (timeRep a v) ξ‖ ^ 2 + 2 * ‖unitaryLaplace (timeRep a w) ξ‖ ^ 2 := by
      rw [one_mul, neg_one_mul, ← sub_eq_add_neg, Complex.sq_norm, Complex.sq_norm,
        Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
      ring
    linear_combination (levelSymbol a ξ - μ) * key
  rw [hzv, hzw] at hpar
  have h1 := hq _ (hadd 1)
  have h2 := hq _ (hadd (-1))
  rw [source_sub_eq_integral a _ (hadd 1)] at h1
  rw [source_sub_eq_integral a _ (hadd (-1))] at h2
  have hz1 : ∫ ξ : ℝ, (levelSymbol a ξ - μ) *
      ‖unitaryLaplace (timeRep a (v + (1 : ℂ) • w)) ξ‖ ^ 2 = 0 := by linarith
  have hvw : v + w = v + (1 : ℂ) • w := by rw [one_smul]
  refine ⟨by rw [hvw]; exact hadd 1, ?_⟩
  have := source_sub_eq_integral a _ (hadd 1)
  rw [hz1, ← hvw] at this
  linarith

theorem isPolarConstrained_zero : IsPolarConstrained a 0 := by
  unfold IsPolarConstrained
  simp only [map_zero, inner_zero_right, and_self]

theorem source_zero : ccmRestrictedWeilSourceQuadratic a 0 = 0 := by
  rw [source_eq_integral a 0 (isPolarConstrained_zero a)]
  simp only [unitaryLaplace_timeRep_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, integral_zero]

/-- The polar ground states form a subspace of the form domain. -/
def groundSubmodule : Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | IsPolarGround a u}
  add_mem' := fun hv hw => isPolarGround_add a hv hw
  zero_mem' := ⟨isPolarConstrained_zero a, by rw [source_zero, map_zero, norm_zero]; ring⟩
  smul_mem' := fun c _ hv => isPolarGround_smul a hv c

theorem mem_groundSubmodule {u : CCMArchimedeanFormDomain a} :
    u ∈ groundSubmodule a ↔ IsPolarGround a u := Iff.rfl

theorem isClosed_groundSubmodule :
    IsClosed (groundSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
  set J := ccmArchimedeanFormToAperture a
  have hset : (groundSubmodule a : Set (CCMArchimedeanFormDomain a)) =
      ({u | inner ℂ (ccmPolarApertureVector a (1 / 2)) (J u) = 0} ∩
        {u | inner ℂ (ccmPolarApertureVector a (-1 / 2)) (J u) = 0}) ∩
        {u | (ccmRestrictedWeilForm a u u).re -
          ccmRestrictedWeilPolarGroundEnergy a * ‖J u‖ ^ 2 = 0} := by
    ext u
    simp only [SetLike.mem_coe, mem_groundSubmodule, IsPolarGround, IsPolarConstrained,
      mem_inter_iff, mem_setOf_eq, ccmRestrictedWeilForm_self_re_eq_source, sub_eq_zero, J]
  rw [hset]
  have hJ : Continuous J := J.continuous
  have hform : Continuous fun u : CCMArchimedeanFormDomain a => ccmRestrictedWeilForm a u u := by
    unfold ccmRestrictedWeilForm
    exact (continuous_id.inner continuous_id).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp hJ).inner hJ)
  refine ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)).inter
    (isClosed_eq ?_ continuous_const)
  · exact continuous_const.inner hJ
  · exact continuous_const.inner hJ
  · exact (Complex.continuous_re.comp hform).sub (continuous_const.mul (hJ.norm.pow 2))

/-- **The polar ground level has finite multiplicity.** -/
theorem finiteDimensional_groundSubmodule : FiniteDimensional ℂ (groundSubmodule a) := by
  haveI : CompleteSpace (groundSubmodule a) :=
    (isClosed_groundSubmodule a).completeSpace_coe
  set J := ccmArchimedeanFormToAperture a with hJdef
  set T : groundSubmodule a →L[ℂ] suzukiApertureHilbert a :=
    J.comp (groundSubmodule a).subtypeL with hTdef
  set C : ℝ := ccmRestrictedWeilPolarGroundEnergy a + ‖ccmRestrictedWeilBoundedRemainder a‖
  have hbound : ∀ x : groundSubmodule a,
      ‖x‖ ≤ ((Real.sqrt (max C 0)).toNNReal : ℝ) * ‖T x‖ := by
    intro x
    have hx : IsPolarGround a (x : CCMArchimedeanFormDomain a) := x.2
    have h1 := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a x
    rw [hx.2] at h1
    have h2 : ‖x‖ ^ 2 ≤ max C 0 * ‖T x‖ ^ 2 := by
      have hTx : T x = J x := rfl
      have hnx : ‖x‖ = ‖(x : CCMArchimedeanFormDomain a).1‖ := rfl
      rw [hTx, hnx]
      calc ‖(x : CCMArchimedeanFormDomain a).1‖ ^ 2 ≤ C * ‖J x‖ ^ 2 := by
            simp only [C]; linarith
        _ ≤ max C 0 * ‖J x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    have h3 : ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h3, ← Real.sqrt_sq (norm_nonneg (T x)), ← Real.sqrt_mul (le_max_right _ _)]
    exact Real.sqrt_le_sqrt h2
  have hanti := T.antilipschitz_of_bound hbound
  have hemb := hanti.isClosedEmbedding T.uniformContinuous
  have hK := (isCompactOperator_ccmArchimedeanFormToAperture a).isCompact_closure_image_closedBall 1
  have hpre := hemb.isCompact_preimage hK
  refine FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos
    (hpre.of_isClosed_subset Metric.isClosed_closedBall ?_)
  intro x hx
  show T x ∈ closure (J '' Metric.closedBall 0 1)
  refine subset_closure ⟨(x : CCMArchimedeanFormDomain a), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact hx

/-- The transform on the real line, as a linear map on the ground subspace. -/
def realTransform : groundSubmodule a →ₗ[ℂ] (ℝ → ℂ) where
  toFun u := fun t : ℝ => unitaryLaplace (timeRep a (u : CCMArchimedeanFormDomain a)) t
  map_add' u v := by
    funext t
    have h := unitaryLaplace_timeRep_add_smul a u v 1 t
    rw [one_smul, one_mul] at h
    simpa only [Submodule.coe_add, Pi.add_apply] using h
  map_smul' c u := by
    funext t
    simpa only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] using
      unitaryLaplace_timeRep_smul a u c t

theorem exists_real_ne_zero {u : CCMArchimedeanFormDomain a}
    (hu : ccmArchimedeanFormToAperture a u ≠ 0) :
    ∃ t : ℝ, unitaryLaplace (timeRep a u) t ≠ 0 := by
  by_contra h
  push Not at h
  apply hu
  have h0 : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 = 0 := by
    rw [← integral_norm_sq_eq a u]
    simp only [h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)

theorem infinite_real_ne_zero {u : CCMArchimedeanFormDomain a}
    (hu : ccmArchimedeanFormToAperture a u ≠ 0) :
    {t : ℝ | unitaryLaplace (timeRep a u) t ≠ 0}.Infinite := by
  obtain ⟨t, ht⟩ := exists_real_ne_zero a hu
  have hopen : IsOpen {t : ℝ | unitaryLaplace (timeRep a u) t ≠ 0} :=
    isOpen_ne_fun (continuous_unitaryLaplace_ofReal (integrable_timeRep a u)) continuous_const
  intro hfin
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t ht
  refine (Set.Ioo_infinite (show t - ε < t + ε by linarith)) (hfin.subset fun x hx => ?_)
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- **Real-rooted polar ground states exist at every aperture.** -/
theorem exists_realRooted_polarGround :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarGround a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a u) w = 0 → w ≠ polarPoint (1 / 2) →
        w ≠ polarPoint (-1 / 2) → w.im = 0 := by
  classical
  obtain ⟨u₀, hpol₀, hn₀, hQ₀⟩ := exists_polarConstrained_groundState a
  have hg₀ : IsPolarGround a u₀ := ⟨hpol₀, by rw [hQ₀, hn₀]; ring⟩
  have hne₀ : ccmArchimedeanFormToAperture a u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn₀
    exact zero_ne_one hn₀
  by_contra hcon
  push Not at hcon
  let S := {u : CCMArchimedeanFormDomain a //
    IsPolarGround a u ∧ ccmArchimedeanFormToAperture a u ≠ 0}
  have hstep : ∀ s : S, ∃ w : ℂ, ∃ v : S, unitaryLaplace (timeRep a s.1) w = 0 ∧ w.im ≠ 0 ∧
      ∀ t : ℝ, unitaryLaplace (timeRep a v.1) t =
        unitaryLaplace (timeRep a s.1) t / ((t : ℂ) - w) := by
    intro s
    obtain ⟨w, hw, hp, hm, him⟩ := hcon s.1 s.2.1 s.2.2
    obtain ⟨v, hv⟩ := exists_div a s.1 hw
    have hgv : IsPolarGround a v := isPolarGround_div a s.2.1 him hp hm hv
    have hnv : ccmArchimedeanFormToAperture a v ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := exists_real_ne_zero a s.2.2
      have hv0 : v = 0 := ccmArchimedeanFormToAperture_injective a (by rw [h0, map_zero])
      have h1 := hv t (ne_of_im_ne_zero t him)
      rw [hv0, unitaryLaplace_timeRep_zero, eq_comm, div_eq_zero_iff] at h1
      exact ht (h1.resolve_right (sub_ne_zero.mpr (ne_of_im_ne_zero t him)))
    exact ⟨w, ⟨v, hgv, hnv⟩, hw, him, fun t => hv t (ne_of_im_ne_zero t him)⟩
  choose zf nx _ himf hnx using hstep
  let chain : ℕ → S := fun k => nx^[k] ⟨u₀, hg₀, hne₀⟩
  let zs : ℕ → ℂ := fun k => zf (chain k)
  have hsucc : ∀ k, chain (k + 1) = nx (chain k) := fun k =>
    Function.iterate_succ_apply' nx k _
  have hform : ∀ (k : ℕ) (t : ℝ), unitaryLaplace (timeRep a (chain k).1) t =
      unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range k, ((t : ℂ) - zs l) := by
    intro k t
    induction k with
    | zero => simp [chain]
    | succ k ih => rw [hsucc, hnx, ih, Finset.prod_range_succ, div_div]
  haveI := finiteDimensional_groundSubmodule a
  set d := Module.finrank ℂ (groundSubmodule a)
  let g : Fin (d + 1) → groundSubmodule a := fun i => ⟨(chain i).1, (chain i).2.1⟩
  have hli : LinearIndependent ℂ g := by
    apply LinearIndependent.of_comp (realTransform a)
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let c' : ℕ → ℂ := fun j => if h : j < d + 1 then c ⟨j, h⟩ else 0
    have hreal : ∀ j < d, ∀ t : ℝ, (t : ℂ) - zs j ≠ 0 :=
      fun j _ t => sub_ne_zero.mpr (ne_of_im_ne_zero t (himf (chain j)))
    have hsum : ∀ t : ℝ, ∑ j ∈ Finset.range (d + 1), c' j *
        (unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range j, ((t : ℂ) - zs l)) = 0 := by
      intro t
      have h0 := congrFun hc t
      simp only [Finset.sum_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at h0
      rw [← h0, ← Fin.sum_univ_eq_sum_range (fun j => c' j *
        (unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range j, ((t : ℂ) - zs l)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c', dif_pos j.isLt, Fin.eta]
      rw [← hform j t]
      rfl
    have := eq_zero_of_sum_div_prod (infinite_real_ne_zero a hne₀) zs d hreal c' hsum i
      (Nat.lt_succ_iff.mp i.isLt)
    simp only [c', dif_pos i.isLt, Fin.eta] at this
    exact this
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

end RHTower.CCMRealRootedGround
