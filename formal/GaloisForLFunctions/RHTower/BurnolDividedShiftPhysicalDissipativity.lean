import GaloisForLFunctions.RHTower.BurnolDividedShiftSourceLeakage
import GaloisForLFunctions.RHTower.BurnolSoninDividedShift

/-!
# Burnol divided shift: physical dilation port and source dissipativity

This module identifies the abstract Mellin Cauchy multiplier used by Route R with Burnol's
physical one-sided dilation integral.  Absolute product integrability is proved before Fubini.
The fixed co-Poisson atom then converts source flatness into one explicit scalar source law:
nonpositivity of the real part of its physical dilation autocorrelation port.

The comparison and strict positive sign are unconditional.  The remaining Route R producer is
exactly the pre-divisor Euler--Gamma--Stokes derivation of the opposite, nonpositive sign at actual
right-half Xi divisor points.
-/

noncomputable section

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace RHTower

/-! ## Mellin--Laplace kernel -/

theorem burnolShiftWeight_mul_mellinCharacter_eq_cpow
    (rho : ℂ) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    burnolShiftWeight rho u * MellinL2.mellinCharacter u t =
      (u : ℂ) ^ (-rho - 1 / 2 + Complex.I * (t : ℂ)) := by
  rw [burnolShiftWeight, MellinL2.mellinCharacter_eq_cpow u hu]
  rw [← Complex.cpow_add _ _ (by exact_mod_cast ne_of_gt hu)]

/-- Scalar Mellin--Laplace integral giving the Cauchy divided-shift symbol. -/
theorem integral_burnolShiftWeight_mul_mellinCharacter
    {rho : ℂ} (h : 1 / 2 < rho.re) (t : ℝ) :
    (∫ u in Ioi (1 : ℝ),
        burnolShiftWeight rho u * MellinL2.mellinCharacter u t) =
      burnolDividedShiftSymbol rho t := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu =>
    burnolShiftWeight_mul_mellinCharacter_eq_cpow rho (lt_trans zero_lt_one hu) t)]
  have hlt : (-rho - 1 / 2 + Complex.I * (t : ℂ)).re < -1 := by
    norm_num
    linarith
  rw [integral_Ioi_cpow_of_lt hlt zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  unfold burnolDividedShiftSymbol criticalLineArgument
  have hne : rho - ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  rw [show -rho - 1 / 2 + Complex.I * (t : ℂ) + 1 =
      -(rho - ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) by ring]
  field_simp

/-- Joint Mellin--Laplace kernel, globally measurable by exponential coordinates. -/
def burnolMellinLaplaceKernel (rho : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp ((Real.log p.1 : ℂ) *
    (-rho - 1 / 2 + Complex.I * (p.2 : ℂ)))

theorem measurable_burnolMellinLaplaceKernel (rho : ℂ) :
    Measurable (burnolMellinLaplaceKernel rho) := by
  apply Complex.measurable_exp.comp
  exact ((Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)).mul
    (measurable_const.add (measurable_const.mul
      (Complex.measurable_ofReal.comp measurable_snd))))

theorem burnolMellinLaplaceKernel_eq
    (rho : ℂ) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    burnolMellinLaplaceKernel rho (u, t) =
      burnolShiftWeight rho u * MellinL2.mellinCharacter u t := by
  rw [burnolShiftWeight_mul_mellinCharacter_eq_cpow rho hu t]
  unfold burnolMellinLaplaceKernel
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hu),
    ← Complex.ofReal_log hu.le]

theorem norm_burnolMellinLaplaceKernel
    (rho : ℂ) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖burnolMellinLaplaceKernel rho (u, t)‖ = u ^ (-rho.re - 1 / 2) := by
  rw [burnolMellinLaplaceKernel_eq rho hu t, norm_mul,
    norm_burnolShiftWeight hu, MellinL2.norm_mellinCharacter, mul_one]

/-- Absolute product integrability required for the physical/spectral Fubini exchange. -/
theorem integrable_burnolMellinLaplaceKernel_mul_inner
    {rho : ℂ} (h : 1 / 2 < rho.re) (G F : SpectralL2) :
    Integrable (fun p : ℝ × ℝ => burnolMellinLaplaceKernel rho p *
        (starRingEnd ℂ (G p.2) * F p.2))
      ((volume.restrict (Ioi (1 : ℝ))).prod volume) := by
  let phi : ℝ → ℂ := fun t => starRingEnd ℂ (G t) * F t
  have hphi : Integrable phi volume := by
    simpa [phi, RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) G F)
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => burnolMellinLaplaceKernel rho p * phi p.2)
      ((volume.restrict (Ioi (1 : ℝ))).prod volume) :=
    (measurable_burnolMellinLaplaceKernel rho).aestronglyMeasurable.mul
      hphi.aestronglyMeasurable.comp_snd
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hmajor : Integrable
        (fun t : ℝ => u ^ (-rho.re - 1 / 2) * ‖phi t‖) volume :=
      hphi.norm.const_mul _
    have hpair : Measurable (fun t : ℝ => (u, t)) := measurable_const.prodMk measurable_id
    have hsliceMeas : AEStronglyMeasurable
        (fun t : ℝ => burnolMellinLaplaceKernel rho (u, t) * phi t) volume :=
      ((measurable_burnolMellinLaplaceKernel rho).comp hpair).aestronglyMeasurable.mul
        hphi.aestronglyMeasurable
    refine Integrable.mono' hmajor hsliceMeas ?_
    filter_upwards with t
    rw [norm_mul, norm_burnolMellinLaplaceKernel rho hu0]
  · have hweight : IntegrableOn (fun u : ℝ => u ^ (-rho.re - 1 / 2))
        (Ioi (1 : ℝ)) volume :=
      (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)
    have houter : IntegrableOn
        (fun u : ℝ => u ^ (-rho.re - 1 / 2) * ∫ t : ℝ, ‖phi t‖)
        (Ioi (1 : ℝ)) volume := hweight.mul_const _
    refine Integrable.congr houter ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simpa only [norm_mul] using
      (congrArg (fun x : ℝ => x * ‖phi t‖)
        (norm_burnolMellinLaplaceKernel rho hu0 t)).symm

/-! ## Physical/spectral identity -/

theorem archimedeanMellinUnitary_burnolShift_eq_integral
    {rho : ℂ} (h : 1 / 2 < rho.re) (f : evenSubspace) :
    archimedeanMellinUnitary (burnolShift rho f) =
      ∫ u in Ioi (1 : ℝ), burnolShiftWeight rho u •
        MellinL2.mellinCharacterMulUnitary u (archimedeanMellinUnitary f) := by
  rw [burnolShift]
  change archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap
      (∫ u in Ioi (1 : ℝ), burnolShiftWeight rho u • evenRayDilate u f) = _
  rw [← archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
    (integrable_burnolShift_integrand h f)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  rw [map_smul]
  congr 1
  rw [evenRayDilate_of_pos hu0]
  exact archimedeanMellinUnitary_evenDilation u hu0 f

theorem inner_archimedeanMellinUnitary_burnolShift_eq_spectral
    {rho : ℂ} (h : 1 / 2 < rho.re) (G : SpectralL2) (f : evenSubspace) :
    inner ℂ G (archimedeanMellinUnitary (burnolShift rho f)) =
      inner ℂ G (burnolSpectralDividedShift h (archimedeanMellinUnitary f)) := by
  let F : SpectralL2 := archimedeanMellinUnitary f
  let phi : ℝ → ℂ := fun t => starRingEnd ℂ (G t) * F t
  have hunit : inner ℂ G (archimedeanMellinUnitary (burnolShift rho f)) =
      inner ℂ (archimedeanMellinUnitary.symm G) (burnolShift rho f) := by
    simpa using (archimedeanMellinUnitary.inner_map_map
      (archimedeanMellinUnitary.symm G) (burnolShift rho f))
  rw [hunit, inner_burnolShift h]
  have hinneru : ∀ u ∈ Ioi (1 : ℝ),
      inner ℂ (archimedeanMellinUnitary.symm G) (evenRayDilate u f) =
        inner ℂ G (MellinL2.mellinCharacterMulUnitary u F) := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    calc
      inner ℂ (archimedeanMellinUnitary.symm G) (evenRayDilate u f) =
          inner ℂ (archimedeanMellinUnitary (archimedeanMellinUnitary.symm G))
            (archimedeanMellinUnitary (evenRayDilate u f)) :=
        (archimedeanMellinUnitary.inner_map_map
          (archimedeanMellinUnitary.symm G) (evenRayDilate u f)).symm
      _ = inner ℂ G (MellinL2.mellinCharacterMulUnitary u F) := by
        rw [archimedeanMellinUnitary.apply_symm_apply, evenRayDilate_of_pos hu0]
        change inner ℂ G (archimedeanMellinUnitary (evenDilationUnitary u hu0 f)) = _
        rw [archimedeanMellinUnitary_evenDilation]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => by rw [hinneru u hu])]
  have hslice : ∀ u ∈ Ioi (1 : ℝ),
      burnolShiftWeight rho u * inner ℂ G (MellinL2.mellinCharacterMulUnitary u F) =
        ∫ t : ℝ, burnolMellinLaplaceKernel rho (u, t) * phi t := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [MellinL2.mellinCharacterMulUnitary_ae u F] with t ht
    rw [ht, burnolMellinLaplaceKernel_eq rho hu0]
    simp only [phi, RCLike.inner_apply]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hslice]
  have hprod := integrable_burnolMellinLaplaceKernel_mul_inner h G F
  rw [integral_integral_swap hprod]
  have ht : ∀ t : ℝ,
      (∫ u in Ioi (1 : ℝ), burnolMellinLaplaceKernel rho (u, t) * phi t) =
        burnolDividedShiftSymbol rho t * phi t := by
    intro t
    rw [integral_mul_const]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu =>
      burnolMellinLaplaceKernel_eq rho (lt_trans zero_lt_one hu) t)]
    exact integral_burnolShiftWeight_mul_mellinCharacter h t
  rw [integral_congr_ae (Filter.Eventually.of_forall ht)]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolSpectralDividedShift_ae h F] with t htF
  rw [htF]
  simp only [phi, RCLike.inner_apply]
  ring

/-- Burnol's physical one-sided dilation integral is exactly the Route R Mellin Cauchy
multiplier, as an equality in the even Hilbert space. -/
theorem burnolShift_eq_burnolMellinDividedShift
    {rho : ℂ} (h : 1 / 2 < rho.re) (f : evenSubspace) :
    burnolShift rho f = burnolMellinDividedShift h f := by
  apply archimedeanMellinUnitary.injective
  apply ext_inner_left ℂ
  intro G
  rw [inner_archimedeanMellinUnitary_burnolShift_eq_spectral h G f]
  change inner ℂ G (burnolSpectralDividedShift h (archimedeanMellinUnitary f)) =
    inner ℂ G (archimedeanMellinUnitary
      (archimedeanMellinUnitary.symm
        (burnolSpectralDividedShift h (archimedeanMellinUnitary f))))
  rw [archimedeanMellinUnitary.apply_symm_apply]

/-! ## Fixed physical port -/

/-- Fixed aperture-`1/2` co-Poisson atom used by the divided-shift endpoint. -/
def burnolFixedSubWindowSourceAtom : evenSubspace :=
  coPoissonSubWindowEven (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num)

theorem burnolFixedSubWindowSourceAtom_ne_zero : burnolFixedSubWindowSourceAtom ≠ 0 := by
  exact coPoissonSubWindowEven_ne_zero (c := (1 / 2 : ℝ)) (d := 1)
    (by norm_num) (by norm_num)

/-- Physical autocorrelation port of the fixed source atom under the one-sided dilation
resolvent. -/
def burnolDividedShiftPhysicalPort (rho : ℂ) : ℂ :=
  ∫ u in Ioi (1 : ℝ), burnolShiftWeight rho u *
    inner ℂ burnolFixedSubWindowSourceAtom
      (evenRayDilate u burnolFixedSubWindowSourceAtom)

theorem burnolDividedShiftPhysicalPort_eq_inner_burnolShift
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    burnolDividedShiftPhysicalPort rho =
      inner ℂ burnolFixedSubWindowSourceAtom
        (burnolShift rho burnolFixedSubWindowSourceAtom) := by
  exact (inner_burnolShift h burnolFixedSubWindowSourceAtom
    burnolFixedSubWindowSourceAtom).symm

/-- Exact identification of the physical dilation port with the fixed Mellin Cauchy quadratic
form. -/
theorem burnolDividedShiftPhysicalPort_eq_inner_mellin
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    burnolDividedShiftPhysicalPort rho =
      inner ℂ burnolFixedSubWindowSourceAtom
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by
  rw [burnolDividedShiftPhysicalPort_eq_inner_burnolShift h,
    burnolShift_eq_burnolMellinDividedShift h]

/-- Exact Herglotz energy law for the physical fixed-source port. -/
theorem re_burnolDividedShiftPhysicalPort_eq
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    (burnolDividedShiftPhysicalPort rho).re =
      (rho.re - 1 / 2) *
        ‖burnolMellinDividedShift h burnolFixedSubWindowSourceAtom‖ ^ 2 := by
  rw [burnolDividedShiftPhysicalPort_eq_inner_mellin h]
  exact re_inner_burnolMellinDividedShift_eq h burnolFixedSubWindowSourceAtom

/-- The fixed physical source port is strictly positive throughout the open right half-plane. -/
theorem re_burnolDividedShiftPhysicalPort_pos
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    0 < (burnolDividedShiftPhysicalPort rho).re := by
  rw [re_burnolDividedShiftPhysicalPort_eq h]
  have hshift : burnolMellinDividedShift h burnolFixedSubWindowSourceAtom ≠ 0 := by
    intro hz
    have hinner := burnolMellinDividedShift_inner_ne_zero h
      burnolFixedSubWindowSourceAtom_ne_zero
    apply hinner
    rw [hz, inner_zero_right]
  exact mul_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hshift))

/-- Scalar pre-divisor producer target: at every actual right-half Xi divisor, the oriented
Euler--Gamma--Stokes law makes the fixed physical dilation port nonpositive. -/
def BurnolXiDividedShiftPhysicalDissipativity : Prop :=
  ∀ (rho : XiDivisorSupport) (_hh : 1 / 2 < (rho : ℂ).re),
    (burnolDividedShiftPhysicalPort (rho : ℂ)).re ≤ 0

/-- Vector source flatness and scalar physical dissipativity are equivalent endpoint producers. -/
theorem burnolXiDividedShiftSourceFlatness_iff_physicalDissipativity :
    BurnolXiDividedShiftSourceFlatness ↔ BurnolXiDividedShiftPhysicalDissipativity := by
  constructor
  · intro hflat rho hright
    have hne := xiDivisor_burnolSubWindow_mellinDividedShift_sourceProjection_ne_zero
      rho hright (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num)
    exfalso
    exact hne (hflat rho hright)
  · intro hdiss rho hright
    have hle := hdiss rho hright
    have hpos := re_burnolDividedShiftPhysicalPort_pos hright
    exfalso
    linarith

/-- The scalar physical source law is sufficient to close RH. -/
theorem riemannHypothesis_of_burnolXiDividedShiftPhysicalDissipativity
    (hsource : BurnolXiDividedShiftPhysicalDissipativity) : RiemannHypothesis := by
  apply riemannHypothesis_of_burnolXiDividedShiftSourceFlatness
  exact burnolXiDividedShiftSourceFlatness_iff_physicalDissipativity.mpr hsource

end RHTower
