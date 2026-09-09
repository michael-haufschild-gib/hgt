import GaloisForLFunctions.RHTower.SelbergMaassCharacterCoreGreen
import GaloisForLFunctions.RHTower.SelbergMaassReadoutCusp
import GaloisForLFunctions.RHTower.SelbergMaassResidualSupport

/-!
# Original character core–cusp gluing and arithmetic seam control

Every coordinate observation of an actual upper-character Maass source retains its
physical mass and flux. Unit-period transport and genuine cusp integrability match
the full coordinate sum to the literal character top current and unit-strip tail.
The complete core–cusp identity cancels the cutoff flux, preserves the curved seam,
and keeps every Bessel boundary mode and nonnegative square remainder. The boundary
form is exactly the original residue-class Fourier-vector form. Square completion
on the physical half-arc bounds the squared glued balance by two thirds of the
actual inversion-loss times full-gradient integral on that arc.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterCuspGlue
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassCuspTransport
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassCharacterGradient
open SelbergMaassCharacterDynamics SelbergMaassCharacterCoreGreen SelbergMaassReadoutCusp
open SelbergMaassTraceEnergy SelbergMaassUnipotentBlocks SelbergMaassMean SelbergMaassFourier
open SelbergMaassUnipotentFourier
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- A literal coordinate observation of the actual upper-character source. -/
def upperReadout (N : ℕ) (r : ZMod (N+1)) (q : Deck N) : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ :=
  (EuclideanSpace.proj q).comp (characterProjection N (upperBlock N) r).toContinuousLinearMap

/-- The actual character mass has continuous horizontal slices at positive height. -/
theorem mass_slice_continuous (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => characterMass N f (upperBlock N) r (point x y)) := by
  apply (characterMass_contDiffOn N f (upperBlock N) r).continuousOn.comp_continuous
    (show Continuous (fun x => point x y) by unfold point; fun_prop)
  intro x
  simpa [point] using hy

/-- Unit translation preserves the literal physical character mass slice. -/
theorem mass_slice_periodic (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => characterMass N f (upperBlock N) r (point x y)) 1 := by
  intro x
  have h := characterMass_translation N f r (ofComplex (point x y))
  rw [SelbergMaassTraceBoundary.translation_point x hy] at h
  simpa only [SelbergMaassUnipotentPaths.coe_ofComplex_point _ hy] using h

/-- Each actual physical character current has the same unit period. -/
theorem current_slice_periodic (r : ZMod (N+1)) (v : ℂ) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => dir v (characterMass N f (upperBlock N) r) (point x y)) 1 := by
  intro x
  have h := characterMass_current_translation N f r v (ofComplex (point x y))
  rw [SelbergMaassTraceBoundary.translation_point x hy] at h
  simpa only [SelbergMaassUnipotentPaths.coe_ofComplex_point _ hy] using h

/-- An actual readout mass is the period-normalized physical squared-modulus integral. -/
theorem readoutMass_eq_integral (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    readoutMass N f L y = (((N+1 : ℕ) : ℝ)⁻¹)*
      ∫ x in (0 : ℝ)..(N+1 : ℕ), normSq (L (sourceVector N f (ofComplex (point x y)))) := by
  rw [readoutMass,SelbergMaassFlux.pairing_self _ (readout_contDiffOn N f L).continuousOn hy,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N+1 : ℕ))]

/-- Summing every observed coordinate gives exactly one physical unit strip of character mass. -/
theorem mass_integral_eq_sum_readout (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, characterMass N f (upperBlock N) r (point x y)) =
      ∑ q : Deck N, readoutMass N f (upperReadout N r q) y := by
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun x => characterMass N f (upperBlock N) r (point x y)) volume a b :=
    (mass_slice_continuous N f r hy).intervalIntegrable
  have hp := (mass_slice_periodic N f r hy).intervalIntegral_add_zsmul_eq
    ((N+1 : ℕ) : ℤ) 0 hint
  have hscale : (∫ x in (0 : ℝ)..(N+1 : ℕ), characterMass N f (upperBlock N) r (point x y)) =
      ((N+1 : ℕ) : ℝ)*(∫ x in (0 : ℝ)..1, characterMass N f (upperBlock N) r (point x y)) := by
    simpa only [zero_add,zsmul_eq_mul,Int.cast_natCast,mul_one] using hp
  simp_rw [readoutMass_eq_integral N f _ hy]
  rw [← Finset.mul_sum,← intervalIntegral.integral_finsetSum]
  · have hm (x : ℝ) :
        (∑ q : Deck N, normSq (upperReadout N r q (sourceVector N f (ofComplex (point x y))))) =
          characterMass N f (upperBlock N) r (point x y) :=
      (characterMass_eq_sum N f (upperBlock N) r _).symm
    simp_rw [hm]
    rw [hscale]
    field_simp
  · intro q _
    exact (Complex.continuous_normSq.comp
      (slice_continuous (readout_contDiffOn N f (upperReadout N r q)).continuousOn hy)).intervalIntegrable _ _

/-- Every actual observed mass differentiates to twice its literal physical flux. -/
theorem readoutMass_hasDerivAt (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (readoutMass N f L) (2*readoutFlux N f L y) y := by
  let F := fun w => L (sourceVector N f (ofComplex w))
  have hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} := (readout_contDiffOn N f L).of_le (by simp)
  have hd := directional_contDiffOn hf (m := 0) (by simp) Complex.I
  change HasDerivAt (fun t => ((N+1 : ℕ) : ℝ)⁻¹*SelbergMaassFlux.pairing (N+1 : ℕ) F F t) _ y
  apply ((SelbergMaassFlux.pairing_hasDerivAt (N+1 : ℕ) hf hf hy).const_mul
    ((N+1 : ℕ) : ℝ)⁻¹).congr_deriv
  rw [SelbergMaassFlux.pairing_symm (N+1 : ℕ) hf.continuousOn hd.continuousOn hy]
  change _ = 2*(((N+1 : ℕ) : ℝ)⁻¹*SelbergMaassFlux.pairing (N+1 : ℕ) (directional Complex.I F) F y)
  ring

/-- The derivative of the unit-strip character mass retains all coordinate fluxes. -/
theorem mass_integral_hasDerivAt (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..1, characterMass N f (upperBlock N) r (point x t))
      (2*∑ q : Deck N, readoutFlux N f (upperReadout N r q) y) y := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Deck N)))
    (fun q _ => readoutMass_hasDerivAt N f (upperReadout N r q) hy)
  rw [← Finset.mul_sum] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact mass_integral_eq_sum_readout N f r ht

/-- Literal unit-period current equals twice the complete sum of physical observed fluxes. -/
theorem unit_current_eq_sum_readoutFlux (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, dir Complex.I (characterMass N f (upperBlock N) r) (point x y)) =
      2*∑ q : Deck N, readoutFlux N f (upperReadout N r q) y := by
  let D := characterMass N f (upperBlock N) r
  let G : ℂ → ℂ := fun z => (D z : ℂ)
  have hD : ContDiffOn ℝ 1 D {z : ℂ | 0 < z.im} :=
    (characterMass_contDiffOn N f (upperBlock N) r).of_le (by simp)
  have hG : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hD
  have he (x : ℝ) : directional Complex.I G (point x y) =
      ((dir Complex.I D (point x y) : ℝ) : ℂ) := by
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have hd := ((hD.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have hs := hd.comp_hasDerivAt y (point_vertical x y)
    exact (slice_vertical hG x hy).unique (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y hs)
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (periodIntegral_hasDerivAt 1 hG hy)
  change HasDerivAt (fun t => (periodIntegral 1 G t).re)
    (periodIntegral 1 (directional Complex.I G) y).re y at h
  have hv : (periodIntegral 1 (directional Complex.I G) y).re =
      ∫ x in (0 : ℝ)..1, dir Complex.I D (point x y) := by
    unfold periodIntegral
    simp_rw [he]
    rw [integral_complex_ofReal,Complex.ofReal_re,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hv] at h
  have hf : (fun t => (periodIntegral 1 G t).re) =
      (fun t => ∫ x in (0 : ℝ)..1, D (point x t)) := by
    funext t
    simp only [periodIntegral,G,integral_complex_ofReal,Complex.ofReal_re,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hf] at h
  exact h.unique (mass_integral_hasDerivAt N f r hy)

/-- All actual cusp observations match exactly half the original core top current. -/
theorem sum_readoutFlux_eq_topCurrent (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∑ q : Deck N, readoutFlux N f (upperReadout N r q) y) = topCurrent N f r y/2 := by
  have hp := (current_slice_periodic N f r Complex.I hy).intervalIntegral_add_eq (-(1/2)) 0
  norm_num at hp
  have h := unit_current_eq_sum_readoutFlux N f r hy
  change topCurrent N f r y = _ at hp
  rw [← hp] at h
  linarith

/-- Every observed hyperbolic mass has a genuine integrable cusp tail, including zero observations. -/
theorem readout_hyperbolicMass_tail_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => readoutMass N f L y/y^2) (Ioi Y) := by
  rcases readout_zero_or_maass N f L with h0 | ⟨g,hg⟩
  · have hz : readoutMass N f L = 0 := by
      funext y
      change (((N+1 : ℕ) : ℝ)⁻¹)*
        (periodIntegral (N+1 : ℕ) (fun w => L (sourceVector N f (ofComplex w))*
          (starRingEnd ℂ) (L (sourceVector N f (ofComplex w)))) y).re = 0
      simp [h0,periodIntegral]
    simp [hz]
  · have he : g.1.1 ∘ ofComplex = (fun w => L (sourceVector N f (ofComplex w))) := funext (fun w => hg _)
    simpa only [SelbergMaassFlux.mass,he,readoutMass] using
      SelbergMaassTailEnergy.hyperbolicMass_tail_integrable N lam g hY

/-- Literal hyperbolic mass of one actual character on the complete unit-width cusp. -/
def tailMass (r : ZMod (N+1)) (Y : ℝ) : ℝ :=
  ∫ y in Ioi Y, (∫ x in (0 : ℝ)..1, characterMass N f (upperBlock N) r (point x y))/y^2

/-- The character's original unit-strip mass is integrable over every positive cusp tail. -/
theorem character_tail_mass_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y =>
      (∫ x in (0 : ℝ)..1, characterMass N f (upperBlock N) r (point x y))/y^2) (Ioi Y) := by
  apply (integrable_finsetSum Finset.univ
    (fun q _ => readout_hyperbolicMass_tail_integrable N lam f (upperReadout N r q) hY)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [mass_integral_eq_sum_readout N f r (hY.trans hy),Finset.sum_div]

/-- The complete physical character tail mass equals the sum of all observed tail masses. -/
theorem tailMass_eq_sum (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) {Y : ℝ} (hY : 0 < Y) :
    tailMass N f r Y = ∑ q : Deck N, ∫ y in Ioi Y, readoutMass N f (upperReadout N r q) y/y^2 := by
  unfold tailMass
  rw [← integral_finsetSum Finset.univ (fun q _ =>
    readout_hyperbolicMass_tail_integrable N lam f (upperReadout N r q) hY)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [mass_integral_eq_sum_readout N f r (hY.trans hy),Finset.sum_div]

/-- The complete Bessel boundary form on every original coordinate of the character channel. -/
def boundarySum (r : ZMod (N+1)) (T : ℝ) : ℝ :=
  ∑ q : Deck N, ∑' n : ℤ, SelbergBesselModes.seam (Real.log (N+1 : ℕ)) T n *
    normSq (coefficient (N+1 : ℕ) n
      (fun w => upperReadout N r q (sourceVector N f (ofComplex w))) (Real.exp T))

/-- Every actual Fourier square remainder in every original character coordinate. -/
def squareSum (r : ZMod (N+1)) (T : ℝ) : ℝ :=
  ∑ q : Deck N, ∑' n : ℤ, readoutModeSquareTail N f (upperReadout N r q) T n

/-- The complete original character square remainder is nonnegative. -/
theorem squareSum_nonneg (r : ZMod (N+1)) (T : ℝ) : 0 ≤ squareSum N f r T :=
  Finset.sum_nonneg (fun q _ => tsum_nonneg (readoutModeSquareTail_nonneg N f (upperReadout N r q) T))

/-- The complete character cusp form retains the original top current and literal spectral tail mass. -/
theorem character_flux_boundary_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) (T : ℝ) :
    -topCurrent N f r (Real.exp T)/2+((lam : ℝ)-1/4)*tailMass N f r (Real.exp T) =
      boundarySum N f r T+squareSum N f r T := by
  rw [tailMass_eq_sum N lam f r (Real.exp_pos T)]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Deck N))) rfl
    (fun q _ => readout_flux_boundary_identity N lam f (upperReadout N r q) T)
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,← Finset.mul_sum,
    sum_readoutFlux_eq_topCurrent N f r (Real.exp_pos T)] at h
  change _ = boundarySum N f r T+squareSum N f r T at h
  simpa only [neg_div] using h

/-- Exact original character core–cusp gluing cancels the cutoff flux and retains the coherent curved seam. -/
theorem core_cusp_quarter_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) (T : ℝ) (hT : 1 ≤ Real.exp T) :
    SelbergMaassCharacterCoreGreen.coreQuarter N f r (Real.exp T)+boundarySum N f r T+squareSum N f r T =
      (1/2)*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x)+
        ((lam : ℝ)-1/4)*(SelbergMaassCharacterCoreGreen.coreMass N f r (Real.exp T)+tailMass N f r (Real.exp T)) := by
  have hc := SelbergMaassCharacterCoreGreen.core_quarter_identity N f r hT
  have ht := character_flux_boundary_identity N lam f r T
  linear_combination hc-ht

/-- Complete observed cusp forms equal the literal projected Fourier-vector boundary form. -/
theorem boundarySum_eq_projected_fourier (r : ZMod (N+1)) (T : ℝ) :
    boundarySum N f r T = ∑' n : ℤ, SelbergBesselModes.seam (Real.log (N+1 : ℕ)) T n *
      ‖characterProjection N (upperBlock N) r (coefficientVector N f n (Real.exp T))‖^2 := by
  unfold boundarySum
  rw [← Summable.tsum_finsetSum (fun q _ => readout_seam_summable N f (upperReadout N r q) T)]
  apply tsum_congr
  intro n
  simp_rw [coefficient_readout N f _ n (Real.exp_pos T)]
  rw [← Finset.mul_sum,EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rfl

/-- The actual cusp boundary form retains precisely the original Fourier residue channel. -/
theorem boundarySum_eq_residue_fourier (r : ZMod (N+1)) (T : ℝ) :
    boundarySum N f r T = ∑' n : ℤ, if (n : ZMod (N+1))=r then
      SelbergBesselModes.seam (Real.log (N+1 : ℕ)) T n *
        ‖coefficientVector N f n (Real.exp T)‖^2 else 0 := by
  rw [boundarySum_eq_projected_fourier]
  apply tsum_congr
  intro n
  rw [upperProjection_coefficientVector N f r n (Real.exp_pos T)]
  split_ifs <;> simp

/-- The complete nonnegative character square series may be grouped by original integer mode. -/
theorem squareSum_eq_mode_sum (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) (T : ℝ) :
    squareSum N f r T = ∑' n : ℤ, ∑ q : Deck N, readoutModeSquareTail N f (upperReadout N r q) T n := by
  exact (Summable.tsum_finsetSum
    (fun q _ => readout_square_tail_summable N lam f (upperReadout N r q) T)).symm

/-- At height one the full original character quarter balance has no cutoff-height condition. -/
theorem core_cusp_quarter_identity_one (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) :
    SelbergMaassCharacterCoreGreen.coreQuarter N f r 1+boundarySum N f r 0+squareSum N f r 0 =
      (1/2)*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x)+
        ((lam : ℝ)-1/4)*(SelbergMaassCharacterCoreGreen.coreMass N f r 1+tailMass N f r 1) := by
  simpa only [Real.exp_zero] using core_cusp_quarter_identity N lam f r 0 (by simp)

/-- Actual inversion-transfer loss times the original full physical gradient on the circular seam. -/
def arcLossGradient (r : ZMod (N+1)) (x : ℝ) : ℝ :=
  (‖sourceVector N f (ofComplex (point x (SelbergMaassTraceStokes.arcHeight x)))‖^2-
    ‖inversionTransfer N r r (sourceVector N f (ofComplex (point x (SelbergMaassTraceStokes.arcHeight x))))‖^2)*
      gradientDensity N f (point x (SelbergMaassTraceStokes.arcHeight x))

/-- Original smoothness makes the arithmetic loss–gradient density continuous on the entire modular arc. -/
theorem arcLossGradient_continuousOn (r : ZMod (N+1)) :
    ContinuousOn (arcLossGradient N f r) (Icc (-(1/2 : ℝ)) (1/2)) := by
  let c := fun x => point x (SelbergMaassTraceStokes.arcHeight x)
  have hc : Continuous c := by
    unfold c point
    exact continuous_ofReal.comp continuous_id |>.add
      ((continuous_ofReal.comp SelbergModularDomainSlices.continuous_arcHeight).mul continuous_const)
  have hm : MapsTo c (Icc (-(1/2 : ℝ)) (1/2)) {z : ℂ | 0 < z.im} := by
    intro x hx
    simpa [c,point] using SelbergMaassTraceStokes.arcHeight_pos hx
  have hs := (sourceVector_continuousOn N f).comp hc.continuousOn hm
  have ht := (inversionTransfer N r r).continuous_of_finiteDimensional.comp_continuousOn hs
  have hg := (SelbergMaassResidualSupport.gradientDensity_continuousOn N f).comp hc.continuousOn hm
  exact ((hs.norm.pow 2).sub (ht.norm.pow 2)).mul hg

/-- Completing the square of the literal seam current retains the exact half-interval constant. -/
theorem pairedArc_integral_sq_le (r : ZMod (N+1)) :
    (∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x)^2 ≤
      (1/2)*(∫ x in (0 : ℝ)..(1/2), (pairedArcCurrent N f r x)^2) := by
  let J := pairedArcCurrent N f r
  let A := ∫ x in (0 : ℝ)..(1/2), J x
  have hsub : uIcc (0 : ℝ) (1/2) ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
    intro x hx
    have h : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
    exact ⟨by linarith [h.1],h.2⟩
  have hj : IntervalIntegrable J volume 0 (1/2) :=
    ((pairedArcCurrent_continuousOn N f r).mono hsub).intervalIntegrable
  have hj2 : IntervalIntegrable (fun x => J x^2) volume 0 (1/2) :=
    (((pairedArcCurrent_continuousOn N f r).mono hsub).pow 2).intervalIntegrable
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1/2) (fun x => sq_nonneg (J x-2*A))
  have he : (∫ x in (0 : ℝ)..(1/2), (J x-2*A)^2) =
      (∫ x in (0 : ℝ)..(1/2), J x^2)-2*A^2 := by
    calc
      _ = ∫ x in (0 : ℝ)..(1/2), (J x^2-(4*A)*J x)+4*A^2 :=
        intervalIntegral.integral_congr (fun _ _ => by ring)
      _ = _ := by
        rw [intervalIntegral.integral_add (hj2.sub (hj.const_mul (4*A))) intervalIntegrable_const,
          intervalIntegral.integral_sub hj2 (hj.const_mul (4*A)),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
        change (∫ x in (0 : ℝ)..(1/2), J x^2)-(4*A)*A+((1/2 : ℝ)-0) • (4*A^2) = _
        rw [smul_eq_mul]
        ring
  rw [he] at hn
  change A^2 ≤ _
  linarith

/-- The exact integrated seam response is bounded by original arithmetic loss and full gradient. -/
theorem half_pairedArc_integral_sq_le (r : ZMod (N+1)) :
    ((1/2)*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x))^2 ≤
      (2/3)*(∫ x in (0 : ℝ)..(1/2), arcLossGradient N f r x) := by
  have hsub : uIcc (0 : ℝ) (1/2) ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
    intro x hx
    have h : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
    exact ⟨by linarith [h.1],h.2⟩
  have hj : IntervalIntegrable (fun x => (pairedArcCurrent N f r x)^2) volume 0 (1/2) :=
    (((pairedArcCurrent_continuousOn N f r).mono hsub).pow 2).intervalIntegrable
  have hg : IntervalIntegrable (arcLossGradient N f r) volume 0 (1/2) :=
    ((arcLossGradient_continuousOn N f r).mono hsub).intervalIntegrable
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1/2) hj
    (hg.const_mul (16/3)) (fun x hx =>
      SelbergMaassCharacterSeamFlux.modular_arc_normal_current_sq_le N f r
        ⟨x,⟨by linarith [hx.1],hx.2⟩⟩)
  rw [intervalIntegral.integral_const_mul] at hm
  have hc := pairedArc_integral_sq_le N f r
  nlinarith

/-- The full glued character quarter balance has an original-source arithmetic seam bound. -/
theorem core_cusp_balance_sq_le (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) :
    (SelbergMaassCharacterCoreGreen.coreQuarter N f r 1+boundarySum N f r 0+squareSum N f r 0-
      ((lam : ℝ)-1/4)*(SelbergMaassCharacterCoreGreen.coreMass N f r 1+tailMass N f r 1))^2 ≤
        (2/3)*(∫ x in (0 : ℝ)..(1/2), arcLossGradient N f r x) := by
  rw [core_cusp_quarter_identity_one,add_sub_cancel_right]
  exact half_pairedArc_integral_sq_le N f r

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterCuspGlue
