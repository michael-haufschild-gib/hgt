import GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics
import GaloisForLFunctions.RHTower.SelbergMaassBoundaryForm

/-!
# Actual cuspidal observations and complete observed cusp forms

Every fixed continuous linear observation of the original finite Maass source is
congruence-invariant, retains its eigenvalue, and decays at every integral cusp.
It is therefore zero or a genuine Maass cusp eigenform at the unchanged level.
The zero case is retained when transporting the complete Bessel boundary form,
convergent nonnegative square series, physical cusp energy, outgoing flux, and
spectral tail mass to the literal observed source.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassReadoutCusp
open SelbergMaassCongruenceTrace SelbergMaassCuspTransport SelbergMaassCongruenceAverage
open SelbergMaassTraceEnergy SelbergMaassCharacterDynamics SelbergMaassCharacterGradient
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open SelbergMaassMean SelbergMaassFourier SelbergMaassBessel SelbergMaassParseval SelbergMaassTrace
open SelbergMaassBoundaryForm SelbergBoundaryOperator _root_.RHTower
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- A fixed observation of the original source is invariant under its actual congruence group. -/
def readoutInvariant (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma (N+1))) :=
  ⟨fun z => L (sourceVector N f z), by
    intro γ z
    change L (sourceVector N f ((γ : SL2R) • z)) = L (sourceVector N f z)
    apply congrArg L
    ext q
    exact (quotientForm N f q).1.2 γ z⟩

/-- The entire original source vector tends to zero at every integral cusp. -/
theorem sourceVector_cusp_decay (A : SL2Z) :
    Tendsto (fun z : ℍ => sourceVector N f (integralSL2ToReal A • z)) atImInfty (𝓝 0) := by
  have h : Tendsto (fun z : ℍ => fun q : Deck N => (quotientForm N f q).1.1 (integralSL2ToReal A • z))
      atImInfty (𝓝 (fun _ : Deck N => (0 : ℂ))) :=
    tendsto_pi_nhds.mpr (fun q => (quotientForm N f q).2.2.2 A)
  exact ((PiLp.continuous_toLp 2 (fun _ : Deck N => ℂ)).tendsto _).comp h

/-- Every fixed continuous linear observation retains all original integral-cusp conditions. -/
theorem readout_cuspidal (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    IsCuspidalAtIntegralCusps (fun z => L (sourceVector N f z)) := by
  intro A
  change Tendsto (fun z : ℍ => L (sourceVector N f (integralSL2ToReal A • z))) atImInfty (𝓝 0)
  have h := (L.continuous.tendsto 0).comp (sourceVector_cusp_decay N f A)
  simpa only [Function.comp_def,map_zero] using h

/-- The positive hyperbolic eigen-equation of every original source observation. -/
theorem readout_eigen (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (z : ℍ) :
    positiveHyperbolicLaplacian (fun z => L (sourceVector N f z)) z =
      (lam : ℂ)*L (sourceVector N f z) := by
  change -(z.im : ℂ)^2*(dir 1 (dir 1 (fun w => L (sourceVector N f (ofComplex w)))) (z : ℂ)+
    dir Complex.I (dir Complex.I (fun w => L (sourceVector N f (ofComplex w)))) (z : ℂ)) = _
  rw [source_readout_laplacian]
  have hz : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  push_cast
  field_simp [hz]

/-- Every original observation is zero or a genuine Maass cusp eigenform with unchanged level and eigenvalue. -/
theorem readout_zero_or_maass (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    (∀ z : ℍ, L (sourceVector N f z)=0) ∨
      ∃ g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam,
        ∀ z : ℍ, g.1.1 z = L (sourceVector N f z) := by
  classical
  by_cases h : readoutInvariant N f L = 0
  · left
    intro z
    exact congrArg (fun F => F.1 z) h
  · right
    refine ⟨⟨readoutInvariant N f L,h,?_,readout_cuspidal N f L⟩,fun _ => rfl⟩
    exact ⟨readout_contDiffOn N f L,readout_eigen N f L⟩

/-- The zero case is retained when turning an actual projected component into a cuspidal Maass source. -/
theorem characterField_zero_or_maass
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1)) (q : Deck N) :
    (∀ z : ℍ, characterField N f p r q (z : ℂ)=0) ∨
      ∃ g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam,
        ∀ z : ℍ, g.1.1 z = characterField N f p r q (z : ℂ) := by
  have h := readout_zero_or_maass N f
    ((EuclideanSpace.proj q).comp (characterProjection N p r).toContinuousLinearMap)
  change (∀ z : ℍ, characterProjection N p r (sourceVector N f z) q=0) ∨
    ∃ g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam,
      ∀ z : ℍ, g.1.1 z = characterProjection N p r (sourceVector N f z) q at h
  simpa only [characterField,ofComplex_apply] using h

/-- Original physical quarter-energy slice of a fixed linear source observation. -/
def readoutQuarterSlice (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(N+1 : ℕ),
    normSq (directional 1 (fun w => L (sourceVector N f (ofComplex w))) (point x y))+
    normSq (directional Complex.I (fun w => L (sourceVector N f (ofComplex w))) (point x y))-
    (1/(4*y^2))*normSq (L (sourceVector N f (ofComplex (point x y))))

/-- The complete original Bessel square integral for each observed Fourier mode. -/
def readoutModeSquareTail (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (T : ℝ) (n : ℤ) : ℝ :=
  if n=0 then 0 else ∫ y in Ioi (Real.exp T), remainder (modeRate N n)
    (coefficient (N+1 : ℕ) n (fun w => L (sourceVector N f (ofComplex w)))) y

private theorem zero_coefficient (w : ℝ) (n : ℤ) : coefficient w n (fun _ : ℂ => 0) = 0 := by
  funext y
  simp [coefficient,deningerFourierCoeff]

theorem readoutModeSquareTail_nonneg (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (T : ℝ) (n : ℤ) :
    0 ≤ readoutModeSquareTail N f L T n := by
  unfold readoutModeSquareTail
  split_ifs
  · exact le_rfl
  · exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

/-- The complete boundary series of an actual observed source is genuinely summable. -/
theorem readout_seam_summable (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (T : ℝ) :
    Summable (fun n : ℤ => SelbergBesselModes.seam (Real.log (N+1 : ℕ)) T n *
      normSq (coefficient (N+1 : ℕ) n (fun w => L (sourceVector N f (ofComplex w))) (Real.exp T))) := by
  rcases readout_zero_or_maass N f L with h0 | ⟨g,hg⟩
  · simp [h0,coefficient,deningerFourierCoeff]
  · have he : g.1.1 ∘ ofComplex = (fun w => L (sourceVector N f (ofComplex w))) := funext (fun w => hg _)
    simpa only [maassCoefficient,he] using maass_seam_summable N g T

/-- The full observed cusp quarter form equals its actual Bessel form plus every original mode square. -/
theorem readout_boundary_square_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (T : ℝ) :
    (((N+1 : ℕ) : ℝ)⁻¹)*(∫ y in Ioi (Real.exp T), readoutQuarterSlice N f L y) =
      (∑' n : ℤ, SelbergBesselModes.seam (Real.log (N+1 : ℕ)) T n *
        normSq (coefficient (N+1 : ℕ) n (fun w => L (sourceVector N f (ofComplex w))) (Real.exp T)))+
      ∑' n : ℤ, readoutModeSquareTail N f L T n := by
  rcases readout_zero_or_maass N f L with h0 | ⟨g,hg⟩
  · simp [readoutQuarterSlice,readoutModeSquareTail,h0,zero_coefficient,coefficient,deningerFourierCoeff,directional,remainder]
  · have he : g.1.1 ∘ ofComplex = (fun w => L (sourceVector N f (ofComplex w))) := funext (fun w => hg _)
    have h := maass_boundary_square_identity N lam g T
    simpa only [quarterSlice,boundaryForm,formTrace,boundaryTrace_apply,modeSquareTail,maassCoefficient,he,
      readoutQuarterSlice,readoutModeSquareTail] using h

/-- The complete observed cusp square series converges, including zero observations. -/
theorem readout_square_tail_summable (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (T : ℝ) :
    Summable (readoutModeSquareTail N f L T) := by
  rcases readout_zero_or_maass N f L with h0 | ⟨g,hg⟩
  · have hz : readoutModeSquareTail N f L T = 0 := by
      funext n
      simp [readoutModeSquareTail,h0,zero_coefficient,coefficient,deningerFourierCoeff,remainder]
    rw [hz]
    exact summable_zero
  · have he : g.1.1 ∘ ofComplex = (fun w => L (sourceVector N f (ofComplex w))) := funext (fun w => hg _)
    have hm : readoutModeSquareTail N f L T = modeSquareTail N g T := by
      funext n
      simp only [modeSquareTail,maassCoefficient,he,readoutModeSquareTail]
    rw [hm]
    exact (maass_square_tail_hasSum N lam g T).summable

/-- Original period-normalized squared mass of the observed source. -/
def readoutMass (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (y : ℝ) : ℝ :=
  (((N+1 : ℕ) : ℝ)⁻¹)*SelbergMaassFlux.pairing (N+1 : ℕ)
    (fun w => L (sourceVector N f (ofComplex w))) (fun w => L (sourceVector N f (ofComplex w))) y

/-- Original period-normalized physical vertical flux of the observed source. -/
def readoutFlux (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (y : ℝ) : ℝ :=
  (((N+1 : ℕ) : ℝ)⁻¹)*SelbergMaassFlux.pairing (N+1 : ℕ)
    (directional Complex.I (fun w => L (sourceVector N f (ofComplex w))))
    (fun w => L (sourceVector N f (ofComplex w))) y

private theorem zero_pairing (w y : ℝ) :
    SelbergMaassFlux.pairing w (fun _ : ℂ => 0) (fun _ : ℂ => 0) y = 0 := by
  change (periodIntegral w (fun _ : ℂ => (0 : ℂ)*(starRingEnd ℂ) 0) y).re = 0
  simp [periodIntegral]

private theorem zero_directional (v : ℂ) : directional v (fun _ : ℂ => 0) = 0 := by
  funext z
  simp [directional]

/-- The complete observed cusp form has the original outgoing flux and spectral tail mass. -/
theorem readout_flux_boundary_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (T : ℝ) :
    -readoutFlux N f L (Real.exp T)+((lam : ℝ)-1/4)*
      (∫ y in Ioi (Real.exp T), readoutMass N f L y/y^2) =
      (∑' n : ℤ, SelbergBesselModes.seam (Real.log (N+1 : ℕ)) T n *
        normSq (coefficient (N+1 : ℕ) n (fun w => L (sourceVector N f (ofComplex w))) (Real.exp T)))+
      ∑' n : ℤ, readoutModeSquareTail N f L T n := by
  rcases readout_zero_or_maass N f L with h0 | ⟨g,hg⟩
  · simp [readoutFlux,readoutMass,readoutModeSquareTail,h0,zero_directional,zero_pairing,
      zero_coefficient,coefficient,deningerFourierCoeff,remainder]
    exact Or.inr (zero_pairing _ _)
  · have he : g.1.1 ∘ ofComplex = (fun w => L (sourceVector N f (ofComplex w))) := funext (fun w => hg _)
    have h := maass_flux_boundary_identity N lam g T
    simpa only [SelbergMaassFlux.flux,SelbergMaassFlux.mass,boundaryForm,formTrace,boundaryTrace_apply,
      modeSquareTail,maassCoefficient,he,readoutFlux,readoutMass,readoutModeSquareTail] using h

end
end GaloisForLFunctions.RHTower.SelbergMaassReadoutCusp
