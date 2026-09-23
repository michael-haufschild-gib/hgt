import GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics
import GaloisForLFunctions.RHTower.SelbergModularPotentialGreen

/-!
# Original characterwise core Green identity with coherent seam flux

The actual character mass is C² and its physical currents match on the vertical
sides. Horizontal and vertical area integration retain the complete paired circle
normal current, including its arc-length factor. The resulting original core
quarter identity keeps the top current, the coherent curved-seam current, and
the exact spectral mass correction. No characterwise inversion cancellation or
boundary positivity is an input.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterCoreGreen
open SelbergMaassCongruenceTrace SelbergMaassCuspTransport SelbergMaassTraceEnergy
open SelbergMaassCongruenceAverage SelbergMaassCharacterDynamics
open SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection
open SelbergMaassCharacterSeamFlux SelbergMaassMean
open SelbergMaassTraceStokes SelbergModularDomainSlices SelbergModularArcIntegration
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The original character current restricted to the actual circular boundary. -/
def arcCurrent (r : ZMod (N+1)) (v : ℂ) (x : ℝ) : ℝ :=
  dir v (characterMass N f (upperBlock N) r) (point x (arcHeight x))

theorem arcCurrent_continuousOn (r : ZMod (N+1)) (v : ℂ) :
    ContinuousOn (arcCurrent N f r v) (Icc (-(1/2 : ℝ)) (1/2)) :=
  SelbergModularPotentialGreen.current_arc_continuousOn _ (characterMass_contDiffOn N f _ r) v

theorem reflected_arcCurrent_continuousOn (r : ZMod (N+1)) (v : ℂ) :
    ContinuousOn (fun x => arcCurrent N f r v (-x)) (Icc (-(1/2 : ℝ)) (1/2)) :=
  (arcCurrent_continuousOn N f r v).comp continuous_neg.continuousOn
    (by intro x hx; constructor <;> linarith [hx.1,hx.2])

/-- The literal normal-density current has the two physical coordinate components. -/
theorem circleNormalCurrent_components (r : ZMod (N+1)) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    circleNormalCurrent N f r x y =
      (-x/y)*dir 1 (characterMass N f (upperBlock N) r) (point x y)-
        dir Complex.I (characterMass N f (upperBlock N) r) (point x y) := by
  have hv : (-y⁻¹) • point x y = (-x/y) • (1 : ℂ)-Complex.I := by
    have hcy : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    simp only [point,Complex.real_smul]
    push_cast
    field_simp [hcy]
    ring
  unfold circleNormalCurrent
  rw [hv,dir,map_sub,map_smul]
  rfl

/-- The exact paired outward normal current retained on the original core seam. -/
def pairedArcCurrent (r : ZMod (N+1)) (x : ℝ) : ℝ :=
  circleNormalCurrent N f r x (arcHeight x)+circleNormalCurrent N f r (-x) (arcHeight x)

theorem pairedArcCurrent_components (r : ZMod (N+1))
    {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    pairedArcCurrent N f r x =
      (x/arcHeight x)*(arcCurrent N f r 1 (-x)-arcCurrent N f r 1 x)-
        (arcCurrent N f r Complex.I (-x)+arcCurrent N f r Complex.I x) := by
  have hn : arcHeight (-x)=arcHeight x := by simp [arcHeight]
  rw [pairedArcCurrent,circleNormalCurrent_components N f r x (arcHeight_pos hx),
    circleNormalCurrent_components N f r (-x) (arcHeight_pos hx)]
  simp only [arcCurrent,hn]
  ring

theorem horizontalArc_continuousOn (r : ZMod (N+1)) :
    ContinuousOn (fun x => (x/arcHeight x)*(arcCurrent N f r 1 (-x)-arcCurrent N f r 1 x))
      (Icc (-(1/2 : ℝ)) (1/2)) :=
  (continuousOn_id.div continuous_arcHeight.continuousOn
    (fun _ hx => (arcHeight_pos hx).ne')).mul
      ((reflected_arcCurrent_continuousOn N f r 1).sub (arcCurrent_continuousOn N f r 1))

theorem pairedArcCurrent_continuousOn (r : ZMod (N+1)) :
    ContinuousOn (pairedArcCurrent N f r) (Icc (-(1/2 : ℝ)) (1/2)) := by
  apply ((horizontalArc_continuousOn N f r).sub
    ((reflected_arcCurrent_continuousOn N f r Complex.I).add
      (arcCurrent_continuousOn N f r Complex.I))).congr
  intro x hx
  exact pairedArcCurrent_components N f r hx

/-- The actual upper boundary current of one original character mass. -/
def topCurrent (r : ZMod (N+1)) (Y : ℝ) : ℝ :=
  ∫ x in (-(1/2 : ℝ))..(1/2), dir Complex.I (characterMass N f (upperBlock N) r) (point x Y)

/-- Original characterwise planar Stokes retains the complete paired circular current. -/
theorem character_area_stokes (r : ZMod (N+1)) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian (characterMass N f (upperBlock N) r) (point p.1 p.2)) =
      topCurrent N f r Y + ∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x := by
  let M := characterMass N f (upperBlock N) r
  have hM := characterMass_contDiffOn N f (upperBlock N) r
  have hside : ∀ {y : ℝ}, 0 < y → SelbergModularPotentialGreen.currentAt M 1 (1/2) y =
      SelbergModularPotentialGreen.currentAt M 1 (-(1/2)) y :=
    fun hy => characterMass_current_sides N f r 1 hy
  have hi (v : ℂ) := SelbergModularPotentialGreen.secondAt_integrableOn M hM v v Y
  change (∫ p in domain Y, SelbergModularPotentialGreen.secondAt M 1 1 p +
    SelbergModularPotentialGreen.secondAt M Complex.I Complex.I p) = _
  rw [integral_add (hi 1) (hi Complex.I),
    SelbergModularPotentialGreen.horizontal_area_eq_arc M hM hside hY,
    SelbergModularPotentialGreen.vertical_area_eq_top_sub_bottom M hM hY,
    fold_integral (SelbergModularPotentialGreen.current_arc_continuousOn M hM Complex.I)]
  have hxsub : uIcc (0 : ℝ) (1/2) ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
    intro x hx
    have h : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
    exact ⟨by linarith [h.1],h.2⟩
  have hh : IntervalIntegrable
      (fun x => (x/arcHeight x)*(arcCurrent N f r 1 (-x)-arcCurrent N f r 1 x)) volume 0 (1/2) :=
    ((horizontalArc_continuousOn N f r).mono hxsub).intervalIntegrable
  have hb : IntervalIntegrable
      (fun x => arcCurrent N f r Complex.I (-x)+arcCurrent N f r Complex.I x) volume 0 (1/2) :=
    (((reflected_arcCurrent_continuousOn N f r Complex.I).add
      (arcCurrent_continuousOn N f r Complex.I)).mono hxsub).intervalIntegrable
  have he : (∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x) =
      (∫ x in (0 : ℝ)..(1/2), (x/arcHeight x)*(arcCurrent N f r 1 (-x)-arcCurrent N f r 1 x))-
      ∫ x in (0 : ℝ)..(1/2), arcCurrent N f r Complex.I (-x)+arcCurrent N f r Complex.I x := by
    rw [← intervalIntegral.integral_sub hh hb]
    exact intervalIntegral.integral_congr (fun x hx => pairedArcCurrent_components N f r (hxsub hx))
  rw [he]
  have hn (x : ℝ) : arcHeight (-x)=arcHeight x := by simp [arcHeight]
  simp only [topCurrent,arcCurrent,SelbergModularPotentialGreen.currentAt,M,hn]
  ring

/-- Original character hyperbolic mass density in the physical planar coordinates. -/
def massAt (r : ZMod (N+1)) (p : ℝ × ℝ) : ℝ :=
  characterMass N f (upperBlock N) r (point p.1 p.2)/p.2^(2 : ℕ)

/-- Original character physical gradient minus its quarter hyperbolic mass density. -/
def quarterAt (r : ZMod (N+1)) (p : ℝ × ℝ) : ℝ :=
  characterGradient N f (upperBlock N) r (ofComplex (point p.1 p.2))-
    characterMass N f (upperBlock N) r (point p.1 p.2)/(4*p.2^(2 : ℕ))

def coreMass (r : ZMod (N+1)) (Y : ℝ) : ℝ := ∫ p in domain Y, massAt N f r p

def coreQuarter (r : ZMod (N+1)) (Y : ℝ) : ℝ := ∫ p in domain Y, quarterAt N f r p

/-- Exact pointwise channel quarter form, with original spectral mass correction retained. -/
theorem quarterAt_eq_laplacian_mass (r : ZMod (N+1)) {p : ℝ × ℝ} (hp : 0 < p.2) :
    quarterAt N f r p =
      (1/2)*realLaplacian (characterMass N f (upperBlock N) r) (point p.1 p.2)+
        (lam-1/4)*massAt N f r p := by
  have hc := SelbergMaassUnipotentPaths.coe_ofComplex_point p.1 hp
  have hi : (ofComplex (point p.1 p.2)).im = p.2 := by
    change ((ofComplex (point p.1 p.2) : ℍ) : ℂ).im = p.2
    rw [hc]
    simp [point]
  have h := characterMass_laplacian N f (upperBlock N) r (ofComplex (point p.1 p.2))
  rw [hc,hi] at h
  rw [quarterAt,massAt,h]
  ring

/-- Actual channel mass is integrable on every compact modular core. -/
theorem massAt_integrableOn (r : ZMod (N+1)) (Y : ℝ) :
    IntegrableOn (massAt N f r) (domain Y) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => characterMass N f (upperBlock N) r (point p.1 p.2))
      (cell Y) := by
    apply (characterMass_contDiffOn N f (upperBlock N) r).continuousOn.comp
      (show Continuous (fun p : ℝ × ℝ => point p.1 p.2) by unfold point; fun_prop).continuousOn
    intro p hp
    have hy := hp.2.1
    change 0 < (point p.1 p.2).im
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    linarith
  apply ContinuousOn.integrableOn_compact (isCompact_domain Y)
  apply (hc.div₀ (continuous_snd.pow 2).continuousOn (fun p hp => ?_)).mono (domain_subset_cell Y)
  apply pow_ne_zero 2
  have hy := hp.2.1
  linarith

/-- The original channel mass Laplacian is integrable for ordinary two-dimensional core area. -/
theorem laplacian_integrableOn (r : ZMod (N+1)) (Y : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      realLaplacian (characterMass N f (upperBlock N) r) (point p.1 p.2)) (domain Y) :=
  (SelbergModularPotentialGreen.secondAt_integrableOn _ (characterMass_contDiffOn N f _ r) 1 1 Y).add
    (SelbergModularPotentialGreen.secondAt_integrableOn _ (characterMass_contDiffOn N f _ r) Complex.I Complex.I Y)

/-- Actual channel quarter energy is integrable with all source terms retained. -/
theorem quarterAt_integrableOn (r : ZMod (N+1)) (Y : ℝ) :
    IntegrableOn (quarterAt N f r) (domain Y) := by
  apply Integrable.congr (((laplacian_integrableOn N f r Y).const_mul (1/2)).add
    ((massAt_integrableOn N f r Y).const_mul (lam-1/4)))
  filter_upwards [ae_restrict_mem (isCompact_domain Y).measurableSet] with p hp
  have hy : 0 < p.2 := by have h := (domain_subset_cell Y hp).2.1; linarith
  exact (quarterAt_eq_laplacian_mass N f r hy).symm

/-- Exact original characterwise core quarter energy, including the coherent curved seam current. -/
theorem core_quarter_identity (r : ZMod (N+1)) {Y : ℝ} (hY : 1 ≤ Y) :
    coreQuarter N f r Y = (1/2)*topCurrent N f r Y+
      (1/2)*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x)+
        (lam-1/4)*coreMass N f r Y := by
  have he : coreQuarter N f r Y =
      ∫ p in domain Y, (1/2)*realLaplacian (characterMass N f (upperBlock N) r) (point p.1 p.2)+
        (lam-1/4)*massAt N f r p := by
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro p hp
    have hy : 0 < p.2 := by have h := (domain_subset_cell Y hp).2.1; linarith
    exact quarterAt_eq_laplacian_mass N f r hy
  rw [he,integral_add ((laplacian_integrableOn N f r Y).const_mul (1/2))
    ((massAt_integrableOn N f r Y).const_mul (lam-1/4)),integral_const_mul,integral_const_mul,
    character_area_stokes N f r hY]
  change (1/2)*(_+_)+(lam-1/4)*coreMass N f r Y = _
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterCoreGreen
