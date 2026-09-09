import GaloisForLFunctions.RHTower.SelbergMaassProjectionFlux
import GaloisForLFunctions.RHTower.SelbergMaassCurrentTransport
import GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary
import GaloisForLFunctions.RHTower.SelbergMaassCharacterGradient
import GaloisForLFunctions.RHTower.SelbergMaassTraceStokes

/-!
# Original character flux across the modular inversion seam

The complete source derivative is its actual real Fréchet derivative. Modular
transport reverses its radial direction under inversion. The paired character
radial flux is therefore exactly the upper/lower projection-mismatch pairing.
The proved inversion loss bounds its square by physical radial energy.

An exact polar identity retains both radial and angular derivative energy.
The character flux is half the literal derivative of projected source mass.
On the unit circle, complete arithmetic phase displacement controls the paired
flux. The actual outward normal density retains its arc-length Jacobian; on the
modular core arc its square is bounded by 16/3 times inversion loss times the
original planar gradient density, uniformly in the congruence level.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterSeamFlux
open SelbergMaassCongruenceTrace SelbergMaassCuspTransport SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassCurrentTransport SelbergMaassCongruenceAverage
open SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open SelbergMaassInversionPhaseEnergy SelbergMaassProjectionFlux
open SelbergMaassMean
open GaloisForLFunctions.HTGeometry
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The complete vector of original physical directional derivatives. -/
def sourceDerivative (v : ℂ) (z : ℍ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q : Deck N => dir v (field N f q) (z : ℂ))

theorem sourceDerivative_neg (v : ℂ) (z : ℍ) :
    sourceDerivative N f (-v) z = -sourceDerivative N f v z := by
  ext q
  exact map_neg (fderiv ℝ (field N f q) (z : ℂ)) v

theorem sourceDerivative_components (v : ℂ) (z : ℍ) :
    sourceDerivative N f v z =
      v.re • sourceDerivative N f 1 z + v.im • sourceDerivative N f Complex.I z := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul,mul_one] using v.re_add_im.symm
  ext q
  change fderiv ℝ (field N f q) (z : ℂ) v =
    v.re • (fderiv ℝ (field N f q) (z : ℂ) 1) +
      v.im • (fderiv ℝ (field N f q) (z : ℂ) Complex.I)
  conv_lhs => rw [hv,map_add,map_smul,map_smul]

theorem sourceDerivative_gradient (z : ℍ) :
    ‖sourceDerivative N f 1 z‖^2 + ‖sourceDerivative N f Complex.I z‖^2 =
      gradientDensity N f (z : ℂ) := by
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,← Finset.sum_add_distrib]
  rfl

/-- Both polar directions retain exactly the original full physical gradient. -/
theorem sourceDerivative_polar_energy (v : ℂ) (z : ℍ) :
    ‖sourceDerivative N f v z‖^2 + ‖sourceDerivative N f (Complex.I*v) z‖^2 =
      normSq v * gradientDensity N f (z : ℂ) := by
  rw [sourceDerivative_components N f v,sourceDerivative_components N f (Complex.I*v)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,zero_add]
  rw [norm_add_sq_real,norm_add_sq_real]
  simp only [real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,neg_sq]
  rw [← sourceDerivative_gradient N f z]
  simp only [Complex.normSq_apply]
  ring

theorem sourceDerivative_sq_le_gradient (v : ℂ) (z : ℍ) :
    ‖sourceDerivative N f v z‖^2 ≤ normSq v*gradientDensity N f (z : ℂ) := by
  rw [← sourceDerivative_polar_energy N f v z]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Original derivatives transform with the literal reciprocal-square Jacobian. -/
theorem sourceDerivative_modular (A : SL2Z) (z : ℍ) (v : ℂ) :
    sourceDerivative N f ((1/(denom A z)^2)*v) (A • z) =
      finiteRegularUnitary (QuotientGroup.mk A : Deck N) (sourceDerivative N f v z) := by
  ext q
  exact field_dir_modular N f q A z v

/-- The physical radial derivative reverses under modular inversion. -/
theorem sourceDerivative_radial_inversion (z : ℍ) :
    sourceDerivative N f ((S • z : ℍ) : ℂ) (S • z) =
      -finiteRegularUnitary (QuotientGroup.mk S : Deck N) (sourceDerivative N f (z : ℂ) z) := by
  have h := sourceDerivative_modular N f S z (z : ℂ)
  have hv : (1/(denom S z)^2)*(z : ℂ) = -((S • z : ℍ) : ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul]
    simp [denom,ModularGroup.S,inv_neg]
    field_simp
  rw [hv,sourceDerivative_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Actual upper-character radial flux of the original source. -/
def radialFlux (r : ZMod (N+1)) (z : ℍ) : ℝ :=
  (inner ℂ (characterProjection N (upperBlock N) r (sourceVector N f z))
    (sourceDerivative N f (z : ℂ) z)).re

/-- The paired radial flux equals the coherent upper/lower mismatch pairing. -/
theorem radialFlux_seam_identity (r : ZMod (N+1)) (z : ℍ) :
    radialFlux N f r z + radialFlux N f r (S⁻¹ • z) =
      (inner ℂ (characterProjection N (upperBlock N) r (sourceVector N f z) -
        characterProjection N (lowerBlock N) (-r) (sourceVector N f z))
        (sourceDerivative N f (z : ℂ) z)).re := by
  have hd := sourceDerivative_radial_inversion N f (S⁻¹ • z)
  simp only [smul_inv_smul] at hd
  rw [← character_flux_difference]
  have hl : (inner ℂ (characterProjection N (lowerBlock N) (-r) (sourceVector N f z))
      (sourceDerivative N f (z : ℂ) z)).re = -radialFlux N f r (S⁻¹ • z) := by
    rw [source_lower_character,neg_neg,hd]
    simp only [inner_neg_right,LinearIsometryEquiv.inner_map_map,Complex.neg_re,radialFlux]
  rw [hl,sub_neg_eq_add]
  rfl

/-- Squared paired flux is bounded by actual transfer loss and physical radial energy. -/
theorem radialFlux_seam_sq_le_loss (r : ZMod (N+1)) (z : ℍ) :
    (radialFlux N f r z + radialFlux N f r (S⁻¹ • z))^2 ≤
      (‖sourceVector N f z‖^2-‖inversionTransfer N r r (sourceVector N f z)‖^2)*
        ‖sourceDerivative N f (z : ℂ) z‖^2 := by
  rw [radialFlux_seam_identity,← character_flux_difference]
  exact character_flux_sq_le_transfer_loss N r r _ _

/-- Quantitative paired flux bound in the original planar gradient density. -/
theorem radialFlux_seam_sq_le_gradient (r : ZMod (N+1)) (z : ℍ) :
    (radialFlux N f r z + radialFlux N f r (S⁻¹ • z))^2 ≤
      (‖sourceVector N f z‖^2-‖inversionTransfer N r r (sourceVector N f z)‖^2)*
        (normSq (z : ℂ)*gradientDensity N f (z : ℂ)) :=
  (radialFlux_seam_sq_le_loss N f r z).trans
    (mul_le_mul_of_nonneg_left (sourceDerivative_sq_le_gradient N f (z : ℂ) z)
      (transfer_loss_nonneg N r r _))

/-- The complete derivative vector is the original source chart's Fréchet derivative. -/
theorem sourceDerivative_eq_dir (v : ℂ) (z : ℍ) :
    sourceDerivative N f v z = dir v (fun w => sourceVector N f (ofComplex w)) (z : ℂ) := by
  have hf := (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hd := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  ext q
  have hp := ((EuclideanSpace.proj q).restrictScalars ℝ).hasFDerivAt.comp (z : ℂ) hd.hasFDerivAt
  have h := congrArg (fun L => L v) hp.fderiv
  change dir v (field N f q) (z : ℂ) =
    (dir v (fun w => sourceVector N f (ofComplex w)) (z : ℂ)) q at h
  exact h

/-- The character current is the literal derivative of its original projected mass. -/
theorem character_mass_dir
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1)) (v : ℂ) (z : ℍ) :
    dir v (fun w => ‖characterProjection N p r (sourceVector N f (ofComplex w))‖^2) (z : ℂ) =
      2*(inner ℂ (characterProjection N p r (sourceVector N f z)) (sourceDerivative N f v z)).re := by
  have hf := (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hd := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hp := ((characterProjection N p r).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp
    (z : ℂ) hd.hasFDerivAt
  have hn := hp.norm_sq
  have h := congrArg (fun L => L v) hn.fderiv
  simp only [smul_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,nsmul_eq_mul] at h
  change dir v (fun w => ‖characterProjection N p r (sourceVector N f (ofComplex w))‖^2) (z : ℂ) =
    2*(inner ℝ (characterProjection N p r (sourceVector N f (ofComplex (z : ℂ)) ))
      (characterProjection N p r (dir v (fun w => sourceVector N f (ofComplex w)) (z : ℂ)))) at h
  rw [ofComplex_apply,← sourceDerivative_eq_dir] at h
  rw [h]
  congr 1
  rw [characterProjection_inner_left]
  simp only [PiLp.inner_apply,Complex.re_sum]
  rfl

/-- The seam estimate retains the entire positive angular-energy remainder. -/
theorem radialFlux_seam_angular_remainder (r : ZMod (N+1)) (z : ℍ) :
    (radialFlux N f r z + radialFlux N f r (S⁻¹ • z))^2 +
      (‖sourceVector N f z‖^2-‖inversionTransfer N r r (sourceVector N f z)‖^2)*
        ‖sourceDerivative N f (Complex.I*(z : ℂ)) z‖^2 ≤
      (‖sourceVector N f z‖^2-‖inversionTransfer N r r (sourceVector N f z)‖^2)*
        (normSq (z : ℂ)*gradientDensity N f (z : ℂ)) := by
  rw [← sourceDerivative_polar_energy N f (z : ℂ) z,mul_add]
  exact add_le_add (radialFlux_seam_sq_le_loss N f r z) le_rfl

/-- On the actual circle, the inverse inversion point is its reflected horizontal point. -/
theorem inverse_inversion_on_unit_circle {x y : ℝ} (hy : 0 < y) (hxy : x^2+y^2=1) :
    S⁻¹ • ofComplex (point x y) = ofComplex (point (-x) y) := by
  have h := SelbergMaassTraceBoundary.inversion_on_unit_circle hy (x := -x) (by simpa using hxy)
  simpa using (congrArg (fun z : ℍ => S⁻¹ • z) h).symm

/-- The literal circle flux is controlled by the complete arithmetic phase displacement. -/
theorem unit_circle_flux_sq_le_phase_gradient (r : ZMod (N+1))
    {x y : ℝ} (hy : 0 < y) (hxy : x^2+y^2=1) :
    (radialFlux N f r (ofComplex (point x y))+
      radialFlux N f r (ofComplex (point (-x) y)))^2 ≤
      (((((N+1 : ℕ) : ℝ)⁻¹)^3/2)*
        (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
          ‖sourceVector N f (ofComplex (point x y))-
            tripleMotion N r r a b c (sourceVector N f (ofComplex (point x y)))‖^2))*
        gradientDensity N f (point x y) := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  have hs : normSq (point x y)=1 := by simpa only [point,Complex.normSq_add_mul_I] using hxy
  have h := radialFlux_seam_sq_le_gradient N f r (ofComplex (point x y))
  rw [inverse_inversion_on_unit_circle hy hxy,ofComplex_apply_of_im_pos hp,hs,one_mul] at h
  rw [triple_displacement_energy]
  simpa only [ofComplex_apply_of_im_pos hp] using h

/-- Original character-mass current in the circular boundary's outward normal density.
On the unit circle the tangent is `(-x/y,-1)`, including the arc-length Jacobian. -/
def circleNormalCurrent (r : ZMod (N+1)) (x y : ℝ) : ℝ :=
  dir ((-y⁻¹) • point x y)
    (fun w => ‖characterProjection N (upperBlock N) r (sourceVector N f (ofComplex w))‖^2)
    (point x y)

/-- The actual outward normal density has its exact radial-flux and height factor. -/
theorem circleNormalCurrent_eq_radialFlux (r : ZMod (N+1)) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    circleNormalCurrent N f r x y = -2*y⁻¹*radialFlux N f r (ofComplex (point x y)) := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  have hz : ((ofComplex (point x y) : ℍ) : ℂ)=point x y := by
    simp only [ofComplex_apply_of_im_pos hp]
  have h := character_mass_dir N f (upperBlock N) r (point x y) (ofComplex (point x y))
  rw [hz] at h
  unfold circleNormalCurrent
  simp only [dir,map_smul]
  change (-y⁻¹) • dir (point x y)
    (fun w => ‖characterProjection N (upperBlock N) r (sourceVector N f (ofComplex w))‖^2)
      (point x y) = _
  rw [h,smul_eq_mul,radialFlux,hz]
  ring

/-- Literal paired outward normal current is controlled by inversion loss and physical gradient. -/
theorem unit_circle_normal_current_sq_le_loss_gradient (r : ZMod (N+1))
    {x y : ℝ} (hy : 0 < y) (hxy : x^2+y^2=1) :
    (circleNormalCurrent N f r x y+circleNormalCurrent N f r (-x) y)^2 ≤
      (4/y^2)*
        ((‖sourceVector N f (ofComplex (point x y))‖^2-
          ‖inversionTransfer N r r (sourceVector N f (ofComplex (point x y)))‖^2)*
          gradientDensity N f (point x y)) := by
  have h := unit_circle_flux_sq_le_phase_gradient N f r hy hxy
  rw [triple_displacement_energy] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 4/y^2 by positivity)
  rw [circleNormalCurrent_eq_radialFlux N f r x hy,circleNormalCurrent_eq_radialFlux N f r (-x) hy]
  have he (a b : ℝ) : (-2*y⁻¹*a + -2*y⁻¹*b)^2 = (4/y^2)*(a+b)^2 := by
    rw [div_eq_mul_inv,← inv_pow]
    ring
  rw [he]
  exact hm

/-- On the actual modular core arc, the full outward normal density has a level-independent bound. -/
theorem modular_arc_normal_current_sq_le (r : ZMod (N+1))
    (x : Set.Icc (-(1/2 : ℝ)) (1/2)) :
    (circleNormalCurrent N f r x (SelbergMaassTraceStokes.arcHeight x)+
      circleNormalCurrent N f r (-x) (SelbergMaassTraceStokes.arcHeight x))^2 ≤
      (16/3 : ℝ)*
        ((‖sourceVector N f (ofComplex (point x (SelbergMaassTraceStokes.arcHeight x)))‖^2-
          ‖inversionTransfer N r r (sourceVector N f (ofComplex (point x (SelbergMaassTraceStokes.arcHeight x))))‖^2)*
          gradientDensity N f (point x (SelbergMaassTraceStokes.arcHeight x))) := by
  have hy := SelbergMaassTraceStokes.arcHeight_pos x.property
  have hys := SelbergMaassTraceStokes.arcHeight_sq x.property
  have hx : (x : ℝ)^2 ≤ 1/4 := by
    nlinarith [x.property.1,x.property.2,sq_nonneg ((x : ℝ)+1/2),sq_nonneg (1/2-(x : ℝ))]
  have hb : 4/SelbergMaassTraceStokes.arcHeight (x : ℝ)^2 ≤ (16/3 : ℝ) :=
    (div_le_iff₀ (show 0 < SelbergMaassTraceStokes.arcHeight (x : ℝ)^2 by positivity)).mpr (by nlinarith)
  exact (unit_circle_normal_current_sq_le_loss_gradient N f r hy (by linarith)).trans
    (mul_le_mul_of_nonneg_right hb (mul_nonneg (transfer_loss_nonneg N r r _)
      (gradientDensity_nonneg N f _)))

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterSeamFlux
