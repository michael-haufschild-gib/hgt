import GaloisForLFunctions.RHTower.SelbergMaassProjectionFlux
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.SelbergMaassPhaseRellich
import GaloisForLFunctions.RHTower.SelbergMaassCharacterCuspGlue

/-!
# Both original transfer losses control the coherent Maass seam

Two exact projection-square identities bound the original character mismatch by
its transfer-loss quadratic form with the golden-ratio constant. Real polarization
and the nonnegative-quadratic lemma give the mixed bound, including every nullspace
case. Physical source specialization and the full modular normal-density factor
then give an integrated seam estimate in actual weighted phase mass and radial
phase energy. The complete original phase Rellich and core–cusp identities retain
all angular energy, spectral mass, and physical side/top stress contributions.
-/

open Complex
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassMixedLoss
open SelbergMaassCongruenceTrace SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionPhaseEnergy
open SelbergMaassProjectionFlux
open GaloisForLFunctions.HTGeometry
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)
variable (N : ℕ) (r s : ZMod (N+1))
local notation "P" => characterProjection N (upperBlock N) s
local notation "Q" => characterProjection N (lowerBlock N) (-r)

/-- Actual inversion-transfer loss on the complete original deck representation. -/
def lossEnergy (v : EuclideanSpace ℂ (Deck N)) : ℝ :=
  ‖v‖^2-‖inversionTransfer N r s v‖^2

/-- Coherent real pairing of the original upper/lower character mismatch. -/
def mismatchPair (v w : EuclideanSpace ℂ (Deck N)) : ℝ := (inner ℂ (P v-Q v) w).re

private theorem self_re (v : EuclideanSpace ℂ (Deck N)) :
    (inner ℂ v v).re=‖v‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) v

private theorem re_symm (v w : EuclideanSpace ℂ (Deck N)) :
    (inner ℂ v w).re=(inner ℂ w v).re := inner_re_symm (𝕜 := ℂ) v w

/-- Actual character mismatch has its exact projected-norm diagonal. -/
theorem mismatchPair_diagonal (v : EuclideanSpace ℂ (Deck N)) :
    mismatchPair N r s v v=‖P v‖^2-‖Q v‖^2 := by
  rw [mismatchPair,inner_sub_left,Complex.sub_re,
    characterProjection_inner_left N (upperBlock N) s v v,
    characterProjection_inner_left N (lowerBlock N) (-r) v v,
    self_re,self_re]

/-- Loss and coherent mismatch add to two complete physical projection squares. -/
theorem loss_plus_mismatch_squares (v : EuclideanSpace ℂ (Deck N)) :
    lossEnergy N r s v+mismatchPair N r s v v = ‖v-Q v‖^2+‖P v-Q (P v)‖^2 := by
  rw [lossEnergy,mismatchPair_diagonal,characterProjection_loss,characterProjection_loss,
    lowerProjection_transfer_norm]
  ring

private theorem mismatch_diagonal_corners (v : EuclideanSpace ℂ (Deck N)) :
    mismatchPair N r s v v = ‖P v-Q (P v)‖^2+
      2*(inner ℂ (P v-Q (P v)) (v-P v)).re-‖Q (v-P v)‖^2 := by
  let a := v-P v
  have hv : Q v=Q (P v)+Q a := by simp only [a,map_sub]; module
  have ho : (inner ℂ (P v) a).re=0 := by
    rw [re_symm]
    exact congrArg Complex.re (character_complement_orthogonal N (upperBlock N) s v v)
  have hb : (inner ℂ (P v-Q (P v)) a).re= -(inner ℂ (Q (P v)) (Q a)).re := by
    rw [inner_sub_left,Complex.sub_re,ho,
      characterProjection_inner_left N (lowerBlock N) (-r) (P v) a]
    ring
  have hn : ‖Q v‖^2=‖Q (P v)‖^2+2*(inner ℂ (Q (P v)) (Q a)).re+‖Q a‖^2 := by
    rw [hv]
    exact norm_add_sq (𝕜 := ℂ) _ _
  rw [mismatchPair_diagonal,characterProjection_loss]
  change ‖P v‖^2-‖Q v‖^2 = ‖P v‖^2-‖Q (P v)‖^2+
    2*(inner ℂ (P v-Q (P v)) a).re-‖Q a‖^2
  linarith

/-- Exact golden-ratio square completion for the original coherent mismatch and transfer loss. -/
theorem golden_loss_minus_mismatch_squares (v : EuclideanSpace ℂ (Deck N)) :
    Real.goldenRatio*lossEnergy N r s v-mismatchPair N r s v v =
      (Real.goldenRatio-1)*‖Real.goldenRatio • (v-P v)-(P v-Q (P v))‖^2+‖Q (v-P v)‖^2 := by
  have hn (a b : EuclideanSpace ℂ (Deck N)) :
      ‖Real.goldenRatio • a-b‖^2=Real.goldenRatio^2*‖a‖^2-
        2*Real.goldenRatio*(inner ℂ a b).re+‖b‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    change Real.goldenRatio^2*‖a‖^2-2*(inner ℂ (Real.goldenRatio • a) b).re+‖b‖^2 = _
    rw [inner_smul_left_eq_smul,Complex.smul_re,smul_eq_mul]
    ring
  rw [lossEnergy,transfer_loss_decomposition,mismatch_diagonal_corners,hn,
    re_symm N (P v-Q (P v)) (v-P v)]
  linear_combination
    (-Real.goldenRatio*‖v-P v‖^2+2*(inner ℂ (v-P v) (P v-Q (P v))).re)*Real.goldenRatio_sq

/-- Original transfer loss is nonnegative, including its entire nullspace. -/
theorem lossEnergy_nonneg (v : EuclideanSpace ℂ (Deck N)) : 0 ≤ lossEnergy N r s v :=
  transfer_loss_nonneg N r s v

/-- The exact positive forms bound the actual mismatch diagonal in absolute value. -/
theorem mismatchPair_diagonal_abs_le (v : EuclideanSpace ℂ (Deck N)) :
    |mismatchPair N r s v v| ≤ Real.goldenRatio*lossEnergy N r s v := by
  have hl := loss_plus_mismatch_squares N r s v
  have hu := golden_loss_minus_mismatch_squares N r s v
  have hphi : 0 ≤ Real.goldenRatio-1 := by linarith [Real.one_lt_goldenRatio]
  have hp := mul_nonneg hphi (sq_nonneg ‖Real.goldenRatio • (v-P v)-(P v-Q (P v))‖)
  have hA := mul_nonneg hphi (lossEnergy_nonneg N r s v)
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg ‖v-Q v‖,sq_nonneg ‖P v-Q (P v)‖]
  · nlinarith [sq_nonneg ‖Q (v-P v)‖]

/-- The actual coherent character mismatch is symmetric as a real bilinear pairing. -/
theorem mismatchPair_symm (v w : EuclideanSpace ℂ (Deck N)) :
    mismatchPair N r s v w=mismatchPair N r s w v := by
  simp only [mismatchPair,inner_sub_left,Complex.sub_re]
  rw [characterProjection_self_adjoint N (upperBlock N) s v w,
    characterProjection_self_adjoint N (lowerBlock N) (-r) v w,
    re_symm N v (P w),re_symm N v (Q w)]

private theorem norm_pair_difference (v w : EuclideanSpace ℂ (Deck N)) :
    ‖v+w‖^2-‖v-w‖^2=4*(inner ℂ v w).re := by
  have ha : ‖v+w‖^2=‖v‖^2+2*(inner ℂ v w).re+‖w‖^2 := norm_add_sq (𝕜 := ℂ) v w
  have hs : ‖v-w‖^2=‖v‖^2-2*(inner ℂ v w).re+‖w‖^2 := norm_sub_sq (𝕜 := ℂ) v w
  linarith

private theorem norm_pair_sum (v w : EuclideanSpace ℂ (Deck N)) :
    ‖v+w‖^2+‖v-w‖^2=2*‖v‖^2+2*‖w‖^2 := by
  have ha : ‖v+w‖^2=‖v‖^2+2*(inner ℂ v w).re+‖w‖^2 := norm_add_sq (𝕜 := ℂ) v w
  have hs : ‖v-w‖^2=‖v‖^2-2*(inner ℂ v w).re+‖w‖^2 := norm_sub_sq (𝕜 := ℂ) v w
  linarith

/-- Real polarization recovers the complete original mixed character pairing. -/
theorem mismatchPair_polarization (v w : EuclideanSpace ℂ (Deck N)) :
    mismatchPair N r s (v+w) (v+w)-mismatchPair N r s (v-w) (v-w)=
      4*mismatchPair N r s v w := by
  have hp := norm_pair_difference N (P v) (P w)
  have hq := norm_pair_difference N (Q v) (Q w)
  have hm : mismatchPair N r s v w=(inner ℂ (P v) (P w)).re-(inner ℂ (Q v) (Q w)).re := by
    rw [mismatchPair,inner_sub_left,Complex.sub_re,
      characterProjection_inner_left N (upperBlock N) s v w,
      characterProjection_inner_left N (lowerBlock N) (-r) v w]
  rw [mismatchPair_diagonal,mismatchPair_diagonal,hm]
  simp only [map_add,map_sub]
  linarith

/-- Original transfer loss retains the exact parallelogram law. -/
theorem lossEnergy_parallelogram (v w : EuclideanSpace ℂ (Deck N)) :
    lossEnergy N r s (v+w)+lossEnergy N r s (v-w)=
      2*lossEnergy N r s v+2*lossEnergy N r s w := by
  have h := norm_pair_sum N v w
  have hT := norm_pair_sum N (inversionTransfer N r s v) (inversionTransfer N r s w)
  simp only [lossEnergy,map_add,map_sub]
  linarith

private theorem mixed_sum_bound (v w : EuclideanSpace ℂ (Deck N)) :
    2*mismatchPair N r s v w ≤ Real.goldenRatio*(lossEnergy N r s v+lossEnergy N r s w) := by
  have hp := (abs_le.mp (mismatchPair_diagonal_abs_le N r s (v+w))).2
  have hm := (abs_le.mp (mismatchPair_diagonal_abs_le N r s (v-w))).1
  have hB := mismatchPair_polarization N r s v w
  have hA := congrArg (fun t : ℝ => Real.goldenRatio*t) (lossEnergy_parallelogram N r s v w)
  nlinarith

private theorem lossEnergy_real_smul (t : ℝ) (v : EuclideanSpace ℂ (Deck N)) :
    lossEnergy N r s ((t : ℂ) • v)=t^2*lossEnergy N r s v := by
  simp only [lossEnergy,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

private theorem mismatchPair_real_smul_right (t : ℝ) (v w : EuclideanSpace ℂ (Deck N)) :
    mismatchPair N r s v ((t : ℂ) • w)=t*mismatchPair N r s v w := by
  simp only [mismatchPair,inner_smul_right,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]

/-- Every real scaling gives the original coherent mismatch's exact transfer-loss Young bound. -/
theorem mismatchPair_young (t : ℝ) (v w : EuclideanSpace ℂ (Deck N)) :
    2*t*mismatchPair N r s v w ≤
      Real.goldenRatio*(lossEnergy N r s v+t^2*lossEnergy N r s w) := by
  have h := mixed_sum_bound N r s v ((t : ℂ) • w)
  rw [lossEnergy_real_smul,mismatchPair_real_smul_right] at h
  nlinarith

/-- Uniform coherent mismatch bound using the actual transfer loss in both arguments, with all zero-loss cases included. -/
theorem mismatchPair_sq_le_losses (v w : EuclideanSpace ℂ (Deck N)) :
    mismatchPair N r s v w^2 ≤
      Real.goldenRatio^2*lossEnergy N r s v*lossEnergy N r s w := by
  have hquad (t : ℝ) : 0 ≤ Real.goldenRatio*lossEnergy N r s v+
      2*(-mismatchPair N r s v w)*t+(Real.goldenRatio*lossEnergy N r s w)*t^2 := by
    have h := mixed_sum_bound N r s v ((t : ℂ) • w)
    rw [lossEnergy_real_smul,mismatchPair_real_smul_right] at h
    nlinarith
  have h := sq_le_mul_of_quadratic_nonneg
    (mul_nonneg Real.goldenRatio_pos.le (lossEnergy_nonneg N r s w)) hquad
  rw [neg_sq] at h
  nlinarith

open Set UpperHalfPlane ModularGroup MeasureTheory
open SelbergMaassCongruenceAverage SelbergMaassCuspTransport SelbergMaassCharacterSeamFlux
open SelbergMaassPhaseRellich SelbergMaassCharacterCoreGreen SelbergMaassCharacterCuspGlue
open SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices SelbergMaassTraceEnergy

variable {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Actual paired radial seam flux is controlled by original source and derivative transfer losses. -/
theorem radialFlux_seam_sq_le_two_losses (z : ℍ) :
    (radialFlux N f r z+radialFlux N f r (S⁻¹ • z))^2 ≤
      Real.goldenRatio^2*lossEnergy N r r (sourceVector N f z)*
        lossEnergy N r r (sourceDerivative N f (z : ℂ) z) := by
  rw [radialFlux_seam_identity]
  exact mismatchPair_sq_le_losses N r r _ _

/-- The literal physical arc current is exactly the original mixed character pairing with its full height factor. -/
theorem pairedArcCurrent_eq_mismatch {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    pairedArcCurrent N f r x = (-2/arcHeight x)*mismatchPair N r r
      (sourceVector N f (ofComplex (point x (arcHeight x))))
      (sourceDerivative N f (point x (arcHeight x)) (ofComplex (point x (arcHeight x)))) := by
  have hy := arcHeight_pos hx
  have hz : ((ofComplex (point x (arcHeight x)) : ℍ) : ℂ)=point x (arcHeight x) := by
    exact SelbergMaassUnipotentPaths.coe_ofComplex_point x hy
  have h := radialFlux_seam_identity N f r (ofComplex (point x (arcHeight x)))
  rw [inverse_inversion_on_unit_circle hy (by rw [arcHeight_sq hx]; ring),hz] at h
  change radialFlux N f r (ofComplex (point x (arcHeight x)))+
    radialFlux N f r (ofComplex (point (-x) (arcHeight x))) = _ at h
  rw [pairedArcCurrent,circleNormalCurrent_eq_radialFlux N f r x hy,
    circleNormalCurrent_eq_radialFlux N f r (-x) hy]
  change _=(-2/arcHeight x)*(inner ℂ
    (characterProjection N (upperBlock N) r (sourceVector N f (ofComplex (point x (arcHeight x))))-
      characterProjection N (lowerBlock N) (-r) (sourceVector N f (ofComplex (point x (arcHeight x)))))
    (sourceDerivative N f (point x (arcHeight x)) (ofComplex (point x (arcHeight x))))).re
  rw [← h]
  ring

private theorem radialDensity_loss {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    radialPhaseDensity N f r r x =
      lossEnergy N r r (sourceDerivative N f (point x (arcHeight x))
        (ofComplex (point x (arcHeight x))))/arcHeight x := by
  rw [sourceDerivative_eq_dir,SelbergMaassUnipotentPaths.coe_ofComplex_point x (arcHeight_pos hx)]
  rfl

/-- Every original radial phase-loss density is nonnegative, including source and derivative zeros. -/
theorem radialPhaseDensity_nonneg (x : ℝ) : 0 ≤ radialPhaseDensity N f r r x := by
  apply div_nonneg
  · exact lossEnergy_nonneg N r r _
  · exact Real.sqrt_nonneg _

/-- Every actual weighted source phase-loss density is nonnegative. -/
theorem massPhaseDensity_nonneg (x : ℝ) : 0 ≤ massPhaseDensity N f r r x := by
  apply div_nonneg
  · exact lossEnergy_nonneg N r r _
  · exact pow_nonneg (Real.sqrt_nonneg _) 3

/-- The actual source, current, and radial derivative satisfy a nonnegative quadratic with the exact physical arc weights. -/
theorem arc_phase_quadratic_weighted {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) (t : ℝ) :
    0 ≤ massPhaseDensity N f r r x+t*pairedArcCurrent N f r x+
      Real.goldenRatio^2*(arcHeight x)^2*radialPhaseDensity N f r r x*t^2 := by
  let y := arcHeight x
  let v := sourceVector N f (ofComplex (point x y))
  let w := sourceDerivative N f (point x y) (ofComplex (point x y))
  have hy : 0 < y := arcHeight_pos hx
  have h := mismatchPair_young N r r (Real.goldenRatio*y^2*t) v w
  have hn := div_nonneg (sub_nonneg.mpr h) (show 0 ≤ Real.goldenRatio*y^3 by positivity)
  have he : (Real.goldenRatio*(lossEnergy N r r v+(Real.goldenRatio*y^2*t)^2*lossEnergy N r r w)-
      2*(Real.goldenRatio*y^2*t)*mismatchPair N r r v w)/(Real.goldenRatio*y^3) =
      lossEnergy N r r v/y^3+t*((-2/y)*mismatchPair N r r v w)+
        Real.goldenRatio^2*y^2*(lossEnergy N r r w/y)*t^2 := by
    field_simp [hy.ne',Real.goldenRatio_ne_zero]
    ring
  rw [he] at hn
  rw [pairedArcCurrent_eq_mismatch N r f hx,radialDensity_loss N r f hx]
  exact hn

/-- The complete physical arc quadratic gives an unweighted radial phase-energy comparison. -/
theorem arc_phase_quadratic {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) (t : ℝ) :
    0 ≤ massPhaseDensity N f r r x+t*pairedArcCurrent N f r x+
      Real.goldenRatio^2*radialPhaseDensity N f r r x*t^2 := by
  have h := arc_phase_quadratic_weighted N r f hx t
  have hy : (arcHeight x)^2 ≤ 1 := by rw [arcHeight_sq hx]; nlinarith [sq_nonneg x]
  have hd := mul_nonneg (show 0 ≤ 1-(arcHeight x)^2 by linarith)
    (mul_nonneg (sq_nonneg Real.goldenRatio) (mul_nonneg (radialPhaseDensity_nonneg N r f x) (sq_nonneg t)))
  nlinarith

private theorem arc_chart_continuous : Continuous (fun x => point x (arcHeight x)) := by
  unfold point
  exact continuous_ofReal.add ((continuous_ofReal.comp continuous_arcHeight).mul continuous_const)

private theorem arc_chart_maps :
    MapsTo (fun x => point x (arcHeight x)) (Icc (-(1/2 : ℝ)) (1/2)) {z : ℂ | 0 < z.im} := by
  intro x hx
  simpa [point] using arcHeight_pos hx

/-- Original C² regularity makes radial derivative transfer loss continuous on the entire physical arc. -/
theorem radialPhaseDensity_continuousOn :
    ContinuousOn (radialPhaseDensity N f r r) (Icc (-(1/2 : ℝ)) (1/2)) := by
  have hd := (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hv := hd.clm_apply continuousOn_id
  have hc := hv.comp arc_chart_continuous.continuousOn arc_chart_maps
  have ht := (inversionTransfer N r r).continuous_of_finiteDimensional.comp_continuousOn hc
  unfold radialPhaseDensity
  exact ((hc.norm.pow 2).sub (ht.norm.pow 2)).div₀ continuous_arcHeight.continuousOn
    (fun x hx => (arcHeight_pos hx).ne')

/-- Literal weighted transfer-mass loss is continuous on the complete modular arc. -/
theorem massPhaseDensity_continuousOn :
    ContinuousOn (massPhaseDensity N f r r) (Icc (-(1/2 : ℝ)) (1/2)) := by
  have hc := (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f).continuousOn.comp
    arc_chart_continuous.continuousOn arc_chart_maps
  have ht := (inversionTransfer N r r).continuous_of_finiteDimensional.comp_continuousOn hc
  unfold massPhaseDensity
  exact ((hc.norm.pow 2).sub (ht.norm.pow 2)).div₀ (continuous_arcHeight.pow 3).continuousOn
    (fun x hx => pow_ne_zero 3 (arcHeight_pos hx).ne')

private theorem half_arc_inclusion : uIcc (0 : ℝ) (1/2) ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
  intro x hx
  have h : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
  exact ⟨by linarith [h.1],h.2⟩

private theorem pair_intervalIntegrable {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-(1/2 : ℝ)) (1/2))) :
    IntervalIntegrable (fun x => g x+g (-x)) volume 0 (1/2) := by
  have hr : ContinuousOn (fun x => g (-x)) (Icc (-(1/2 : ℝ)) (1/2)) :=
    hg.comp continuous_neg.continuousOn
      (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  exact ((hg.add hr).mono half_arc_inclusion).intervalIntegrable

/-- Original radial phase energy is nonnegative on the complete paired arc. -/
theorem radialPhaseBoundary_nonneg : 0 ≤ radialPhaseBoundary N f r r := by
  rw [radialPhaseBoundary_eq_loss_integral]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1/2)
    (fun x => add_nonneg (radialPhaseDensity_nonneg N r f x) (radialPhaseDensity_nonneg N r f (-x)))

/-- Exact reflection preserves the complete paired physical current. -/
theorem pairedArcCurrent_neg (x : ℝ) : pairedArcCurrent N f r (-x)=pairedArcCurrent N f r x := by
  simp only [pairedArcCurrent,arcHeight,neg_sq,neg_neg]
  exact add_comm _ _

/-- The complete original seam quadratic integrates with its actual phase mass and radial energy. -/
theorem integrated_phase_quadratic (t : ℝ) :
    0 ≤ massPhaseBoundary N f r r+2*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x)*t+
      (Real.goldenRatio^2*radialPhaseBoundary N f r r)*t^2 := by
  have hM := pair_intervalIntegrable (massPhaseDensity_continuousOn N r f)
  have hR := pair_intervalIntegrable (radialPhaseDensity_continuousOn N r f)
  have hJ : IntervalIntegrable (pairedArcCurrent N f r) volume 0 (1/2) :=
    ((pairedArcCurrent_continuousOn N f r).mono half_arc_inclusion).intervalIntegrable
  have hn := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1/2)
    (f := fun x => (massPhaseDensity N f r r x+massPhaseDensity N f r r (-x))+
      (2*t)*pairedArcCurrent N f r x+(Real.goldenRatio^2*t^2)*
        (radialPhaseDensity N f r r x+radialPhaseDensity N f r r (-x))) (fun x hx => by
      have hp : x ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨by linarith [hx.1],hx.2⟩
      have hm : -x ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
      have h1 := arc_phase_quadratic N r f hp t
      have h2 := arc_phase_quadratic N r f hm t
      rw [pairedArcCurrent_neg] at h2
      nlinarith)
  rw [intervalIntegral.integral_add (hM.add (hJ.const_mul (2*t)))
      (hR.const_mul (Real.goldenRatio^2*t^2)),
    intervalIntegral.integral_add hM (hJ.const_mul (2*t)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← massPhaseBoundary_eq_loss_integral,← radialPhaseBoundary_eq_loss_integral] at hn
  nlinarith

/-- The squared physical seam response is controlled by original weighted phase mass and radial phase energy. -/
theorem half_pairedArc_sq_le_phase_mass_radial :
    ((1/2)*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x))^2 ≤
      (Real.goldenRatio^2/4)*massPhaseBoundary N f r r*radialPhaseBoundary N f r r := by
  have h := sq_le_mul_of_quadratic_nonneg
    (mul_nonneg (sq_nonneg Real.goldenRatio) (radialPhaseBoundary_nonneg N r f))
    (integrated_phase_quadratic N r f)
  nlinarith

/-- The coherent seam response retains the positive spectral phase mass after the exact original Rellich substitution. -/
theorem half_pairedArc_rellich_bound :
    ((1/2)*(∫ x in (0 : ℝ)..(1/2), pairedArcCurrent N f r x))^2+
      (Real.goldenRatio^2/4)*lam*(massPhaseBoundary N f r r)^2 ≤
      (Real.goldenRatio^2/4)*massPhaseBoundary N f r r*
        (angularPhaseBoundary N f r r+sidePhaseFlux N f r r 1+topPhaseFlux N f r r 1) := by
  have h := half_pairedArc_sq_le_phase_mass_radial N r f
  have he := congrArg (fun q : ℝ => (Real.goldenRatio^2/4)*massPhaseBoundary N f r r*q)
    (phase_rellich_identity N f r r (Y := 1) le_rfl)
  nlinarith

/-- The complete original core–cusp quarter balance has the phase-mass/Rellich estimate with every original term retained. -/
theorem core_cusp_phase_rellich_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) :
    (coreQuarter N f r 1+boundarySum N f r 0+squareSum N f r 0-
      ((lam : ℝ)-1/4)*(coreMass N f r 1+tailMass N f r 1))^2+
      (Real.goldenRatio^2/4)*(lam : ℝ)*(massPhaseBoundary N f r r)^2 ≤
      (Real.goldenRatio^2/4)*massPhaseBoundary N f r r*
        (angularPhaseBoundary N f r r+sidePhaseFlux N f r r 1+topPhaseFlux N f r r 1) := by
  rw [core_cusp_quarter_identity_one,add_sub_cancel_right]
  exact half_pairedArc_rellich_bound N r f

end
end GaloisForLFunctions.RHTower.SelbergMaassMixedLoss
