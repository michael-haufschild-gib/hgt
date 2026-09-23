import GaloisForLFunctions.RHTower.SelbergMaassMixedLoss

/-!
# Complete original phase stress and physical side/top boundary flux

Polarization of the full arithmetic phase norm identity recovers the real mixed
Gram loss of the original inversion transfer. Its actual upper-character input
proves unit-translation invariance of all three physical stress components.
The entire dilation jump across the original vertical sides is consequently the
horizontal phase stress. Source regularity justifies every finite-sum/integral
exchange, giving exact side and top stress records in the original phase Rellich
identity and complete core–cusp bound. All mixed derivative terms are retained.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseStress
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassCuspTransport
open SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open SelbergMaassCharacterDynamics SelbergMaassCharacterSeamFlux SelbergMaassDilationStress
open SelbergMaassPhaseRellich SelbergMaassMixedLoss SelbergMaassTraceEnergy
open GaloisForLFunctions.HTGeometry
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)
variable (N : ℕ) (r s : ZMod (N+1))

/-- The full real mixed Gram loss of the original inversion transfer. -/
def lossPair (v w : EuclideanSpace ℂ (Deck N)) : ℝ :=
  (inner ℂ v w).re-(inner ℂ (inversionTransfer N r s v) (inversionTransfer N r s w)).re

private theorem self_re (v : EuclideanSpace ℂ (Deck N)) :
    (inner ℂ v v).re=‖v‖^(2 : ℕ) := inner_self_eq_norm_sq (𝕜 := ℂ) v

/-- The complete mixed Gram loss has the original transfer energy on its diagonal. -/
theorem lossPair_self (v : EuclideanSpace ℂ (Deck N)) : lossPair N r s v v=lossEnergy N r s v := by
  rw [lossPair,self_re,self_re]
  rfl

/-- Addition in the original source retains the full real mixed transfer loss. -/
theorem lossEnergy_add (v w : EuclideanSpace ℂ (Deck N)) :
    lossEnergy N r s (v+w)=lossEnergy N r s v+lossEnergy N r s w+2*lossPair N r s v w := by
  have hn (a b : EuclideanSpace ℂ (Deck N)) :
      ‖a+b‖^(2 : ℕ)=‖a‖^(2 : ℕ)+2*(inner ℂ a b).re+‖b‖^(2 : ℕ) := norm_add_sq (𝕜 := ℂ) a b
  simp only [lossEnergy,lossPair,map_add,hn]
  ring

private theorem average_add (N : ℕ) (A B : PhaseIndex N → ℝ) :
    phaseAverage N (fun i => A i+B i)=phaseAverage N A+phaseAverage N B := by
  simp only [phaseAverage,Finset.sum_add_distrib,mul_add]

private theorem average_sub (N : ℕ) (A B : PhaseIndex N → ℝ) :
    phaseAverage N (fun i => A i-B i)=phaseAverage N A-phaseAverage N B := by
  simp only [phaseAverage,Finset.sum_sub_distrib,mul_sub]

private theorem average_mul (N : ℕ) (c : ℝ) (A : PhaseIndex N → ℝ) :
    phaseAverage N (fun i => c*A i)=c*phaseAverage N A := by
  simp only [phaseAverage,← Finset.mul_sum]
  ring

/-- Full phase averaging recovers the original mixed derivative Gram loss, not only diagonal energies. -/
theorem phaseAverage_pair (v w : EuclideanSpace ℂ (Deck N)) :
    phaseAverage N (fun i => (phaseReadout N r s i v*(starRingEnd ℂ) (phaseReadout N r s i w)).re)=
      lossPair N r s v w := by
  have hv : phaseAverage N (fun i => normSq (phaseReadout N r s i v))=lossEnergy N r s v :=
    phaseAverage_norm N r s v
  have hw : phaseAverage N (fun i => normSq (phaseReadout N r s i w))=lossEnergy N r s w :=
    phaseAverage_norm N r s w
  have h : phaseAverage N (fun i => normSq (phaseReadout N r s i (v+w)))=lossEnergy N r s (v+w) :=
    phaseAverage_norm N r s (v+w)
  simp_rw [map_add,Complex.normSq_add] at h
  rw [average_add,average_add,average_mul,hv,hw,lossEnergy_add] at h
  linarith

/-- The original transfer transforms by its exact input character under every upper-block motion. -/
theorem inversionTransfer_upper_motion (j : Multiplicative (ZMod (N+1)))
    (v : EuclideanSpace ℂ (Deck N)) :
    inversionTransfer N r s (finiteRegularUnitary (upperBlock N j) v)=
      residueCharacter N s j • inversionTransfer N r s v := by
  unfold inversionTransfer
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [characterProjection_commute_block,characterProjection_intertwine]
  simp only [map_smul]

/-- The full mixed Gram loss is invariant under the actual upper-block unitary. -/
theorem lossPair_upper_motion (j : Multiplicative (ZMod (N+1)))
    (v w : EuclideanSpace ℂ (Deck N)) :
    lossPair N r s (finiteRegularUnitary (upperBlock N j) v) (finiteRegularUnitary (upperBlock N j) w)=
      lossPair N r s v w := by
  unfold lossPair
  rw [LinearIsometryEquiv.inner_map_map,inversionTransfer_upper_motion,inversionTransfer_upper_motion,
    inner_smul_left,inner_smul_right,← mul_assoc,residueCharacter_unit,one_mul]

/-- Every original transfer-loss energy retains complete upper-block motion invariance. -/
theorem lossEnergy_upper_motion (j : Multiplicative (ZMod (N+1)))
    (v : EuclideanSpace ℂ (Deck N)) :
    lossEnergy N r s (finiteRegularUnitary (upperBlock N j) v)=lossEnergy N r s v := by
  rw [← lossPair_self,lossPair_upper_motion,lossPair_self]

variable {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Complete horizontal phase stress of every original arithmetic displacement. -/
def phaseStressXX (w : ℂ) : ℝ := phaseAverage N (fun i => stressXX N f (phaseReadout N r s i) w)
/-- Complete mixed horizontal/vertical phase stress, retaining all interference terms. -/
def phaseStressXY (w : ℂ) : ℝ := phaseAverage N (fun i => stressXY N f (phaseReadout N r s i) w)
/-- Complete vertical phase stress of all original arithmetic displacements. -/
def phaseStressYY (w : ℂ) : ℝ := phaseAverage N (fun i => stressYY N f (phaseReadout N r s i) w)

/-- The actual horizontal phase stress is physical derivative loss plus the original potential mass. -/
theorem phaseStressXX_eq (z : ℍ) :
    phaseStressXX N r s f (z : ℂ)=lossEnergy N r s (sourceDerivative N f 1 z)-
      lossEnergy N r s (sourceDerivative N f Complex.I z)+(lam/z.im^(2 : ℕ))*lossEnergy N r s (sourceVector N f z) := by
  unfold phaseStressXX stressXX potentialMass potential
  simp_rw [phaseReadout_dir]
  simp only [observedField,ofComplex_apply,UpperHalfPlane.coe_im]
  rw [average_add,average_sub,average_mul,phaseAverage_norm,phaseAverage_norm,phaseAverage_norm]
  rfl

/-- The actual mixed phase stress is the full original horizontal/vertical Gram loss. -/
theorem phaseStressXY_eq (z : ℍ) :
    phaseStressXY N r s f (z : ℂ)=2*lossPair N r s
      (sourceDerivative N f 1 z) (sourceDerivative N f Complex.I z) := by
  unfold phaseStressXY stressXY
  simp_rw [phaseReadout_dir]
  rw [average_mul,phaseAverage_pair]

/-- The actual vertical phase stress keeps the full signed derivative loss and original potential. -/
theorem phaseStressYY_eq (z : ℍ) :
    phaseStressYY N r s f (z : ℂ)=lossEnergy N r s (sourceDerivative N f Complex.I z)-
      lossEnergy N r s (sourceDerivative N f 1 z)+(lam/z.im^(2 : ℕ))*lossEnergy N r s (sourceVector N f z) := by
  unfold phaseStressYY stressYY potentialMass potential
  simp_rw [phaseReadout_dir]
  simp only [observedField,ofComplex_apply,UpperHalfPlane.coe_im]
  rw [average_add,average_sub,average_mul,phaseAverage_norm,phaseAverage_norm,phaseAverage_norm]
  rfl

open SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices SelbergMaassDilationRellich

private theorem sourceDerivative_translation (v : ℂ) (z : ℍ) :
    sourceDerivative N f v (T • z)=finiteRegularUnitary (QuotientGroup.mk T : Deck N) (sourceDerivative N f v z) := by
  have h := sourceDerivative_modular N f T z v
  simpa [denom,ModularGroup.T] using h

private theorem translation_im (z : ℍ) : (T • z).im=z.im := by
  rw [UpperHalfPlane.modular_T_smul,UpperHalfPlane.vadd_im]

/-- Original horizontal phase stress has exact unit-translation symmetry. -/
theorem phaseStressXX_translation (z : ℍ) :
    phaseStressXX N r s f ((T • z : ℍ) : ℂ)=phaseStressXX N r s f (z : ℂ) := by
  rw [phaseStressXX_eq,phaseStressXX_eq,sourceDerivative_translation,sourceDerivative_translation,
    sourceVector_pullback,translation_im,← upperBlock_one_eq_T,
    lossEnergy_upper_motion,lossEnergy_upper_motion,lossEnergy_upper_motion]

/-- Unit translation preserves the complete physical mixed phase stress. -/
theorem phaseStressXY_translation (z : ℍ) :
    phaseStressXY N r s f ((T • z : ℍ) : ℂ)=phaseStressXY N r s f (z : ℂ) := by
  rw [phaseStressXY_eq,phaseStressXY_eq,sourceDerivative_translation,sourceDerivative_translation,
    ← upperBlock_one_eq_T,lossPair_upper_motion]

/-- Original vertical phase stress retains its exact unit-translation law. -/
theorem phaseStressYY_translation (z : ℍ) :
    phaseStressYY N r s f ((T • z : ℍ) : ℂ)=phaseStressYY N r s f (z : ℂ) := by
  rw [phaseStressYY_eq,phaseStressYY_eq,sourceDerivative_translation,sourceDerivative_translation,
    sourceVector_pullback,translation_im,← upperBlock_one_eq_T,
    lossEnergy_upper_motion,lossEnergy_upper_motion,lossEnergy_upper_motion]

/-- The actual horizontal phase stresses match on the two physical vertical sides. -/
theorem phaseStressXX_sides {y : ℝ} (hy : 0 < y) :
    phaseStressXX N r s f (point (1/2) y)=phaseStressXX N r s f (point (-(1/2)) y) := by
  have h := phaseStressXX_translation N r s f (ofComplex (point (-(1/2)) y))
  rw [SelbergMaassTraceBoundary.translation_point _ hy] at h
  norm_num at h
  simpa only [SelbergMaassUnipotentPaths.coe_ofComplex_point _ hy] using h

/-- The full mixed stress matches across the original sides, including all phase interference. -/
theorem phaseStressXY_sides {y : ℝ} (hy : 0 < y) :
    phaseStressXY N r s f (point (1/2) y)=phaseStressXY N r s f (point (-(1/2)) y) := by
  have h := phaseStressXY_translation N r s f (ofComplex (point (-(1/2)) y))
  rw [SelbergMaassTraceBoundary.translation_point _ hy] at h
  norm_num at h
  simpa only [SelbergMaassUnipotentPaths.coe_ofComplex_point _ hy] using h

/-- Complete phase averaging retains the physical horizontal dilation contraction. -/
theorem phaseAverage_dilationX (w : ℂ) :
    phaseAverage N (fun i => dilationX N f (phaseReadout N r s i) w)=
      w.re*phaseStressXX N r s f w+w.im*phaseStressXY N r s f w := by
  unfold dilationX
  rw [average_add,average_mul,average_mul]
  rfl

/-- Complete phase averaging retains the physical vertical dilation contraction. -/
theorem phaseAverage_dilationY (w : ℂ) :
    phaseAverage N (fun i => dilationY N f (phaseReadout N r s i) w)=
      w.re*phaseStressXY N r s f w+w.im*phaseStressYY N r s f w := by
  unfold dilationY
  rw [average_add,average_mul,average_mul]
  rfl

/-- The actual dilation side jump is exactly horizontal phase stress; the mixed stress cancels by proved translation symmetry. -/
theorem phase_dilation_side_jump {y : ℝ} (hy : 0 < y) :
    phaseAverage N (fun i => dilationX N f (phaseReadout N r s i) (point (1/2) y)-
      dilationX N f (phaseReadout N r s i) (point (-(1/2)) y))=
        phaseStressXX N r s f (point (1/2) y) := by
  rw [average_sub,phaseAverage_dilationX,phaseAverage_dilationX,
    phaseStressXX_sides N r s f hy,phaseStressXY_sides N r s f hy]
  simp only [point,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,
    mul_one,sub_zero,add_zero,zero_add]
  ring

private theorem average_continuousOn (N : ℕ) (A : PhaseIndex N → ℂ → ℝ)
    (hA : ∀ i, ContinuousOn (A i) {w : ℂ | 0 < w.im}) :
    ContinuousOn (fun w => phaseAverage N (fun i => A i w)) {w : ℂ | 0 < w.im} := by
  unfold phaseAverage
  exact continuousOn_const.mul (continuousOn_finsetSum Finset.univ (fun i _ => hA i))

/-- Every component of the original horizontal phase stress has sufficient physical boundary regularity. -/
theorem phaseStressXX_continuousOn : ContinuousOn (phaseStressXX N r s f) {w : ℂ | 0 < w.im} :=
  average_continuousOn N _ (fun i => (stressXX_contDiffOn N f (phaseReadout N r s i)).continuousOn)

/-- The full mixed phase stress is continuous on the original physical half-plane. -/
theorem phaseStressXY_continuousOn : ContinuousOn (phaseStressXY N r s f) {w : ℂ | 0 < w.im} :=
  average_continuousOn N _ (fun i => (stressXY_contDiffOn N f (phaseReadout N r s i)).continuousOn)

/-- Original vertical phase stress retains physical boundary continuity. -/
theorem phaseStressYY_continuousOn : ContinuousOn (phaseStressYY N r s f) {w : ℂ | 0 < w.im} :=
  average_continuousOn N _ (fun i => (stressYY_contDiffOn N f (phaseReadout N r s i)).continuousOn)

private theorem height_positive {Y y : ℝ} (hY : 0 < Y) (hy : y ∈ uIcc arcFloor Y) : 0 < y :=
  lt_of_lt_of_le (lt_min arcFloor_pos hY) hy.1

private theorem vertical_continuousOn (H : ℂ → ℝ)
    (hH : ContinuousOn H {w : ℂ | 0 < w.im}) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ContinuousOn (fun y => H (point x y)) (uIcc arcFloor Y) := by
  have hc : Continuous (fun y => point x y) := by unfold point; fun_prop
  apply hH.comp hc.continuousOn
  intro y hy
  simpa [point] using height_positive hY hy

private theorem horizontal_continuous (H : ℂ → ℝ)
    (hH : ContinuousOn H {w : ℂ | 0 < w.im}) {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun x => H (point x Y)) := by
  apply hH.comp_continuous (show Continuous (fun x => point x Y) by unfold point; fun_prop)
  intro x
  simpa [point] using hY

private theorem average_integral (N : ℕ) (H : PhaseIndex N → ℝ → ℝ) (a b : ℝ)
    (hH : ∀ i, IntervalIntegrable (H i) volume a b) :
    phaseAverage N (fun i => ∫ y in a..b, H i y)=∫ y in a..b, phaseAverage N (fun i => H i y) := by
  unfold phaseAverage
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hH i),← intervalIntegral.integral_const_mul]

/-- Full original side phase flux equals the actual horizontal phase-stress integral, with every displacement retained. -/
theorem sidePhaseFlux_eq {Y : ℝ} (hY : 0 < Y) :
    sidePhaseFlux N f r s Y=∫ y in arcFloor..Y, phaseStressXX N r s f (point (1/2) y) := by
  have hi (i : PhaseIndex N) : IntervalIntegrable
      (fun y => dilationX N f (phaseReadout N r s i) (point (1/2) y)-
        dilationX N f (phaseReadout N r s i) (point (-(1/2)) y)) volume arcFloor Y :=
    ((vertical_continuousOn _ (dilationX_contDiffOn N f (phaseReadout N r s i)).continuousOn (1/2) hY).sub
      (vertical_continuousOn _ (dilationX_contDiffOn N f (phaseReadout N r s i)).continuousOn (-(1/2)) hY)).intervalIntegrable
  change phaseAverage N (fun i => ∫ y in arcFloor..Y,
    dilationX N f (phaseReadout N r s i) (point (1/2) y)-
      dilationX N f (phaseReadout N r s i) (point (-(1/2)) y)) = _
  rw [average_integral N _ _ _ hi]
  exact intervalIntegral.integral_congr (fun y hy => phase_dilation_side_jump N r s f (height_positive hY hy))

/-- The complete physical top phase flux retains both the mixed and vertical stress integrals. -/
theorem topPhaseFlux_eq {Y : ℝ} (hY : 0 < Y) :
    topPhaseFlux N f r s Y=∫ x in (-(1/2 : ℝ))..(1/2),
      x*phaseStressXY N r s f (point x Y)+Y*phaseStressYY N r s f (point x Y) := by
  have hi (i : PhaseIndex N) : IntervalIntegrable
      (fun x => dilationY N f (phaseReadout N r s i) (point x Y)) volume (-(1/2)) (1/2) :=
    (horizontal_continuous _ (dilationY_contDiffOn N f (phaseReadout N r s i)).continuousOn hY).intervalIntegrable _ _
  change phaseAverage N (fun i => ∫ x in (-(1/2 : ℝ))..(1/2),
    dilationY N f (phaseReadout N r s i) (point x Y)) = _
  rw [average_integral N _ _ _ hi]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [phaseAverage_dilationY]
  simp [point]

/-- The original phase Rellich identity now has a complete explicit physical side/top stress record. -/
theorem phase_rellich_boundary_record :
    radialPhaseBoundary N f r s+lam*massPhaseBoundary N f r s =
      angularPhaseBoundary N f r s+
        (∫ y in arcFloor..(1 : ℝ), phaseStressXX N r s f (point (1/2) y))+
        (∫ x in (-(1/2 : ℝ))..(1/2), x*phaseStressXY N r s f (point x 1)+phaseStressYY N r s f (point x 1)) := by
  have h := phase_rellich_identity N f r s (Y := 1) le_rfl
  rw [sidePhaseFlux_eq N r s f zero_lt_one,topPhaseFlux_eq N r s f zero_lt_one] at h
  simpa only [one_mul] using h

open SelbergMaassCharacterCoreGreen SelbergMaassCharacterCuspGlue

/-- The complete original quarter balance is controlled by the exact angular and physical phase-stress boundary record. -/
theorem core_cusp_phase_stress_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r : ZMod (N+1)) :
    (coreQuarter N f r 1+boundarySum N f r 0+squareSum N f r 0-
      ((lam : ℝ)-1/4)*(coreMass N f r 1+tailMass N f r 1))^(2 : ℕ)+
      (Real.goldenRatio^(2 : ℕ)/4)*(lam : ℝ)*(massPhaseBoundary N f r r)^(2 : ℕ) ≤
      (Real.goldenRatio^(2 : ℕ)/4)*massPhaseBoundary N f r r*
        (angularPhaseBoundary N f r r+
          (∫ y in arcFloor..(1 : ℝ), phaseStressXX N r r f (point (1/2) y))+
          (∫ x in (-(1/2 : ℝ))..(1/2), x*phaseStressXY N r r f (point x 1)+phaseStressYY N r r f (point x 1))) := by
  have h := core_cusp_phase_rellich_bound N lam f r
  rw [sidePhaseFlux_eq N r r f zero_lt_one,topPhaseFlux_eq N r r f zero_lt_one] at h
  simpa only [one_mul] using h

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseStress
