import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricSourceTransfers

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMOriginalCompleteTransfer
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalAngularCurrent
open D4BMOriginalOrbitCurrent D4BMOriginalReaderEquation D4BMOriginalCompactBoundary
open D4BMLeftModeRadialEquation
open D4BMOriginalMetricSourceTransfers D4BMOriginalCuspFlux D4BMOriginalMetricForcingMatch
open D4BMOriginalAngularReaderBounds D4BMOriginalAngularProducts D4BMOriginalReaderCuspBounds
noncomputable section
set_option autoImplicit false
private abbrev P := Fin 4 → ℝ

private def leftField (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4) : P → ℂ :=
  ![sourceScalar q br amp,modeScalar q w true,angularLap (sourceScalar q br amp),
    D4BMOriginalSourceContact.originalForcing q br amp] j
private def rightField (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4) : P → ℂ :=
  ![modeScalar q w true,sourceScalar q br amp,modeScalar q w true,modeScalar q w true] j

/-- The original four transfers before their horizontal integration. -/
def physicalTransfer (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4)
    (p R x Y : ℝ) : ℂ :=
  transfer (leftField q br amp w j) (rightField q br amp w j) 1 ![p,R,x,Y]

private theorem transfer_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (R Y : ℝ) (hr : 1<R) (hy : 0<Y) (j : Fin 4) (z : ℝ×ℝ) (hp : 0<z.1) :
    ContinuousAt (fun t : ℝ×ℝ => physicalTransfer q br amp w j t.1 R t.2 Y) z := by
  let F := fun t : ℝ×ℝ => (![t.1,R,t.2,Y]:P)
  have hF : Continuous F := by dsimp [F];fun_prop
  have hU := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q br amp (F z) hp hr hy
  have hW := modeScalar_smooth q w hw true (F z) hr hy
  have hD {V : P→ℂ} (hV : ContDiffAt ℝ ∞ V (F z)) (i : Fin 4) :=
    coordDeriv_contDiffAt (m:=∞) hV (by simp) i
  have hLap : ContDiffAt ℝ ∞ (angularLap (sourceScalar q br amp)) (F z) := by
    have hY : ContDiffAt ℝ ∞ (fun t : P => (t 3:ℂ)) (F z) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))).contDiffAt
    exact (hY.pow 2).mul ((hD (hD hU 2) 2).add (hD (hD hU 3) 3))
  fin_cases j
  · exact ((hU.continuousAt.mul (hD hW 3).continuousAt).comp hF.continuousAt)
  · exact ((hW.continuousAt.mul (hD hU 3).continuousAt).comp hF.continuousAt)
  · exact ((hLap.continuousAt.mul (hD hW 3).continuousAt).comp hF.continuousAt)
  · have hSq := (fullSquarePotential_smooth q ![z.2,Y] hy 0).continuousAt.comp (f:=fun t : ℝ×ℝ => (![t.2,Y]:Fin 2→ℝ))
      (show ContinuousAt (fun t : ℝ×ℝ => (![t.2,Y]:Fin 2→ℝ)) z by fun_prop)
    have hGr := (fullGradientEnergy_smooth q ![z.2,Y] hy).continuousAt.comp (f:=fun t : ℝ×ℝ => (![t.2,Y]:Fin 2→ℝ))
      (show ContinuousAt (fun t : ℝ×ℝ => (![t.2,Y]:Fin 2→ℝ)) z by fun_prop)
    have hO := (timeOnset_hasDerivAt (2*physicalRate q br) z.1).continuousAt.comp
      (show ContinuousAt (fun t : ℝ×ℝ => t.1) z by fun_prop)
    have hForcing : ContinuousAt (fun t : ℝ×ℝ =>
        D4BMOriginalSourceContact.originalForcing q br amp (F t)) z := by
      unfold D4BMOriginalSourceContact.originalForcing timeOriginalForcing
      dsimp only [F,Matrix.cons_val]
      simp only [sub_add_cancel]
      unfold D4BMJointSource.originalForcing
      exact (continuousAt_const.mul ((continuousAt_const.mul hSq).add
        (continuousAt_const.mul ((continuousAt_const.mul hSq).sub (hGr.div_const 2))))).mul hO
    exact hForcing.mul ((hD hW 3).continuousAt.comp hF.continuousAt)

private theorem coefficient_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (R : ℝ) (j : Fin 4) (i : Fin 3) :
    Continuous (fun p => modeTransferCoefficient q q br true amp w j p R i) := by
  let s := physicalRate q br
  have hO : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun p => (timeOnset_hasDerivAt (2*s) p).continuousAt)
  have hL : Continuous (radialLift s 0 amp 1) := continuous_iff_continuousAt.mpr
    (fun x => (radialLift_hasDerivAt s 0 amp 1 x).continuousAt)
  have hD := (D4BMNativeResponse.radialResponse_continuous (-principalExponent q i) s amp).comp
    (show Continuous (fun p : ℝ => ((p+(p-2*D4BMIngoingCoordinates.tortoise R))/2,
      (p-(p-2*D4BMIngoingCoordinates.tortoise R))/2)) by fun_prop)
  have hN := (hL.comp (show Continuous (fun p : ℝ =>
    (p-(p-2*D4BMIngoingCoordinates.tortoise R))/2) by fun_prop)).mul hO
  have hA : Continuous (fun p => D4BMOriginalOrbitCusp.principalCoefficient q br amp p R i) :=
    ((hD.const_mul (principalAmplitude q i)).add (hN.mul_const (principalAmplitude q i))).const_mul (R:ℂ)
  have hB : Continuous (fun p => modeAmplitude q w true ![p,R]*readerCoefficient q) := by
    dsimp [modeAmplitude];fun_prop
  have hF : Continuous (fun p => forcingPrincipalCoefficient q br amp p R i) :=
    ((hO.const_mul _ |>.mul_const _).add (((hO.const_mul _ |>.mul_const _).mul_const _).mul_const _)).mul_const _
  fin_cases j
  · exact hA.mul (hB.mul_const _)
  · exact (hA.mul_const _).mul hB
  · exact ((hA.mul_const _).mul_const _).mul (hB.mul_const _)
  · exact hF.mul (hB.mul_const _)

/-- The boundary functional is exactly the finite-time original metric identity,
including both source endpoints and the fourth forcing moment. -/
def boundaryCombination (mu w R : ℂ) (a b : ℝ) (F : Fin 4→ℝ→ℂ) : ℂ :=
  (-(mu-2)*(F 0 b-F 0 a)+w*(mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-
    2*(mu-2)*(∫ p in a..b,F 0 p)-R^3/(R^2-1)*(∫ p in a..b,F 3 p)))/(R^2*(R^2-1))

private theorem top_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) (j : Fin 4) :
    IntervalIntegrable (fun p => ∫ x in (-1/2:ℝ)..1/2,physicalTransfer q br amp w j p R x Y) volume a b := by
  have hc : ContinuousOn (fun z : ℝ×ℝ => physicalTransfer q br amp w j z.1 R z.2 Y)
      (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) :=
    fun z hz => (transfer_continuous q br amp w hw R Y hr hy j z (ha.trans_le hz.1.1)).continuousWithinAt
  have hi : Integrable (fun z : ℝ×ℝ => physicalTransfer q br amp w j z.1 R z.2 Y)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

/-- Exact attachment to the existing complete metric top flux. -/
theorem complete_metric_boundary_combination (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    (∫ p in a..b,
      (D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 0 p R Y-
        D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 1 p R Y/((R:ℂ)^2-1))/(R:ℂ)^2)=
      boundaryCombination (eigenvalue q) w R a b
        (fun j p => ∫ x in (-1/2:ℝ)..1/2,physicalTransfer q br amp w j p R x Y) := by
  have h0 := top_integrable q br amp w hw a b R Y ha hab hr hy 0
  have h1 := top_integrable q br amp w hw a b R Y ha hab hr hy 1
  have h2 := top_integrable q br amp w hw a b R Y ha hab hr hy 2
  have h3 := top_integrable q br amp w hw a b R Y ha hab hr hy 3
  have ht := D4BMOriginalModularOrbit.mode_complete_boundary_time_transfer
    q q br true amp w hw a b R Y ha hab hr hy
  simp only [D4BMOriginalModularOrbit.topFlux,D4BMOriginalOrbitCurrent.slice,
    GaloisForLFunctions.RHTower.SelbergMaassMean.point,← neg_div,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,sub_zero] at ht
  change _=boundaryCombination (eigenvalue q) w R a b _
  rw [ht]
  unfold boundaryCombination
  simp only [physicalTransfer,leftField,rightField,Matrix.cons_val] at h0 h1 h2 h3 ⊢
  rw [intervalIntegral.integral_sub (((h1.const_mul _).sub h2).sub (h0.const_mul _)) (h3.const_mul _),
    intervalIntegral.integral_sub ((h1.const_mul _).sub h2) (h0.const_mul _),
    intervalIntegral.integral_sub (h1.const_mul _) h2]
  simp only [intervalIntegral.integral_const_mul]

private theorem horizontal_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (j : Fin 4) (p L k : ℝ) (hp : 0<p) (hL : 0<L) :
    (∫ x in (-1/2:ℝ)..1/2,transferCut q br amp w j p L x k)=
      (∫ x in (-1/2:ℝ)..1/2,physicalTransfer q br amp w j p (tortoiseRadius (-L/2)) x (Real.exp k))-
        ∑ i : Fin 3,modeTransferCoefficient q q br true amp w j p (tortoiseRadius (-L/2)) i*
          Complex.exp (fluxExponent q q i*(k:ℂ)) := by
  have hR := tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0)
  have hc : Continuous (fun x : ℝ => physicalTransfer q br amp w j p (tortoiseRadius (-L/2)) x (Real.exp k)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (transfer_continuous q br amp w hw _ _ hR (Real.exp_pos k) j (p,x) hp).comp
      (show ContinuousAt (fun u : ℝ => (p,u)) x by fun_prop)
  change (∫ x in (-1/2:ℝ)..1/2,physicalTransfer q br amp w j p (tortoiseRadius (-L/2)) x (Real.exp k)-_)=_
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const]
  norm_num [smul_eq_mul]

private theorem time_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (j : Fin 4) (a b L k : ℝ) (ha : 0<a) (hab : a≤b) (hL : 0<L) :
    (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,transferCut q br amp w j p L x k)=
      (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,
        physicalTransfer q br amp w j p (tortoiseRadius (-L/2)) x (Real.exp k))-
      ∑ i : Fin 3,(∫ p in a..b,modeTransferCoefficient q q br true amp w j p (tortoiseRadius (-L/2)) i)*
        Complex.exp (fluxExponent q q i*(k:ℂ)) := by
  have hR := tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0)
  have hi := top_integrable q br amp w hw a b _ _ ha hab hR (Real.exp_pos k) j
  have hci (i : Fin 3) : IntervalIntegrable (fun p => modeTransferCoefficient q q br true amp w j p (tortoiseRadius (-L/2)) i) volume a b :=
    (coefficient_continuous q br amp w (tortoiseRadius (-L/2)) j i).intervalIntegrable a b
  calc
    _ = ∫ p in a..b,(∫ x in (-1/2:ℝ)..1/2,
        physicalTransfer q br amp w j p (tortoiseRadius (-L/2)) x (Real.exp k))-
        ∑ i : Fin 3,modeTransferCoefficient q q br true amp w j p (tortoiseRadius (-L/2)) i*
          Complex.exp (fluxExponent q q i*(k:ℂ)) := by
      apply intervalIntegral.integral_congr
      intro p hp
      have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
      exact horizontal_cut q br amp w hw j p L k (ha.trans_le hp'.1) hL
    _ = _ := by
      have hsum : IntervalIntegrable (fun p => ∑ i : Fin 3,
          modeTransferCoefficient q q br true amp w j p (tortoiseRadius (-L/2)) i*
            Complex.exp (fluxExponent q q i*(k:ℂ))) volume a b := by
        apply Continuous.intervalIntegrable
        apply continuous_finsetSum
        intro i _
        exact (coefficient_continuous q br amp w (tortoiseRadius (-L/2)) j i).mul_const _
      rw [intervalIntegral.integral_sub hi hsum,
        intervalIntegral.integral_finsetSum (fun i _ => (hci i).mul_const _)]
      simp only [intervalIntegral.integral_mul_const]

/-- Complete original metric boundary minus its original three counterterms,
expressed in the actual four transfer cuts. No temporal endpoint is omitted. -/
theorem complete_metric_boundary_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (a b L k : ℝ) (ha : 0<a) (hab : a≤b) (hL : 0<L) :
    (∫ p in a..b,
      (D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 0 p (tortoiseRadius (-L/2)) (Real.exp k)-
        D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 1 p (tortoiseRadius (-L/2)) (Real.exp k)/
          ((tortoiseRadius (-L/2):ℂ)^2-1))/(tortoiseRadius (-L/2):ℂ)^2)-
      ∑ i : Fin 3,compactBoundaryCoefficient q q br true amp w a b (tortoiseRadius (-L/2)) i*
        Complex.exp (fluxExponent q q i*(k:ℂ))=
      boundaryCombination (eigenvalue q) w (tortoiseRadius (-L/2)) a b
        (fun j p => ∫ x in (-1/2:ℝ)..1/2,transferCut q br amp w j p L x k) := by
  rw [complete_metric_boundary_combination q br amp w hw a b _ _ ha hab
    (tortoiseRadius_exterior (-L/2) (by linarith)) (Real.exp_pos k)]
  unfold boundaryCombination
  dsimp only
  rw [horizontal_cut q br amp w hw 0 b L k (ha.trans_le hab) hL,
    horizontal_cut q br amp w hw 0 a L k ha hL]
  simp_rw [time_cut q br amp w hw _ a b L k ha hab hL]
  simp only [compactBoundaryCoefficient,Fin.sum_univ_three]
  ring

/-- Actual normalized source and forcing products in the complete boundary.
The logarithmic Laplacian retains both second derivatives and the first derivative. -/
def normalizedTransfer (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4)
    (p L x k : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*
    ![angularProduct q br amp w 0 true p L x k,
      Complex.exp (-(k:ℂ))*angularProduct q br amp w 1 false p L x k,
      Complex.exp (2*(k:ℂ))*angularProduct q br amp w 2 true p L x k+
        angularProduct q br amp w 3 true p L x k-angularProduct q br amp w 1 true p L x k,
      D4BMOriginalForcingProductBounds.rawProduct q br amp w true p L x k] j

private theorem normalized_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (p L x k : ℝ) (hp : 0<p) (hL : 0<L) (j : Fin 4) :
    transferCut q br amp w j p L x k=
      ![(tortoiseRadius (-L/2):ℂ)^2,(tortoiseRadius (-L/2):ℂ)^2,
        (tortoiseRadius (-L/2):ℂ)^2,(tortoiseRadius (-L/2):ℂ)] j*
        normalizedTransfer q br amp w j p L x k := by
  have hs := physical_source_transfer_products q br amp w hw p L x k hp hL
  have hf := physical_forcing_transfer_product q br amp w hw p L x k hL
  fin_cases j
  · change transferCut q br amp w 0 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hs.1
  · change transferCut q br amp w 1 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hs.2.1
  · change transferCut q br amp w 2 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hs.2.2
  · change transferCut q br amp w 3 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hf

/-- Complete boundary after cancellation of the physical radius reconstruction.
Each moment remains the original time/horizontal integral, with the prescribed forcing weight. -/
def normalizedBoundary (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  let R : ℂ := tortoiseRadius (-L/2)
  let mu := eigenvalue q
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,normalizedTransfer q br amp w j p L x k
  (-(mu-2)*(F 0 b-F 0 a)+w*(mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-
    2*(mu-2)*(∫ p in a..b,F 0 p)-R^2/(R^2-1)*(∫ p in a..b,F 3 p)))/(R^2-1)

/-- The complete original metric boundary with its unchanged three counterterms
is exactly the full source-product expression, including both temporal endpoints. -/
theorem complete_metric_boundary_products (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (a b L k : ℝ) (ha : 0<a) (hab : a≤b) (hL : 0<L) :
    (∫ p in a..b,
      (D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 0 p (tortoiseRadius (-L/2)) (Real.exp k)-
        D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 1 p (tortoiseRadius (-L/2)) (Real.exp k)/
          ((tortoiseRadius (-L/2):ℂ)^2-1))/(tortoiseRadius (-L/2):ℂ)^2)-
      ∑ i : Fin 3,compactBoundaryCoefficient q q br true amp w a b (tortoiseRadius (-L/2)) i*
        Complex.exp (fluxExponent q q i*(k:ℂ))=
      normalizedBoundary q br amp w a b L k := by
  rw [complete_metric_boundary_cut q br amp w hw a b L k ha hab hL]
  let R : ℂ := tortoiseRadius (-L/2)
  let c := ![R^2,R^2,R^2,R]
  have hh (j : Fin 4) (p : ℝ) (hp : 0<p) :
      (∫ x in (-1/2:ℝ)..1/2,transferCut q br amp w j p L x k)=
        c j*(∫ x in (-1/2:ℝ)..1/2,normalizedTransfer q br amp w j p L x k) := by
    calc
      _ = ∫ x in (-1/2:ℝ)..1/2,c j*normalizedTransfer q br amp w j p L x k := by
        apply intervalIntegral.integral_congr
        intro x _
        exact normalized_cut q br amp w hw p L x k hp hL j
      _ = _ := intervalIntegral.integral_const_mul _ _
  have ht (j : Fin 4) :
      (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,transferCut q br amp w j p L x k)=
        c j*(∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,normalizedTransfer q br amp w j p L x k) := by
    calc
      _ = ∫ p in a..b,c j*(∫ x in (-1/2:ℝ)..1/2,normalizedTransfer q br amp w j p L x k) := by
        apply intervalIntegral.integral_congr
        intro p hp
        have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
        exact hh j p (ha.trans_le hp'.1)
      _ = _ := intervalIntegral.integral_const_mul _ _
  unfold boundaryCombination normalizedBoundary
  dsimp only
  rw [hh 0 b (ha.trans_le hab),hh 0 a ha,ht 0,ht 1,ht 2,ht 3]
  dsimp only [c,Matrix.cons_val]
  have hR : 1<tortoiseRadius (-L/2) := tortoiseRadius_exterior (-L/2) (by linarith)
  have hr : R≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : R^2-1≠0 := by
    change (tortoiseRadius (-L/2):ℂ)^2-1≠0
    exact_mod_cast (show tortoiseRadius (-L/2)^2-1≠0 by nlinarith)
  change _= (-(eigenvalue q-2)*_+w*(_-_-_-R^2/(R^2-1)*_))/(R^2-1)
  change (-(eigenvalue q-2)*(R^2*_-R^2*_)+w*(_-_-_-R^3/(R^2-1)*(R*_)))/(R^2*(R^2-1))=_
  field_simp [hr,hf]

/-- After the actual radial Jacobian, the fourth transfer uses normalized forcing;
the three evolved-source transfers keep their original products. -/
def radialTransfer (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4)
    (p L x k : ℝ) : ℂ :=
  if j=3 then Complex.exp (-w*(p:ℂ))*
    D4BMOriginalForcingProductBounds.normalizedProduct q br amp w true p L x k
  else normalizedTransfer q br amp w j p L x k

/-- The full boundary in the original radial measure, with every endpoint retained. -/
def radialBoundary (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  let mu := eigenvalue q
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,radialTransfer q br amp w j p L x k
  (-(mu-2)*(F 0 b-F 0 a)+w*(mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-
    2*(mu-2)*(∫ p in a..b,F 0 p)-(∫ p in a..b,F 3 p)))

/-- The actual radial Jacobian cancels every extra metric denominator in the
complete source/forcing boundary. The collar coordinate contributes a further factor one-half. -/
theorem complete_boundary_radial_density (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b L k : ℝ) (hL : 0<L) :
    ((tortoiseRadius (-L/2):ℂ)^2-1)*normalizedBoundary q br amp w a b L k=
      radialBoundary q br amp w a b L k := by
  let R : ℂ := tortoiseRadius (-L/2)
  let Z : ℂ := horizonCoordinate (-L/2)
  have hR : 1<tortoiseRadius (-L/2) := tortoiseRadius_exterior (-L/2) (by linarith)
  have hf : R^2-1≠0 := by
    change (tortoiseRadius (-L/2):ℂ)^2-1≠0
    exact_mod_cast (show tortoiseRadius (-L/2)^2-1≠0 by nlinarith)
  have hZ : R^2*Z=R^2-1 := by
    dsimp only [Z,horizonCoordinate]
    rw [radialUnit_inverse_radius]
    push_cast
    change R^2*(1-(R⁻¹)^2)=R^2-1
    field_simp [show R≠0 from Complex.ofReal_ne_zero.mpr (by linarith)]
  have h3 (p x : ℝ) : normalizedTransfer q br amp w 3 p L x k=
      Z*radialTransfer q br amp w 3 p L x k := by
    simp only [normalizedTransfer,radialTransfer,Matrix.cons_val,↓reduceIte,
      D4BMOriginalForcingProductBounds.raw_product_factor q br amp w true p L x k hL]
    ring
  have hi : (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,normalizedTransfer q br amp w 3 p L x k)=
      Z*(∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,radialTransfer q br amp w 3 p L x k) := by
    simp_rw [h3,intervalIntegral.integral_const_mul]
  unfold normalizedBoundary radialBoundary
  simp only [radialTransfer,show (0:Fin 4)≠3 by decide,show (1:Fin 4)≠3 by decide,
    show (2:Fin 4)≠3 by decide,if_false,if_true]
  rw [hi]
  change (R^2-1)*(_/(R^2-1))=_
  rw [mul_div_cancel₀ _ hf]
  have he : R^2/(R^2-1)*Z=1 := by rw [div_mul_eq_mul_div,hZ];exact div_self hf
  rw [← mul_assoc,he,one_mul]
  rfl

/-- Actual joint time/horizontal continuity of every normalized physical
transfer at positive source time and any fixed exterior collar. -/
theorem radial_transfer_continuousAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (L k : ℝ) (hL : 0<L) (j : Fin 4) (z : ℝ×ℝ) (hp : 0<z.1) :
    ContinuousAt (fun t : ℝ×ℝ => radialTransfer q br amp w j t.1 L t.2 k) z := by
  let R : ℂ := tortoiseRadius (-L/2)
  let Z : ℂ := horizonCoordinate (-L/2)
  let c : Fin 4→ℂ := ![R^2,R^2,R^2,R*Z]
  have hR := tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0)
  have hR0 : R≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hZ0 : Z≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (horizonCoordinate_interior (-L/2) (by linarith)).1)
  have hc0 : c j≠0 := by fin_cases j <;> simp [c,hR0,hZ0]
  have hscale (p x : ℝ) (hp : 0<p) :
      transferCut q br amp w j p L x k=c j*radialTransfer q br amp w j p L x k := by
    rw [normalized_cut q br amp w hw p L x k hp hL j]
    fin_cases j <;> simp [c,R,Z,radialTransfer,normalizedTransfer,
      D4BMOriginalForcingProductBounds.raw_product_factor q br amp w true p L x k hL]; ring
  have hco : Continuous (fun t : ℝ×ℝ => ∑ i : Fin 3,
      modeTransferCoefficient q q br true amp w j t.1 (tortoiseRadius (-L/2)) i*
        Complex.exp (fluxExponent q q i*(k:ℂ))) := by
    apply continuous_finsetSum
    intro i _
    exact ((coefficient_continuous q br amp w (tortoiseRadius (-L/2)) j i).comp continuous_fst).mul_const _
  have hcut : ContinuousAt (fun t : ℝ×ℝ => transferCut q br amp w j t.1 L t.2 k) z :=
    (transfer_continuous q br amp w hw _ _ hR (Real.exp_pos k) j z hp).sub hco.continuousAt
  have he : (fun t : ℝ×ℝ => radialTransfer q br amp w j t.1 L t.2 k) =ᶠ[𝓝 z]
      (fun t : ℝ×ℝ => transferCut q br amp w j t.1 L t.2 k/c j) := by
    have hpos : ∀ᶠ t : ℝ×ℝ in 𝓝 z,0<t.1 := continuous_fst.continuousAt.eventually (lt_mem_nhds hp)
    filter_upwards [hpos] with t ht
    rw [hscale t.1 t.2 ht]
    field_simp [hc0]
  exact (hcut.div_const (c j)).congr_of_eventuallyEq he

end
end RHTower.D4BMOriginalCompleteTransfer
