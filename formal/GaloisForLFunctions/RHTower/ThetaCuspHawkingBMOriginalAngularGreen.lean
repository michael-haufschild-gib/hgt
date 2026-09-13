import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalPotential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspMeanDerivative
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules

/-!
Exact angular Green transfer for the complete original causal potential.

The coexact angular-action transfer defect is the divergence of
`(Delta Z) grad S - mu S grad Z`. Original modular periodicity cancels the
two vertical sides. Finite height integration retains both cusp fluxes.
The full causal source, fixed onset lift and physical reader remain unchanged.
No infinite cusp limit, temporal transform or extinction is asserted here.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalAngularGreen
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMHorizon D4BMModularCore
open D4BMOriginalCausalPotential D4BMCuspResponse D4BMJointSource

/-- The complete original causal potential, with both null coordinates retained. -/
def source (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) (z : Point) : ℂ :=
  originalPotential q branch amp p r (z 0) (Real.log (z 1))

private theorem source_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ)
    (z : Point) (hz : 0 < z 1) : ContDiffAt ℝ ∞ (source q branch amp p r) z := by
  have hc : ContDiffAt ℝ ∞ (fun v : Point => (v 0,Real.log (v 1))) z :=
    (contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.prodMk
      ((contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hz.ne')
  have h := (originalPotential_angular_smooth q branch amp p r).contDiffAt.comp z hc
  exact h

private theorem source_periodic (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) :
    Function.Periodic (source q branch amp p r) ![1,0] := by
  intro z
  let w : UpperHalfPlane := ⟨⟨z 0,Real.exp (Real.log (z 1))⟩,Real.exp_pos _⟩
  have h := originalPotential_modular q branch amp p r ModularGroup.T w
  rw [ModularGroup.re_T_smul,ModularGroup.im_T_smul] at h
  change originalPotential q branch amp p r (z 0+1) (Real.log (Real.exp (Real.log (z 1))))=
    originalPotential q branch amp p r (z 0) (Real.log (Real.exp (Real.log (z 1)))) at h
  rw [Real.log_exp] at h
  change originalPotential q branch amp p r (z 0+1) (Real.log (z 1+0))=
    originalPotential q branch amp p r (z 0) (Real.log (z 1))
  simpa only [add_zero] using h

private theorem reader_smooth (u : ℂ) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar u) z :=
  (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

private theorem reader_periodic (u : ℂ) : Function.Periodic (D4BMLiteralCusp.scalar u) ![1,0] := by
  intro z
  simpa [D4BMLiteralCusp.scalar,Pi.add_apply] using
    d4BM_completedEisensteinCuspLeg_scalar_periodic u (z 1) (z 0)

private theorem partial_smooth {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z) (j : Fin 2) :
    ContDiffAt ℝ ∞ (coordDeriv j F) z :=
  coordDeriv_contDiffAt hF (by simp) j

private theorem partial_periodic {F : Point → ℂ}
    (hF : Function.Periodic F ![1,0]) (j : Fin 2) : Function.Periodic (coordDeriv j F) ![1,0] := by
  intro z
  have he : (fun w => F (w+![1,0]))=F := funext hF
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := z) ![1,0]
  rw [he] at hd
  exact congrArg (fun L => L (Pi.single j 1)) hd.symm

/-- Original hyperbolic scalar Laplacian in the positive-height chart. -/
def lap (F : Point → ℂ) (z : Point) : ℂ :=
  (z 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 F) z+coordDeriv 1 (coordDeriv 1 F) z)

private theorem lap_smooth {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z) :
    ContDiffAt ℝ ∞ (lap F) z := by
  have hy : ContDiffAt ℝ ∞ (fun v : Point => (v 1:ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt
  exact (hy.pow 2).mul ((partial_smooth (partial_smooth hF 0) 0).add
    (partial_smooth (partial_smooth hF 1) 1))

private theorem lap_periodic {F : Point → ℂ} (hF : Function.Periodic F ![1,0]) :
    Function.Periodic (lap F) ![1,0] := by
  intro z
  simp only [lap,(partial_periodic (partial_periodic hF 0) 0) z,
    (partial_periodic (partial_periodic hF 1) 1) z,Pi.add_apply,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,add_zero]

private theorem lap_reader (u : ℂ) (z : Point) (hz : 0 < z 1) :
    lap (D4BMLiteralCusp.scalar u) z=(u^2-1/4)*D4BMLiteralCusp.scalar u z := by
  have h := D4BMLiteralCusp.scalar_equation u z hz
  rw [scalarLaplacian_eq _ z hz] at h
  simpa only [lap,D4BMLiteralCusp.scalarQ,neg_sub] using h

/-- Exact Green flux for transferring the angular action to the original scalar reader. -/
def flux (F : Point → ℂ) (u : ℂ) (j : Fin 2) (z : Point) : ℂ :=
  lap F z*coordDeriv j (D4BMLiteralCusp.scalar u) z-
    (u^2-1/4)*D4BMLiteralCusp.scalar u z*coordDeriv j F z

/-- Angular-action transfer defect, expressed using the unchanged coexact fields. -/
def defect (F : Point → ℂ) (u : ℂ) (z : Point) : ℂ :=
  ∑ j : Fin 2, (coexact (lap F) j z-(u^2-1/4)*coexact F j z)*
    D4BMLiteralCusp.vector u j z

private theorem flux_smooth {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z)
    (hz : 0 < z 1) (u : ℂ) (j : Fin 2) : ContDiffAt ℝ ∞ (flux F u j) z :=
  ((lap_smooth hF).mul (partial_smooth (reader_smooth u z hz) j)).sub
    ((contDiffAt_const.mul (reader_smooth u z hz)).mul (partial_smooth hF j))

private theorem flux_periodic {F : Point → ℂ} (hF : Function.Periodic F ![1,0])
    (u : ℂ) (j : Fin 2) : Function.Periodic (flux F u j) ![1,0] := by
  intro z
  simp only [flux,lap_periodic hF z,partial_periodic (reader_periodic u) j z,
    reader_periodic u z,partial_periodic hF j z]

/-- Exact local transfer, with no source equation or discarded boundary. -/
theorem divergence_flux {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z)
    (hz : 0 < z 1) (u : ℂ) :
    (∑ j : Fin 2, coordDeriv j (flux F u j) z)=defect F u z := by
  have hS := reader_smooth u z hz
  have dS := hS.differentiableAt (by simp)
  have hmu : DifferentiableAt ℝ (fun v => (u^2-1/4)*D4BMLiteralCusp.scalar u v) z :=
    dS.const_mul _
  have hd (j : Fin 2) : coordDeriv j (flux F u j) z=
      coordDeriv j (lap F) z*coordDeriv j (D4BMLiteralCusp.scalar u) z+
      lap F z*coordDeriv j (coordDeriv j (D4BMLiteralCusp.scalar u)) z-
      ((u^2-1/4)*coordDeriv j (D4BMLiteralCusp.scalar u) z*coordDeriv j F z+
        (u^2-1/4)*D4BMLiteralCusp.scalar u z*coordDeriv j (coordDeriv j F) z) := by
    have hleft : DifferentiableAt ℝ (fun v => lap F v*coordDeriv j (D4BMLiteralCusp.scalar u) v) z :=
      ((lap_smooth hF).differentiableAt (by simp)).mul ((partial_smooth hS j).differentiableAt (by simp))
    have hright : DifferentiableAt ℝ (fun v => (u^2-1/4)*D4BMLiteralCusp.scalar u v*coordDeriv j F v) z :=
      hmu.mul ((partial_smooth hF j).differentiableAt (by simp))
    have hmuD : coordDeriv j (fun v => (u^2-1/4)*D4BMLiteralCusp.scalar u v) z=
        (u^2-1/4)*coordDeriv j (D4BMLiteralCusp.scalar u) z := by
      change (fderiv ℝ (fun v => (u^2-1/4)*D4BMLiteralCusp.scalar u v) z) (Pi.single j 1)=_
      rw [(dS.hasFDerivAt.const_mul (u^2-1/4)).fderiv]
      rfl
    unfold flux
    rw [coordDeriv_sub hleft hright,
      coordDeriv_mul ((lap_smooth hF).differentiableAt (by simp)) ((partial_smooth hS j).differentiableAt (by simp)),
      coordDeriv_mul hmu ((partial_smooth hF j).differentiableAt (by simp)),hmuD]
  have he := lap_reader u z hz
  simp only [Fin.sum_univ_two,hd,defect,coexact,D4BMLiteralCusp.vector,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  dsimp only [lap] at he ⊢
  linear_combination
    (coordDeriv 0 (coordDeriv 0 F) z+coordDeriv 1 (coordDeriv 1 F) z)*he


private theorem coexact_lap {F : Point → ℂ} {z : Point} (hz : 0 < z 1) (j : Fin 2) :
    coexact (scalarLaplacian F) j z=coexact (lap F) j z := by
  have he : scalarLaplacian F =ᶠ[𝓝 z] lap F := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
    exact scalarLaplacian_eq F v hv
  have hd := he.fderiv_eq (𝕜 := ℝ)
  fin_cases j
  · change (fderiv ℝ (scalarLaplacian F) z) (Pi.single 1 1)=
      (fderiv ℝ (lap F) z) (Pi.single 1 1)
    rw [hd]
  · change -((fderiv ℝ (scalarLaplacian F) z) (Pi.single 0 1))=
      -((fderiv ℝ (lap F) z) (Pi.single 0 1))
    rw [hd]

/-- The defect is that of the original covariant vector Laplacian, not a substituted operator. -/
theorem defect_eq_rough {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z)
    (hz : 0 < z 1) (u : ℂ) :
    defect F u z=∑ j : Fin 2,
      (roughLaplacian (coexact F) j z*D4BMLiteralCusp.vector u j z-
        coexact F j z*roughLaplacian (D4BMLiteralCusp.vector u) j z) := by
  have hC (j : Fin 2) := coexact_roughLaplacian F z hz
    (hF.of_le (show (3:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)) j
  simp_rw [coexact_lap hz] at hC
  unfold defect
  apply Finset.sum_congr rfl
  intro j _
  rw [hC j,D4BMLiteralCusp.vector_equation u z hz j]
  simp only [d4HyperbolicHodgePairedVectorEigenvalue,D4BMLiteralCusp.scalarQ]
  ring

private def planarFlux (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ)
    (u : ℂ) (j : Fin 2) : ℂ → ℂ := flux (source q branch amp p r) u j ∘ angularCoordinates

private theorem planarFlux_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) (j : Fin 2) :
    ContDiffOn ℝ ∞ (planarFlux q branch amp p r u j) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((flux_smooth (source_smooth q branch amp p r (angularCoordinates z) hz) hz u j).comp z
    angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private def planarDivergence (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ)
    (u : ℂ) (z : ℂ) : ℂ :=
  horizontal (planarFlux q branch amp p r u 0) z+vertical (planarFlux q branch amp p r u 1) z

private theorem planarDivergence_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) (z : ℂ) (hz : 0 < z.im) :
    planarDivergence q branch amp p r u z=defect (source q branch amp p r) u (angularCoordinates z) := by
  have h0 := angularCoordinates_derivative (flux (source q branch amp p r) u 0) 0 z
  have h1 := angularCoordinates_derivative (flux (source q branch amp p r) u 1) 1 z
  have h := divergence_flux (source_smooth q branch amp p r (angularCoordinates z) hz) hz u
  rw [Fin.sum_univ_two] at h
  exact (congrArg₂ (·+·) h0 h1).trans h

private theorem planarDivergence_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) :
    ContDiffOn ℝ ∞ (planarDivergence q branch amp p r u) {z : ℂ | 0 < z.im} :=
  (planar_derivative_contDiffOn (planarFlux_smooth q branch amp p r u 0) (1:ℂ)).add
    (planar_derivative_contDiffOn (planarFlux_smooth q branch amp p r u 1) Complex.I)

/-- Original width-one cusp flux: `(Delta Z)*S_Y-mu*S*Z_Y`. -/
def cuspFlux (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) (u : ℂ) : ℝ → ℂ :=
  average (planarFlux q branch amp p r u 1)

/-- Actual coexact angular-action transfer defect on a full cusp section. -/
def cuspDefect (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) (u : ℂ) : ℝ → ℂ :=
  average (fun z => defect (source q branch amp p r) u (angularCoordinates z))

private theorem horizontal_mean_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) {y : ℝ} (hy : 0 < y) :
    average (horizontal (planarFlux q branch amp p r u 0)) y=0 := by
  have hs := planarFlux_smooth q branch amp p r u 0
  have hd := planar_derivative_contDiffOn hs (1:ℂ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1/2:ℝ)) (b := (1/2:ℝ))
    (fun x _ => slice_horizontal_derivative (planarFlux q branch amp p r u 0) hs y hy x)
    ((slice_continuous (horizontal (planarFlux q branch amp p r u 0)) hd hy).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)] at he
  change average (horizontal (planarFlux q branch amp p r u 0)) y=_ at he
  rw [he]
  have hp := flux_periodic (source_periodic q branch amp p r) u 0
    (angularCoordinates (point (-1/2) y))
  have hc : angularCoordinates (point (1/2) y)=angularCoordinates (point (-1/2) y)+![1,0] := by
    ext i
    fin_cases i <;> norm_num [angularCoordinates,point,Pi.add_apply]
  exact sub_eq_zero.mpr (by change flux (source q branch amp p r) u 0 _=_; rw [hc]; exact hp)

private theorem divergence_average_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) {y : ℝ} (hy : 0 < y) :
    average (planarDivergence q branch amp p r u) y=cuspDefect q branch amp p r u y := by
  apply integral_congr_ae
  filter_upwards with X
  exact planarDivergence_eq q branch amp p r u (point X y) (by simpa [point] using hy)

/-- Actual angular operator transfer differentiates to the retained cusp flux. -/
theorem cuspFlux_hasDerivAt (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) (y : Ioi (0:ℝ)) :
    HasDerivAt (cuspFlux q branch amp p r u) (cuspDefect q branch amp p r u y) y := by
  have hv := average_hasDerivAt (planarFlux q branch amp p r u 1)
    (planarFlux_smooth q branch amp p r u 1) y.2
  have h0 := (slice_continuous (horizontal (planarFlux q branch amp p r u 0))
    (planar_derivative_contDiffOn (planarFlux_smooth q branch amp p r u 0) (1:ℂ)) y.2).integrableOn_Ioc
      (μ := (volume : Measure ℝ)) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  have h1 := (slice_continuous (vertical (planarFlux q branch amp p r u 1))
    (planar_derivative_contDiffOn (planarFlux_smooth q branch amp p r u 1) Complex.I) y.2).integrableOn_Ioc
      (μ := (volume : Measure ℝ)) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  have he : cuspDefect q branch amp p r u y=average (vertical (planarFlux q branch amp p r u 1)) y := by
    rw [← divergence_average_eq q branch amp p r u y.2]
    change (∫ X in Ioc (-1/2:ℝ) (1/2),
      horizontal (planarFlux q branch amp p r u 0) (point X y)+
      vertical (planarFlux q branch amp p r u 1) (point X y))=_
    rw [integral_add h0 h1]
    change average (horizontal (planarFlux q branch amp p r u 0)) y+_=_
    rw [horizontal_mean_zero q branch amp p r u y.2,zero_add]
    rfl
  exact hv.congr_deriv he.symm

private theorem defect_intervalIntegrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (u : ℂ) (a b : Ioi (0:ℝ)) :
    IntervalIntegrable (cuspDefect q branch amp p r u) volume (a:ℝ) b := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hpos := (lt_min a.2 b.2).trans_le hy.1
  have h := (average_hasDerivAt (planarDivergence q branch amp p r u)
    (planarDivergence_smooth q branch amp p r u) hpos).continuousAt
  have he : average (planarDivergence q branch amp p r u) =ᶠ[𝓝 y]
      cuspDefect q branch amp p r u := by
    filter_upwards [isOpen_Ioi.mem_nhds hpos] with z hz
    exact divergence_average_eq q branch amp p r u hz
  exact (h.congr_of_eventuallyEq he.symm).continuousWithinAt

/-- The original full retarded source and unchanged physical reader satisfy exact
finite-cusp Green transfer, retaining both height endpoints and every source term. -/
theorem original_coexact_green (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) (a b : Ioi (0:ℝ)) :
    (∫ y in (a:ℝ)..b, cuspDefect q branch amp p v (physicalAngularParameter r) y)=
      cuspFlux q branch amp p v (physicalAngularParameter r) b-
        cuspFlux q branch amp p v (physicalAngularParameter r) a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => cuspFlux_hasDerivAt q branch amp p v (physicalAngularParameter r)
      ⟨y,(lt_min a.2 b.2).trans_le hy.1⟩)
    (defect_intervalIntegrable q branch amp p v (physicalAngularParameter r) a b)

end RHTower.D4BMOriginalAngularGreen
