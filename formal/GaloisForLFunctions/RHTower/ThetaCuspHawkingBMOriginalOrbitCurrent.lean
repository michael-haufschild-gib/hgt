import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceContact
import GaloisForLFunctions.RHTower.SelbergModularCurrentGreen

/-!
# Original temporal and radial metric currents on the finite modular domain

For the actual reconstructed causal metric and unchanged left QNM, both orbit
components reduce to scalar pairings and the complete angular normal flux.
The scalar contact is the full angular Laplacian minus twice the reconstructed
source plus its original forcing. Both angular integrations by parts place
all Laplacians on the reader; the source forcing is not differentiated in the
scalar bulk. The curved core, vertical side jump and top flux are retained.

The identities hold on every finite modular domain at positive ingoing time
and exterior radius. They do not interchange temporal, cusp or horizon limits.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalOrbitCurrent
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMOriginalAngularCurrent
open D4BMOriginalSourceContact D4BMMetricReconstruction
open GaloisForLFunctions.RHTower
open SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices
private abbrev P := Fin 4 → ℝ
private abbrev F := P → ℂ

def slice (p R : ℝ) (z : ℂ) : P := ![p,R,z.re,z.im]

private def sliceLinear : ℂ →L[ℝ] P :=
  ContinuousLinearMap.pi ![0,0,Complex.reCLM,Complex.imCLM]

private theorem slice_deriv (p R : ℝ) (z : ℂ) :
    HasFDerivAt (slice p R) sliceLinear z := by
  convert! sliceLinear.hasFDerivAt.add_const (![p,R,0,0] : P) using 1
  funext z i
  fin_cases i <;> simp [slice,sliceLinear]

private theorem slice_smooth (p R : ℝ) : ContDiff ℝ ∞ (slice p R) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact Complex.reCLM.contDiff
  · exact Complex.imCLM.contDiff

private theorem slice_direction {A : F} {p R : ℝ} {z : ℂ}
    (hA : DifferentiableAt ℝ A (slice p R z)) (j : Fin 2) :
    fderiv ℝ (A ∘ slice p R) z (if j=0 then 1 else Complex.I)=
      coordDeriv (angularIndex j) A (slice p R z) := by
  rw [(hA.hasFDerivAt.comp z (slice_deriv p R z)).fderiv]
  change fderiv ℝ A (slice p R z) (sliceLinear (if j=0 then 1 else Complex.I))=_
  have hv : sliceLinear (if j=0 then 1 else Complex.I)=Pi.single (angularIndex j) 1 := by
    fin_cases j <;> ext i <;> fin_cases i <;> simp [sliceLinear,angularIndex]
  rw [hv]

private theorem partial_smooth {A : F} {x : P} (hA : ContDiffAt ℝ ∞ A x) (i : Fin 4) :
    ContDiffAt ℝ ∞ (coordDeriv i A) x := coordDeriv_contDiffAt hA (by simp) i

private theorem area_integrable {A : F} {p R : ℝ}
    (hA : ∀ z : ℂ, 0<z.im → ContinuousAt A (slice p R z)) (Y : ℝ) :
    IntegrableOn (fun w : ℝ×ℝ => A (slice p R (point w.1 w.2))) (domain Y) := by
  have hc : ContinuousOn (fun w : ℝ×ℝ => A (slice p R (point w.1 w.2))) (cell Y) := by
    intro w hw
    have hy : 0 < (point w.1 w.2).im := by
      simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
      linarith [hw.2.1]
    have hmap : Continuous (fun v : ℝ×ℝ => slice p R (point v.1 v.2)) :=
      (slice_smooth p R).continuous.comp (show Continuous (fun v : ℝ×ℝ => point v.1 v.2) by unfold point; fun_prop)
    exact ((hA _ hy).comp (f := fun v : ℝ×ℝ => slice p R (point v.1 v.2)) (x := w) hmap.continuousAt).continuousWithinAt
  exact (hc.mono (domain_subset_cell Y)).integrableOn_compact (isCompact_domain Y)

/-- Every original side, top and curved-core normal-density contribution. -/
def boundary (A B : F) (p R Y : ℝ) : ℂ :=
  (∫ y in arcFloor..Y, A (slice p R (point (1/2) y))-A (slice p R (point (-(1/2)) y)))+
  (∫ x in (-(1/2:ℝ))..1/2, B (slice p R (point x Y)))+
  ∫ x in (0:ℝ)..1/2,
    ((-x/arcHeight x:ℝ):ℂ)*A (slice p R (point x (arcHeight x)))-B (slice p R (point x (arcHeight x)))+
    ((x/arcHeight x:ℝ):ℂ)*A (slice p R (point (-x) (arcHeight x)))-B (slice p R (point (-x) (arcHeight x)))

private theorem angular_divergence_integral (A B : F) (p R : ℝ)
    (hA : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ A (slice p R z))
    (hB : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ B (slice p R z))
    {Y : ℝ} (hY : 1≤Y) :
    (∫ w in domain Y, coordDeriv 2 A (slice p R (point w.1 w.2))+
      coordDeriv 3 B (slice p R (point w.1 w.2)))=boundary A B p R Y := by
  have hi := (area_integrable (fun z hz => (partial_smooth (hA z hz) 2).continuousAt) Y).add
    (area_integrable (fun z hz => (partial_smooth (hB z hz) 3).continuousAt) Y)
  change IntegrableOn (fun w : ℝ×ℝ => coordDeriv 2 A (slice p R (point w.1 w.2))+
    coordDeriv 3 B (slice p R (point w.1 w.2))) (domain Y) at hi
  have hc (C : F) (hC : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ C (slice p R z)) :
      ContinuousOn (C ∘ slice p R) {z : ℂ | 0<z.im} := by
    intro z hz
    exact ((hC z hz).continuousAt.comp (slice_smooth p R).continuous.continuousAt).continuousWithinAt
  have hcurve (C : F) (hC : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ C (slice p R z))
      (γ : ℝ → ℂ) (hγ : Continuous γ) {a b : ℝ}
      (hγpos : ∀ x ∈ uIcc a b, 0<(γ x).im) :
      IntervalIntegrable (fun x => C (slice p R (γ x))) volume a b := by
    exact ((hc C hC).comp hγ.continuousOn hγpos).intervalIntegrable
  have hfloor : arcFloor≤Y := (arcHeight_le_one ⟨by norm_num,le_rfl⟩).trans hY
  have hside (a : ℝ) : IntervalIntegrable (fun y => A (slice p R (point a y))) volume arcFloor Y := by
    apply hcurve A hA _ (by unfold point; fun_prop)
    intro y hy
    have hyI : y ∈ Icc arcFloor Y := by simpa only [uIcc_of_le hfloor] using hy
    simpa [point] using arcFloor_pos.trans_le hyI.1
  have htop : IntervalIntegrable (fun x => B (slice p R (point x Y))) volume (-(1/2:ℝ)) (1/2) := by
    apply hcurve B hB _ (by unfold point; fun_prop)
    intro x hx
    simpa [point] using (show 0<Y by linarith)
  have harc (C : F) (hC : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ C (slice p R z))
      (negate : Bool) : ContinuousOn (fun x => C (slice p R
        (point (if negate then -x else x) (arcHeight x)))) (uIcc (0:ℝ) (1/2)) := by
    apply (hc C hC).comp (show Continuous (fun x => point (if negate then -x else x) (arcHeight x)) by
      cases negate <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> unfold point
      · exact Complex.continuous_ofReal.add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)
      · exact (Complex.continuous_ofReal.comp continuous_neg).add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)).continuousOn
    intro x hx
    have hxI : x ∈ Icc (0:ℝ) (1/2) := by simpa using hx
    simpa [point] using arcHeight_pos (show x ∈ Icc (-(1/2:ℝ)) (1/2) from ⟨by linarith [hxI.1],hxI.2⟩)
  have hscale : ContinuousOn (fun x : ℝ => ((x/arcHeight x:ℝ):ℂ)) (uIcc (0:ℝ) (1/2)) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    refine continuousOn_id.div continuous_arcHeight.continuousOn ?_
    intro x hx
    have hxI : x ∈ Icc (0:ℝ) (1/2) := by simpa using hx
    exact (arcHeight_pos ⟨by linarith [hxI.1],hxI.2⟩).ne'
  have hab : IntervalIntegrable (fun x : ℝ =>
      ((-x/arcHeight x:ℝ):ℂ)*A (slice p R (point x (arcHeight x)))-B (slice p R (point x (arcHeight x)))+
      ((x/arcHeight x:ℝ):ℂ)*A (slice p R (point (-x) (arcHeight x)))-B (slice p R (point (-x) (arcHeight x))))
      volume 0 (1/2) := by
    have hh := (((hscale.neg.mul (harc A hA false)).sub (harc B hB false)).add
        (hscale.mul (harc A hA true)) |>.sub (harc B hB true)).intervalIntegrable (μ := volume)
    convert! hh using 1
    ext x
    simp [neg_div]
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ w in domain Y, coordDeriv 2 A (slice p R (point w.1 w.2))+
        coordDeriv 3 B (slice p R (point w.1 w.2)))=L (boundary A B p R Y) := by
    have hs (C : F) (hC : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ C (slice p R z)) :
        ContDiffOn ℝ 1 (L ∘ C ∘ slice p R) {z : ℂ | 0<z.im} := by
      intro z hz
      exact (L.contDiff.contDiffAt.comp z ((hC z hz).comp z (slice_smooth p R).contDiffAt)
        |>.of_le (by simp)).contDiffWithinAt
    have h := SelbergModularCurrentGreen.current_green_identity (L ∘ A ∘ slice p R) (hs A hA)
      (L ∘ B ∘ slice p R) (hs B hB) hY
    have hd (C : F) (hC : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ C (slice p R z))
        (z : ℂ) (hz : 0<z.im) (j : Fin 2) :
        fderiv ℝ (L ∘ C ∘ slice p R) z (if j=0 then 1 else Complex.I)=
          L (coordDeriv (angularIndex j) C (slice p R z)) := by
      have hf := ((hC z hz).differentiableAt (by simp)).comp z (slice_deriv p R z).differentiableAt
      rw [(L.hasFDerivAt.comp z hf.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply,
        slice_direction ((hC z hz).differentiableAt (by simp))]
    have he : (∫ w in domain Y, SelbergMaassTraceEnergy.dir 1 (L ∘ A ∘ slice p R) (point w.1 w.2)+
        SelbergMaassTraceEnergy.dir Complex.I (L ∘ B ∘ slice p R) (point w.1 w.2))=
        L (∫ w in domain Y, coordDeriv 2 A (slice p R (point w.1 w.2))+
          coordDeriv 3 B (slice p R (point w.1 w.2))) := by
      rw [← L.integral_comp_comm hi]
      apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
      intro w hw
      have hz : 0<(point w.1 w.2).im := by simpa [point] using (show 0<w.2 by linarith [hw.1.2.1])
      have h0 := hd A hA _ hz 0
      have h1 := hd B hB _ hz 1
      simpa [SelbergMaassTraceEnergy.dir,angularIndex,map_add] using congrArg₂ (·+·) h0 h1
    rw [he] at h
    rw [h]
    unfold boundary
    rw [map_add,map_add,← L.intervalIntegral_comp_comm ((hside (1/2)).sub (hside (-(1/2)))),
      ← L.intervalIntegral_comp_comm htop,← L.intervalIntegral_comp_comm hab]
    have hmul (a : ℝ) (b : ℂ) : L ((a:ℂ)*b)=a*L b := by
      simpa only [Complex.real_smul,smul_eq_mul] using L.map_smul a b
    simp only [SelbergModularCurrentGreen.normalPair,Function.comp_def,map_add,map_sub,hmul]
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)


/-- Bilinear pairing of the genuine coexact scalar fields. -/
def pairing (A B : F) (x : P) : ℂ :=
  ∑ j : Fin 2, coexactField A j x*coexactField B j x

/-- Angular transfer current with its derivative on the physical reader. -/
def transfer (A B : F) (j : Fin 2) (x : P) : ℂ :=
  A x*coordDeriv (angularIndex j) B x

/-- Scalar Laplacian pairing expressed in the planar area density. -/
def scalarDensity (A B : F) (x : P) : ℂ :=
  A x*(coordDeriv 2 (coordDeriv 2 B) x+coordDeriv 3 (coordDeriv 3 B) x)

/-- The planar scalar density includes exactly the original hyperbolic area weight. -/
theorem scalarDensity_eq (A B : F) (x : P) (hy : 0<x 3) :
    scalarDensity A B x=A x*angularLap B x/(x 3:ℂ)^(2 : ℕ) := by
  unfold scalarDensity angularLap
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne']

private theorem pairing_smooth {A B : F} {x : P}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (pairing A B) x := by
  change ContDiffAt ℝ ∞ (fun z => ∑ j : Fin 2, coexactField A j z*coexactField B j z) x
  simp only [Fin.sum_univ_two,coexactField,ite_true,one_ne_zero,ite_false]
  exact ((partial_smooth hA 3).mul (partial_smooth hB 3)).add
    ((partial_smooth hA 2).neg.mul (partial_smooth hB 2).neg)

private theorem density_smooth {A B : F} {x : P}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (scalarDensity A B) x :=
  hA.mul ((partial_smooth (partial_smooth hB 2) 2).add
    (partial_smooth (partial_smooth hB 3) 3))

private theorem transfer_smooth {A B : F} {x : P}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) (j : Fin 2) :
    ContDiffAt ℝ ∞ (transfer A B j) x := hA.mul (partial_smooth hB (angularIndex j))

private theorem transfer_divergence {A B : F} {x : P}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) :
    coordDeriv 2 (transfer A B 0) x+coordDeriv 3 (transfer A B 1) x=
      pairing A B x+scalarDensity A B x := by
  have hd (j : Fin 2) : coordDeriv (angularIndex j) (transfer A B j) x=
      coordDeriv (angularIndex j) A x*coordDeriv (angularIndex j) B x+
      A x*coordDeriv (angularIndex j) (coordDeriv (angularIndex j) B) x :=
    coordDeriv_mul (hA.differentiableAt (by simp))
      ((partial_smooth hB (angularIndex j)).differentiableAt (by simp)) (angularIndex j)
  have h0 := hd 0
  have h1 := hd 1
  simp only [angularIndex,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  rw [h0,h1]
  simp only [pairing,Fin.sum_univ_two,coexactField,ite_true,one_ne_zero,ite_false,scalarDensity]
  ring

private theorem pairing_integral (A B : F) (p R : ℝ)
    (hA : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ A (slice p R z))
    (hB : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ B (slice p R z))
    {Y : ℝ} (hY : 1≤Y) :
    (∫ w in domain Y, pairing A B (slice p R (point w.1 w.2)))+
      (∫ w in domain Y, scalarDensity A B (slice p R (point w.1 w.2)))=
      boundary (transfer A B 0) (transfer A B 1) p R Y := by
  have h := angular_divergence_integral (transfer A B 0) (transfer A B 1) p R
    (fun z hz => transfer_smooth (hA z hz) (hB z hz) 0)
    (fun z hz => transfer_smooth (hA z hz) (hB z hz) 1) hY
  have he : (∫ w in domain Y, coordDeriv 2 (transfer A B 0) (slice p R (point w.1 w.2))+
      coordDeriv 3 (transfer A B 1) (slice p R (point w.1 w.2)))=
      ∫ w in domain Y, pairing A B (slice p R (point w.1 w.2))+
        scalarDensity A B (slice p R (point w.1 w.2)) := by
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hz : 0<(point w.1 w.2).im := by simpa [point] using (show 0<w.2 by linarith [hw.1.2.1])
    exact transfer_divergence (hA _ hz) (hB _ hz)
  rw [he,integral_add (area_integrable (fun z hz => (pairing_smooth (hA z hz) (hB z hz)).continuousAt) Y)
    (area_integrable (fun z hz => (density_smooth (hA z hz) (hB z hz)).continuousAt) Y)] at h
  exact h

/-- Antisymmetrizing the two original integrations by parts transfers the
scalar Laplacian while retaining every finite-domain normal flux. -/
theorem scalar_green_integral (A B : F) (p R : ℝ)
    (hA : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ A (slice p R z))
    (hB : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ B (slice p R z))
    {Y : ℝ} (hY : 1≤Y) :
    (∫ w in domain Y, scalarDensity B A (slice p R (point w.1 w.2)))-
      (∫ w in domain Y, scalarDensity A B (slice p R (point w.1 w.2)))=
      boundary (transfer B A 0) (transfer B A 1) p R Y-
        boundary (transfer A B 0) (transfer A B 1) p R Y := by
  have hab := pairing_integral A B p R hA hB hY
  have hba := pairing_integral B A p R hB hA hY
  have hs : pairing B A=pairing A B := by
    funext x
    unfold pairing
    simp_rw [mul_comm]
  rw [hs] at hba
  linear_combination hba-hab

/-- Public exact field type for finite modular-domain Green identities. -/
abbrev PhysicalField := (Fin 4 → ℝ) → ℂ

/-- Physical angular slice used by the finite modular current. -/
def physicalSlice (p R : ℝ) (z : ℂ) : Fin 4 → ℝ := slice p R z

/-- Public finite-domain scalar density; this is the exact planar density used
by the original current, not a cutoff surrogate. -/
def physicalScalarDensity (A B : PhysicalField) (x : Fin 4 → ℝ) : ℂ :=
  scalarDensity A B x

/-- Public angular transfer current on the same physical slice. -/
def physicalTransfer (A B : PhysicalField) (j : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  transfer A B j x

/-- Every side, top, and curved-core flux of the finite modular domain. -/
def physicalBoundary (A B : PhysicalField) (p R Y : ℝ) : ℂ :=
  boundary A B p R Y

/-- Exact finite modular Green identity in public physical coordinates.  This
exports the existing full-boundary identity without discarding a side, top, or
curved-core flux. -/
theorem physical_scalar_green_integral (A B : PhysicalField) (p R : ℝ)
    (hA : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ ∞ A (physicalSlice p R z))
    (hB : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ ∞ B (physicalSlice p R z))
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in domain Y,
      physicalScalarDensity B A (physicalSlice p R (point w.1 w.2))) -
      (∫ w in domain Y,
        physicalScalarDensity A B (physicalSlice p R (point w.1 w.2))) =
      physicalBoundary (physicalTransfer B A 0) (physicalTransfer B A 1) p R Y -
        physicalBoundary (physicalTransfer A B 0) (physicalTransfer A B 1) p R Y := by
  exact scalar_green_integral A B p R hA hB hY

/-- Ingoing time current uses U_R; radial current uses f U_R+U_p. -/
def orbitDerivative (U : F) (j : Fin 2) (x : P) : ℂ :=
  if j=0 then coordDeriv 1 U x else
    ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 U x+coordDeriv 0 U x

private theorem orbit_smooth {U : F} {x : P} (hU : ContDiffAt ℝ ∞ U x) (j : Fin 2) :
    ContDiffAt ℝ ∞ (orbitDerivative U j) x := by
  have hr : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  fin_cases j
  · exact partial_smooth hU 1
  · exact (((hr.pow 2).sub contDiffAt_const).mul (partial_smooth hU 1)).add (partial_smooth hU 0)

private theorem contact_smooth {U : F} {x : P} (hU : ContDiffAt ℝ ∞ U x) :
    ContDiffAt ℝ ∞ (scalarContact U) x := by
  have hr : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  change ContDiffAt ℝ ∞ (fun z =>
    -(z 1:ℂ)^(2 : ℕ)*((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 U) z-
    (z 1:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 1 U) z+coordDeriv 1 (coordDeriv 0 U) z)-
    2*(z 1:ℂ)*coordDeriv 1 U z+2*(z 1:ℂ)*coordDeriv 0 U z) x
  exact ((((hr.pow 2).neg.mul ((hr.pow 2).sub contDiffAt_const)).mul
    (partial_smooth (partial_smooth hU 1) 1)).sub
    ((hr.pow 2).mul ((partial_smooth (partial_smooth hU 1) 0).add
      (partial_smooth (partial_smooth hU 0) 1))) |>.sub
    ((contDiffAt_const.mul hr).mul (partial_smooth hU 1))).add
    ((contDiffAt_const.mul hr).mul (partial_smooth hU 0))

private theorem coexact_first {U : F} {x : P} (hU : ContDiffAt ℝ ∞ U x)
    (i : Fin 4) (a : Fin 2) :
    (ofField (coexactField U a) x).first i=coexactField (coordDeriv i U) a x := by
  have h2 : ContDiffAt ℝ 2 U x := hU.of_le (WithTop.coe_le_coe.mpr le_top)
  fin_cases a
  · exact coordDeriv_comm h2 i 3
  · change coordDeriv i (fun z => -coordDeriv 2 U z) x= -coordDeriv 2 (coordDeriv i U) x
    simp only [coordDeriv,fderiv_fun_neg,neg_apply]
    exact congrArg Neg.neg (coordDeriv_comm h2 i 2)

private theorem orbit_coexact {U : F} {x : P} (hU : ContDiffAt ℝ ∞ U x)
    (j a : Fin 2) :
    coexactField (orbitDerivative U j) a x=
    if j=0 then coexactField (coordDeriv 1 U) a x else
      ((x 1:ℂ)^(2 : ℕ)-1)*coexactField (coordDeriv 1 U) a x+coexactField (coordDeriv 0 U) a x := by
  have hr : ContDiff ℝ ∞ (fun z : P => ((z 1:ℂ)^(2 : ℕ)-1)) := by fun_prop
  have hd (i : Fin 4) (hi : i≠1) : coordDeriv i (fun z : P => ((z 1:ℂ)^(2 : ℕ)-1)) x=0 := by
    have hR := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply (1:Fin 4) x)
    have h := (hR.mul hR).sub_const (1:ℂ)
    simp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply] at h
    simp only [pow_two]
    change coordDeriv i (fun z : P => (z 1:ℂ)*(z 1:ℂ)-1) x=0
    unfold coordDeriv
    rw [h.fderiv]
    simp [Ne.symm hi]
  have hdU1 := (partial_smooth hU 1).differentiableAt (by simp)
  have hdU0 := (partial_smooth hU 0).differentiableAt (by simp)
  have he (i : Fin 4) (hi : i≠1) :
      coordDeriv i (orbitDerivative U 1) x=
        ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv i (coordDeriv 1 U) x+coordDeriv i (coordDeriv 0 U) x := by
    change coordDeriv i (fun z => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 U z+coordDeriv 0 U z) x=_
    have hprod : DifferentiableAt ℝ (fun z : P => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 U z) x :=
      (hr.differentiable (by simp) x).mul hdU1
    rw [coordDeriv_add hprod hdU0 i,
      coordDeriv_mul (hr.differentiable (by simp) x) hdU1 i,hd i hi]
    ring
  fin_cases j
  · rfl
  · fin_cases a
    · exact he 3 (by decide)
    · change -coordDeriv 2 (orbitDerivative U 1) x=_
      rw [he 2 (by decide)]
      simp [coexactField]
      ring

private theorem orbit_current {U W : F} {x : P}
    (hU : ContDiffAt ℝ ∞ U x) (hW : ContDiffAt ℝ ∞ W x) (j : Fin 2) :
    D4BMIngoingFullCurrent.current (x 1) (x 3)
      (fun a => ofField (coexactField U a) x) (fun a => ofField (coexactField W a) x) (if j=0 then 0 else 1)=
      1/(x 1:ℂ)^(2 : ℕ)*(pairing (orbitDerivative U j) (scalarContact W) x-
        pairing (orbitDerivative W j) (scalarContact U) x) := by
  fin_cases j <;> simp [D4BMIngoingFullCurrent.current,coexact_first hU,coexact_first hW,
    coexact_contact hU,coexact_contact hW,pairing,Fin.sum_univ_two,orbit_coexact hU,orbit_coexact hW]



/-- The complete source contact, including the original forcing and reconstruction. -/
def forcedContact (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  angularLap (sourceScalar q branch amp) x-2*sourceScalar q branch amp x+
    (x 1:ℂ)^(3 : ℕ)/((x 1:ℂ)^(2 : ℕ)-1)*originalForcing q branch amp x

private theorem forcedContact_germ (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    scalarContact (sourceScalar q branch amp) =ᶠ[𝓝 x] forcedContact q branch amp := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hzp hzr hzy
  exact original_scalar_contact q branch amp z hzp hzr hzy

private theorem forcedContact_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    ContDiffAt ℝ ∞ (forcedContact q branch amp) x :=
  (contact_smooth (D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp x hp hr hy)).congr_of_eventuallyEq
    (forcedContact_germ q branch amp x hp hr hy).symm

/-- Actual metric is reconstructed and differentiated before the ingoing current is read. -/
def metricDensity (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ) (j : Fin 2) (x : P) : ℂ :=
  let z : P := ![x 0-D4BMIngoingCoordinates.tortoise (x 1),x 1,x 2,x 3]
  let P := D4BMActualIngoingCurrent.originalStaticStream q branch amp
  let Q := D4BMPhysicalModeAction.physicalLeftModeStream r (D4BMLeftModeRadialEquation.frequency r side) outer
  let w := fun k => (x 1:ℂ)^(2 : ℕ)/(x 3:ℂ)^(2 : ℕ)*D4BMMixedActionCurrent.actionSymplectic
    (D4BMBackground.jet (x 1) (x 3))
    (ofMetricField (D4BMActualIngoingCurrent.reconstructedMetric P) z)
    (ofMetricField (D4BMActualIngoingCurrent.reconstructedMetric Q) z) k
  if j=0 then w 0+w 1/((x 1:ℂ)^(2 : ℕ)-1) else w 1

private theorem metricDensity_stream (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    metricDensity q r branch side outer amp j x=
      D4BMIngoingFullCurrent.current (x 1) (x 3)
        (fun a => ofField (coexactField (sourceScalar q branch amp) a) x)
        (fun a => ofField (coexactField (leftScalar r side outer) a) x) (if j=0 then 0 else 1) := by
  let z : D4BMBackground.ExteriorPoint :=
    ⟨![x 0-D4BMIngoingCoordinates.tortoise (x 1),x 1,x 2,x 3],hr,hy⟩
  have hz : D4BMActualIngoingCurrent.ingoingPoint z.val=x := by
    ext i
    fin_cases i <;> simp [D4BMActualIngoingCurrent.ingoingPoint,z]
  have hpz : 0<D4BMActualIngoingCurrent.ingoingPoint z.val 0 := by rw [hz]; exact hp
  have he := D4BMOriginalGreenBoundary.original_metric_current_eq q r branch side outer amp z hpz
  rw [hz] at he
  have hS := D4BMOriginalGreenBoundary.originalPotential_exterior_smooth q branch amp x hp hr hy
  have hSJ (a : Fin 2) : ofField (coexactField (sourceScalar q branch amp) a) x=
      ofField (D4BMActualIngoingCurrent.originalStream q branch amp a) x := by
    apply ofField_germ
    filter_upwards [(hS.of_le (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)] with y hys
    exact source_coexact q branch amp y (hys.differentiableAt (by norm_num)) a
  have hWJ (a : Fin 2) : ofField (coexactField (leftScalar r side outer) a) x=
      ofField (leftStream r side outer a) x :=
    ofField_germ (left_coexact_germ r side outer x hr hy a)
  simp_rw [hSJ,hWJ]
  have h := congrArg (fun v : Fin 4 → ℂ => v (if j=0 then 0 else 1)) he
  calc
    _ = D4BMActualIngoingCurrent.metricIngoingCurrent z
        (D4BMActualIngoingCurrent.originalStaticStream q branch amp)
        (D4BMPhysicalModeAction.physicalLeftModeStream r (D4BMLeftModeRadialEquation.frequency r side) outer)
        (if j=0 then 0 else 1) := by fin_cases j <;> rfl
    _ = _ := h

/-- Both original temporal/radial metric-current densities with the full forcing retained. -/
theorem original_metric_density (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    metricDensity q r branch side outer amp j x=
      1/(x 1:ℂ)^(2 : ℕ)*(pairing (orbitDerivative (sourceScalar q branch amp) j) (scalarContact (leftScalar r side outer)) x-
        pairing (forcedContact q branch amp) (orbitDerivative (leftScalar r side outer) j) x) := by
  rw [metricDensity_stream q r branch side outer amp x hp hr hy j,
    orbit_current (D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp x hp hr hy)
      (leftScalar_smooth r side outer x hr hy) j]
  have hg := forcedContact_germ q branch amp x hp hr hy
  have hc (a : Fin 2) : coexactField (scalarContact (sourceScalar q branch amp)) a x=
      coexactField (forcedContact q branch amp) a x := by
    have hd (i : Fin 4) := congrArg (fun L => L (Pi.single i 1)) (hg.fderiv_eq (𝕜 := ℝ))
    fin_cases a
    · exact hd 3
    · exact congrArg Neg.neg (hd 2)
  simp only [pairing,hc,Fin.sum_univ_two]
  ring

/-- Exact finite-height metric/scalar comparison against the unchanged original left QNM.
The side jump, top flux and complete curved-core flux are explicit in `boundary`.
The full source contact is used; no eigenmode nonvanishing or limiting admission is assumed. -/
theorem original_metric_integral (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := leftScalar r side outer
    let A := orbitDerivative U j
    let B := scalarContact W
    let D := forcedContact q branch amp
    let E := orbitDerivative W j
    (∫ w in domain Y, metricDensity q r branch side outer amp j (slice p R (point w.1 w.2)))+
      1/(R:ℂ)^(2 : ℕ)*((∫ w in domain Y, scalarDensity A B (slice p R (point w.1 w.2)))-
        ∫ w in domain Y, scalarDensity D E (slice p R (point w.1 w.2)))=
      1/(R:ℂ)^(2 : ℕ)*(boundary (transfer A B 0) (transfer A B 1) p R Y-
        boundary (transfer D E 0) (transfer D E 1) p R Y) := by
  dsimp only
  let U := sourceScalar q branch amp
  let W := leftScalar r side outer
  let A := orbitDerivative U j
  let B := scalarContact W
  let D := forcedContact q branch amp
  let E := orbitDerivative W j
  have hU (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ ∞ U (slice p R z) :=
    D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp _ hp hr hz
  have hW (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ ∞ W (slice p R z) :=
    leftScalar_smooth r side outer _ hr hz
  have hA (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ ∞ A (slice p R z) := orbit_smooth (hU z hz) j
  have hB (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ ∞ B (slice p R z) := contact_smooth (hW z hz)
  have hD (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ ∞ D (slice p R z) := forcedContact_smooth q branch amp _ hp hr hz
  have hE (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ ∞ E (slice p R z) := orbit_smooth (hW z hz) j
  have hAB := pairing_integral A B p R hA hB hY
  have hDE := pairing_integral D E p R hD hE hY
  have he : (∫ w in domain Y, metricDensity q r branch side outer amp j (slice p R (point w.1 w.2)))=
      1/(R:ℂ)^(2 : ℕ)*((∫ w in domain Y, pairing A B (slice p R (point w.1 w.2)))-
        ∫ w in domain Y, pairing D E (slice p R (point w.1 w.2))) := by
    rw [← integral_sub (area_integrable (fun z hz => (pairing_smooth (hA z hz) (hB z hz)).continuousAt) Y)
      (area_integrable (fun z hz => (pairing_smooth (hD z hz) (hE z hz)).continuousAt) Y),← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hy : 0<(point w.1 w.2).im := by simpa [point] using (show 0<w.2 by linarith [hw.1.2.1])
    exact original_metric_density q r branch side outer amp _ hp hr hy j
  rw [he]
  linear_combination (1/(R:ℂ)^(2 : ℕ))*hAB-(1/(R:ℂ)^(2 : ℕ))*hDE



/-- Reusable full-boundary pairing identity for the independently varying physical reader. -/
theorem coexact_pairing_integral (A B : F) (p R : ℝ)
    (hA : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ A (slice p R z))
    (hB : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ ∞ B (slice p R z))
    {Y : ℝ} (hY : 1≤Y) :
    (∫ w in domain Y, pairing A B (slice p R (point w.1 w.2)))+
      (∫ w in domain Y, scalarDensity A B (slice p R (point w.1 w.2)))=
      boundary (transfer A B 0) (transfer A B 1) p R Y := pairing_integral A B p R hA hB hY

/-- Original orbit-current reduction for a smooth scalar source and reader family. -/
theorem coexact_orbit_current {U W : F} {x : P}
    (hU : ContDiffAt ℝ ∞ U x) (hW : ContDiffAt ℝ ∞ W x) (j : Fin 2) :
    D4BMIngoingFullCurrent.current (x 1) (x 3)
      (fun a => ofField (coexactField U a) x) (fun a => ofField (coexactField W a) x) (if j=0 then 0 else 1)=
      1/(x 1:ℂ)^(2 : ℕ)*(pairing (orbitDerivative U j) (scalarContact W) x-
        pairing (orbitDerivative W j) (scalarContact U) x) := orbit_current hU hW j

end RHTower.D4BMOriginalOrbitCurrent
