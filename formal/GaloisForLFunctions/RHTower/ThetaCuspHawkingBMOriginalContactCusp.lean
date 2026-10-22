import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricCusp

/-!
The complete original source contact and both metric cusp transfers.

The genuine physical angular restriction identifies the reconstructed source
Laplacian. Original potential and half-square jet bounds then give the full
contact coefficients, including the unchanged forcing and onset. Pairing with
the actual orbit-reader derivative closes the second metric transfer.

Both integrable top fluxes retain their signed difference and their derived
three-power subtraction. Original diagonal/reflected readers have no constant
cusp contribution. Time and exterior radius remain fixed; the prescribed
temporal/horizon/corner comparison and full temporal/metric/QNM matching are
not asserted here.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
namespace RHTower.D4BMOriginalContactCusp
open D4BMJointSource D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent
open D4BMOriginalSourceContact D4BMOriginalReaderEquation D4BMOriginalOrbitCusp
open D4BMOriginalCuspFlux D4BMOriginalMetricCusp D4BMMetricReconstruction
open D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev P := Fin 4 → ℝ
private abbrev A := Fin 2 → ℝ
local notation "L" => hyperbolicLaplacian

private def sectionPoint (p R : ℝ) (z : A) : P := ![p,R,z 0,z 1]

private theorem section_smooth (p R : ℝ) : ContDiff ℝ ∞ (sectionPoint p R) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sectionPoint] <;> fun_prop

private theorem coordinate_update {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    coordDeriv i f x=deriv (fun a => f (Function.update x i a)) (x i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

private theorem section_first (F : P → ℂ) (p R : ℝ) (z : A) (j : Fin 2)
    (hF : DifferentiableAt ℝ F (sectionPoint p R z)) :
    coordDeriv j (fun v => F (sectionPoint p R v)) z=
      coordDeriv (angularIndex j) F (sectionPoint p R z) := by
  have hs := (section_smooth p R).differentiable (by simp)
  change coordDeriv j (F ∘ sectionPoint p R) z=_
  rw [coordinate_update _ _ _ (hF.comp z hs.differentiableAt),coordinate_update _ _ _ hF]
  fin_cases j <;> simp [sectionPoint,angularIndex]
  all_goals
    congr 1
    funext a
    congr 1
    ext i
    fin_cases i <;> simp

private theorem section_second (F : P → ℂ) (p R : ℝ) (z : A) (j : Fin 2)
    (hF : ContDiffAt ℝ ∞ F (sectionPoint p R z)) :
    coordDeriv j (coordDeriv j (fun v => F (sectionPoint p R v))) z=
      coordDeriv (angularIndex j) (coordDeriv (angularIndex j) F) (sectionPoint p R z) := by
  have h1 : ContDiffAt ℝ 1 F (sectionPoint p R z) := hF.of_le (by simp)
  have he : coordDeriv j (fun v => F (sectionPoint p R v))=ᶠ[𝓝 z]
      fun v => coordDeriv (angularIndex j) F (sectionPoint p R v) := by
    filter_upwards [(section_smooth p R).continuous.continuousAt.eventually
      (h1.eventually (by norm_num))] with v hv
    exact section_first F p R v j (hv.differentiableAt (by norm_num))
  have hd : ContDiffAt ℝ ∞ (coordDeriv (angularIndex j) F) (sectionPoint p R z) :=
    coordDeriv_contDiffAt hF (by simp) _
  change fderiv ℝ (coordDeriv j (fun v => F (sectionPoint p R v))) z (Pi.single j 1)=_
  rw [he.fderiv_eq]
  exact section_first _ p R z j (hd.differentiableAt (by simp))

private theorem section_laplacian (F : P → ℂ) (p R : ℝ) (z : A)
    (hF : ContDiffAt ℝ ∞ F (sectionPoint p R z)) :
    L (fun v => F (sectionPoint p R v)) z=angularLap F (sectionPoint p R z) := by
  dsimp only [hyperbolicLaplacian]
  rw [section_second F p R z 0 hF,section_second F p R z 1 hF]
  rfl

/-- Angular restriction of the actual reconstructed source retains its radius factor. -/
theorem source_angular_restriction (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p R : ℝ) (z : A) (hp : 0<p) (hr : 1<R) (hy : 0<z 1) :
    angularLap (sourceScalar q br amp) ![p,R,z 0,z 1]=
      (R:ℂ)*L (D4BMOriginalAngularGreen.source q br amp p
        (p-2*D4BMIngoingCoordinates.tortoise R)) z := by
  have hf := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q br amp
    (sectionPoint p R z) hp hr hy
  change angularLap (sourceScalar q br amp) (sectionPoint p R z)=_
  rw [← section_laplacian _ p R z hf]
  have he : (fun v => sourceScalar q br amp (sectionPoint p R v))=
      fun v => (R:ℂ)*D4BMOriginalAngularGreen.source q br amp p
        (p-2*D4BMIngoingCoordinates.tortoise R) v := rfl
  rw [he]
  have hc : ContDiffAt ℝ ∞ (fun v : A => (v 0,Real.log (v 1))) z :=
    (contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.prodMk
      ((contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hy.ne')
  have hs := (D4BMOriginalCausalPotential.originalPotential_angular_smooth q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R)).contDiffAt.comp z hc
  have hs2 : ContDiffAt ℝ 2 (D4BMOriginalAngularGreen.source q br amp p
      (p-2*D4BMIngoingCoordinates.tortoise R)) z :=
    hs.of_le (WithTop.coe_le_coe.mpr le_top)
  exact hyperbolicLaplacian_const_mul hs2 (R:ℂ)


private theorem exp_cpow (a : ℂ) (k : ℝ) :
    (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring

private theorem positive_nhds {z : A} (hy : 0<z 1) : domain∈𝓝 z :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hy

theorem power_laplacian_sum {ι : Type*} (s : Finset ι) (F : ι → A → ℂ)
    {z : A} (hF : ∀ i∈s, ContDiffAt ℝ 2 (F i) z) :
    L (fun x => ∑ i∈s, F i x) z=∑ i∈s, L (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (z 1:ℂ)^(2 : ℕ)*(fderiv ℝ (fun x => fderiv ℝ (fun _ : A => (0:ℂ)) x (Pi.single 0 1)) z (Pi.single 0 1)+
      fderiv ℝ (fun x => fderiv ℝ (fun _ : A => (0:ℂ)) x (Pi.single 1 1)) z (Pi.single 1 1))=0
    simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hyperbolicLaplacian_add (hF i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun j hj => hF j (Finset.mem_insert_of_mem hj)))).trans
        (congrArg (fun a => L (F i) z+a) (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))))

theorem principal_laplacian (q : XiZeroCopy) (z : A) (hy : 0<z 1) :
    L (principalSquare q) z=∑ i : Fin 3, principalAmplitude q i*
      principalExponent q i*(principalExponent q i-1)*(z 1:ℂ)^(principalExponent q i) := by
  have he : principalSquare q=ᶠ[𝓝 z] fun v => ∑ i : Fin 3,
      principalAmplitude q i*(v 1:ℂ)^(principalExponent q i) := by
    filter_upwards [positive_nhds hy] with v hv
    exact principalSquare_expansion q v hv
  have hs (i : Fin 3) : ContDiffAt ℝ 2
      (fun v : A => principalAmplitude q i*(v 1:ℂ)^(principalExponent q i)) z :=
    contDiffAt_const.mul ((height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt (positive_nhds hy))
  rw [hyperbolicLaplacian_congr he,power_laplacian_sum Finset.univ _ (fun i _ => hs i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hyperbolicLaplacian_const_mul
    ((height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt (positive_nhds hy)),
    height_cpow_hyperbolicLaplacian _ z hy]
  ring

theorem square_decomposition (q : XiZeroCopy) :
    D4BMModularCore.fullSquarePotential q=fun z => principalSquare q z+
      (1/2:ℂ)*D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q) z := by
  funext z
  dsimp [D4BMModularCore.fullSquarePotential,principalSquare,D4BMGlobalAngularResponse.squareRemainder]
  ring

theorem square_laplacian_decomposition (q : XiZeroCopy) (z : A) (hy : 0<z 1) :
    L (D4BMModularCore.fullSquarePotential q) z=L (principalSquare q) z+
      (1/2:ℂ)*L (D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q)) z := by
  have hp : ContDiffAt ℝ 2 (principalSquare q) z :=
    ((principalSquare_smooth q).contDiffAt (positive_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hs : ContDiffAt ℝ 2
      (D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q)) z :=
    ((D4BMSquareCuspJets.squareRemainder_jet_smooth (D4BMGlobalAngularResponse.center q) []).contDiffAt
      (positive_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [square_decomposition q,hyperbolicLaplacian_add hp (contDiffAt_const.mul hs),
    hyperbolicLaplacian_const_mul hs]

theorem square_jet_exp (q : XiZeroCopy) (word : List (Fin 2)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      D4BMSquareCuspJets.coordinateJet word
        (D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q))
        ![X k,Real.exp k]) atTop (𝓝 0) := by
  have h := (D4BMSquareCuspJets.squareRemainder_jet_tendsto_zero
    (D4BMGlobalAngularResponse.center q) w word (fun y => X (Real.log y))).comp Real.tendsto_exp_atTop
  simpa only [Function.comp_def,Real.log_exp,exp_cpow] using h

theorem square_expansion (q : XiZeroCopy) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (D4BMModularCore.fullSquarePotential q ![X k,Real.exp k]-
        ∑ i : Fin 3, principalAmplitude q i*Complex.exp (principalExponent q i*(k:ℂ))))
      atTop (𝓝 0) := by
  have h := (square_jet_exp q [] X w).const_mul (1/2:ℂ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  rw [square_decomposition q]
  simp only [principalSquare_expansion q ![X k,Real.exp k] (Real.exp_pos k),Matrix.cons_val,exp_cpow,
    D4BMSquareCuspJets.coordinateJet]
  ring

theorem square_laplacian_expansion (q : XiZeroCopy) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (L (D4BMModularCore.fullSquarePotential q) ![X k,Real.exp k]-
        ∑ i : Fin 3, principalAmplitude q i*principalExponent q i*(principalExponent q i-1)*
          Complex.exp (principalExponent q i*(k:ℂ)))) atTop (𝓝 0) := by
  have h := ((square_jet_exp q [0,0] X (w+2)).add
    (square_jet_exp q [1,1] X (w+2))).const_mul (1/2:ℂ)
  simp only [zero_add,mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  rw [square_laplacian_decomposition q _ (Real.exp_pos k),principal_laplacian q _ (Real.exp_pos k)]
  simp only [Matrix.cons_val,exp_cpow,D4BMSquareCuspJets.coordinateJet]
  have he : Complex.exp ((w+2)*(k:ℂ))=Complex.exp (w*(k:ℂ))*(Real.exp k:ℂ)^(2 : ℕ) := by
    rw [show (w+2)*(k:ℂ)=w*(k:ℂ)+2*(k:ℂ) by ring,Complex.exp_add,
      ← exp_cpow (2:ℂ) k,Complex.cpow_two]
  rw [he]
  dsimp only [hyperbolicLaplacian]
  simp only [Matrix.cons_val]
  ring

private theorem source_expansion (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (D4BMOriginalAngularGreen.source q br amp p v ![X k,Real.exp k]-
        ∑ i : Fin 3, D4BMOriginalCuspJets.coefficient q br amp p v i*
          Complex.exp (principalExponent q i*(k:ℂ)))) atTop (𝓝 0) := by
  have h := D4BMOriginalCuspJets.original_remainder_jet_tendsto_zero q br amp p v [] X w
  simpa only [D4BMOriginalAngularGreen.source,D4BMSquareCuspJets.coordinateJet,
    D4BMOriginalCuspJets.remainder,D4BMOriginalCuspJets.principal,Matrix.cons_val,Real.log_exp] using h

/-- Principal coefficient of the complete original contact, including its forcing. -/
def contactCoefficient (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p R : ℝ) (i : Fin 3) : ℂ :=
  (principalExponent q i*(principalExponent q i-1)-2)*principalCoefficient q br amp p R i+
    (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*(forcingValueCoefficient q br amp p R+
      forcingLaplacianCoefficient q br amp p R*principalExponent q i*(principalExponent q i-1))*
        principalAmplitude q i

/-- The actual source contact has the derived three-power expansion at every exterior point. -/
theorem original_contact_expansion (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (forcedContact q br amp ![p,R,X k,Real.exp k]-
        ∑ i : Fin 3, contactCoefficient q br amp p R i*
          Complex.exp (principalExponent q i*(k:ℂ)))) atTop (𝓝 0) := by
  have ht : D4BMIngoingCoordinates.tortoise R<0 := by
    have hl := Real.log_lt_log (show 0<R-1 by linarith) (show R-1<R+1 by linarith)
    dsimp [D4BMIngoingCoordinates.tortoise]
    linarith
  let v : Ici (0:ℝ) := ⟨p-2*D4BMIngoingCoordinates.tortoise R,by
    show 0≤p-2*D4BMIngoingCoordinates.tortoise R
    linarith⟩
  let pp : Ici (0:ℝ) := ⟨p,hp.le⟩
  have hs := source_expansion q br amp pp v X w
  have hl := original_source_laplacian_expansion q br amp pp v X w
  have hP := square_expansion q X w
  have hL := square_laplacian_expansion q X w
  have h := ((hl.const_mul (R:ℂ)).sub ((hs.const_mul (R:ℂ)).const_mul 2)).add
    (((hP.const_mul (forcingValueCoefficient q br amp p R)).add
      (hL.const_mul (forcingLaplacianCoefficient q br amp p R))).const_mul
        ((R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)))
  simp only [mul_zero,sub_zero,zero_add] at h
  apply h.congr'
  filter_upwards [] with k
  have hRestr := source_angular_restriction q br amp p R ![X k,Real.exp k] hp hr (Real.exp_pos k)
  have hForce := original_forcing_laplacian q br amp ![p,R,X k,Real.exp k] (Real.exp_pos k)
  simp only [Matrix.cons_val] at hRestr hForce
  rw [forcedContact,hRestr,hForce,
    D4BMHorizon.scalarLaplacian_eq _ ![X k,Real.exp k] (Real.exp_pos k)]
  change _=Complex.exp (w*(k:ℂ))*
    ((R:ℂ)*L (D4BMOriginalAngularGreen.source q br amp p v) ![X k,Real.exp k]-
      2*((R:ℂ)*D4BMOriginalAngularGreen.source q br amp p v ![X k,Real.exp k])+
      (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*(forcingValueCoefficient q br amp p R*
        D4BMModularCore.fullSquarePotential q ![X k,Real.exp k]+
        forcingLaplacianCoefficient q br amp p R*L (D4BMModularCore.fullSquarePotential q) ![X k,Real.exp k])-
      ∑ i : Fin 3, contactCoefficient q br amp p R i*Complex.exp (principalExponent q i*(k:ℂ)))
  simp only [Fin.sum_univ_three,contactCoefficient,principalCoefficient,pp,v]
  ring

/-- Principal coefficient of the second complete metric top transfer. -/
def secondFluxCoefficient (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (j : Fin 2) (p R : ℝ) (i : Fin 3) : ℂ :=
  readerOrbitAmplitude r side outer j p R*
    (contactCoefficient q br amp p R i*readerCoefficient r*readerExponent r)

/-- Full contact and genuine orbit-reader differentiation determine the second cusp transfer. -/
theorem second_metric_cusp_expansion (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 2) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2, Complex.exp (w*(k:ℂ))*
      (transfer (forcedContact q br amp) (orbitDerivative (leftScalar r side outer) j)
        1 ![p,R,X,Real.exp k]-∑ i : Fin 3, secondFluxCoefficient q r br side outer amp j p R i*
          Complex.exp (fluxExponent q r i*(k:ℂ)))) atTop (𝓝 0) := by
  let b := readerOrbitAmplitude r side outer j p R
  have ht := normal_flux_integral_of_expansion q r
    (fun z : A => forcedContact q br amp ![p,R,z 0,z 1])
    (contactCoefficient q br amp p R)
    (fun X w => original_contact_expansion q br amp p R hp hr X w) w
  have h := ht.const_mul b
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  have hs : (∑ i : Fin 3, secondFluxCoefficient q r br side outer amp j p R i*
      Complex.exp (fluxExponent q r i*(k:ℂ)))=
      b*∑ i : Fin 3, contactCoefficient q br amp p R i*readerCoefficient r*
        readerExponent r*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    simp only [secondFluxCoefficient,b,Finset.mul_sum,mul_assoc]
  rw [hs,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro X _
  change b*(Complex.exp (w*(k:ℂ))*
    (forcedContact q br amp ![p,R,X,Real.exp k]*
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![X,Real.exp k]-_))=
    Complex.exp (w*(k:ℂ))*(forcedContact q br amp ![p,R,X,Real.exp k]*
      coordDeriv 3 (orbitDerivative (leftScalar r side outer) j) ![p,R,X,Real.exp k]-_)
  rw [reader_orbit_normal r side outer j ![p,R,X,Real.exp k] hr (Real.exp_pos k)]
  simp only [Matrix.cons_val]
  dsimp only [b]
  ring

/-- The two original metric transfers retain their signed difference. -/
def metricFluxCoefficient (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (j : Fin 2) (p R : ℝ) (i : Fin 3) : ℂ :=
  (1/(R:ℂ)^(2 : ℕ))*(firstFluxCoefficient q r br side outer amp j p R i-
    secondFluxCoefficient q r br side outer amp j p R i)

/-- Neither original diagonal/reflected transfer contributes a constant cusp term. -/
theorem complete_metric_cusp_constant (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (p R : ℝ) (j : Fin 2)
    (h : (r.1:ℂ).im=(q.1:ℂ).im ∨ (r.1:ℂ).im= -(q.1:ℂ).im) :
    (∑ i : Fin 3, if fluxExponent q r i=0 then
      metricFluxCoefficient q r br side outer amp j p R i else 0)=0 := by
  classical
  simp only [fluxExponent_nonzero_original q r h,if_false,Finset.sum_const_zero]

private theorem partial_smooth {F : P → ℂ} {x : P}
    (hF : ContDiffAt ℝ ∞ F x) (i : Fin 4) : ContDiffAt ℝ ∞ (coordDeriv i F) x :=
  coordDeriv_contDiffAt hF (by simp) i

private theorem orbit_smooth {U : P → ℂ} {x : P} (hU : ContDiffAt ℝ ∞ U x) (j : Fin 2) :
    ContDiffAt ℝ ∞ (orbitDerivative U j) x := by
  have hr : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  fin_cases j
  · exact partial_smooth hU 1
  · exact (((hr.pow 2).sub contDiffAt_const).mul (partial_smooth hU 1)).add (partial_smooth hU 0)

private theorem contact_smooth {U : P → ℂ} {x : P} (hU : ContDiffAt ℝ ∞ U x) :
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

private theorem forced_smooth (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    ContDiffAt ℝ ∞ (forcedContact q br amp) x := by
  have he : scalarContact (sourceScalar q br amp)=ᶠ[𝓝 x] forcedContact q br amp := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hzp hzr hzy
    exact original_scalar_contact q br amp z hzp hzr hzy
  exact (contact_smooth (D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth
    q br amp x hp hr hy)).congr_of_eventuallyEq he.symm

theorem transfer_subtraction (F G : P → ℂ) (p R Y : ℝ) (c : ℂ)
    (hF : ∀ X : ℝ, ContDiffAt ℝ ∞ F ![p,R,X,Y])
    (hG : ∀ X : ℝ, ContDiffAt ℝ ∞ G ![p,R,X,Y]) :
    (∫ X in (-1/2:ℝ)..1/2, transfer F G 1 ![p,R,X,Y]-c)=
      D4BMOriginalModularOrbit.topFlux F G p R Y-c := by
  have hm : Continuous (fun X : ℝ => (![p,R,X,Y]:P)) := by fun_prop
  have hc : Continuous (fun X : ℝ => transfer F G 1 ![p,R,X,Y]) := by
    apply continuous_iff_continuousAt.mpr
    intro X
    change ContinuousAt ((fun z : P => F z*coordDeriv 3 G z) ∘
      (fun u : ℝ => (![p,R,u,Y]:P))) X
    exact ((hF X).continuousAt.mul (partial_smooth (hG X) 3).continuousAt).comp
      (f:=fun u : ℝ => (![p,R,u,Y]:P)) hm.continuousAt
  have hslice (X : ℝ) : slice p R (GaloisForLFunctions.RHTower.SelbergMaassMean.point X Y)=![p,R,X,Y] := by
    simp [slice,GaloisForLFunctions.RHTower.SelbergMaassMean.point]
  unfold D4BMOriginalModularOrbit.topFlux
  simp_rw [hslice]
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const]
  norm_num [smul_eq_mul]

/-- Both complete original metric top transfers have the prescribed finite cusp part. -/
theorem complete_metric_top_cusp_limit (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 2) :
    Tendsto (fun k : ℝ => (1/(R:ℂ)^(2 : ℕ))*
      (D4BMOriginalModularOrbit.topFlux (orbitDerivative (sourceScalar q br amp) j)
        (scalarContact (leftScalar r side outer)) p R (Real.exp k)-
      D4BMOriginalModularOrbit.topFlux (forcedContact q br amp)
        (orbitDerivative (leftScalar r side outer) j) p R (Real.exp k))-
      ∑ i : Fin 3, metricFluxCoefficient q r br side outer amp j p R i*
        Complex.exp (fluxExponent q r i*(k:ℂ))) atTop (𝓝 0) := by
  have h1 := first_metric_cusp_expansion q r br side outer amp p R hp hr j 0
  have h2 := second_metric_cusp_expansion q r br side outer amp p R hp hr j 0
  simp only [zero_mul,Complex.exp_zero,one_mul] at h1 h2
  have h := (h1.sub h2).const_mul (1/(R:ℂ)^(2 : ℕ))
  simp only [sub_zero,mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  have hU (X : ℝ) := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth
    q br amp ![p,R,X,Real.exp k] hp hr (Real.exp_pos k)
  have hW (X : ℝ) := leftScalar_smooth r side outer ![p,R,X,Real.exp k] hr (Real.exp_pos k)
  rw [transfer_subtraction _ _ p R (Real.exp k) _ (fun X => orbit_smooth (hU X) j)
      (fun X => contact_smooth (hW X)),
    transfer_subtraction _ _ p R (Real.exp k) _
      (fun X => forced_smooth q br amp ![p,R,X,Real.exp k] hp hr (Real.exp_pos k))
      (fun X => orbit_smooth (hW X) j)]
  simp only [metricFluxCoefficient,Fin.sum_univ_three]
  ring


/-- The actual reconstructed source's normal derivative includes its radius factor. -/
theorem original_source_normal (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p R : ℝ) (z : A) (hp : 0<p) (hr : 1<R) (hy : 0<z 1) :
    coordDeriv 3 (sourceScalar q br amp) ![p,R,z 0,z 1]=
      (R:ℂ)*coordDeriv 1 (D4BMOriginalAngularGreen.source q br amp p
        (p-2*D4BMIngoingCoordinates.tortoise R)) z := by
  have hf := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q br amp
    (sectionPoint p R z) hp hr hy
  have hc : ContDiffAt ℝ ∞ (fun v : A => (v 0,Real.log (v 1))) z :=
    (contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.prodMk
      ((contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hy.ne')
  have hs := (D4BMOriginalCausalPotential.originalPotential_angular_smooth q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R)).contDiffAt.comp z hc
  change ContDiffAt ℝ ∞ (D4BMOriginalAngularGreen.source q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R)) z at hs
  have h := section_first (sourceScalar q br amp) p R z 1 (hf.differentiableAt (by simp))
  change fderiv ℝ (fun v => (R:ℂ)*D4BMOriginalAngularGreen.source q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R) v) z (Pi.single 1 1)=
    coordDeriv 3 (sourceScalar q br amp) ![p,R,z 0,z 1] at h
  rw [fderiv_const_mul (hs.differentiableAt (by simp))] at h
  exact h.symm

private theorem original_green_transfer (q r : XiZeroCopy) (br side outer : Bool)
    (amp : ℂ) (p R X Y : ℝ) (hp : 0<p) (hr : 1<R) (hy : 0<Y) (j : Fin 2) :
    transfer (orbitDerivative (leftScalar r side outer) j) (sourceScalar q br amp) 1 ![p,R,X,Y]-
      transfer (sourceScalar q br amp) (orbitDerivative (leftScalar r side outer) j) 1 ![p,R,X,Y]=
    ((R:ℂ)*readerOrbitAmplitude r side outer j p R)*
      scalarGreenFlux q r br amp p (p-2*D4BMIngoingCoordinates.tortoise R) ![X,Y] := by
  change orbitDerivative (leftScalar r side outer) j ![p,R,X,Y]*
      coordDeriv 3 (sourceScalar q br amp) ![p,R,X,Y]-
    sourceScalar q br amp ![p,R,X,Y]*
      coordDeriv 3 (orbitDerivative (leftScalar r side outer) j) ![p,R,X,Y]=_
  have hn := original_source_normal q br amp p R ![X,Y] hp hr hy
  simp only [Matrix.cons_val] at hn
  rw [reader_orbit_value r side outer j ![p,R,X,Y] hr hy,hn,
    reader_orbit_normal r side outer j ![p,R,X,Y] hr hy]
  have hs : sourceScalar q br amp ![p,R,X,Y]=(R:ℂ)*
      D4BMOriginalAngularGreen.source q br amp p (p-2*D4BMIngoingCoordinates.tortoise R) ![X,Y] := rfl
  rw [hs]
  simp only [scalarGreenFlux,Matrix.cons_val]
  ring

/-- The extra Green transfer retains the actual orbit-reader amplitude. -/
def greenOrbitCoefficient (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (j : Fin 2) (p R : ℝ) (i : Fin 3) : ℂ :=
  ((R:ℂ)*readerOrbitAmplitude r side outer j p R)*
    scalarGreenCoefficient q r br amp p (p-2*D4BMIngoingCoordinates.tortoise R) i

private theorem original_green_cusp_expansion (q r : XiZeroCopy) (br side outer : Bool)
    (amp : ℂ) (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 2) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2, Complex.exp (w*(k:ℂ))*
      (transfer (orbitDerivative (leftScalar r side outer) j) (sourceScalar q br amp) 1 ![p,R,X,Real.exp k]-
        transfer (sourceScalar q br amp) (orbitDerivative (leftScalar r side outer) j) 1 ![p,R,X,Real.exp k]-
        ∑ i : Fin 3, greenOrbitCoefficient q r br side outer amp j p R i*
          Complex.exp (fluxExponent q r i*(k:ℂ)))) atTop (𝓝 0) := by
  have hlog := Real.log_lt_log (show 0<R-1 by linarith) (show R-1<R+1 by linarith)
  have hv : 0≤p-2*D4BMIngoingCoordinates.tortoise R := by
    dsimp [D4BMIngoingCoordinates.tortoise]
    linarith
  let b := (R:ℂ)*readerOrbitAmplitude r side outer j p R
  have h := (original_scalarGreenFlux_expansion q r br amp ⟨p,hp.le⟩
    ⟨p-2*D4BMIngoingCoordinates.tortoise R,hv⟩ w).const_mul b
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro X _
  dsimp only
  rw [original_green_transfer q r br side outer amp p R X (Real.exp k) hp hr (Real.exp_pos k) j]
  simp only [greenOrbitCoefficient,← Finset.mul_sum,mul_assoc]
  dsimp only [b]
  ring

/-- Complete metric cusp coefficients include the scalar Green transposition. -/
def completeFluxCoefficient (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (j : Fin 2) (p R : ℝ) (i : Fin 3) : ℂ :=
  metricFluxCoefficient q r br side outer amp j p R i+
    (D4BMLeftModeRadialEquation.eigenvalue r/(R:ℂ)^(2 : ℕ))*
      greenOrbitCoefficient q r br side outer amp j p R i

/-- All three original transfers have their complete prescribed cusp subtraction. -/
theorem complete_scalar_top_cusp_limit (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 2) :
    Tendsto (fun k : ℝ => (1/(R:ℂ)^(2 : ℕ))*
      D4BMOriginalModularOrbit.completeTopFlux q r br side outer amp j p R (Real.exp k)-
      ∑ i : Fin 3, completeFluxCoefficient q r br side outer amp j p R i*
        Complex.exp (fluxExponent q r i*(k:ℂ))) atTop (𝓝 0) := by
  have hg := original_green_cusp_expansion q r br side outer amp p R hp hr j 0
  simp only [zero_mul,Complex.exp_zero,one_mul] at hg
  have hc := hg.const_mul (D4BMLeftModeRadialEquation.eigenvalue r/(R:ℂ)^(2 : ℕ))
  simp only [mul_zero] at hc
  have h := (complete_metric_top_cusp_limit q r br side outer amp p R hp hr j).add hc
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with k
  have hU (X : ℝ) := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth
    q br amp ![p,R,X,Real.exp k] hp hr (Real.exp_pos k)
  have hW (X : ℝ) := leftScalar_smooth r side outer ![p,R,X,Real.exp k] hr (Real.exp_pos k)
  have he : (∫ X in (-1/2:ℝ)..1/2,
      transfer (orbitDerivative (leftScalar r side outer) j) (sourceScalar q br amp) 1 ![p,R,X,Real.exp k]-
      transfer (sourceScalar q br amp) (orbitDerivative (leftScalar r side outer) j) 1 ![p,R,X,Real.exp k]-
      ∑ i : Fin 3, greenOrbitCoefficient q r br side outer amp j p R i*Complex.exp (fluxExponent q r i*(k:ℂ)))=
    D4BMOriginalModularOrbit.topFlux (orbitDerivative (leftScalar r side outer) j)
      (sourceScalar q br amp) p R (Real.exp k)-
    D4BMOriginalModularOrbit.topFlux (sourceScalar q br amp)
      (orbitDerivative (leftScalar r side outer) j) p R (Real.exp k)-
      ∑ i : Fin 3, greenOrbitCoefficient q r br side outer amp j p R i*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    have hm : Continuous (fun X : ℝ => (![p,R,X,Real.exp k]:P)) := by fun_prop
    have hT (A B : P → ℂ) (ha : ∀ X, ContDiffAt ℝ ∞ A ![p,R,X,Real.exp k])
        (hb : ∀ X, ContDiffAt ℝ ∞ B ![p,R,X,Real.exp k]) :
        IntervalIntegrable (fun X => transfer A B 1 ![p,R,X,Real.exp k]) volume (-1/2:ℝ) (1/2:ℝ) := by
      apply Continuous.intervalIntegrable
      apply continuous_iff_continuousAt.mpr
      intro X
      exact ((ha X).continuousAt.mul (partial_smooth (hb X) 3).continuousAt).comp
        (f:=fun X : ℝ => (![p,R,X,Real.exp k]:P)) hm.continuousAt
    have h1 := hT _ _ (fun X => orbit_smooth (hW X) j) hU
    have h2 := hT _ _ hU (fun X => orbit_smooth (hW X) j)
    rw [intervalIntegral.integral_sub (h1.sub h2) intervalIntegrable_const,
      intervalIntegral.integral_sub h1 h2,intervalIntegral.integral_const]
    have ht1 := transfer_subtraction _ _ p R (Real.exp k) 0 (fun X => orbit_smooth (hW X) j) hU
    have ht2 := transfer_subtraction _ _ p R (Real.exp k) 0 hU (fun X => orbit_smooth (hW X) j)
    simp only [sub_zero] at ht1 ht2
    rw [ht1,ht2]
    norm_num [smul_eq_mul]
  rw [he]
  simp only [D4BMOriginalModularOrbit.completeTopFlux,completeFluxCoefficient,Fin.sum_univ_three]
  ring

/-- The original diagonal/reflected reader has no constant contribution from any of the three transfers. -/
theorem complete_scalar_cusp_constant (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (p R : ℝ) (j : Fin 2)
    (h : (r.1:ℂ).im=(q.1:ℂ).im ∨ (r.1:ℂ).im= -(q.1:ℂ).im) :
    (∑ i : Fin 3, if fluxExponent q r i=0 then
      completeFluxCoefficient q r br side outer amp j p R i else 0)=0 := by
  classical
  simp only [fluxExponent_nonzero_original q r h,if_false,Finset.sum_const_zero]


/-- The finite part retains exactly the constant exponent for an independent reader. -/
theorem complete_scalar_top_finitePart (q r : XiZeroCopy) (br side outer : Bool)
    (amp : ℂ) (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 2) :
    Tendsto (fun k : ℝ => (1/(R:ℂ)^(2 : ℕ))*
      D4BMOriginalModularOrbit.completeTopFlux q r br side outer amp j p R (Real.exp k)-
      ∑ i : Fin 3, if fluxExponent q r i=0 then 0 else
        completeFluxCoefficient q r br side outer amp j p R i*
          Complex.exp (fluxExponent q r i*(k:ℂ))) atTop
      (𝓝 (∑ i : Fin 3, if fluxExponent q r i=0 then
        completeFluxCoefficient q r br side outer amp j p R i else 0)) := by
  classical
  have h := (complete_scalar_top_cusp_limit q r br side outer amp p R hp hr j).add_const
    (∑ i : Fin 3, if fluxExponent q r i=0 then completeFluxCoefficient q r br side outer amp j p R i else 0)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with k
  have hs : (∑ i : Fin 3, completeFluxCoefficient q r br side outer amp j p R i*
      Complex.exp (fluxExponent q r i*(k:ℂ)))=
    (∑ i : Fin 3, if fluxExponent q r i=0 then 0 else
      completeFluxCoefficient q r br side outer amp j p R i*Complex.exp (fluxExponent q r i*(k:ℂ)))+
    (∑ i : Fin 3, if fluxExponent q r i=0 then completeFluxCoefficient q r br side outer amp j p R i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : fluxExponent q r i=0 <;> simp [hi]
  rw [hs]
  ring

/-- The actual static metric current and forced scalar periods differ only by
the three derived cusp powers. This fixes the angular subtraction before any
infinite-time or horizon limit. -/
theorem original_static_cusp_transfer (q r : XiZeroCopy) (br side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) :
    let U := sourceScalar q br amp
    let W := leftScalar r side outer
    let f := (R:ℂ)^(2 : ℕ)-1
    let mu := D4BMLeftModeRadialEquation.eigenvalue r
    let w := D4BMLeftModeRadialEquation.frequency r side
    Tendsto (fun k : ℝ =>
      (∫ z in GaloisForLFunctions.RHTower.SelbergModularDomainSlices.domain (Real.exp k),
        metricDensity q r br side outer amp 0 (slice p R (GaloisForLFunctions.RHTower.SelbergMaassMean.point z.1 z.2)))-
      (∫ z in GaloisForLFunctions.RHTower.SelbergModularDomainSlices.domain (Real.exp k),
        metricDensity q r br side outer amp 1 (slice p R (GaloisForLFunctions.RHTower.SelbergMaassMean.point z.1 z.2)))/f-
      (mu*(mu-2)/((R:ℂ)^(2 : ℕ)*f)*
        (scalarPeriod (coordDeriv 0 U) W p R (Real.exp k)+
          w*scalarPeriod U W p R (Real.exp k))+
        mu*(R:ℂ)*w/f^(2 : ℕ)*scalarPeriod
          (D4BMOriginalSourceContact.originalForcing q br amp) W p R (Real.exp k))-
      ∑ i : Fin 3, (completeFluxCoefficient q r br side outer amp 0 p R i-
        completeFluxCoefficient q r br side outer amp 1 p R i/f)*
          Complex.exp (fluxExponent q r i*(k:ℂ))) atTop (𝓝 0) := by
  dsimp only
  have h := (complete_scalar_top_cusp_limit q r br side outer amp p R hp hr 0).sub
    ((complete_scalar_top_cusp_limit q r br side outer amp p R hp hr 1).div_const ((R:ℂ)^(2 : ℕ)-1))
  simp only [zero_div,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  rw [D4BMOriginalModularOrbit.original_static_metric_scalar_integral q r br side outer amp
    p R hp hr (Real.one_le_exp hk)]
  simp only [Fin.sum_univ_three]
  ring

end
end RHTower.D4BMOriginalContactCusp
