import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonModeOuterUniformBound
import GaloisForLFunctions.HTGeometry.TwistedRadialDerivative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamMetricField

/-!
# Original left QNM metric equation

Both continued original radial modes at the prescribed fundamental frequencies
provides a smooth radial profile and all three required radius derivatives.
Its complete metric two-jet is realized by an actual symmetric field. Both
master expressions reduce to the literal angular defect, which vanishes by
the coexact source equation. The full Einstein equation is evaluated on the
original time-zero action slice; no boundary cancellation is asserted.
-/

set_option autoImplicit false
open scoped ContDiff
namespace RHTower.D4BMLeftModeRadialEquation
open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMJointWave D4BMPhysicalModeAction
noncomputable section

abbrev frequency (q : XiZeroCopy) (side : Bool) : ℂ := physicalFundamentalFrequency q side
abbrev eigenvalue (q : XiZeroCopy) : ℂ := physicalAngularParameter q^2-1/4
abbrev profile (q : XiZeroCopy) (side outer : Bool) : ℝ → ℂ :=
  tortoiseMode outer (frequency q side) (physicalRadialFrequency q)
abbrev profileFirst (q : XiZeroCopy) (side outer : Bool) : ℝ → ℂ :=
  tortoiseModeFirst outer (frequency q side) (physicalRadialFrequency q)
def potential (q : XiZeroCopy) (side : Bool) (t : ℝ) : ℂ :=
  frequency q side^2-eigenvalue q*(horizonCoordinate t:ℂ)
def profileSecond (q : XiZeroCopy) (side outer : Bool) (t : ℝ) : ℂ :=
  potential q side t*profile q side outer t
def profileThird (q : XiZeroCopy) (side outer : Bool) (t : ℝ) : ℂ :=
  -(eigenvalue q*(coordinateFirst t:ℂ))*profile q side outer t+
    potential q side t*profileFirst q side outer t

private theorem potential_smooth (q : XiZeroCopy) (side : Bool) :
    ContDiff ℝ ∞ (potential q side) := by
  have hc (t : ℝ) : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  unfold potential horizonCoordinate radialUnit
  fun_prop

private theorem continued_mode_derivatives (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    HasDerivAt (profile q side outer) (profileFirst q side outer t) t ∧
    HasDerivAt (profileFirst q side outer)
      (tortoiseModeSecond outer (frequency q side) (physicalRadialFrequency q) t) t := by
  cases outer
  · exact tortoiseMode_hasDerivAt_continued (frequency q side) (physicalRadialFrequency q) t t.property
  · have hd := D4BMLaplaceRadial.normalizable_derivatives_continued
      (w := frequency q side) (chi := physicalRadialFrequency q) (horizonCoordinate_interior t t.property)
    have hc := horizonCoordinate_hasDerivAt t
    have hF := hd.1.scomp (t:ℝ) hc
    have hF1 := hd.2.scomp (t:ℝ) hc
    constructor
    · simpa only [profile,profileFirst,tortoiseMode,tortoiseModeFirst,radialMode,radialModeFirst,
        if_true,Function.comp_def,Complex.real_smul] using! hF
    · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul hF1).congr_deriv
      dsimp only [tortoiseModeSecond,radialModeFirst,radialModeSecond,if_true,Function.comp_apply]
      simp only [Complex.real_smul,↓reduceIte]
      ring

private theorem continued_mode_equation (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    tortoiseModeSecond outer (frequency q side) (physicalRadialFrequency q) t =
      (frequency q side^2+(horizonCoordinate t:ℂ)*(1/4+physicalRadialFrequency q^2))*
        profile q side outer t := by
  have hz := horizonCoordinate_interior t t.property
  have he : D4BMPhysicalMaster.radialJet (Complex.I*frequency q side) (physicalRadialFrequency q)
      (horizonCoordinate t) (radialMode outer (frequency q side) (physicalRadialFrequency q) (horizonCoordinate t))
      (radialModeFirst outer (frequency q side) (physicalRadialFrequency q) (horizonCoordinate t))
      (radialModeSecond outer (frequency q side) (physicalRadialFrequency q) (horizonCoordinate t))=0 := by
    cases outer
    · exact D4BMLaplaceRadial.horizon_equation_continued (physicalFundamentalFrequency_strip q side).1 hz
    · exact D4BMLaplaceRadial.normalizable_equation_continued hz
  dsimp only [D4BMPhysicalMaster.radialJet] at he
  rw [mul_pow,Complex.I_sq] at he
  have hz0 : (horizonCoordinate t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  field_simp [hz0] at he
  dsimp only [profile,tortoiseMode,tortoiseModeSecond,coordinateFirst,coordinateSecond]
  have hu : (radialUnit t:ℂ)^2=1-(horizonCoordinate t:ℂ) := by
    simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    ring
  push_cast
  simp only [mul_pow,hu] at he ⊢
  linear_combination (1/8:ℂ)*he

/-- Both original continued modes satisfy their physical radial equation
at each prescribed fundamental QNM frequency. -/
theorem profile_derivatives (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    HasDerivAt (profile q side outer) (profileFirst q side outer t) t ∧
    HasDerivAt (profileFirst q side outer) (profileSecond q side outer t) t := by
  have h := continued_mode_derivatives q side outer t
  refine ⟨h.1,h.2.congr_deriv ?_⟩
  rw [continued_mode_equation q side outer t,
    physicalRadialFrequency_parameter]
  dsimp [profileSecond,potential,profile,eigenvalue]
  ring

/-- Smoothness follows from the original radial equation, including at the
prescribed resonances; no response-band hypothesis is supplied. -/
theorem profile_smooth (q : XiZeroCopy) (side outer : Bool) :
    ContDiffOn ℝ ∞ (profile q side outer) (Iio (0:ℝ)) := by
  apply TwistedRadial.contDiffOn_of_linear_ode isOpen_Iio (profile q side outer)
    (profileFirst q side outer) (fun _ => 0) (potential q side) (fun _ => 0)
    contDiffOn_const (potential_smooth q side).contDiffOn contDiffOn_const
  · intro t ht
    exact (profile_derivatives q side outer ⟨t,ht⟩).1
  · intro t ht
    simpa only [zero_mul,zero_add,add_zero,profileSecond] using! (profile_derivatives q side outer ⟨t,ht⟩).2

/-- The third tortoise derivative is forced by the differentiated original potential. -/
theorem profileSecond_hasDerivAt (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    HasDerivAt (profileSecond q side outer) (profileThird q side outer t) t := by
  have hV : HasDerivAt (potential q side) (-(eigenvalue q*(coordinateFirst t:ℂ))) t := by
    convert! (hasDerivAt_const (t:ℝ) (frequency q side^2)).sub
      (((horizonCoordinate_hasDerivAt t).ofReal_comp).const_mul (eigenvalue q)) using 1
    simp
  exact hV.mul (profile_derivatives q side outer t).1

/-- Full third radius derivative of the original tortoise lift. -/
def radiusLiftThird (df ddf dddf : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((r:ℂ)*dddf (D4BMIngoingCoordinates.tortoise r)-
    3*((r:ℂ)^2+1)*ddf (D4BMIngoingCoordinates.tortoise r)+
    8*(r:ℂ)*df (D4BMIngoingCoordinates.tortoise r))/((r:ℂ)^2-1)^3

private theorem radiusLiftSecond_hasDerivAt (df ddf dddf : ℝ → ℂ) (r : ℝ) (hr : 1 < r)
    (hd : HasDerivAt df (ddf (D4BMIngoingCoordinates.tortoise r)) (D4BMIngoingCoordinates.tortoise r))
    (hdd : HasDerivAt ddf (dddf (D4BMIngoingCoordinates.tortoise r)) (D4BMIngoingCoordinates.tortoise r)) :
    HasDerivAt (radiusLiftSecond df ddf) (radiusLiftThird df ddf dddf r) r := by
  have ht := D4BMIngoingCoordinates.tortoise_hasDerivAt r hr
  have hD := hd.scomp r ht
  have hDD := hdd.scomp r ht
  have hR := (hasDerivAt_id r).ofReal_comp
  have hn : (r:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show r^2-1 ≠ 0 by nlinarith)
  apply (((hR.mul hDD).sub (hD.const_mul 2)).div (((hR.pow 2).sub_const 1).pow 2)
    (pow_ne_zero 2 hn)).congr_deriv
  dsimp [radiusLiftThird]
  push_cast
  field_simp
  ring

/-- The original first derivative is smooth on the full negative tortoise domain. -/
theorem profileFirst_smooth (q : XiZeroCopy) (side outer : Bool) :
    ContDiffOn ℝ ∞ (profileFirst q side outer) (Iio (0:ℝ)) := by
  apply ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Iio).mp (profile_smooth q side outer)).2.congr
  intro t ht
  exact (profile_derivatives q side outer ⟨t,ht⟩).1.deriv.symm

private theorem original_coordinate (t : Iio (0:ℝ)) :
    (horizonCoordinate t:ℂ)=((tortoiseRadius t:ℂ)^2-1)/(tortoiseRadius t:ℂ)^2 ∧
    (coordinateFirst t:ℂ)=2*((tortoiseRadius t:ℂ)^2-1)/(tortoiseRadius t:ℂ)^3 := by
  have hr : (tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t ≠ 0 by linarith [tortoiseRadius_exterior t t.property])
  simp only [horizonCoordinate,coordinateFirst,radialUnit_inverse_radius]
  push_cast
  constructor <;> field_simp

/-- The actual radius lift reduces both original vector-master components to
exactly the independent angular defect. -/
theorem radius_master_defect (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) (A D : ℂ) :
    D4BMVectorStream.master (-frequency q side) (tortoiseRadius t)
      (radiusLift (profile q side outer) (tortoiseRadius t))
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (tortoiseRadius t))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (tortoiseRadius t)) A D =
      radiusLift (profile q side outer) (tortoiseRadius t)*(D-eigenvalue q*A) ∧
    D4BMVectorStream.masterFirst (-frequency q side) (tortoiseRadius t)
      (radiusLift (profile q side outer) (tortoiseRadius t))
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (tortoiseRadius t))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (tortoiseRadius t))
      (radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer)
        (tortoiseRadius t)) A D =
      radiusLiftFirst (profile q side outer) (profileFirst q side outer) (tortoiseRadius t)*(D-eigenvalue q*A) := by
  have hr : (tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t ≠ 0 by linarith [tortoiseRadius_exterior t t.property])
  have hf : (tortoiseRadius t:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius t)^2-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t t.property])
  dsimp only [D4BMVectorStream.master,D4BMVectorStream.masterFirst,radiusLift,radiusLiftFirst,
    radiusLiftSecond,radiusLiftThird]
  rw [tortoise_original_inverse t t.property]
  dsimp only [profileSecond,profileThird,potential]
  rw [(original_coordinate t).1,(original_coordinate t).2]
  constructor <;> field_simp <;> ring

private theorem tortoise_negative (r : ℝ) (hr : 1 < r) :
    D4BMIngoingCoordinates.tortoise r < 0 := by
  have h := Real.log_lt_log (show 0 < r-1 by linarith) (show r-1 < r+1 by linarith)
  dsimp [D4BMIngoingCoordinates.tortoise]
  linarith

private theorem tortoise_smooth (r : ℝ) (hr : 1 < r) :
    ContDiffAt ℝ ∞ D4BMIngoingCoordinates.tortoise r := by
  have hm : r-1 ≠ 0 := by linarith
  have hp : r+1 ≠ 0 := by linarith
  unfold D4BMIngoingCoordinates.tortoise
  fun_prop

private theorem lift_smooth (q : XiZeroCopy) (side outer : Bool) (r : ℝ) (hr : 1 < r) :
    ContDiffAt ℝ 2 (radiusLift (profile q side outer)) r ∧
    ContDiffAt ℝ 2 (radiusLiftFirst (profile q side outer) (profileFirst q side outer)) r := by
  have ht := (tortoise_smooth r hr).of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hP := ((profile_smooth q side outer).of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (isOpen_Iio.mem_nhds (tortoise_negative r hr))
  have hP1 := ((profileFirst_smooth q side outer).of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (isOpen_Iio.mem_nhds (tortoise_negative r hr))
  have hR : ContDiffAt ℝ 2 (fun r : ℝ => (r:ℂ)) r := Complex.ofRealCLM.contDiff.contDiffAt
  have hF : (r:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show r^2-1 ≠ 0 by nlinarith)
  refine ⟨hR.mul (hP.comp r ht),?_⟩
  simpa only [radiusLiftFirst,div_eq_mul_inv,Function.comp_def,Pi.inv_apply] using! (hP.comp r ht).add
    ((hR.mul (hP1.comp r ht)).mul (((hR.pow 2).sub (contDiffAt_const (c := (1:ℂ)))).inv hF))

private theorem lift_derivatives_at (q : XiZeroCopy) (side outer : Bool) (r : ℝ) (hr : 1 < r) :
    HasDerivAt (radiusLift (profile q side outer))
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) r) r ∧
    HasDerivAt (radiusLiftFirst (profile q side outer) (profileFirst q side outer))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) r) r ∧
    HasDerivAt (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer))
      (radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer) r) r := by
  let t : Iio (0:ℝ) := ⟨D4BMIngoingCoordinates.tortoise r,tortoise_negative r hr⟩
  have h := profile_derivatives q side outer t
  have hh := radiusLift_derivatives _ _ _ _ hr h.1 h.2
  exact ⟨hh.1,hh.2,radiusLiftSecond_hasDerivAt _ _ _ _ hr h.2 (profileSecond_hasDerivAt q side outer t)⟩

/-- Three successive actual radius derivatives, at the original inverse tortoise radius. -/
theorem radius_derivatives (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) :
    HasDerivAt (radiusLift (profile q side outer))
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (tortoiseRadius t)) (tortoiseRadius t) ∧
    HasDerivAt (radiusLiftFirst (profile q side outer) (profileFirst q side outer))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (tortoiseRadius t)) (tortoiseRadius t) ∧
    HasDerivAt (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer))
      (radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer)
        (tortoiseRadius t)) (tortoiseRadius t) :=
  lift_derivatives_at q side outer (tortoiseRadius t) (tortoiseRadius_exterior t t.property)

private theorem lift_deriv_values (q : XiZeroCopy) (side outer : Bool) (r : ℝ) (hr : 1 < r) :
    deriv (radiusLift (profile q side outer)) r=radiusLiftFirst (profile q side outer) (profileFirst q side outer) r ∧
    deriv (deriv (radiusLift (profile q side outer))) r=radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) r ∧
    deriv (radiusLiftFirst (profile q side outer) (profileFirst q side outer)) r=
      radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) r ∧
    deriv (deriv (radiusLiftFirst (profile q side outer) (profileFirst q side outer))) r=
      radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer) r := by
  have h := lift_derivatives_at q side outer r hr
  have h0 : deriv (radiusLift (profile q side outer)) =ᶠ[𝓝 r]
      radiusLiftFirst (profile q side outer) (profileFirst q side outer) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact (lift_derivatives_at q side outer x hx).1.deriv
  have h1 : deriv (radiusLiftFirst (profile q side outer) (profileFirst q side outer)) =ᶠ[𝓝 r]
      radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact (lift_derivatives_at q side outer x hx).2.1.deriv
  exact ⟨h.1.deriv,h0.deriv_eq.trans h.2.1.deriv,h.2.1.deriv,h1.deriv_eq.trans h.2.2.deriv⟩

open ScalarTwoJet D4BMModularCore D4BMMetricReconstruction

private def radialField (q : XiZeroCopy) (side outer : Bool) (x : Fin 4 → ℝ) : ℂ :=
  Complex.exp ((-frequency q side)*(x 0:ℂ))*radiusLift (profile q side outer) (x 1)
private def radialFirstField (q : XiZeroCopy) (side outer : Bool) (x : Fin 4 → ℝ) : ℂ :=
  Complex.exp ((-frequency q side)*(x 0:ℂ))*radiusLiftFirst (profile q side outer) (profileFirst q side outer) (x 1)
private def timeBlock (q : XiZeroCopy) (side outer : Bool) (x : Fin 4 → ℝ) : ℂ :=
  ((x 1:ℂ)*(x 1:ℂ)+(-1))*radialFirstField q side outer x
private def radiusBlock (q : XiZeroCopy) (side outer : Bool) (x : Fin 4 → ℝ) : ℂ :=
  ((-frequency q side)*radialField q side outer x)*((x 1:ℂ)*(x 1:ℂ)+(-1))⁻¹

/-- The symmetric metric reconstructed from the original left stream's temporal
and radial derivatives, at the original prescribed QNM frequency. -/
def metricField (q : XiZeroCopy) (side outer : Bool) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let T := timeBlock q side outer x
  let R := radiusBlock q side outer x
  let A := D4BMLiteralCusp.vector (physicalAngularParameter q) 0 (angularPoint x)
  let C := D4BMLiteralCusp.vector (physicalAngularParameter q) 1 (angularPoint x)
  !![0,0,T*A,T*C; 0,0,R*A,R*C; T*A,R*A,0,0; T*C,R*C,0,0]

/-- All radial and angular entries in the full metric jet come from the original mode. -/
def fullMetricJet (q : XiZeroCopy) (side outer : Bool) (r : ℝ) (z : D4BMHorizon.Point) :
    CoordinateMetricTwoJet 4 ℂ :=
  let V := D4BMLiteralCusp.vector (physicalAngularParameter q)
  D4BMVectorStream.metricJet (-frequency q side) r
    (radiusLift (profile q side outer) r) (radiusLiftFirst (profile q side outer) (profileFirst q side outer) r)
    (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) r)
    (radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer) r)
    (V 0 z) (V 1 z) (coordDeriv 0 (V 0) z) (coordDeriv 1 (V 0) z) (coordDeriv 0 (V 1) z)
    (coordDeriv 0 (coordDeriv 0 (V 0)) z) (coordDeriv 0 (coordDeriv 1 (V 0)) z)
    (coordDeriv 0 (coordDeriv 0 (V 1)) z) (coordDeriv 1 (coordDeriv 1 (V 0)) z)

private theorem separated_jet (w : ℂ) (h : ℝ → ℂ) (x : Fin 4 → ℝ) (hx : x 0=0)
    (hh : ContDiffAt ℝ 2 h (x 1)) :
    ofField (fun y => Complex.exp (w*(y 0:ℂ))*h (y 1)) x =
      D4BMVectorStream.radialJet w (h (x 1)) (deriv h (x 1)) (deriv (deriv h) (x 1)) := by
  have hj := staticStreamJet_actual w h (fun _ => 1) x hx hh contDiffAt_const
  simpa [staticStreamJet,D4BMVectorStream.radialJet,ofField_constant,constant] using! hj

private theorem radial_smooth (q : XiZeroCopy) (side outer : Bool) (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (radialField q side outer) p.val ∧ ContDiffAt ℝ 2 (radialFirstField q side outer) p.val := by
  have htime : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ =>
      Complex.exp ((-frequency q side)*(x 0:ℂ))) p.val :=
    (contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).contDiffAt)).cexp
  have h := lift_smooth q side outer (p.val 1) p.property.1
  exact ⟨htime.mul (h.1.comp p.val (contDiff_apply ℝ ℝ 1).contDiffAt),
    htime.mul (h.2.comp p.val (contDiff_apply ℝ ℝ 1).contDiffAt)⟩

private theorem radial_jets (q : XiZeroCopy) (side outer : Bool) (p : D4BMBackground.ExteriorPoint)
    (hp : p.val 0=0) :
    ofField (radialField q side outer) p.val = D4BMVectorStream.radialJet (-frequency q side)
      (radiusLift (profile q side outer) (p.val 1))
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (p.val 1))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (p.val 1)) ∧
    ofField (radialFirstField q side outer) p.val = D4BMVectorStream.radialJet (-frequency q side)
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (p.val 1))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (p.val 1))
      (radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer) (p.val 1)) := by
  have hs := lift_smooth q side outer (p.val 1) p.property.1
  have hd := lift_deriv_values q side outer (p.val 1) p.property.1
  exact ⟨(separated_jet _ _ p.val hp hs.1).trans (by rw [hd.1,hd.2.1]),
    (separated_jet _ _ p.val hp hs.2).trans (by rw [hd.2.2.1,hd.2.2.2])⟩

private theorem block_smooth (q : XiZeroCopy) (side outer : Bool) (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (timeBlock q side outer) p.val ∧ ContDiffAt ℝ 2 (radiusBlock q side outer) p.val := by
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1:ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hF := (hR.mul hR).add (contDiffAt_const (c := (-1:ℂ)))
  have hn : (p.val 1:ℂ)*(p.val 1:ℂ)+(-1) ≠ 0 := by
    have h : (p.val 1:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show (p.val 1)^2-1 ≠ 0 by nlinarith [p.property.1])
    simpa only [←pow_two,←sub_eq_add_neg] using h
  exact ⟨hF.mul (radial_smooth q side outer p).2,
    ((contDiffAt_const (c := -frequency q side)).mul (radial_smooth q side outer p).1).mul (hF.inv hn)⟩

private theorem block_jets (q : XiZeroCopy) (side outer : Bool) (p : D4BMBackground.ExteriorPoint)
    (hp : p.val 0=0) :
    let r := (p.val 1:ℂ)
    let F := ((D4BMScalarLinearEquation.coord r 1).mul (D4BMScalarLinearEquation.coord r 1)).add (constant (-1))
    ofField (timeBlock q side outer) p.val = F.mul (D4BMVectorStream.radialJet (-frequency q side)
      (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (p.val 1))
      (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (p.val 1))
      (radiusLiftThird (profileFirst q side outer) (profileSecond q side outer) (profileThird q side outer) (p.val 1))) ∧
    ofField (radiusBlock q side outer) p.val =
      ((constant (-frequency q side)).mul (D4BMVectorStream.radialJet (-frequency q side)
        (radiusLift (profile q side outer) (p.val 1))
        (radiusLiftFirst (profile q side outer) (profileFirst q side outer) (p.val 1))
        (radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (p.val 1)))).mul F.inv := by
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1:ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hF := (hR.mul hR).add (contDiffAt_const (c := (-1:ℂ)))
  have hn : (p.val 1:ℂ)*(p.val 1:ℂ)+(-1) ≠ 0 := by
    have h : (p.val 1:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show (p.val 1)^2-1 ≠ 0 by nlinarith [p.property.1])
    simpa only [←pow_two,←sub_eq_add_neg] using h
  have hjR : ofField (fun x : Fin 4 → ℝ => (x 1:ℂ)) p.val = D4BMScalarLinearEquation.coord (p.val 1) 1 := by
    convert! D4BMFundamentalScalarMetric.coordinate_jet p.val 1 using 1
  have hjF : ofField (fun x : Fin 4 → ℝ => (x 1:ℂ)*(x 1:ℂ)+(-1)) p.val =
      ((D4BMScalarLinearEquation.coord (p.val 1) 1).mul (D4BMScalarLinearEquation.coord (p.val 1) 1)).add (constant (-1)) := by
    rw [ofField_add (hR.mul hR) contDiffAt_const,ofField_mul hR hR,ofField_constant,hjR]
  constructor
  · unfold timeBlock
    rw [ofField_mul hF (radial_smooth q side outer p).2,hjF,(radial_jets q side outer p hp).2]
  · have hFi : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => ((x 1:ℂ)*(x 1:ℂ)+(-1))⁻¹) p.val := hF.inv hn
    have hjFi : ofField (fun x : Fin 4 → ℝ => ((x 1:ℂ)*(x 1:ℂ)+(-1))⁻¹) p.val =
        (ofField (fun x : Fin 4 → ℝ => (x 1:ℂ)*(x 1:ℂ)+(-1)) p.val).inv := by
      convert! ofField_inv hF hn using 1
    unfold radiusBlock
    rw [ofField_mul ((contDiffAt_const (c := -frequency q side)).mul (radial_smooth q side outer p).1)
      hFi,ofField_mul (contDiffAt_const (c := -frequency q side)) (radial_smooth q side outer p).1,
      ofField_constant,hjFi,hjF,(radial_jets q side outer p hp).1]

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) : CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value,fun k i j => (J i j).first k,fun k l i j => (J i j).second k l⟩

/-- Every ordered slot of the QNM metric two-jet is an actual coordinate derivative. -/
theorem metricField_jet (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ))
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    ofMetricField (metricField q side outer) (modePoint t z.val z.property).val =
      fullMetricJet q side outer (tortoiseRadius t) z.val := by
  let p := modePoint t z.val z.property
  let V := D4BMLiteralCusp.vector (physicalAngularParameter q)
  have hza : angularPoint p.val=z.val := by
    ext k
    fin_cases k <;> rfl
  have hV (j : Fin 2) : ContDiffAt ℝ 2 (V j) (angularPoint p.val) := by
    rw [hza]
    exact D4BMLiteralCusp.vector_contDiffAt (physicalAngularParameter q) 2 z.val z.property j
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (j : Fin 2) : ContDiffAt ℝ 2 (fun x => V j (angularPoint x)) p.val :=
    (hV j).comp p.val hu.contDiffAt
  have ht (j : Fin 2) := ofField_mul (block_smooth q side outer p).1 (hLift j)
  have hr (j : Fin 2) := ofField_mul (block_smooth q side outer p).2 (hLift j)
  simp_rw [(block_jets q side outer p rfl).1,streamAngularJet_actual V p hV
    (D4BMLiteralCusp.vector_divergence (physicalAngularParameter q))] at ht
  simp_rw [(block_jets q side outer p rfl).2,streamAngularJet_actual V p hV
    (D4BMLiteralCusp.vector_divergence (physicalAngularParameter q))] at hr
  simp_rw [hza] at ht hr
  change assemble _ = assemble _
  congr 1
  funext i j
  fin_cases i <;> fin_cases j
  all_goals solve | exact ofField_constant 0 p.val | convert! ht 0 using 1 |
    convert! ht 1 using 1 | convert! hr 0 using 1 | convert! hr 1 using 1

/-- The literal coexact source discharges the angular defect at its unchanged
physical parameter. -/
theorem angular_equation (q : XiZeroCopy) (z : {z : D4BMHorizon.Point // 0 < z 1}) (j : Fin 2) :
    streamAngularOperator (D4BMLiteralCusp.vector (physicalAngularParameter q)) j z.val =
      eigenvalue q*D4BMLiteralCusp.vector (physicalAngularParameter q) j z.val := by
  rw [streamAngularOperator_actual _ z.val z.property
    (D4BMLiteralCusp.vector_contDiffAt (physicalAngularParameter q) 2 z.val z.property)
    (D4BMLiteralCusp.vector_divergence (physicalAngularParameter q)),
    D4BMLiteralCusp.vector_equation (physicalAngularParameter q) z.val z.property j]
  dsimp [eigenvalue,D4BMLiteralCusp.scalarQ,d4HyperbolicHodgePairedVectorEigenvalue]
  ring

/-- All sixteen components of the actual reconstructed left QNM metric solve
the full linearized cosmological Einstein equation at the original frequency. -/
theorem metricField_einstein (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ))
    (z : {z : D4BMHorizon.Point // 0 < z 1}) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (tortoiseRadius t) (z.val 1))
      (ofMetricField (metricField q side outer) (modePoint t z.val z.property).val) (-3) i j = 0 := by
  have hr : (tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t ≠ 0 by linarith [tortoiseRadius_exterior t t.property])
  have hf : (tortoiseRadius t:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius t)^2-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t t.property])
  have hy : (z.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.property.ne'
  let V := D4BMLiteralCusp.vector (physicalAngularParameter q)
  have h0 := radius_master_defect q side outer t (V 0 z.val) (streamAngularOperator V 0 z.val)
  have h1 := radius_master_defect q side outer t (V 1 z.val) (streamAngularOperator V 1 z.val)
  have ha0 : streamAngularOperator V 0 z.val-eigenvalue q*V 0 z.val=0 :=
    sub_eq_zero.mpr (angular_equation q z 0)
  have ha1 : streamAngularOperator V 1 z.val-eigenvalue q*V 1 z.val=0 :=
    sub_eq_zero.mpr (angular_equation q z 1)
  rw [ha0,mul_zero,mul_zero] at h0
  rw [ha1,mul_zero,mul_zero] at h1
  rw [metricField_jet]
  unfold fullMetricJet
  rw [D4BMVectorStream.cosmological_component _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hf i j]
  have hT0 := congrArg (fun a : ℂ => -((tortoiseRadius t:ℂ)^2-1)/(2*(tortoiseRadius t:ℂ)^2)*a) h0.2
  have hT1 := congrArg (fun a : ℂ => -((tortoiseRadius t:ℂ)^2-1)/(2*(tortoiseRadius t:ℂ)^2)*a) h1.2
  have hR0 := congrArg (fun a : ℂ => -(-frequency q side)/(2*(tortoiseRadius t:ℂ)^2*((tortoiseRadius t:ℂ)^2-1))*a) h0.1
  have hR1 := congrArg (fun a : ℂ => -(-frequency q side)/(2*(tortoiseRadius t:ℂ)^2*((tortoiseRadius t:ℂ)^2-1))*a) h1.1
  simp only [mul_zero] at hT0 hT1 hR0 hR1
  fin_cases i <;> fin_cases j
  all_goals solve | rfl | convert! hT0 using 1 | convert! hT1 using 1 |
    convert! hR0 using 1 | convert! hR1 using 1

private theorem coordinate_partial (f : ℝ → ℂ) (k i : Fin 4) (x : Fin 4 → ℝ)
    (hf : DifferentiableAt ℝ f (x k)) :
    coordDeriv i (fun y => f (y k)) x = if i=k then deriv f (x k) else 0 := by
  have hi : HasFDerivAt (fun y : Fin 4 → ℝ => y k)
      (ContinuousLinearMap.proj k : (Fin 4 → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply k x
  have h := hf.hasDerivAt.hasFDerivAt.comp x hi
  change fderiv ℝ (f ∘ fun y => y k) x (Pi.single i 1) = _
  rw [h.fderiv]
  by_cases hi : i=k
  · subst i
    simp
  · simp [hi,Ne.symm hi]

private theorem partial_mul {f g : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    coordDeriv i (fun y => f y*g y) x = coordDeriv i f x*g x+f x*coordDeriv i g x := by
  simp only [coordDeriv,fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul]
  ring

private theorem separated_first (w : ℂ) (h : ℝ → ℂ) (S : D4BMHorizon.Point → ℂ)
    (x : Fin 4 → ℝ) (hh : ContDiffAt ℝ 2 h (x 1))
    (hS : ContDiffAt ℝ 2 S (angularPoint x)) :
    coordDeriv 0 (fun y => Complex.exp (w*(y 0:ℂ))*h (y 1)*S (angularPoint y)) x =
      w*Complex.exp (w*(x 0:ℂ))*h (x 1)*S (angularPoint x) ∧
    coordDeriv 1 (fun y => Complex.exp (w*(y 0:ℂ))*h (y 1)*S (angularPoint y)) x =
      Complex.exp (w*(x 0:ℂ))*deriv h (x 1)*S (angularPoint x) := by
  have he (u : ℝ) : HasDerivAt (fun v : ℝ => Complex.exp (w*(v:ℂ)))
      (w*Complex.exp (w*(u:ℂ))) u := by
    convert! (((hasDerivAt_id u).ofReal_comp).const_mul w).cexp using 1
    simp [mul_comm]
  have hEt : ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => Complex.exp (w*(y 0:ℂ))) x :=
    (contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).contDiffAt)).cexp
  have hE := hEt.differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ (fun y : Fin 4 → ℝ => h (y 1)) x :=
    (hh.differentiableAt (by norm_num)).comp x (differentiableAt_apply 1 x)
  have hA : DifferentiableAt ℝ (fun y => S (angularPoint y)) x := by
    apply (hS.differentiableAt (by norm_num)).comp x
    change DifferentiableAt ℝ (fun y : Fin 4 → ℝ => ![y 2,y 3]) x
    apply differentiableAt_pi.mpr
    intro k
    fin_cases k <;> exact differentiableAt_apply _ x
  have hEH : DifferentiableAt ℝ (fun y : Fin 4 → ℝ => Complex.exp (w*(y 0:ℂ))*h (y 1)) x := hE.mul hH
  have ha0 : coordDeriv 0 (fun y => S (angularPoint y)) x=0 := by
    change (ofField (fun y => S (angularPoint y)) x).first 0=0
    rw [D4BMScalarLinearEquation.angular_lift_jet S x hS]
    rfl
  have ha1 : coordDeriv 1 (fun y => S (angularPoint y)) x=0 := by
    change (ofField (fun y => S (angularPoint y)) x).first 1=0
    rw [D4BMScalarLinearEquation.angular_lift_jet S x hS]
    rfl
  constructor
  · rw [partial_mul hEH hA,partial_mul hE hH,
      coordinate_partial _ 0 0 x (he (x 0)).differentiableAt,
      coordinate_partial h 1 0 x (hh.differentiableAt (by norm_num)),ha0,(he (x 0)).deriv]
    simp
  · rw [partial_mul hEH hA,partial_mul hE hH,
      coordinate_partial _ 0 1 x (he (x 0)).differentiableAt,
      coordinate_partial h 1 1 x (hh.differentiableAt (by norm_num)),ha1]
    simp

/-- Pointwise identification on the entire exterior with the original left
stream's actual temporal and radial coordinate derivatives. -/
theorem metricField_is_original_stream (q : XiZeroCopy) (side outer : Bool)
    (p : D4BMBackground.ExteriorPoint) :
    metricField q side outer p.val = D4BMMixedActionCurrent.mixedMatrix
      (fun a => ((p.val 1:ℂ)^2-1)*coordDeriv 1
        (physicalLeftModeStream q (frequency q side) outer a) p.val)
      (fun a => coordDeriv 0 (physicalLeftModeStream q (frequency q side) outer a) p.val/
        ((p.val 1:ℂ)^2-1)) := by
  have h (a : Fin 2) := separated_first (-frequency q side) (radiusLift (profile q side outer))
    (D4BMLiteralCusp.vector (physicalAngularParameter q) a) p.val
    (lift_smooth q side outer (p.val 1) p.property.1).1
    (D4BMLiteralCusp.vector_contDiffAt (physicalAngularParameter q) 2 (angularPoint p.val) p.property.2 a)
  have hd := (lift_derivatives_at q side outer (p.val 1) p.property.1).1.deriv
  unfold physicalLeftModeStream
  simp_rw [(h _).1,(h _).2,hd]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [metricField,D4BMMixedActionCurrent.mixedMatrix,timeBlock,radiusBlock,
    radialField,radialFirstField,div_eq_mul_inv,pow_two]
  all_goals ring

end
end RHTower.D4BMLeftModeRadialEquation
