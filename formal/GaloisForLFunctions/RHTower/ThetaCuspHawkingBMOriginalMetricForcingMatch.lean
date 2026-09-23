import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcingProductBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCompactBoundary

/-! Exact attachment of the literal forcing product and all three counterterms
to the fourth physical metric-boundary transfer. Its radius coefficient is
retained through independent cusp/horizon limits and every nonnegative time
cutoff. These estimates do not assert matching of the full metric action. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMOriginalMetricForcingMatch
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalCornerForcing
open D4BMOriginalForcingAngularPeriod D4BMOriginalForcingProductBounds D4BMOriginalReaderCuspBounds
open D4BMOriginalReaderEquation D4BMOriginalCompactBoundary D4BMOriginalCuspFlux
open D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent D4BMOriginalAngularReaderBounds D4BMMetricReconstruction
open GaloisForLFunctions.HTGeometry ScalarTwoJet
noncomputable section
set_option autoImplicit false

private theorem coordinate_update {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    coordDeriv i f x=deriv (fun a => f (Function.update x i a)) (x i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

/-- Exact normal derivative of the physical reader before any cutoff removal. -/
theorem physical_mode_normal (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : Fin 4 → ℝ) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (modeScalar r w outer) x=modeAmplitude r w outer ![x 0,x 1]*
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x 2,x 3] := by
  have hn (z : Fin 2 → ℝ) (hz : 0<z 1) :
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=
        deriv (fun Y => D4BMLiteralCusp.scalar (physicalAngularParameter r) ![z 0,Y]) (z 1) := by
    rw [coordinate_update _ _ _ ((D4BMLiteralCusp.scalar_contDiffAt
      (physicalAngularParameter r) 2 z hz).differentiableAt (by norm_num))]
    congr 1
  rw [coordinate_update _ _ _ ((modeScalar_smooth r w hw outer x hr hy).differentiableAt (by simp))]
  simp_rw [modeScalar_value]
  simp only [angularPoint,Function.update_self,
    Function.update_of_ne (by decide : (0:Fin 4)≠3),
    Function.update_of_ne (by decide : (1:Fin 4)≠3),
    Function.update_of_ne (by decide : (2:Fin 4)≠3)]
  rw [deriv_const_mul_field,hn ![x 2,x 3] hy]
  rfl

/-- The actual ingoing mode amplitude contains the radius reconstruction factor. -/
theorem mode_amplitude_collar (q : XiZeroCopy) (w : ℂ) (p L : ℝ) (hL : 0<L) :
    modeAmplitude q w true ![p,tortoiseRadius (-L/2)]=
      (tortoiseRadius (-L/2):ℂ)*Complex.exp (-w*(p:ℂ))*reader q w L := by
  simp only [modeAmplitude,D4BMPhysicalModeAction.radiusLift,Matrix.cons_val]
  rw [tortoise_original_inverse (-L/2) (by linarith)]
  unfold reader
  rw [show -w*((p:ℂ)-((-L/2:ℝ):ℂ))= -w*(p:ℂ)+w*((-L/2:ℝ):ℂ) by ring,
    Complex.exp_add]
  simp only [modeProfile]
  ring

/-- The metric counterterm is exactly the forcing profile counterterm, including
the original onset and geometric horizon factor, for each of its three powers. -/
theorem forcing_principal_collar (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p L : ℝ) (hL : 0<L) (i : Fin 3) :
    forcingPrincipalCoefficient q br amp p (tortoiseRadius (-L/2)) i=
      (horizonCoordinate (-L/2):ℂ)*timeOnset (2*physicalRate q br) p*
        profilePrincipal q br amp (radialUnit (-L/2)) i := by
  unfold forcingPrincipalCoefficient D4BMOriginalMetricCusp.forcingValueCoefficient
    D4BMOriginalMetricCusp.forcingLaplacianCoefficient D4BMOriginalMetricCusp.forcingScale
  rw [tortoise_original_inverse (-L/2) (by linarith)]
  simp only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one,
    horizonCoordinate,profilePrincipal,forcingProfile]
  push_cast
  ring

private theorem principal_product (q : XiZeroCopy) (a : Fin 3 → ℂ) (k : ℝ) :
    (∑ i : Fin 3,a i*(Real.exp k:ℂ)^principalExponent q i)*angularPrincipal q true k=
      ∑ i : Fin 3,a i*readerCoefficient q*readerExponent q*
        Complex.exp (fluxExponent q q i*(k:ℂ)) := by
  have he (i : Fin 3) : (Real.exp k:ℂ)^principalExponent q i=
      Complex.exp (principalExponent q i*(k:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
      ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
    congr 1
    ring
  simp_rw [he]
  simp only [angularPrincipal,↓reduceIte,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hex : Complex.exp (fluxExponent q q i*(k:ℂ))=
      Complex.exp (principalExponent q i*(k:ℂ))*Complex.exp ((readerExponent q-1)*(k:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold fluxExponent
    ring
  rw [hex]
  ring

/-- The fourth transfer with precisely the counterterms of the complete physical boundary. -/
def forcingTransferCut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L x k : ℝ) : ℂ :=
  transfer (D4BMOriginalSourceContact.originalForcing q br amp) (modeScalar q w true) 1
    ![p,tortoiseRadius (-L/2),x,Real.exp k]-
    ∑ i : Fin 3,modeTransferCoefficient q q br true amp w 3 p (tortoiseRadius (-L/2)) i*
      Complex.exp (fluxExponent q q i*(k:ℂ))

/-- Exact attachment of the complete forcing product to the physical fourth transfer. -/
theorem forcing_transfer_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (p L x k : ℝ) (hL : 0<L) :
    forcingTransferCut q br amp w p L x k=
      (tortoiseRadius (-L/2):ℂ)*Complex.exp (-w*(p:ℂ))*rawProduct q br amp w true p L x k := by
  have hR := tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0)
  have hnorm := physical_mode_normal q w hwi true ![p,tortoiseRadius (-L/2),x,Real.exp k] hR (Real.exp_pos k)
  simp only [Matrix.cons_val] at hnorm
  have hc (i : Fin 3) := forcing_principal_collar q br amp p L hL i
  have hp := principal_product q (profilePrincipal q br amp (radialUnit (-L/2))) k
  unfold forcingTransferCut transfer
  simp only [angularIndex,Matrix.cons_val]
  rw [hnorm]
  simp only [D4BMOriginalSourceContact.originalForcing,Matrix.cons_val]
  rw [tortoise_original_inverse (-L/2) (by linarith),show p- -L/2=p+L/2 by ring]
  simp only [modeTransferCoefficient,Matrix.cons_val,hc,mode_amplitude_collar q w p L hL]
  unfold rawProduct
  simp only [mul_assoc]
  rw [hp]
  simp only [Fin.sum_univ_three,angularJet,↓reduceIte]
  ring

/-- The unchanged forcing trace transported back to the physical transfer. -/
def horizonForcingTransfer (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L x k : ℝ) : ℂ :=
  (tortoiseRadius (-L/2):ℂ)*Complex.exp (-w*(p:ℂ))*
    (horizonCoordinate (-L/2):ℂ)*horizonProduct q br amp w true p x k

/-- The fourth term's exact coefficient in the complete finite-time metric boundary. -/
def metricForcingBoundaryError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (T L x k : ℝ) : ℂ :=
  (-w*(tortoiseRadius (-L/2):ℂ))/((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)^(2 : ℕ)*
    ∫ p in (0:ℝ)..T,forcingTransferCut q br amp w p L x k-horizonForcingTransfer q br amp w p L x k

theorem metric_forcing_boundary_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (T L x k : ℝ) (hL : 0<L) :
    metricForcingBoundaryError q br amp w T L x k=
      -w*((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*
        (∫ p in (0:ℝ)..T,Complex.exp (-w*(p:ℂ))*(rawProduct q br amp w true p L x k-
          (horizonCoordinate (-L/2):ℂ)*horizonProduct q br amp w true p x k))/
            ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)^(2 : ℕ)) := by
  have he (p : ℝ) : forcingTransferCut q br amp w p L x k-horizonForcingTransfer q br amp w p L x k=
      (tortoiseRadius (-L/2):ℂ)*(Complex.exp (-w*(p:ℂ))*(rawProduct q br amp w true p L x k-
        (horizonCoordinate (-L/2):ℂ)*horizonProduct q br amp w true p x k)) := by
    rw [forcing_transfer_cut q br amp w hwi p L x k hL,horizonForcingTransfer]
    ring
  unfold metricForcingBoundaryError
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The actual fourth physical metric-boundary transfer, with its prescribed
counterterms and radius coefficient, matches independently in cusp, horizon and time cutoff. -/
theorem physical_forcing_boundary_joint_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im≠0) (hw : 1≤w.re) (T : ℝ × ℝ → Ici (0:ℝ)) (X : ℝ × ℝ → ℝ) :
    Tendsto (fun z : ℝ × ℝ => metricForcingBoundaryError q br amp w (T z) z.1 (X z) z.2)
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  have h := (metric_forcing_product_joint_limit q br amp w true hwi hw T X).const_mul (-w)
  simp only [mul_zero] at h
  apply h.congr'
  have hL : ∀ᶠ z : ℝ × ℝ in ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)),0<z.1 :=
    tendsto_fst.eventually (eventually_gt_atTop (0:ℝ))
  filter_upwards [hL] with z hz
  exact (metric_forcing_boundary_error q br amp w hwi (T z) z.1 (X z) z.2 hz).symm

/-- Horizontal period of the time-integrated physical fourth-transfer comparison.
The estimate is uniform before the horizontal integral is taken. -/
theorem physical_forcing_boundary_period_joint_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im≠0) (hw : 1≤w.re) (T : ℝ × ℝ → Ici (0:ℝ)) :
    Tendsto (fun z : ℝ × ℝ => ∫ x in (-1/2:ℝ)..1/2,
      metricForcingBoundaryError q br amp w (T z) z.1 x z.2)
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨B,hB,hb⟩ := metric_forcing_product_time_error q br amp w true 1 hwi hw
  have he : Tendsto (fun z : ℝ × ℝ => (‖w‖*B)*Real.exp (-z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (‖w‖*B)).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  have hL := hb.and (eventually_gt_atTop (0:ℝ))
  filter_upwards [hL.prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
  have hx (x : ℝ) : ‖metricForcingBoundaryError q br amp w (T z) z.1 x z.2‖ ≤
      (‖w‖*B)*Real.exp (-z.2) := by
    rw [metric_forcing_boundary_error q br amp w hwi (T z) z.1 x z.2 hz.1.2,norm_mul,norm_neg]
    have ht := mul_le_mul_of_nonneg_left
      (hz.1.1 (T z) x z.2 (T z).property hz.2) (norm_nonneg w)
    simpa only [Nat.cast_one,neg_one_mul,mul_assoc] using ht
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hx x)
  simpa only [neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] using hi

end
end RHTower.D4BMOriginalMetricForcingMatch
