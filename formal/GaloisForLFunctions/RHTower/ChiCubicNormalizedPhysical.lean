import GaloisForLFunctions.RHTower.ChiCubicNormalizedFourier

/-!
# Exact normalized physical phase of the original cubic cone

The full original physical amplitude has a reciprocal height factor `1/r`.
Coordinate Fubini, three positive dilations, and the exact selected slice
identity give the normalized cone as `2*pi*N` times its compact oscillatory
integral, with reciprocal factor `1/R` and phase
`2*pi*N*(P-R*y)*(Q-R*x)/R`. Every original Gaussian, logarithmic factor,
conjugate and physical height window remains. This exact identity supplies
the physical phase for nonstationary derivative-tail estimates; no
stationary approximation, cancellation or regularity bound is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem rescale {N : ℝ} (hN : 0<N) (f : ℝ→ℂ) :
    (∫x : ℝ, f x)=(N : ℂ)*∫x : ℝ, f (N*x) := by
  rw [Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hN),Complex.real_smul,
    Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hN.ne'),one_mul]

private theorem rescale_three {N : ℝ} (hN : 0<N) (f : ℝ→ℝ→ℝ→ℂ) :
    (∫r : ℝ,∫q : ℝ,∫p : ℝ, f r q p)=
      (N : ℂ)^3*∫r : ℝ,∫q : ℝ,∫p : ℝ, f (N*r) (N*q) (N*p) := by
  have hq (r : ℝ) : (∫q : ℝ,∫p : ℝ, f r q p)=
      (N : ℂ)^2*∫q : ℝ,∫p : ℝ, f r (N*q) (N*p) := by
    rw [rescale hN (fun q => ∫p : ℝ, f r q p)]
    have hp : (∫q : ℝ,∫p : ℝ, f r (N*q) p)=
        ∫q : ℝ, (N : ℂ)*∫p : ℝ, f r (N*q) (N*p) := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact rescale hN _
    rw [hp,integral_const_mul]
    ring
  rw [rescale hN (fun r => ∫q : ℝ,∫p : ℝ, f r q p)]
  simp_rw [hq,integral_const_mul]
  ring

private theorem physical_phase_factor (N : ℝ) (η : ℝ→ℝ) (x y p q r : ℝ) :
    Complex.exp ((-2*Real.pi*inner ℝ (WithLp.toLp 2 ![p,q,r] : BAGPhysicalSpace)
      (bagCubicConeNode (WithLp.toLp 2 ![x,y])) : ℝ)*Complex.I)*
      bagCubicPhysicalAmplitude N η (WithLp.toLp 2 ![p,q,r]) =
    (2*Real.pi : ℂ)*bagCubicMellinSliceValue N η 0 p*bagCubicMellinSliceValue N η 0 q*
      star (bagCubicMellinSliceValue N η 0 r)/(r : ℂ)*
      (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ)*
      bourgainOscillation (2*Real.pi*(p*q/r-p*x-q*y+r*x*y)) := by
  have he : Complex.exp ((-2*Real.pi*(p*x+q*y-r*x*y) : ℝ)*Complex.I)*
      bourgainOscillation (2*Real.pi*(p*q/r)) =
      bourgainOscillation (2*Real.pi*(p*q/r-p*x-q*y+r*x*y)) := by
    unfold bourgainOscillation
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  have hinner : inner ℝ (WithLp.toLp 2 ![p,q,r] : BAGPhysicalSpace)
      (bagCubicConeNode (WithLp.toLp 2 ![x,y]))=p*x+q*y-r*x*y := by
    simp only [bagCubicConeNode,PiLp.inner_apply,Real.inner_apply,
      Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    ring
  rw [hinner]
  change Complex.exp ((-2*Real.pi*(p*x+q*y-r*x*y) : ℝ)*Complex.I)*
    ((2*Real.pi : ℂ)*bagCubicMellinSliceValue N η 0 p*bagCubicMellinSliceValue N η 0 q*
      star (bagCubicMellinSliceValue N η 0 r)/(r : ℂ)*
      (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ)*bourgainOscillation (2*Real.pi*(p*q/r)))=_
  convert congrArg (fun z : ℂ =>
    (2*Real.pi : ℂ)*bagCubicMellinSliceValue N η 0 p*bagCubicMellinSliceValue N η 0 q*
      star (bagCubicMellinSliceValue N η 0 r)/(r : ℂ)*
      (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ)*z) he using 1
  ring

/-- Literal physical cone phase after normalization and positive dilation. -/
def bagCubicNormalizedPhysicalKernel (δ h N x y : ℝ) : ℂ :=
  (2*Real.pi*N : ℂ)*∫r : ℝ,∫q : ℝ,∫p : ℝ,
    bagCubicNormalizedSlice δ h p*bagCubicNormalizedSlice δ h q*
      star (bagCubicNormalizedSlice δ h r)/(r : ℂ)*
      (bagPhysicalHeightWindow (p*q/r) : ℂ)*
      bourgainOscillation (2*Real.pi*N*((p-r*y)*(q-r*x)/r))

private theorem normalized_physical_integrand (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (x y p q r : ℝ) :
    ((((Real.log N.1)^3/N.1 : ℝ) : ℂ)*(N.1 : ℂ)^3)*
      ((2*Real.pi : ℂ)*bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*p)*
        bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*q)*
        star (bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*r))/(N.1*r : ℂ)*
        (bagPhysicalHeightWindow ((N.1*p)*(N.1*q)/((N.1*r)*N.1)) : ℂ)*
        bourgainOscillation (2*Real.pi*((N.1*p)*(N.1*q)/(N.1*r)-(N.1*p)*x-(N.1*q)*y+(N.1*r)*x*y))) =
    (2*Real.pi*N.1 : ℂ)*(bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1) p*
      bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1) q*
      star (bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1) r)/(r : ℂ)*
      (bagPhysicalHeightWindow (p*q/r) : ℂ)*
      bourgainOscillation (2*Real.pi*N.1*((p-r*y)*(q-r*x)/r))) := by
  have hN : 0<N.1 := zero_lt_one.trans N.2
  have hn : (N.1 : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hL : (Real.log N.1 : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.log_pos N.2).ne'
  have hslice (u : ℝ) : bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*u)=
      bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1) u/(Real.log N.1 : ℂ) := by
    apply (eq_div_iff hL).mpr
    simpa only [mul_comm] using bagCubicNormalizedSlice_eq_actual N H u
  by_cases hr : r=0
  · simp only [hr,mul_zero,Complex.ofReal_zero,div_zero,zero_mul,mul_zero]
  have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  have hw : (N.1*p)*(N.1*q)/((N.1*r)*N.1)=p*q/r := by field_simp
  have hp : (N.1*p)*(N.1*q)/(N.1*r)-(N.1*p)*x-(N.1*q)*y+(N.1*r)*x*y=
      N.1*((p-r*y)*(q-r*x)/r) := by field_simp; ring
  rw [hslice p,hslice q,hslice r,hw,hp]
  simp only [star_div₀,Complex.star_def,Complex.conj_ofReal,
    Complex.ofReal_div,Complex.ofReal_pow]
  have hphase : 2*Real.pi*(N.1*((p-r*y)*(q-r*x)/r))=2*Real.pi*N.1*((p-r*y)*(q-r*x)/r) := by ring
  rw [hphase]
  field_simp

/-- Exact attachment of the normalized oscillatory kernel to the original physical cone. -/
theorem bagCubicControlledCone_normalized_physical (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (x y : ℝ) :
    (((Real.log N.1)^3/N.1 : ℝ) : ℂ)*
      bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H) (WithLp.toLp 2 ![x,y]) =
      bagCubicNormalizedPhysicalKernel (H.1/N.1) (1/Real.log N.1) N.1 x y := by
  let f := bagCubicControlledPhysicalSchwartz N H
  let w := bagCubicConeNode (WithLp.toLp 2 ![x,y])
  let K : BAGPhysicalSpace→ℂ := fun v => Complex.exp ((-2*Real.pi*inner ℝ v w : ℝ)*Complex.I)*f v
  have hphase : Continuous (fun v : BAGPhysicalSpace => Complex.exp ((-2*Real.pi*inner ℝ v w : ℝ)*Complex.I)) := by fun_prop
  have hi : Integrable K := f.integrable.bdd_mul (c := 1) hphase.aestronglyMeasurable
    (Eventually.of_forall (fun v => by rw [Complex.norm_exp]; simp))
  have he (p q r : ℝ) := physical_phase_factor N.1 (bagCubicControlledBandCutoff N.1 H.1) x y p q r
  change ∀p q r : ℝ, K (WithLp.toLp 2 ![p,q,r])=_ at he
  rw [bagCubicConeSchwartz_apply,SchwartzMap.fourier_coe,Real.fourier_eq']
  change (((Real.log N.1)^3/N.1 : ℝ) : ℂ)*(∫v, K v)=_
  rw [(Transverse.integral_three K hi).2]
  simp_rw [he]
  rw [rescale_three (zero_lt_one.trans N.2)]
  rw [←mul_assoc,←integral_const_mul]
  simp_rw [←integral_const_mul]
  unfold bagCubicNormalizedPhysicalKernel
  rw [←integral_const_mul]
  simp_rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  apply integral_congr_ae
  filter_upwards [] with q
  apply integral_congr_ae
  filter_upwards [] with p
  simpa only [Complex.ofReal_mul] using normalized_physical_integrand N H x y p q r

end RHTower.BAGTrace
