import GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Physical stress and dilation conservation for original Maass observations

The original inverse-square Maass potential gives exact horizontal stress
conservation and vertical potential forcing. Contraction with the physical dilation
vector cancels that forcing against the stress trace. The resulting C¹ current
is divergence-free, including at source zeros. Its circular normal-density flux
retains the actual radial and angular derivative energies and spectral mass.
Every observation is a fixed continuous linear map of the original finite source.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassDilationStress
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassCuspTransport
open SelbergMaassCharacterGradient SelbergMaassCharacterDynamics SelbergMaassTraceEnergy
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)

/-- The literal scalar observation of the complete original source in its physical chart. -/
def observedField (w : ℂ) : ℂ := L (sourceVector N f (ofComplex w))

private theorem observed_smooth (z : ℍ) : ContDiffAt ℝ 2 (observedField N f L) (z : ℂ) :=
  (readout_contDiffOn N f L).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

private theorem mixed_dir {F : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 F z) (a b : ℂ) :
    dir a (dir b F) z = dir b (dir a F) z := by
  have hd := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiableAt one_ne_zero
  have he (a b : ℂ) : dir a (dir b F) z = fderiv ℝ (fderiv ℝ F) z a b := by
    have h := congrArg (fun D => D a) (hd.hasFDerivAt.clm_apply (hasFDerivAt_const b z)).fderiv
    change fderiv ℝ (fun w => fderiv ℝ F w b) z a = _
    simpa using h
  rw [he,he]
  exact (hf.isSymmSndFDerivAt (by norm_num)) a b

private theorem pair_dir {F G : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => (F w*(starRingEnd ℂ) (G w)).re) z =
      (dir v F z*(starRingEnd ℂ) (G z)+F z*(starRingEnd ℂ) (dir v G z)).re := by
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hg.hasFDerivAt
  have hp := Complex.reCLM.hasFDerivAt.comp z (hf.hasFDerivAt.mul hc)
  have h := congrArg (fun D => D v) hp.fderiv
  change dir v (fun w => (F w*(starRingEnd ℂ) (G w)).re) z =
    (F z*(starRingEnd ℂ) (dir v G z)+(starRingEnd ℂ) (G z)*dir v F z).re at h
  rw [h]
  congr 1
  ring

private theorem mul_dir {F G : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => F w*G w) z = dir v F z*G z+F z*dir v G z := by
  have h := congrArg (fun D => D v) (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  change dir v (fun w => F w*G w) z = F z*dir v G z+G z*dir v F z at h
  rw [h]
  ring

private theorem add_dir {F G : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => F w+G w) z = dir v F z+dir v G z := by
  exact congrArg (fun D => D v) (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

private theorem sub_dir {F G : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => F w-G w) z = dir v F z-dir v G z := by
  exact congrArg (fun D => D v) (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

/-- The original inverse-square spectral potential as a real chart function. -/
def potential (lam : ℝ) (w : ℂ) : ℝ := lam/w.im^(2 : ℕ)

private theorem potential_hasFDerivAt (lam : ℝ) (z : ℍ) :
    HasFDerivAt (potential lam) ((-2*lam/z.im^(3 : ℕ)) • Complex.imCLM) (z : ℂ) := by
  have h := (hasDerivAt_const z.im lam).div ((hasDerivAt_id z.im).pow 2)
    (pow_ne_zero 2 z.im_pos.ne')
  have hd : HasDerivAt (fun y : ℝ => lam/y^(2 : ℕ)) (-2*lam/z.im^(3 : ℕ)) z.im := by
    apply h.congr_deriv
    simp only [Pi.pow_apply,id_eq,zero_mul,zero_sub,Nat.cast_ofNat,mul_one]
    field_simp
    ring
  exact hd.comp_hasFDerivAt (z : ℂ) Complex.imCLM.hasFDerivAt

/-- Exact derivative of the original spectral potential, with its physical height factor. -/
theorem potential_dir (v : ℂ) (z : ℍ) :
    dir v (potential lam) (z : ℂ) = (-2*lam/z.im^(3 : ℕ))*v.im := by
  rw [dir,(potential_hasFDerivAt lam z).fderiv]
  rfl

/-- Original spectral mass appearing in each physical stress diagonal. -/
def potentialMass (w : ℂ) : ℝ := potential lam w*normSq (observedField N f L w)

private theorem mass_diff (z : ℍ) :
    DifferentiableAt ℝ (fun w => normSq (observedField N f L w)) (z : ℂ) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    ((observed_smooth N f L z).differentiableAt (by norm_num)).norm_sq (𝕜 := ℂ)

private theorem derivative_mass_diff (v : ℂ) (z : ℍ) :
    DifferentiableAt ℝ (fun w => normSq (dir v (observedField N f L) w)) (z : ℂ) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    ((dir_contDiffAt (observed_smooth N f L z) v).differentiableAt one_ne_zero).norm_sq (𝕜 := ℂ)

private theorem potentialMass_diff (z : ℍ) : DifferentiableAt ℝ (potentialMass N f L) (z : ℂ) :=
  (potential_hasFDerivAt lam z).differentiableAt.mul (mass_diff N f L z)

/-- Differentiating the actual spectral mass keeps both potential forcing and source current. -/
theorem potentialMass_dir (v : ℂ) (z : ℍ) :
    dir v (potentialMass N f L) (z : ℂ) =
      (-2*lam/z.im^(3 : ℕ))*v.im*normSq (observedField N f L (z : ℂ))+
        (lam/z.im^(2 : ℕ))*2*(dir v (observedField N f L) (z : ℂ)*
          (starRingEnd ℂ) (observedField N f L (z : ℂ))).re := by
  unfold potentialMass
  rw [mul_dir (potential_hasFDerivAt lam z).differentiableAt (mass_diff N f L z),
    potential_dir,normSq_dir ((observed_smooth N f L z).differentiableAt (by norm_num))]
  unfold potential
  change (-2*lam/z.im^(3 : ℕ))*v.im*normSq (observedField N f L (z : ℂ))+
    (lam/z.im^(2 : ℕ))*(2*(dir v (observedField N f L) (z : ℂ)*(starRingEnd ℂ) (observedField N f L (z : ℂ))).re) = _
  ring

/-- Horizontal diagonal of the physical stress tensor of an actual source observation. -/
def stressXX (w : ℂ) : ℝ :=
  normSq (dir 1 (observedField N f L) w)-normSq (dir Complex.I (observedField N f L) w)+potentialMass N f L w

/-- The complete mixed physical derivative pairing in the original stress tensor. -/
def stressXY (w : ℂ) : ℝ :=
  2*(dir 1 (observedField N f L) w*(starRingEnd ℂ) (dir Complex.I (observedField N f L) w)).re

/-- Vertical diagonal of the physical stress tensor of an actual source observation. -/
def stressYY (w : ℂ) : ℝ :=
  normSq (dir Complex.I (observedField N f L) w)-normSq (dir 1 (observedField N f L) w)+potentialMass N f L w

private theorem stressXX_diff (z : ℍ) : DifferentiableAt ℝ (stressXX N f L) (z : ℂ) :=
  ((derivative_mass_diff N f L 1 z).sub (derivative_mass_diff N f L Complex.I z)).add
    (potentialMass_diff N f L z)

private theorem stressYY_diff (z : ℍ) : DifferentiableAt ℝ (stressYY N f L) (z : ℂ) :=
  ((derivative_mass_diff N f L Complex.I z).sub (derivative_mass_diff N f L 1 z)).add
    (potentialMass_diff N f L z)

private theorem stressXY_diff (z : ℍ) : DifferentiableAt ℝ (stressXY N f L) (z : ℂ) := by
  have hx := (dir_contDiffAt (observed_smooth N f L z) 1).differentiableAt one_ne_zero
  have hy := (dir_contDiffAt (observed_smooth N f L z) Complex.I).differentiableAt one_ne_zero
  exact (Complex.reCLM.differentiableAt.comp _ (hx.mul
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp _ hy))).const_mul 2

/-- The full stress trace equals twice the original potential mass. -/
theorem stress_trace (w : ℂ) : stressXX N f L w+stressYY N f L w=2*potentialMass N f L w := by
  unfold stressXX stressYY
  ring

private theorem stressXX_dir (v : ℂ) (z : ℍ) :
    dir v (stressXX N f L) (z : ℂ) =
      2*(dir v (dir 1 (observedField N f L)) (z : ℂ)*
        (starRingEnd ℂ) (dir 1 (observedField N f L) (z : ℂ))).re-
      2*(dir v (dir Complex.I (observedField N f L)) (z : ℂ)*
        (starRingEnd ℂ) (dir Complex.I (observedField N f L) (z : ℂ))).re+
      dir v (potentialMass N f L) (z : ℂ) := by
  unfold stressXX
  rw [add_dir (F := fun w => normSq (dir 1 (observedField N f L) w)-normSq (dir Complex.I (observedField N f L) w)) ((derivative_mass_diff N f L 1 z).sub (derivative_mass_diff N f L Complex.I z))
      (potentialMass_diff N f L z),
    sub_dir (derivative_mass_diff N f L 1 z) (derivative_mass_diff N f L Complex.I z),
    normSq_dir ((dir_contDiffAt (observed_smooth N f L z) 1).differentiableAt one_ne_zero),
    normSq_dir ((dir_contDiffAt (observed_smooth N f L z) Complex.I).differentiableAt one_ne_zero)]

private theorem stressYY_dir (v : ℂ) (z : ℍ) :
    dir v (stressYY N f L) (z : ℂ) =
      2*(dir v (dir Complex.I (observedField N f L)) (z : ℂ)*
        (starRingEnd ℂ) (dir Complex.I (observedField N f L) (z : ℂ))).re-
      2*(dir v (dir 1 (observedField N f L)) (z : ℂ)*
        (starRingEnd ℂ) (dir 1 (observedField N f L) (z : ℂ))).re+
      dir v (potentialMass N f L) (z : ℂ) := by
  unfold stressYY
  rw [add_dir (F := fun w => normSq (dir Complex.I (observedField N f L) w)-normSq (dir 1 (observedField N f L) w)) ((derivative_mass_diff N f L Complex.I z).sub (derivative_mass_diff N f L 1 z))
      (potentialMass_diff N f L z),
    sub_dir (derivative_mass_diff N f L Complex.I z) (derivative_mass_diff N f L 1 z),
    normSq_dir ((dir_contDiffAt (observed_smooth N f L z) Complex.I).differentiableAt one_ne_zero),
    normSq_dir ((dir_contDiffAt (observed_smooth N f L z) 1).differentiableAt one_ne_zero)]

private theorem stressXY_dir (v : ℂ) (z : ℍ) :
    dir v (stressXY N f L) (z : ℂ) =
      2*(dir v (dir 1 (observedField N f L)) (z : ℂ)*
        (starRingEnd ℂ) (dir Complex.I (observedField N f L) (z : ℂ))+
        dir 1 (observedField N f L) (z : ℂ)*
          (starRingEnd ℂ) (dir v (dir Complex.I (observedField N f L)) (z : ℂ))).re := by
  have hx := (dir_contDiffAt (observed_smooth N f L z) 1).differentiableAt one_ne_zero
  have hy := (dir_contDiffAt (observed_smooth N f L z) Complex.I).differentiableAt one_ne_zero
  have hp := Complex.reCLM.differentiableAt.comp _ (hx.mul
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp _ hy))
  have h := congrArg (fun D => D v) (hp.hasFDerivAt.const_mul 2).fderiv
  change dir v (stressXY N f L) (z : ℂ) = 2*dir v
    (fun w => (dir 1 (observedField N f L) w*(starRingEnd ℂ) (dir Complex.I (observedField N f L) w)).re)
    (z : ℂ) at h
  rw [h,pair_dir hx hy]

private theorem observed_laplacian (z : ℍ) :
    dir 1 (dir 1 (observedField N f L)) (z : ℂ)+
      dir Complex.I (dir Complex.I (observedField N f L)) (z : ℂ) =
        ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ)*observedField N f L (z : ℂ) := by
  unfold observedField
  simpa only [ofComplex_apply] using source_readout_laplacian N f L z

/-- The original physical horizontal stress is exactly conserved. -/
theorem stress_horizontal_conservation (z : ℍ) :
    dir 1 (stressXX N f L) (z : ℂ)+dir Complex.I (stressXY N f L) (z : ℂ)=0 := by
  have hm := mixed_dir (observed_smooth N f L z) 1 Complex.I
  have he := eq_sub_of_add_eq (observed_laplacian N f L z)
  rw [stressXX_dir,stressXY_dir,potentialMass_dir,hm,he]
  simp only [Complex.one_im,mul_zero,zero_mul,zero_add,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The original vertical stress retains exactly the inverse-square potential forcing. -/
theorem stress_vertical_forcing (z : ℍ) :
    dir 1 (stressXY N f L) (z : ℂ)+dir Complex.I (stressYY N f L) (z : ℂ)=
      (-2*lam/z.im^(3 : ℕ))*normSq (observedField N f L (z : ℂ)) := by
  have hm := mixed_dir (observed_smooth N f L z) 1 Complex.I
  have he := eq_sub_of_add_eq (observed_laplacian N f L z)
  rw [stressXY_dir,stressYY_dir,potentialMass_dir,hm,he]
  simp only [Complex.I_im,mul_one,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

/-- Horizontal flux of the original stress contracted with the actual Euclidean dilation. -/
def dilationX (w : ℂ) : ℝ := w.re*stressXX N f L w+w.im*stressXY N f L w

/-- Vertical flux of the original stress contracted with the actual Euclidean dilation. -/
def dilationY (w : ℂ) : ℝ := w.re*stressXY N f L w+w.im*stressYY N f L w

private theorem re_dir (v z : ℂ) : dir v Complex.re z = v.re := by
  exact congrArg (fun D => D v) Complex.reCLM.hasFDerivAt.fderiv

private theorem im_dir (v z : ℂ) : dir v Complex.im z = v.im := by
  exact congrArg (fun D => D v) Complex.imCLM.hasFDerivAt.fderiv

private theorem dilationX_dir (v : ℂ) (z : ℍ) :
    dir v (dilationX N f L) (z : ℂ) =
      v.re*stressXX N f L (z : ℂ)+z.re*dir v (stressXX N f L) (z : ℂ)+
      (v.im*stressXY N f L (z : ℂ)+z.im*dir v (stressXY N f L) (z : ℂ)) := by
  unfold dilationX
  rw [add_dir (F := fun w => w.re*stressXX N f L w) (G := fun w => w.im*stressXY N f L w) (Complex.reCLM.differentiableAt.mul (stressXX_diff N f L z))
    (Complex.imCLM.differentiableAt.mul (stressXY_diff N f L z)),
    mul_dir (F := Complex.re) Complex.reCLM.differentiableAt (stressXX_diff N f L z),
    mul_dir (F := Complex.im) Complex.imCLM.differentiableAt (stressXY_diff N f L z),re_dir,im_dir,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]

private theorem dilationY_dir (v : ℂ) (z : ℍ) :
    dir v (dilationY N f L) (z : ℂ) =
      v.re*stressXY N f L (z : ℂ)+z.re*dir v (stressXY N f L) (z : ℂ)+
      (v.im*stressYY N f L (z : ℂ)+z.im*dir v (stressYY N f L) (z : ℂ)) := by
  unfold dilationY
  rw [add_dir (F := fun w => w.re*stressXY N f L w) (G := fun w => w.im*stressYY N f L w) (Complex.reCLM.differentiableAt.mul (stressXY_diff N f L z))
    (Complex.imCLM.differentiableAt.mul (stressYY_diff N f L z)),
    mul_dir (F := Complex.re) Complex.reCLM.differentiableAt (stressXY_diff N f L z),
    mul_dir (F := Complex.im) Complex.imCLM.differentiableAt (stressYY_diff N f L z),re_dir,im_dir,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]

/-- The full original dilation stress current is divergence-free, including zero observations and source zeros. -/
theorem dilation_conservation (z : ℍ) :
    dir 1 (dilationX N f L) (z : ℂ)+dir Complex.I (dilationY N f L) (z : ℂ)=0 := by
  rw [dilationX_dir,dilationY_dir]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,one_mul,zero_mul,zero_add]
  have hx := stress_horizontal_conservation N f L z
  have hy := stress_vertical_forcing N f L z
  have ht := stress_trace N f L (z : ℂ)
  unfold potentialMass potential at ht
  rw [UpperHalfPlane.coe_im] at ht
  have hc : 2*(lam/z.im^(2 : ℕ))*normSq (observedField N f L (z : ℂ))+
      z.im*((-2*lam/z.im^(3 : ℕ))*normSq (observedField N f L (z : ℂ)))=0 := by
    field_simp
    ring
  linear_combination z.re*hx+z.im*hy+ht+hc

private theorem dir_components (F : ℂ → ℂ) (v z : ℂ) :
    dir v F z = v.re • dir 1 F z+v.im • dir Complex.I F z := by
  have hv : v=v.re • (1 : ℂ)+v.im • Complex.I := by
    simpa only [Complex.real_smul,mul_one] using v.re_add_im.symm
  change fderiv ℝ F z v = v.re • fderiv ℝ F z 1+v.im • fderiv ℝ F z Complex.I
  conv_lhs => rw [hv,map_add,map_smul,map_smul]

/-- The radial stress keeps the exact difference of physical radial and angular energies. -/
theorem radial_stress_identity (w : ℂ) :
    w.re*dilationX N f L w+w.im*dilationY N f L w =
      normSq (dir w (observedField N f L) w)-normSq (dir (Complex.I*w) (observedField N f L) w)+
        normSq w*potentialMass N f L w := by
  rw [dir_components (observedField N f L) w w,
    dir_components (observedField N f L) (Complex.I*w) w]
  unfold dilationX dilationY stressXX stressXY stressYY
  simp only [Complex.real_smul,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

/-- Actual outward normal-density flux on the unit-circle boundary of the modular core. -/
def circleStressFlux (x y : ℝ) : ℝ :=
  (-x/y)*dilationX N f L (SelbergMaassMean.point x y)-dilationY N f L (SelbergMaassMean.point x y)

/-- The physical circle flux retains angular energy, radial energy, and the original spectral mass. -/
theorem circleStressFlux_eq_energies {x y : ℝ} (hy : 0 < y) (hxy : x^(2 : ℕ)+y^(2 : ℕ)=1) :
    circleStressFlux N f L x y =
      -(normSq (dir (SelbergMaassMean.point x y) (observedField N f L) (SelbergMaassMean.point x y))-
        normSq (dir (Complex.I*SelbergMaassMean.point x y) (observedField N f L) (SelbergMaassMean.point x y))+
        (lam/y^(2 : ℕ))*normSq (observedField N f L (SelbergMaassMean.point x y)))/y := by
  have hr := radial_stress_identity N f L (SelbergMaassMean.point x y)
  have hx' : (SelbergMaassMean.point x y).re=x := by simp [SelbergMaassMean.point]
  have hy' : (SelbergMaassMean.point x y).im=y := by simp [SelbergMaassMean.point]
  have hn : normSq (SelbergMaassMean.point x y)=1 := by
    rw [Complex.normSq_apply,hx',hy']
    nlinarith [hxy]
  rw [hx',hy',hn,one_mul] at hr
  have hm : potentialMass N f L (SelbergMaassMean.point x y)=
      (lam/y^(2 : ℕ))*normSq (observedField N f L (SelbergMaassMean.point x y)) := by
    unfold potentialMass potential
    rw [hy']
  rw [hm] at hr
  calc
    _ = -(x*dilationX N f L (SelbergMaassMean.point x y)+
        y*dilationY N f L (SelbergMaassMean.point x y))/y := by
      unfold circleStressFlux
      field_simp [hy.ne']
      ring
    _ = _ := by rw [hr]

private theorem observed_contDiffOn :
    ContDiffOn ℝ 2 (observedField N f L) {w : ℂ | 0 < w.im} := readout_contDiffOn N f L

private theorem derivative_mass_contDiffOn (v : ℂ) :
    ContDiffOn ℝ 1 (fun w => normSq (dir v (observedField N f L) w)) {w : ℂ | 0 < w.im} := by
  simpa only [Complex.normSq_eq_norm_sq] using
    (dir_contDiffOn (observed_contDiffOn N f L) (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2) v).norm_sq ℂ

private theorem potentialMass_contDiffOn :
    ContDiffOn ℝ 1 (potentialMass N f L) {w : ℂ | 0 < w.im} := by
  have hp : ContDiffOn ℝ 1 (potential lam) {w : ℂ | 0 < w.im} :=
    contDiffOn_const.div (Complex.imCLM.contDiff.contDiffOn.pow 2) (fun w hw => pow_ne_zero 2 hw.ne')
  have hm : ContDiffOn ℝ 1 (fun w => normSq (observedField N f L w)) {w : ℂ | 0 < w.im} := by
    simpa only [Complex.normSq_eq_norm_sq] using
      ((observed_contDiffOn N f L).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).norm_sq ℂ
  exact hp.mul hm

/-- The original horizontal stress is continuously differentiable on the physical upper half-plane. -/
theorem stressXX_contDiffOn : ContDiffOn ℝ 1 (stressXX N f L) {w : ℂ | 0 < w.im} :=
  ((derivative_mass_contDiffOn N f L 1).sub (derivative_mass_contDiffOn N f L Complex.I)).add
    (potentialMass_contDiffOn N f L)

/-- The original vertical stress has the same physical first-derivative regularity. -/
theorem stressYY_contDiffOn : ContDiffOn ℝ 1 (stressYY N f L) {w : ℂ | 0 < w.im} :=
  ((derivative_mass_contDiffOn N f L Complex.I).sub (derivative_mass_contDiffOn N f L 1)).add
    (potentialMass_contDiffOn N f L)

/-- The mixed physical stress is continuously differentiable, including at source zeros. -/
theorem stressXY_contDiffOn : ContDiffOn ℝ 1 (stressXY N f L) {w : ℂ | 0 < w.im} := by
  have hx := dir_contDiffOn (observed_contDiffOn N f L) (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2) 1
  have hy := dir_contDiffOn (observed_contDiffOn N f L) (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2) Complex.I
  exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
    (hx.mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hy)))

/-- Original dilation flux has the regularity required for physical Green integration. -/
theorem dilationX_contDiffOn : ContDiffOn ℝ 1 (dilationX N f L) {w : ℂ | 0 < w.im} :=
  (Complex.reCLM.contDiff.contDiffOn.mul (stressXX_contDiffOn N f L)).add
    (Complex.imCLM.contDiff.contDiffOn.mul (stressXY_contDiffOn N f L))

/-- The vertical original dilation flux has physical first-derivative regularity. -/
theorem dilationY_contDiffOn : ContDiffOn ℝ 1 (dilationY N f L) {w : ℂ | 0 < w.im} :=
  (Complex.reCLM.contDiff.contDiffOn.mul (stressXY_contDiffOn N f L)).add
    (Complex.imCLM.contDiff.contDiffOn.mul (stressYY_contDiffOn N f L))

end
end GaloisForLFunctions.RHTower.SelbergMaassDilationStress
