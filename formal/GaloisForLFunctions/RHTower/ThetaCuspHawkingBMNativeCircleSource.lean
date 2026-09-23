import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleChart

/-! Actual theta half-square derivatives in the complete hyperbolic circle chart. -/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def logCircle (d theta x k : ℝ) : Point := circle d theta ![x,Real.exp k]
def source (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fullSquarePotential q (logCircle d theta x k)

private theorem logCircle_pos (d theta x k : ℝ) : 0 < logCircle d theta x k 1 :=
  mul_pos (Real.exp_pos k) (one_div_pos.mpr (denominator_pos d theta))

private theorem linear_coordinates (L : Point →L[ℝ] ℂ) (v : Point) :
    L v = (v 0:ℂ)*L (Pi.single 0 1)+(v 1:ℂ)*L (Pi.single 1 1) := by
  rw [pi_eq_sum_univ' v,map_sum]
  simp [Fin.sum_univ_two,Complex.real_smul]

def fieldFirst (q : XiZeroCopy) (p v : Point) : ℂ :=
  fderiv ℝ (fullSquarePotential q) p v
def fieldSecond (q : XiZeroCopy) (p v a : Point) : ℂ :=
  fderiv ℝ (fderiv ℝ (fullSquarePotential q)) p v v+fieldFirst q p a

private theorem first_coordinates (q : XiZeroCopy) (p v : Point) :
    fieldFirst q p v=(v 0:ℂ)*coordDeriv 0 (fullSquarePotential q) p+
      (v 1:ℂ)*coordDeriv 1 (fullSquarePotential q) p :=
  linear_coordinates _ _

private theorem second_coordinates (q : XiZeroCopy) (p v a : Point) (hp : 0 < p 1) :
    fieldSecond q p v a =
      (v 0:ℂ)^(2 : ℕ)*coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) p+
      (v 0:ℂ)*(v 1:ℂ)*(coordDeriv 0 (coordDeriv 1 (fullSquarePotential q)) p+
        coordDeriv 1 (coordDeriv 0 (fullSquarePotential q)) p)+
      (v 1:ℂ)^(2 : ℕ)*coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) p+
      (a 0:ℂ)*coordDeriv 0 (fullSquarePotential q) p+
      (a 1:ℂ)*coordDeriv 1 (fullSquarePotential q) p := by
  have hf := fullSquarePotential_smooth q p hp 2
  have he (i j : Fin 2) : coordDeriv i (coordDeriv j (fullSquarePotential q)) p=
      fderiv ℝ (fderiv ℝ (fullSquarePotential q)) p (Pi.single i 1) (Pi.single j 1) := by
    change fderiv ℝ (coordDeriv j (fullSquarePotential q)) p (Pi.single i 1)=_
    rw [(coordDeriv_hasFDerivAt hf j).fderiv]
    rfl
  simp only [he,fieldSecond,first_coordinates]
  rw [linear_coordinates]
  have hl (w : Point) : fderiv ℝ (fderiv ℝ (fullSquarePotential q)) p v w=
      (v 0:ℂ)*fderiv ℝ (fderiv ℝ (fullSquarePotential q)) p (Pi.single 0 1) w+
      (v 1:ℂ)*fderiv ℝ (fderiv ℝ (fullSquarePotential q)) p (Pi.single 1 1) w := by
    conv_lhs => arg 1; rw [pi_eq_sum_univ' v,map_sum]
    simp [Fin.sum_univ_two,Complex.real_smul]
  rw [hl,hl]
  ring

private theorem field_path_first (q : XiZeroCopy) {g : ℝ → Point} {v : Point} {t : ℝ}
    (hg : HasDerivAt g v t) (hp : 0 < g t 1) :
    HasDerivAt (fun s => fullSquarePotential q (g s)) (fieldFirst q (g t) v) t :=
  ((fullSquarePotential_smooth q _ hp 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hg

private theorem field_path_second (q : XiZeroCopy) {g v : ℝ → Point} {a : Point} {t : ℝ}
    (hg : HasDerivAt g (v t) t) (hv : HasDerivAt v a t) (hp : 0 < g t 1) :
    HasDerivAt (fun s => fieldFirst q (g s) (v s)) (fieldSecond q (g t) (v t) a) t := by
  have hf := fullSquarePotential_smooth q _ hp 2
  have h := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hg
  exact h.clm_apply hv

def radialVelocity (d theta k : ℝ) : Point :=
  ![Real.exp k*offsetRadial d theta,Real.exp k*heightRadial d theta]
def radialAcceleration (d theta k : ℝ) : Point :=
  ![Real.exp k*offsetRadialSecond d theta,Real.exp k*heightRadialSecond d theta]
def angularVelocity (d theta k : ℝ) : Point :=
  ![Real.exp k*offsetAngular d theta,Real.exp k*heightAngular d theta]
def angularAcceleration (d theta k : ℝ) : Point :=
  ![Real.exp k*offsetAngularSecond d theta,Real.exp k*heightAngularSecond d theta]
def heightVelocity (d theta k : ℝ) : Point :=
  ![Real.exp k*offset d theta,Real.exp k*height d theta]

private theorem logCircle_radial (d theta x k : ℝ) :
    HasDerivAt (fun r => logCircle r theta x k) (radialVelocity d theta k) d ∧
    HasDerivAt (fun r => radialVelocity r theta k) (radialAcceleration d theta k) d := by
  obtain ⟨hA,hAA⟩ := offset_radial_derivatives d theta
  obtain ⟨hB,hBB⟩ := height_radial_derivatives d theta
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hA.const_mul (Real.exp k)).const_add x
    · exact hB.const_mul (Real.exp k)
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hAA.const_mul (Real.exp k)
    · exact hBB.const_mul (Real.exp k)

private theorem logCircle_angular (d theta x k : ℝ) :
    HasDerivAt (fun t => logCircle d t x k) (angularVelocity d theta k) theta ∧
    HasDerivAt (fun t => angularVelocity d t k) (angularAcceleration d theta k) theta := by
  obtain ⟨hA,hAA⟩ := offset_angular_derivatives d theta
  obtain ⟨hB,hBB⟩ := height_angular_derivatives d theta
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hA.const_mul (Real.exp k)).const_add x
    · exact hB.const_mul (Real.exp k)
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hAA.const_mul (Real.exp k)
    · exact hBB.const_mul (Real.exp k)

private theorem logCircle_horizontal (d theta x k : ℝ) :
    HasDerivAt (fun t => logCircle d theta t k) (Pi.single 0 1) x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [logCircle,circle] using (hasDerivAt_id x).add_const (Real.exp k*offset d theta)
  · simpa [logCircle,circle] using hasDerivAt_const x (Real.exp k*height d theta)

private theorem logCircle_height (d theta x k : ℝ) :
    HasDerivAt (fun t => logCircle d theta x t) (heightVelocity d theta k) k ∧
    HasDerivAt (fun t => heightVelocity d theta t) (heightVelocity d theta k) k := by
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((Real.hasDerivAt_exp k).mul_const (offset d theta)).const_add x
    · exact (Real.hasDerivAt_exp k).mul_const (height d theta)
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (Real.hasDerivAt_exp k).mul_const (offset d theta)
    · exact (Real.hasDerivAt_exp k).mul_const (height d theta)

def radialFirst (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldFirst q (logCircle d theta x k) (radialVelocity d theta k)
def radialSecond (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldSecond q (logCircle d theta x k) (radialVelocity d theta k) (radialAcceleration d theta k)
def angularFirst (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldFirst q (logCircle d theta x k) (angularVelocity d theta k)
def angularSecond (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldSecond q (logCircle d theta x k) (angularVelocity d theta k) (angularAcceleration d theta k)
def horizontalFirst (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldFirst q (logCircle d theta x k) (Pi.single 0 1)
def horizontalSecond (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldSecond q (logCircle d theta x k) (Pi.single 0 1) 0
def logHeightFirst (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldFirst q (logCircle d theta x k) (heightVelocity d theta k)
def logHeightSecond (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  fieldSecond q (logCircle d theta x k) (heightVelocity d theta k) (heightVelocity d theta k)

private theorem radial_first (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun r => source q r theta x k) (radialFirst q d theta x k) d :=
  field_path_first q (logCircle_radial d theta x k).1 (logCircle_pos d theta x k)
private theorem radial_second (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun r => radialFirst q r theta x k) (radialSecond q d theta x k) d :=
  field_path_second q (logCircle_radial d theta x k).1
    (logCircle_radial d theta x k).2 (logCircle_pos d theta x k)
private theorem angular_first (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => source q d t x k) (angularFirst q d theta x k) theta :=
  field_path_first q (logCircle_angular d theta x k).1 (logCircle_pos d theta x k)
private theorem angular_second (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => angularFirst q d t x k) (angularSecond q d theta x k) theta :=
  field_path_second q (logCircle_angular d theta x k).1
    (logCircle_angular d theta x k).2 (logCircle_pos d theta x k)
private theorem horizontal_first (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => source q d theta t k) (horizontalFirst q d theta x k) x :=
  field_path_first q (logCircle_horizontal d theta x k) (logCircle_pos d theta x k)
private theorem horizontal_second (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => horizontalFirst q d theta t k) (horizontalSecond q d theta x k) x :=
  field_path_second q (logCircle_horizontal d theta x k) (hasDerivAt_const x _)
    (logCircle_pos d theta x k)
private theorem height_first (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => source q d theta x t) (logHeightFirst q d theta x k) k :=
  field_path_first q (logCircle_height d theta x k).1 (logCircle_pos d theta x k)
private theorem height_second (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => logHeightFirst q d theta x t) (logHeightSecond q d theta x k) k :=
  field_path_second q (logCircle_height d theta x k).1
    (logCircle_height d theta x k).2 (logCircle_pos d theta x k)

/-- The full original theta half-square is smooth in radius, angle and both base coordinates. -/
theorem source_smooth (q : XiZeroCopy) :
    ContDiff ℝ ∞ (fun p : Fin 4 → ℝ => source q (p 0) (p 1) (p 2) (p 3)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle (p 0) (p 1) (p 2) (p 3)) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (logCircle_pos _ _ _ _) n)
  apply hs.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem polar_source (q : XiZeroCopy) (d theta x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*radialSecond q d theta x k+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*radialFirst q d theta x k+
      angularSecond q d theta x k=
      (Real.sinh d:ℂ)^(2 : ℕ)*scalarLaplacian (fullSquarePotential q) (logCircle d theta x k) := by
  have hp := logCircle_pos d theta x k
  obtain ⟨hxx,hxy,hyy⟩ := polar_principal d theta
  obtain ⟨hx,hy⟩ := polar_connection d theta
  have hxxC : (Real.sinh d:ℂ)^(2 : ℕ)*(offsetRadial d theta:ℂ)^(2 : ℕ)+(offsetAngular d theta:ℂ)^(2 : ℕ)=
      (Real.sinh d:ℂ)^(2 : ℕ)*(height d theta:ℂ)^(2 : ℕ) := by exact_mod_cast hxx
  have hxyC : (Real.sinh d:ℂ)^(2 : ℕ)*(offsetRadial d theta:ℂ)*(heightRadial d theta:ℂ)+
      (offsetAngular d theta:ℂ)*(heightAngular d theta:ℂ)=0 := by exact_mod_cast hxy
  have hyyC : (Real.sinh d:ℂ)^(2 : ℕ)*(heightRadial d theta:ℂ)^(2 : ℕ)+(heightAngular d theta:ℂ)^(2 : ℕ)=
      (Real.sinh d:ℂ)^(2 : ℕ)*(height d theta:ℂ)^(2 : ℕ) := by exact_mod_cast hyy
  have hxC : (Real.sinh d:ℂ)^(2 : ℕ)*(offsetRadialSecond d theta:ℂ)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(offsetRadial d theta:ℂ)+(offsetAngularSecond d theta:ℂ)=0 := by
    exact_mod_cast hx
  have hyC : (Real.sinh d:ℂ)^(2 : ℕ)*(heightRadialSecond d theta:ℂ)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(heightRadial d theta:ℂ)+(heightAngularSecond d theta:ℂ)=0 := by
    exact_mod_cast hy
  dsimp [radialSecond,radialFirst,angularSecond]
  rw [second_coordinates q _ _ _ hp,first_coordinates,second_coordinates q _ _ _ hp,
    scalarLaplacian_eq _ _ hp]
  dsimp [radialVelocity,radialAcceleration,angularVelocity,angularAcceleration,
    D4BMAngularSeries.hyperbolicLaplacian]
  simp only [Complex.ofReal_mul]
  have he : (logCircle d theta x k 1:ℂ)=(Real.exp k:ℂ)*(height d theta:ℂ) := by
    simp [logCircle,circle]
  rw [he]
  linear_combination
    (Real.exp k:ℂ)^(2 : ℕ)*coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle d theta x k)*hxxC+
    (Real.exp k:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 1 (fullSquarePotential q)) (logCircle d theta x k)+
      coordDeriv 1 (coordDeriv 0 (fullSquarePotential q)) (logCircle d theta x k))*hxyC+
    (Real.exp k:ℂ)^(2 : ℕ)*coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (logCircle d theta x k)*hyyC+
    (Real.exp k:ℂ)*coordDeriv 0 (fullSquarePotential q) (logCircle d theta x k)*hxC+
    (Real.exp k:ℂ)*coordDeriv 1 (fullSquarePotential q) (logCircle d theta x k)*hyC

/-- The actual theta field satisfies the polar Darboux identity with its complete angular Laplacian. -/
theorem source_darboux_integrand (q : XiZeroCopy) (d theta x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => source q r theta x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => source q r theta x k) d+
      deriv (deriv (fun t => source q d t x k)) theta=
      (Real.sinh d:ℂ)^(2 : ℕ)*scalarLaplacian (fullSquarePotential q) (logCircle d theta x k) := by
  have hr : deriv (fun r => source q r theta x k)=fun r => radialFirst q r theta x k :=
    funext (fun r => (radial_first q r theta x k).deriv)
  have ha : deriv (fun t => source q d t x k)=fun t => angularFirst q d t x k :=
    funext (fun t => (angular_first q d t x k).deriv)
  rw [hr,ha,(radial_second q d theta x k).deriv,(angular_second q d theta x k).deriv]
  exact polar_source q d theta x k

def horizontalAngularDerivative (q : XiZeroCopy) (d theta x k : ℝ) : ℂ :=
  (Real.exp k:ℂ)*(offsetAngular d theta:ℂ)*
    coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle d theta x k)+
  (Real.exp k:ℂ)*(heightAngular d theta:ℂ)*
    coordDeriv 1 (coordDeriv 0 (fullSquarePotential q)) (logCircle d theta x k)

private theorem horizontal_angular (q : XiZeroCopy) (d theta x k : ℝ) :
    HasDerivAt (fun t => coordDeriv 0 (fullSquarePotential q) (logCircle d t x k))
      (horizontalAngularDerivative q d theta x k) theta := by
  have hf := fullSquarePotential_smooth q _ (logCircle_pos d theta x k) 2
  apply ((coordDeriv_hasFDerivAt hf 0).comp_hasDerivAt theta
    (logCircle_angular d theta x k).1).congr_deriv
  rw [linear_coordinates]
  dsimp [horizontalAngularDerivative,angularVelocity,coordDeriv]
  rw [(coordDeriv_hasFDerivAt hf 0).fderiv]
  simp only [Complex.ofReal_mul,ContinuousLinearMap.flip_apply]

private theorem base_source (q : XiZeroCopy) (d theta x k : ℝ) :
    (Real.exp k:ℂ)^(2 : ℕ)*horizontalSecond q d theta x k+logHeightSecond q d theta x k-
      logHeightFirst q d theta x k-
      scalarLaplacian (fullSquarePotential q) (logCircle d theta x k)=
      -2*(Real.exp k:ℂ)*horizontalAngularDerivative q d theta x k := by
  have hp := logCircle_pos d theta x k
  have hf := fullSquarePotential_smooth q _ hp 2
  obtain ⟨hx,hy⟩ := base_laplacian_coefficients d theta
  have hxC : 1+(offset d theta:ℂ)^(2 : ℕ)-(height d theta:ℂ)^(2 : ℕ) = -2*(offsetAngular d theta:ℂ) := by
    exact_mod_cast hx
  have hyC : 2*(offset d theta:ℂ)*(height d theta:ℂ) = -2*(heightAngular d theta:ℂ) := by
    exact_mod_cast hy
  dsimp [horizontalSecond,logHeightSecond,logHeightFirst,horizontalAngularDerivative]
  rw [second_coordinates q _ _ _ hp,second_coordinates q _ _ _ hp,first_coordinates,
    scalarLaplacian_eq _ _ hp,coordDeriv_commute hf 0 1]
  simp only [heightVelocity,Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (1:Fin 2) ≠ 0),
    Pi.zero_apply,Complex.ofReal_zero,Complex.ofReal_one,Matrix.cons_val_zero,
    Matrix.cons_val_one,Complex.ofReal_mul]
  have he : (logCircle d theta x k 1:ℂ)=(Real.exp k:ℂ)*(height d theta:ℂ) := by
    simp [logCircle,circle]
  rw [he]
  linear_combination
    (Real.exp k:ℂ)^(2 : ℕ)*coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle d theta x k)*hxC+
    (Real.exp k:ℂ)^(2 : ℕ)*coordDeriv 1 (coordDeriv 0 (fullSquarePotential q)) (logCircle d theta x k)*hyC

/-- The actual base-point hyperbolic Laplacian differs from the transported source Laplacian
by an explicit derivative around the original circle. -/
theorem source_base_laplacian_integrand (q : XiZeroCopy) (d theta x k : ℝ) :
    (Real.exp k:ℂ)^(2 : ℕ)*deriv (deriv (fun t => source q d theta t k)) x+
      deriv (deriv (fun t => source q d theta x t)) k-
      deriv (fun t => source q d theta x t) k-
      scalarLaplacian (fullSquarePotential q) (logCircle d theta x k)=
      -2*(Real.exp k:ℂ)*deriv (fun t => coordDeriv 0 (fullSquarePotential q) (logCircle d t x k)) theta := by
  have hx : deriv (fun t => source q d theta t k)=fun t => horizontalFirst q d theta t k :=
    funext (fun t => (horizontal_first q d theta t k).deriv)
  have hk : deriv (fun t => source q d theta x t)=fun t => logHeightFirst q d theta x t :=
    funext (fun t => (height_first q d theta x t).deriv)
  rw [hx,hk,(horizontal_second q d theta x k).deriv,(height_second q d theta x k).deriv,
    (horizontal_angular q d theta x k).deriv]
  exact base_source q d theta x k

/-- Horizontal base differentiation is the original theta-source derivative at the circle point. -/
theorem source_horizontal_derivative (q : XiZeroCopy) (d theta x k : ℝ) :
    deriv (fun t => source q d theta t k) x=
      coordDeriv 0 (fullSquarePotential q) (logCircle d theta x k) :=
  (horizontal_first q d theta x k).deriv

end
end RHTower.D4BMNativeCircle
