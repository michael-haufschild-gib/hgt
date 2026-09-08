import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceFieldDifferential

/-! Compactification of the full original wave with its actual modular angular operator retained. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMHorizon D4BMAngularSeries
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- A full angular-dependent field with the literal original horizon phase restored. -/
def compactHorizonField (w : ℂ) (V : ℝ → Point → ℂ) (t : ℝ) (z : Point) : ℂ :=
  dress w (fun b => V b z) (horizonCoordinate t)

/-- The compactified full operator retains the actual angular Laplacian and actual radial derivatives. -/
def compactHorizonOperator (w : ℂ) (V : ℝ → Point → ℂ) (b : ℝ) (z : Point) : ℂ :=
  4*(b:ℂ)*(1-b)*deriv (deriv (fun x => V x z)) b+
    (4*(w+1)-(4*w+6)*b)*deriv (fun x => V x z) b+
      scalarLaplacian (V b) z-w*(w+1)*V b z

/-- The two displayed compactification jets are actual tortoise derivatives of the full field. -/
theorem compactHorizonField_hasDerivAt (w : ℂ) (V : ℝ → Point → ℂ) (z : Point)
    (hV : ∀ b ∈ Ioo (0:ℝ) 1, ContDiffAt ℝ 2 (fun x => V x z) b) (t : ℝ) (ht : t < 0) :
    let D := deriv (fun b => V b z)
    let DD := deriv D
    HasDerivAt (fun r => compactHorizonField w V r z)
      ((coordinateFirst t:ℂ)*dressFirst w (fun b => V b z) D (horizonCoordinate t)) t ∧
    HasDerivAt (fun r => (coordinateFirst r:ℂ)*dressFirst w (fun b => V b z) D (horizonCoordinate r))
      ((coordinateFirst t:ℂ)^2*dressSecond w (fun b => V b z) D DD (horizonCoordinate t)+
        (coordinateSecond t:ℂ)*dressFirst w (fun b => V b z) D (horizonCoordinate t)) t := by
  dsimp only
  have hb := horizonCoordinate_interior t ht
  have hd := dress_derivatives w hb.1
    ((hV _ hb).differentiableAt (by norm_num)).hasDerivAt
    (((hV _ hb).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hc := horizonCoordinate_hasDerivAt t
  have hfirst := hd.1.scomp t hc
  have hsecond := hd.2.scomp t hc
  constructor
  · simpa only [compactHorizonField,Function.comp_def,Complex.real_smul] using! hfirst
  · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul hsecond).congr_deriv
    simp only [Function.comp_apply,Complex.real_smul]
    ring

/-- The full compactified wave is exactly the original metric wave, with no angular spectral substitution. -/
theorem compactHorizonField_original_wave (w : ℂ) (V : ℝ → Point → ℂ) (z : Point)
    (hz : 0 < z 1) (hV : ∀ b ∈ Ioo (0:ℝ) 1, ContDiffAt ℝ 2 (fun x => V x z) b)
    (t : ℝ) (ht : t < 0) (hA : ContDiffAt ℝ 2 (V (horizonCoordinate t)) z) :
    fieldWave w (compactHorizonField w V) t z =
      -power (w/2) (horizonCoordinate t)*(horizonCoordinate t:ℂ)*
        compactHorizonOperator w V (horizonCoordinate t) z := by
  let D := deriv (fun b => V b z)
  let DD := deriv D
  have he : deriv (fun r => compactHorizonField w V r z) =ᶠ[𝓝 t]
      (fun r => (coordinateFirst r:ℂ)*dressFirst w (fun b => V b z) D (horizonCoordinate r)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with r hr
    exact (compactHorizonField_hasDerivAt w V z hV r hr).1.deriv
  have hdd := (compactHorizonField_hasDerivAt w V z hV t ht).2.deriv
  have hb0 : (horizonCoordinate t:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (horizonCoordinate_interior t ht).1)
  have hu : (radialUnit t:ℂ)^2 = 1-(horizonCoordinate t:ℂ) := by
    simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    ring
  unfold fieldWave
  rw [he.deriv_eq,hdd]
  simp_rw [scalarLaplacian_eq _ z hz]
  change w^2*compactHorizonField w V t z-_
      -(horizonCoordinate t:ℂ)*hyperbolicLaplacian
        (fun y => power (w/2) (horizonCoordinate t)*V (horizonCoordinate t) y) z = _
  rw [hyperbolicLaplacian_const_mul hA]
  dsimp only [compactHorizonField,compactHorizonOperator,dress,dressFirst,dressSecond,powerFirst,powerSecond,
    coordinateFirst,coordinateSecond,D,DD]
  rw [scalarLaplacian_eq _ z hz]
  push_cast
  simp only [mul_pow,hu]
  unfold hyperbolicLaplacian
  field_simp [hb0]
  ring

/-- The original compactified operator's horizon trace fixes its first normal jet and retains the full angular term. -/
theorem compactHorizonOperator_boundary (w : ℂ) (V : ℝ → Point → ℂ) (z : Point) :
    compactHorizonOperator w V 0 z = 4*(w+1)*deriv (fun b => V b z) 0+
      scalarLaplacian (V 0) z-w*(w+1)*V 0 z := by
  simp only [compactHorizonOperator,Complex.ofReal_zero,mul_zero,zero_mul,sub_zero,zero_add]

end
end RHTower.D4BMJointSource
