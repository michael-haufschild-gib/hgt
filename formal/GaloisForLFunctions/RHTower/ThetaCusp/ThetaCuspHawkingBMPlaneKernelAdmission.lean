import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteSourceAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedSourceHorizon

open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMFixedSourceHorizon
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The original source-time denominator in physical hyperbolic radius. -/
def planeDen (x d : ℝ) : ℝ := Real.cosh x*Real.cosh d+Real.sinh x

private def planeScale (x : ℝ) : ℝ := min (Real.cosh x) (Real.exp x)/2

private theorem planeScale_pos (x : ℝ) : 0 < planeScale x := by
  exact div_pos (lt_min (Real.cosh_pos x) (Real.exp_pos x)) (by norm_num)

/-- Exponential control is uniform in source radius and uses a strictly positive target factor. -/
theorem planeDen_lower (x d : ℝ) : planeScale x*Real.exp d ≤ planeDen x d := by
  let a := min (Real.cosh x) (Real.exp x)
  have ha : 0 ≤ a := le_of_lt (lt_min (Real.cosh_pos x) (Real.exp_pos x))
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (Real.cosh x) (Real.exp x))
    (sub_nonneg.mpr (Real.one_le_cosh d))
  have h2 := min_le_right (Real.cosh x) (Real.exp x)
  have hD : a*Real.cosh d ≤ planeDen x d := by
    dsimp [a,planeDen]
    nlinarith [Real.cosh_add_sinh x]
  have he : Real.exp d ≤ 2*Real.cosh d := by
    linarith [Real.cosh_add_sinh d,Real.cosh_sub_sinh d,Real.exp_pos (-d)]
  calc
    _ ≤ planeScale x*(2*Real.cosh d) :=
      mul_le_mul_of_nonneg_left he (planeScale_pos x).le
    _ = a*Real.cosh d := by dsimp [planeScale,a]; ring
    _ ≤ _ := hD

theorem planeDen_pos (x d : ℝ) : 0 < planeDen x d :=
  (mul_pos (planeScale_pos x) (Real.exp_pos d)).trans_le (planeDen_lower x d)

/-- This is the same source-time denominator as the fixed source-radius cap. -/
theorem planeDen_eq_sourceDen (x d : ℝ) :
    planeDen x d = sourceDen x (Real.log (Real.cosh d)) := by
  rw [sourceDen,Real.exp_log (Real.cosh_pos d)]
  rfl

/-- Original onset derivative and denominator in fixed-plane coordinates. -/
def planeKernel (s : ℂ) (tau x : ℝ) (w z : ℍ) : ℂ :=
  (Real.cosh x:ℂ)*timeOnsetFirst s (tau+Real.log (planeDen x (dist z w)))/
    (planeDen x (dist z w):ℂ)

theorem planeKernel_continuous (s : ℂ) (tau x : ℝ) (w : ℍ) :
    Continuous (planeKernel s tau x w) := by
  have hD : Continuous (fun z : ℍ => planeDen x (dist z w)) := by
    unfold planeDen
    fun_prop
  have ho : Continuous (timeOnsetFirst s) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnsetFirst_hasDerivAt s u).continuousAt)
  have ht : Continuous (fun z : ℍ => tau+Real.log (planeDen x (dist z w))) :=
    continuous_const.add (hD.log (fun z => (planeDen_pos x (dist z w)).ne'))
  exact (continuous_const.mul (ho.comp ht)).div
    (Complex.continuous_ofReal.comp hD)
    (fun z => Complex.ofReal_ne_zero.mpr (planeDen_pos x (dist z w)).ne')

/-- The literal onset kernel has the decay exponent supplied by its original time rate. -/
theorem planeKernel_bound (s : ℂ) (hs : s.re ≤ 1) (tau x : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w z : ℍ,
      ‖planeKernel s tau x w z‖ ≤ C*Real.exp (-(1-s.re)*dist z w) := by
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound s (-s.re) (by simp)
  refine ⟨Real.cosh x*B*Real.exp (s.re*tau+(s.re-1)*Real.log (planeScale x)),
    by positivity,?_⟩
  intro w z
  let d := dist z w
  let D := planeDen x d
  have hD : 0 < D := planeDen_pos x d
  have hL : Real.log (planeScale x)+d ≤ Real.log D := by
    have h := Real.log_le_log (mul_pos (planeScale_pos x) (Real.exp_pos d))
      (planeDen_lower x d)
    rw [Real.log_mul (planeScale_pos x).ne' (Real.exp_pos d).ne',Real.log_exp] at h
    exact h
  have ho : ‖timeOnsetFirst s (tau+Real.log D)‖ ≤
      B*Real.exp (s.re*(tau+Real.log D)) := by
    have h := hb (tau+Real.log D)
    simp only [neg_neg] at h
    linarith [norm_nonneg (timeOnset s (tau+Real.log D))]
  have he : Real.exp (s.re*(tau+Real.log D))/D =
      Real.exp (s.re*tau+(s.re-1)*Real.log D) := by
    calc
      _ = Real.exp (s.re*(tau+Real.log D))/Real.exp (Real.log D) := by rw [Real.exp_log hD]
      _ = Real.exp (s.re*(tau+Real.log D)-Real.log D) := (Real.exp_sub _ _).symm
      _ = _ := by congr 1; ring
  change ‖(Real.cosh x:ℂ)*timeOnsetFirst s (tau+Real.log D)/(D:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,Complex.norm_of_nonneg (Real.cosh_pos x).le,
    Complex.norm_of_nonneg hD.le]
  calc
    _ ≤ Real.cosh x*(B*Real.exp (s.re*(tau+Real.log D)))/D := by gcongr
    _ = (Real.cosh x*B)*(Real.exp (s.re*(tau+Real.log D))/D) := by ring
    _ = (Real.cosh x*B)*Real.exp (s.re*tau+(s.re-1)*Real.log D) := by rw [he]
    _ ≤ (Real.cosh x*B)*Real.exp (s.re*tau+(s.re-1)*(Real.log (planeScale x)+d)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.cosh_pos x).le hB)
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonpos_left hL (sub_nonpos.mpr hs)]
    _ = _ := by
      rw [show s.re*tau+(s.re-1)*(Real.log (planeScale x)+d) =
        (s.re*tau+(s.re-1)*Real.log (planeScale x))+(-(1-s.re)*d) by ring,Real.exp_add]
      ring

/-- Exact density after the substitution h=log(cosh(d)); the original source Jacobian survives. -/
theorem planeKernel_radial_density (s : ℂ) (tau x : ℝ) (w z : ℍ) :
    (sourceJac x (Real.log (Real.cosh (dist z w))):ℂ)*
      timeOnsetFirst s (sourceTime tau x (Real.log (Real.cosh (dist z w))))*
      ((Real.sinh (dist z w)/Real.cosh (dist z w):ℝ):ℂ) =
    planeKernel s tau x w z*(Real.sinh (dist z w):ℂ) := by
  have cancel (a b c d e : ℂ) (hb : b ≠ 0) :
      (a*b/d)*c*(e/b) = (a*c/d)*e := by
    calc
      _ = ((a*c/d)*e)*(b/b) := by ring
      _ = _ := by rw [div_self hb,mul_one]
  rw [sourceJac,sourceTime,Real.exp_log (Real.cosh_pos _),← planeDen_eq_sourceDen]
  unfold planeKernel
  simp only [Complex.ofReal_div,Complex.ofReal_mul]
  exact cancel _ _ _ _ _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos (dist z w)).ne')

/-- The full physical source is absolutely admitted against the original plane kernel. -/
theorem physical_plane_source_integrable (q : XiZeroCopy) (branch : Bool)
    (tau x : ℝ) (w : ℍ) :
    Integrable (fun z : ℍ => planeKernel (2*physicalRate q branch) tau x w z*
      (fullAngular q branch z-
        (physicalRate q branch*(physicalRate q branch-1)/4)*
          fullSquarePotential q (coordinates z))) := by
  let s := physicalRate q branch
  let a := s*(s-1)/4
  let F : ℍ → ℂ := fun z => fullAngular q branch z-a*fullSquarePotential q (coordinates z)
  have hs : (2*s).re < -2 := by
    norm_num [Complex.mul_re]
    change 2*(physicalRate q branch).re < -2
    linarith [(fundamental_physicalRate_re_bounds q branch).2]
  have hF : Continuous F := (ChartSmooth.continuous (fullAngular_smooth q branch)).sub
    ((fullSquarePotential_upperHalfPlane_continuous q).const_mul a)
  have hi := fullAngular_sub_square_radial_weight_integrable_at q branch a
    (1-(2*s).re) (by linarith) w
  obtain ⟨C,hC,hk⟩ := planeKernel_bound (2*s) (by linarith) tau x
  have hc := (planeKernel_continuous (2*s) tau x w).mul hF
  apply (hi.const_mul C).mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  change ‖planeKernel (2*s) tau x w z*F z‖ ≤
    C*(Real.exp (-(1-(2*s).re)*dist z w)*‖F z‖)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hk w z) (norm_nonneg (F z))).trans_eq (mul_assoc _ _ _)

/-- Absolute admission retains the original squared amplitude, normalization, and both horizon arms. -/
theorem original_combined_plane_integrable (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (tau x : ℝ) (w : ℍ) :
    Integrable (fun z : ℍ =>
      (parameter q branch*D4BMLaplaceRadial.power (2*physicalRate q branch) 2*amp^(2 : ℕ)/
        (2*Real.pi:ℂ))*
      ((planeKernel (2*physicalRate q branch) tau x w z-
        planeKernel (2*physicalRate q branch) tau (-x) w z)*
        (fullAngular q branch z-
          (physicalRate q branch*(physicalRate q branch-1)/4)*
            fullSquarePotential q (coordinates z)))) := by
  have h := ((physical_plane_source_integrable q branch tau x w).sub
    (physical_plane_source_integrable q branch tau (-x) w)).const_mul
    (parameter q branch*D4BMLaplaceRadial.power (2*physicalRate q branch) 2*amp^(2 : ℕ)/
      (2*Real.pi:ℂ))
  exact h.congr (Eventually.of_forall (fun z => by dsimp only [Pi.sub_apply]; ring))

end
end RHTower.D4BMFixedSourceHorizon
