import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Recovering strip type from the two axes

Subquadratic entire growth plus real-axis decay and imaginary-axis exponential
type propagate to a global strip estimate. Polynomial damping uses a larger
type for each decay order; compact-support recovery needs only order two.
-/

open Complex Filter Topology Set Asymptotics Bornology
noncomputable section
namespace GaloisForLFunctions.HTGeometry

def SubquadraticType (f : ℂ → ℂ) : Prop :=
  ∃ p : ℝ,1≤p ∧ p<2 ∧ ∃ A B : ℝ,0≤A ∧ 0≤B ∧
    ∀ z,‖f z‖≤A*Real.exp (B*‖z‖^p)

private theorem linear_le_one_add_rpow {p r : ℝ} (hp : 1≤p) (hr : 0≤r) :
    r≤1+r^p := by
  by_cases h1 : 1≤r
  · have hh : r≤r^p := by simpa using Real.rpow_le_rpow_of_exponent_le h1 hp
    linarith
  · linarith [Real.rpow_nonneg hr p]

private theorem norm_axis_damped (f : ℂ → ℂ) (n : ℕ) (a : ℝ) (z : ℂ) :
    ‖f z*(z+I)^n*Complex.exp (I*(a : ℂ)*z)‖=
      ‖f z‖*‖z+I‖^n*Real.exp (-a*z.im) := by
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.mul_im]

theorem SubquadraticType.const_mul_pow {f : ℂ → ℂ} (h : SubquadraticType f)
    (a : ℂ) (n : ℕ) : SubquadraticType (fun z => a*z^n*f z) := by
  obtain ⟨p,hp,hp2,A,B,hA,hB,hb⟩ := h
  refine ⟨p,hp,hp2,‖a‖*A*Real.exp n,B+n,by positivity,by positivity,fun z => ?_⟩
  have hr : ‖z‖≤Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have hpow := pow_le_pow_left₀ (norm_nonneg z) hr n
  rw [← Real.exp_nat_mul] at hpow
  rw [norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ ‖a‖*Real.exp ((n : ℝ)*‖z‖)*(A*Real.exp (B*‖z‖^p)) := by
      gcongr
      exact hb z
    _ = (‖a‖*A)*Real.exp ((n : ℝ)*‖z‖+B*‖z‖^p) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      rw [mul_assoc (‖a‖*A),← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hA)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (linear_le_one_add_rpow hp (norm_nonneg z))
        (Nat.cast_nonneg (α := ℝ) n)
      nlinarith

theorem SubquadraticType.axis_damped {f : ℂ → ℂ} (h : SubquadraticType f)
    (n : ℕ) (a : ℝ) :
    SubquadraticType (fun z => f z*(z+I)^n*Complex.exp (I*(a : ℂ)*z)) := by
  obtain ⟨p,hp,hp2,A,B,hA,hB,hb⟩ := h
  refine ⟨p,hp,hp2,A*Real.exp ((n : ℝ)+|a|),B+n+|a|,by positivity,by positivity,fun z => ?_⟩
  have hpoly : ‖z+I‖^n≤Real.exp ((n : ℝ)*‖z‖) := by
    have hh : ‖z+I‖≤Real.exp ‖z‖ := by
      calc
        ‖z+I‖≤‖z‖+1 := by simpa using norm_add_le z I
        _ ≤ Real.exp ‖z‖ := Real.add_one_le_exp _
    have hh' := pow_le_pow_left₀ (norm_nonneg (z+I)) hh n
    rwa [← Real.exp_nat_mul] at hh'
  have hphase : Real.exp (-a*z.im)≤Real.exp (|a| * ‖z‖) := by
    apply Real.exp_le_exp.mpr
    calc
      -a*z.im = -(a*z.im) := by ring
      _ ≤ |a*z.im| := neg_le_abs _
      _ = |a| * |z.im| := abs_mul _ _
      _ ≤ |a| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (abs_nonneg _)
  rw [norm_axis_damped]
  calc
    _ ≤ (A*Real.exp (B*‖z‖^p))*Real.exp ((n : ℝ)*‖z‖)*Real.exp (|a| * ‖z‖) := by
      gcongr
      exact hb z
    _ ≤ _ := by
      rw [mul_assoc A,← Real.exp_add,mul_assoc A,← Real.exp_add,
        mul_assoc A,← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (linear_le_one_add_rpow hp (norm_nonneg z))
        (show 0≤(n : ℝ)+|a| by positivity)
      nlinarith

/-- Propagate a real-axis polynomial weight and an imaginary-axis type into
the upper half-plane. No global exponential type is assumed for `f`. -/
theorem upper_weighted_bound_of_axes {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hs : SubquadraticType f) (n : ℕ) {M R T : ℝ} (hR : 0≤R)
    (hre : ∀ x : ℝ,‖f x‖*(1+|x|)^n≤M)
    (him : ∀ y : ℝ,0≤y → ‖f ((y : ℂ)*I)‖≤R*Real.exp (T*y))
    (z : ℂ) (hz : 0≤z.im) :
    ‖f z‖*‖z+I‖^n≤max M R*Real.exp ((T+n)*z.im) := by
  let a : ℝ := T+n
  let G := fun w : ℂ => f w*(w+I)^n*Complex.exp (I*(a : ℂ)*w)
  have hG : Differentiable ℂ G := (hf.mul (by fun_prop)).mul (by fun_prop)
  obtain ⟨p,_,hp,A,B,_,_,hb⟩ := hs.axis_damped n a
  have hO (s : Set ℂ) : G =O[cobounded ℂ ⊓ 𝓟 s] fun w => Real.exp (B*‖w‖^p) := by
    apply IsBigO.of_bound A
    filter_upwards with w
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hb w
  have hGr (x : ℝ) : ‖G x‖≤max M R := by
    dsimp only [G]
    rw [norm_axis_damped]
    simp only [Complex.ofReal_im,mul_zero,Real.exp_zero,mul_one]
    apply (le_max_left M R).trans'
    apply (hre x).trans'
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _) _ n
    calc
      ‖(x : ℂ)+I‖≤‖(x : ℂ)‖+‖I‖ := norm_add_le _ _
      _ = 1+|x| := by rw [Complex.norm_real,Real.norm_eq_abs,Complex.norm_I]; ring
  have hGi (y : ℝ) (hy : 0≤y) : ‖G ((y : ℂ)*I)‖≤max M R := by
    have hnorm : ‖(y : ℂ)*I+I‖=1+y := by
      rw [show (y : ℂ)*I+I=((1+y : ℝ) : ℂ)*I by push_cast; ring,norm_mul,Complex.norm_I,mul_one,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hpoly : (1+y)^n≤Real.exp ((n : ℝ)*y) := by
      have hh := pow_le_pow_left₀ (show 0≤1+y by positivity)
        (show 1+y≤Real.exp y by linarith [Real.add_one_le_exp y]) n
      rwa [← Real.exp_nat_mul] at hh
    dsimp only [G]
    rw [norm_axis_damped,hnorm]
    simp only [Complex.mul_I_im,Complex.ofReal_re]
    calc
      _ ≤ (R*Real.exp (T*y))*Real.exp ((n : ℝ)*y)*Real.exp (-a*y) := by
        gcongr
        exact him y hy
      _ = R := by rw [mul_assoc R,← Real.exp_add,mul_assoc R,← Real.exp_add]; dsimp [a]; ring_nf; simp
      _ ≤ max M R := le_max_right _ _
  have hbound : ‖G z‖≤max M R := by
    rcases le_total 0 z.re with hx | hx
    · exact PhragmenLindelof.quadrant_I hG.diffContOnCl ⟨p,hp,B,hO _⟩
        (fun x _ => hGr x) hGi hx hz
    · exact PhragmenLindelof.quadrant_II hG.diffContOnCl ⟨p,hp,B,hO _⟩
        (fun x _ => hGr x) hGi hx hz
  have hh := mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg (a*z.im))
  dsimp only [G] at hh
  rw [norm_axis_damped,mul_assoc _ (Real.exp (-a*z.im)),← Real.exp_add,
    show -a*z.im+a*z.im=0 by ring,Real.exp_zero,mul_one] at hh
  exact hh

theorem quadratic_strip_bound_of_axes {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (he : Function.Even f) (hs : SubquadraticType f) {M R T : ℝ} (hR : 0≤R)
    (hT : 0≤T) (hre : ∀ x : ℝ,‖f x‖*(1+|x|)^2≤M)
    (him : ∀ y : ℝ,0≤y → ‖f ((y : ℂ)*I)‖≤R*Real.exp (T*y)) :
    ∃ C A : ℝ,0≤C ∧ 0≤A ∧ ∀ z,
      ‖f z‖≤C*Real.exp (A*|z.im|)*(1+z.re^2)⁻¹ := by
  refine ⟨max M R,T+2,hR.trans (le_max_right _ _),by linarith,fun z => ?_⟩
  have hupper (w : ℂ) (hw : 0≤w.im) :
      ‖f w‖≤max M R*Real.exp ((T+2)*w.im)*(1+w.re^2)⁻¹ := by
    have hh := upper_weighted_bound_of_axes hf hs 2 hR hre him w hw
    have hden : 1+w.re^2≤‖w+I‖^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,add_zero]
      nlinarith
    have hc := (mul_le_mul_of_nonneg_left hden (norm_nonneg (f w))).trans hh
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact hc
  by_cases hz : 0≤z.im
  · simpa only [abs_of_nonneg hz] using hupper z hz
  · have hh := hupper (-z) (by simp only [Complex.neg_im]; linarith)
    rw [he z] at hh
    simpa only [Complex.neg_re,Complex.neg_im,neg_sq,abs_of_neg (lt_of_not_ge hz)] using hh

end GaloisForLFunctions.HTGeometry
