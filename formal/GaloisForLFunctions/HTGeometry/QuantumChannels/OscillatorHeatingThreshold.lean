import GaloisForLFunctions.RHTower.OperatorWinding
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-!
# Stability and the critical drift of a heated oscillator

The shifted three-dimensional moment matrix in Donadi–Lobo–Fadel (47) has a
single real growth rate. Its left eigenvector selects a scalar observable
even in the forced equations. At the critical damping that observable has a
strictly positive constant drift for a positive bath and nonzero noise.
-/

noncomputable section
namespace GaloisForLFunctions.OscillatorHeating
open Matrix
open scoped NNReal

/-- Heating strength for which r is the undamped real growth exponent.
The physical frequency is exp w. -/
def strength (w r : ℝ) : ℝ := 2*r+r^3/(2*(Real.exp w)^2)

theorem strength_strictMono (w : ℝ) : StrictMono (strength w) := by
  intro a b hab
  have hs : 0 ≤ a^2+a*b+b^2 := by nlinarith only [sq_nonneg (a+b),sq_nonneg a,sq_nonneg b]
  have hp : 0 ≤ (b-a)*(a^2+a*b+b^2) := mul_nonneg (sub_nonneg.mpr hab.le) hs
  have hc : a^3 ≤ b^3 := by nlinarith only [hp]
  exact add_lt_add_of_lt_of_le (by linarith only [hab])
    (div_le_div_of_nonneg_right hc (by positivity))

private theorem root_exists (w : ℝ) (G : ℝ≥0) :
    ∃ r ∈ Set.Icc (0:ℝ) (G/2:ℝ), strength w r = G := by
  have h : Continuous (strength w) := by unfold strength; fun_prop
  apply intermediate_value_Icc (by positivity) h.continuousOn
  constructor
  · simpa [strength] using G.2
  · unfold strength
    have hp : 0 ≤ ((G:ℝ)/2)^3/(2*(Real.exp w)^2) := by positivity
    linarith only [hp]

/-- Unique nonnegative real growth exponent of the undamped moment matrix. -/
def growth (w : ℝ) (G : ℝ≥0) : ℝ := (root_exists w G).choose

theorem growth_interval (w : ℝ) (G : ℝ≥0) : growth w G ∈ Set.Icc 0 ((G:ℝ)/2) :=
  (root_exists w G).choose_spec.1

@[simp] theorem strength_growth (w : ℝ) (G : ℝ≥0) : strength w (growth w G) = G :=
  (root_exists w G).choose_spec.2

theorem growth_lt_iff (w d : ℝ) (G : ℝ≥0) : growth w G < d ↔ (G:ℝ) < strength w d := by
  rw [← (strength_strictMono w).lt_iff_lt (a := growth w G) (b := d),strength_growth]

/-- The shortfall from the high-frequency limiting rate is exactly cubic
in the growth exponent and inverse quadratic in the frequency. -/
theorem growth_gap (w : ℝ) (G : ℝ≥0) :
    (Real.exp w)^2*((G:ℝ)/2-growth w G) = (growth w G)^3/4 := by
  have h := strength_growth w G
  unfold strength at h
  field_simp [Real.exp_ne_zero] at h
  linarith only [h]

/-- The characteristic matrix zI−A in the kinetic, potential and covariance coordinates. -/
def pencil (w d : ℝ) (G : ℝ≥0) (z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![z+d,0,(Real.exp w:ℂ)^2/2; -(G:ℂ),z+d,-(Real.exp w:ℂ)^2/2; -4,4,z+d]

theorem determinant (w d : ℝ) (G : ℝ≥0) (z : ℂ) :
    (pencil w d G z).det = (z+d)^3+4*(Real.exp w:ℂ)^2*(z+d)-2*(G:ℂ)*(Real.exp w:ℂ)^2 := by
  simp [pencil,Matrix.det_fin_three]
  ring

/-- Frequency of the complex conjugate pair. -/
def sideFrequency (w r : ℝ) := Real.sqrt (4*(Real.exp w)^2+3*r^2/4)

private theorem side_sq (w r : ℝ) : (sideFrequency w r)^2 = 4*(Real.exp w)^2+3*r^2/4 :=
  Real.sq_sqrt (by positivity)

theorem roots (w d : ℝ) (G : ℝ≥0) (z : ℂ) :
    let r := growth w G
    let b := sideFrequency w r
    (pencil w d G z).det = 0 ↔
      z = ((r-d:ℝ):ℂ) ∨ z = ((-d-r/2:ℝ):ℂ)+b*Complex.I ∨
        z = ((-d-r/2:ℝ):ℂ)-b*Complex.I := by
  intro r b
  have h := growth_gap w G
  have hc : (Real.exp w:ℂ)^2*((G:ℂ)/2-(r:ℂ)) = (r:ℂ)^3/4 := by exact_mod_cast h
  have hb : (b:ℂ)^2 = 4*(Real.exp w:ℂ)^2+3*(r:ℂ)^2/4 := by exact_mod_cast side_sq w r
  have hI : ((b:ℂ)*Complex.I)^2 = -(b:ℂ)^2 := by rw [mul_pow,Complex.I_sq,mul_neg_one]
  have hf : (pencil w d G z).det =
      (z-((r-d:ℝ):ℂ))*(z-(((-d-r/2:ℝ):ℂ)+b*Complex.I))*
        (z-(((-d-r/2:ℝ):ℂ)-b*Complex.I)) := by
    rw [determinant]
    push_cast
    linear_combination -4*hc + (z+d-r)*(hI-hb)
  rw [hf]
  simp only [mul_eq_zero,sub_eq_zero,or_assoc]

/-- On the real axis the shifted cubic has the sign of its real-root factor.
The other pair contributes a strictly positive damped quadratic. -/
theorem real_dispersion_sign (w d : ℝ) (G : ℝ≥0) (x : ℝ) :
    0 < (x+d)^3+4*(Real.exp w)^2*(x+d)-2*(G:ℝ)*(Real.exp w)^2 ↔
      growth w G-d < x := by
  let r := growth w G
  let a := -d-r/2
  let b := sideFrequency w r
  have hb : 0 < b := by dsimp [b,sideFrequency]; positivity
  have hq := _root_.RHTower.dampedChar_pos (a := a) hb.ne' x
  have h := growth_gap w G
  have he : (x+d)^3+4*(Real.exp w)^2*(x+d)-2*(G:ℝ)*(Real.exp w)^2 =
      (x-(r-d))*(x^2-2*a*x+(a^2+b^2)) := by
    dsimp only [a,b]
    rw [side_sq]
    linear_combination -4*h
  rw [he,mul_pos_iff_of_pos_right hq,sub_pos]

/-- Every spectral exponent decays exactly when damping exceeds the real growth rate. -/
theorem spectral_stability (w d : ℝ) (G : ℝ≥0) :
    (∀ z : ℂ, (pencil w d G z).det = 0 → z.re < 0) ↔ (G:ℝ) < strength w d := by
  rw [← growth_lt_iff]
  have hr := (growth_interval w G).1
  constructor
  · intro h
    have h0 := h _ ((roots w d G _).2 (Or.inl rfl))
    simpa using sub_neg.mp (show growth w G-d < 0 from h0)
  · intro hd z hz
    rcases (roots w d G z).1 hz with rfl | rfl | rfl <;>
      simp [Complex.add_re,Complex.sub_re,Complex.mul_re] <;> linarith only [hr,hd]

/-- Affine vector field of the full second-moment equations; c is the bath energy per sector. -/
def drift (w d c : ℝ) (G : ℝ≥0) (K U S : ℝ) : ℝ × ℝ × ℝ :=
  (-(Real.exp w)^2*S/2+d*(c-K),
    (Real.exp w)^2*S/2+(G:ℝ)*K+d*(c-U),4*K-4*U-d*S)

/-- The left eigenvector expressed as a scalar observable on the three moments. -/
def reading (w r K U S : ℝ) : ℝ :=
  (1+r^2/(2*(Real.exp w)^2))*K+U-r*S/4

/-- Damping and forcing close on a single exact observable. -/
theorem rate_projection (w d c : ℝ) (G : ℝ≥0) (K U S : ℝ) :
    let r := growth w G
    let v := drift w d c G K U S
    reading w r v.1 v.2.1 v.2.2 =
      (r-d)*reading w r K U S+d*c*(2+r^2/(2*(Real.exp w)^2)) := by
  intro r v
  have he : strength w r = G := strength_growth w G
  dsimp only [v,drift,reading]
  rw [← he]
  unfold strength
  field_simp [Real.exp_ne_zero]
  ring

/-- At the threshold positive noise and bath force strictly positive drift at every state. -/
theorem critical_drift (w g k : ℝ) (K U S : ℝ) :
    let G : ℝ≥0 := ⟨Real.exp g,(Real.exp_pos _).le⟩
    let r := growth w G
    let v := drift w r (Real.exp k) G K U S
    reading w r v.1 v.2.1 v.2.2 = r*Real.exp k*(2+r^2/(2*(Real.exp w)^2)) ∧
      0 < reading w r v.1 v.2.1 v.2.2 := by
  intro G r v
  have hr : 0 < r := by
    apply (strength_strictMono w).lt_iff_lt.mp
    rw [strength_growth]
    simpa [strength,G] using Real.exp_pos g
  have he := rate_projection w r (Real.exp k) G K U S
  change _ = (r-r)*_+_ at he
  rw [sub_self,zero_mul,zero_add] at he
  refine ⟨he,?_⟩
  rw [he]
  positivity

#print axioms growth_gap
#print axioms roots
#print axioms real_dispersion_sign
#print axioms spectral_stability
#print axioms rate_projection
#print axioms critical_drift
end GaloisForLFunctions.OscillatorHeating
