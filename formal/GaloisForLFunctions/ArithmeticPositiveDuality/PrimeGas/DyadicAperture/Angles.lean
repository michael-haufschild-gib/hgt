import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ObservationDepth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Unsigned principal angles for a sampled clock

The chord is strictly increasing in the unsigned angle. Squaring doubles
the angle up to π/2 and reflects it about π afterwards.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture

open SampledClocks

def angle (z : Circle) := Real.arccos (z:ℂ).re

theorem angle_mem (z : Circle) : angle z ∈ Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩

theorem angle_exp (a : ℝ) : angle (Circle.exp a) = Real.arccos (Real.cos a) := by
  change Real.arccos (Complex.exp ((a:ℂ)*Complex.I)).re = _
  rw [Complex.exp_ofReal_mul_I_re]

theorem exp_angle (a : ℝ) (ha : a ∈ Set.Icc 0 Real.pi) : angle (Circle.exp a) = a := by
  rw [angle_exp,Real.arccos_cos ha.1 ha.2]

private theorem principal (z : Circle) : angle z = |(z:ℂ).arg| := by
  have hc : Real.cos |(z:ℂ).arg| = (z:ℂ).re := by
    rw [Real.cos_abs,Complex.cos_arg (by intro h; have hu := Circle.norm_coe z; rw [h,norm_zero] at hu; exact zero_ne_one hu),Circle.norm_coe,div_one]
  change Real.arccos (z:ℂ).re = _
  rw [← hc,Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi _)]

theorem representatives (z : Circle) : z = Circle.exp (angle z) ∨ z = Circle.exp (-(angle z)) := by
  have h := Circle.exp_arg z
  rw [principal]
  rcases le_total 0 (z:ℂ).arg with hp | hn
  · exact Or.inl (by simpa only [abs_of_nonneg hp] using h.symm)
  · exact Or.inr (by simpa only [abs_of_nonpos hn,neg_neg] using h.symm)

private theorem square_formula (z : Circle) :
    angle (z^2) = Real.arccos (Real.cos (2*angle z)) := by
  rcases representatives z with h | h
  · calc
      _ = angle ((Circle.exp (angle z))^2) := congrArg (fun w : Circle => angle (w^2)) h
      _ = _ := by rw [← Circle.exp_natCast_mul,angle_exp]; norm_num
  · calc
      _ = angle ((Circle.exp (-angle z))^2) := congrArg (fun w : Circle => angle (w^2)) h
      _ = _ := by rw [← Circle.exp_natCast_mul,angle_exp]; norm_num [mul_neg]

theorem square_low (z : Circle) (h : angle z ≤ Real.pi/2) : angle (z^2) = 2*angle z := by
  rw [square_formula,Real.arccos_cos (by linarith only [(angle_mem z).1]) (by linarith only [h])]

theorem square_high (z : Circle) (h : Real.pi/2 ≤ angle z) : angle (z^2) = 2*Real.pi-2*angle z := by
  rw [square_formula,← Real.cos_two_pi_sub (2*angle z),
    Real.arccos_cos (by linarith only [(angle_mem z).2]) (by linarith only [h])]

private theorem chord_exp (a : ℝ) : chordSq (Circle.exp a) = aperture a := by
  change (dist (Complex.exp ((a:ℂ)*Complex.I)) (1:ℂ))^2 = _
  rw [dist_eq_norm]
  exact HTGeometry.normSq_exp_mul_I_sub_one a

theorem chord_angle (z : Circle) : chordSq z = aperture (angle z) := by
  rcases representatives z with h | h
  · exact (congrArg chordSq h).trans (chord_exp _)
  · exact (congrArg chordSq h).trans ((chord_exp _).trans (by simp [aperture]))

theorem chord_lt_iff (θ : Set.Icc 0 Real.pi) (z : Circle) :
    dist z 1 < Real.sqrt (aperture θ.val) ↔ angle z < θ.val := by
  have hp : 0 ≤ aperture θ.val := by unfold aperture; linarith only [Real.cos_le_one θ.val]
  rw [← sq_lt_sq₀ dist_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hp]
  change chordSq z < aperture θ.val ↔ _
  rw [chord_angle]
  unfold aperture
  constructor
  · intro h
    by_contra! hn
    linarith only [h,Real.cos_le_cos_of_nonneg_of_le_pi θ.property.1 (angle_mem z).2 hn]
  · intro h
    linarith only [Real.strictAntiOn_cos (angle_mem z) θ.property h]

def Survives (θ : ℝ) (z : Circle) := ∀ k : ℕ, angle (z^(2^k : ℕ)) < θ

theorem survives_square (θ : ℝ) (z : Circle) :
    Survives θ z ↔ angle z < θ ∧ Survives θ (z^2) := by
  have step (k : ℕ) : z^(2^(k+1) : ℕ) = (z^2)^(2^k : ℕ) := by rw [pow_succ',pow_mul]
  constructor
  · intro h
    exact ⟨by simpa only [pow_zero,pow_one] using h 0,fun k => step k ▸ h (k+1)⟩
  · rintro ⟨h,hs⟩ (_ | k)
    · simpa only [pow_zero,pow_one] using h
    · rw [step]; exact hs k

#print axioms representatives
#print axioms square_low
#print axioms square_high
#print axioms chord_lt_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture
