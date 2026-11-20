import GaloisForLFunctions.goldbach.GammaFactorBoundary
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Factorization of the three signed Beta integrals

Reflection gives a common triple Gamma product. The sum of its three
sines factors, and duplication converts the two remaining one-variable
terms to the Gamma quotients occurring in the continued model.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex
noncomputable section

/-- The two difference families contribute positively and the sum family negatively. -/
def signedBeta (s z : ℂ) : ℂ :=
  betaIntegral (1/2-s) (s+z) + betaIntegral (1/2-z) (s+z) - betaIntegral (1/2-s) (1/2-z)

private theorem inverse_reflected_gamma {u : ℂ} (hu : 0 < u.re) (hu' : u.re < 1) :
    (Gamma (1-u))⁻¹ = Gamma u * sin (Real.pi*u) / Real.pi := by
  have h1 : Gamma (1-u) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hu')
  have hG := Gamma_mul_Gamma_one_sub u
  have hs : sin (Real.pi * u) ≠ 0 := by
    intro he
    rw [he, div_zero] at hG
    exact mul_ne_zero (Gamma_ne_zero_of_re_pos hu) h1 hG
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (eq_div_iff hs).mp hG
  field_simp [h1,hp]
  linear_combination -h

private theorem beta_reflection {u v t : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    (ht : 0 < t.re) (he : u+v+t=1) :
    betaIntegral u v = Gamma u * Gamma v * Gamma t * sin (Real.pi*t) / Real.pi := by
  have hvu : u+v = 1-t := by linear_combination he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re] at hr
  rw [betaIntegral_eq_Gamma_mul_div _ _ hu hv, hvu, div_eq_mul_inv,
    inverse_reflected_gamma ht (by linarith only [hr,hu,hv])]
  ring

private theorem sine_factor (a b : ℂ) :
    sin (2*a) + sin (2*b) - sin (2*(a+b)) = 4 * sin a * sin b * sin (a+b) := by
  simp only [sin_two_mul, sin_add, cos_add]
  linear_combination -2*sin a*cos a*(sin_sq_add_cos_sq b) - 2*sin b*cos b*(sin_sq_add_cos_sq a)

private theorem gamma_half_factor (r : ℂ) (hr : 0 < r.re) (hr' : r.re < 1) :
    signedBetaGammaFactor (1/2-r) =
      Gamma r * (2:ℂ) ^ (1-r) * sin (Real.pi*r/2) / (Real.sqrt Real.pi : ℂ) := by
  have hh : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hq : (Real.sqrt Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hu : 0 < (r/2).re := by simpa using half_pos hr
  have hu' : (r/2).re < 1 := by norm_num; linarith only [hr']
  have hd := Gamma_mul_Gamma_add_half (r/2)
  rw [show 2*(r/2) = r by ring] at hd
  rw [signedBetaGammaFactor, show (3/2-(1/2-r))/2 = r/2+1/2 by ring,
    show (3/2+(1/2-r))/2 = 1-r/2 by ring, div_eq_mul_inv,
    inverse_reflected_gamma hu hu', show (Real.pi : ℂ)*(r/2) = Real.pi*r/2 by ring]
  calc
    _ = (Gamma (r/2) * Gamma (r/2+1/2)) * sin (Real.pi*r/2) / Real.pi := by ring
    _ = _ := by rw [hd]; field_simp [hp,hq]; linear_combination (Gamma r * (2:ℂ)^(1-r) * sin (Real.pi*r/2))*hh

/-- Equation (4.4) on the common domain of the three Euler integrals. -/
theorem signedBeta_factorization {s z : ℂ} (hs : 0 < s.re) (hs' : s.re < 1/2)
    (hz : 0 < z.re) (hz' : z.re < 1/2) :
    signedBeta s z = (2:ℂ)^(1-(s+z)) * Gamma (s+z) * cos (Real.pi*(s+z)/2) *
      signedBetaGammaFactor s * signedBetaGammaFactor z := by
  let r := 1/2-s
  let t := 1/2-z
  let w := s+z
  have hr : 0 < r.re := by simpa [r] using sub_pos.mpr hs'
  have ht : 0 < t.re := by simpa [t] using sub_pos.mpr hz'
  have hr1 : r.re < 1 := by dsimp [r]; norm_num; linarith only [hs]
  have ht1 : t.re < 1 := by dsimp [t]; norm_num; linarith only [hz]
  have hw : 0 < w.re := by simpa [w] using add_pos hs hz
  have hsum : r+t+w=1 := by dsimp [r,t,w]; ring
  have hrw : r+w+t=1 := by linear_combination hsum
  have htw : t+w+r=1 := by linear_combination hsum
  have hg (u : ℂ) (hu : 0 < u.re) (hu' : u.re < 1) := gamma_half_factor u hu hu'
  have hgs := hg r hr hr1
  have hgz := hg t ht ht1
  rw [show 1/2-r=s by dsimp [r]; ring] at hgs
  rw [show 1/2-t=z by dsimp [t]; ring] at hgz
  change betaIntegral r w + betaIntegral t w - betaIntegral r t = (2:ℂ)^(1-w) * Gamma w *
    cos (Real.pi*w/2) * signedBetaGammaFactor s * signedBetaGammaFactor z
  rw [beta_reflection hr hw ht hrw, beta_reflection ht hw hr htw, beta_reflection hr ht hw hsum,
    hgs, hgz]
  let a := (Real.pi : ℂ)*r/2
  let b := (Real.pi : ℂ)*t/2
  have htr : sin (Real.pi*t) + sin (Real.pi*r) - sin (Real.pi*w) =
      4*sin a*sin b*cos (Real.pi*w/2) := by
    rw [show (Real.pi : ℂ)*t=2*b by dsimp [b]; ring, show (Real.pi : ℂ)*r=2*a by dsimp [a]; ring,
      show (Real.pi : ℂ)*w = Real.pi-2*(a+b) by dsimp [a,b]; linear_combination (Real.pi : ℂ)*hsum,
      sin_pi_sub, show (Real.pi : ℂ)*w/2 = Real.pi/2-(a+b) by dsimp [a,b]; linear_combination ((Real.pi : ℂ)/2)*hsum,
      cos_pi_div_two_sub, add_comm (sin (2*b)), sine_factor]
  have htwo : (2:ℂ)^(1-w) * (2:ℂ)^(1-r) * (2:ℂ)^(1-t) = 4 := by
    rw [← cpow_add _ _ (by norm_num), ← cpow_add _ _ (by norm_num),
      show (1-w)+(1-r)+(1-t) = (2:ℕ) by push_cast; linear_combination -hsum, cpow_natCast]
    norm_num
  have hpi : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hq : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = Gamma r * Gamma t * Gamma w * (sin (Real.pi*t) + sin (Real.pi*r) - sin (Real.pi*w)) / Real.pi := by ring
    _ = _ := by
      rw [htr, ← htwo, ← hpi]
      dsimp [a,b]
      ring

#print axioms signedBeta_factorization
end
end GaloisForLFunctions.Goldbach.LiLiu
