import GaloisForLFunctions.HTGeometry.AppellHumbertFactor

/-!
# The Gaussian bound on the inverse Appell--Humbert factor

The damping estimate of the quasi-abelian jet-ampleness induction needs the inverse automorphy
factor to decay like a Gaussian in the lattice point, uniformly for the base point in a fixed
bounded set.  For the Appell--Humbert factor of a positive semidefinite Hermitian form that follows
from the Cauchy--Schwarz inequality for the form: the cross term `π·Re H(z, γ)` is at most
`π·C·√(H(γ,γ))`, and `π C u − (π/2) u² ≤ π C² − (π/4) u²` because the difference is `π (C − u/2)²`.

Half of the quadratic exponent is spent absorbing the cross term; the other half is the Gaussian.

* `IsHermitianForm.smul_right`, `IsHermitianForm.re_smul_add`;
* `IsHermitianForm.norm_sq_le` — **Cauchy--Schwarz for a positive semidefinite Hermitian form**;
* `IsHermitianForm.norm_le_sqrt` — its square-root form;
* `norm_inv_appellHumbertFactor_le` — **the Gaussian bound**.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

namespace IsHermitianForm

variable {H : V → V → ℂ} (hH : IsHermitianForm H)

include hH

theorem self_eq_re (x : V) : H x x = ((H x x).re : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simp [hH.self_im x]

theorem star_self (x : V) : star (H x x) = H x x := by
  rw [hH.self_eq_re x, Complex.star_def, Complex.conj_ofReal]

theorem smul_right (l : ℂ) (x y : V) : H x (l • y) = star l * H x y := by
  have h1 : H (l • y) x = l * H y x := hH.smul_left l y x
  have h2 : H (l • y) x = star (H x (l • y)) := hH.symm x (l • y)
  have h3 : star (H x (l • y)) = l * H y x := by rw [← h2, h1]
  have h4 : H x (l • y) = star (l * H y x) := by
    rw [← h3, star_star]
  rw [h4, star_mul', hH.symm x y, star_star]

theorem re_smul_add (l : ℂ) (x y : V) :
    (H (x + l • y) (x + l • y)).re
      = (H x x).re + 2 * (star l * H x y).re + ‖l‖ ^ (2 : ℕ) * (H y y).re := by
  have hsq : H (l • y) (l • y) = ((‖l‖ ^ (2 : ℕ) : ℝ) : ℂ) * H y y := by
    rw [hH.smul_left l y (l • y), hH.smul_right l y y, ← mul_assoc, Complex.star_def,
      Complex.mul_conj']
    push_cast
    ring
  have hA : H (x + l • y) (x + l • y)
      = H x x + star l * H x y + (l * H y x + ((‖l‖ ^ (2 : ℕ) : ℝ) : ℂ) * H y y) := by
    rw [hH.add_left x (l • y) (x + l • y), hH.add_right x x (l • y),
      hH.add_right (l • y) x (l • y), hsq, hH.smul_right l x y, hH.smul_left l y x]
  rw [hA]
  simp only [Complex.add_re]
  have hlr : (l * H y x).re = (star l * H x y).re := by
    have hstar : l * H y x = star (star l * H x y) := by
      rw [star_mul', star_star, hH.symm x y]
    rw [hstar, Complex.star_def, Complex.conj_re]
  have hsq' : (((‖l‖ ^ (2 : ℕ) : ℝ) : ℂ) * H y y).re = ‖l‖ ^ (2 : ℕ) * (H y y).re :=
    Complex.re_ofReal_mul _ _
  rw [hlr, hsq']
  ring

/-- **Cauchy--Schwarz for a positive semidefinite Hermitian form.** -/
theorem norm_sq_le (hpos : ∀ v : V, 0 ≤ (H v v).re) (x y : V) :
    ‖H x y‖ ^ (2 : ℕ) ≤ (H x x).re * (H y y).re := by
  set a : ℝ := (H x x).re with ha
  set b : ℝ := (H y y).re with hb
  set w : ℂ := H x y with hw
  have key : ∀ s : ℝ, 0 ≤ a - 2 * s * ‖w‖ ^ (2 : ℕ) + s ^ (2 : ℕ) * ‖w‖ ^ (2 : ℕ) * b := by
    intro s
    have h := hpos (x + (-(s : ℂ) * w) • y)
    rw [hH.re_smul_add] at h
    have h1 : (star (-(s : ℂ) * w) * w).re = -s * ‖w‖ ^ (2 : ℕ) := by
      have hs : star (-(s : ℂ) * w) * w = -(s : ℂ) * ((‖w‖ : ℂ) ^ (2 : ℕ)) := by
        rw [star_mul', ← Complex.mul_conj']
        simp
        ring
      rw [hs]
      rw [show (-(s : ℂ) * ((‖w‖ : ℂ) ^ (2 : ℕ))) = ((-s * ‖w‖ ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    have h2 : ‖(-(s : ℂ) * w)‖ ^ (2 : ℕ) = s ^ (2 : ℕ) * ‖w‖ ^ (2 : ℕ) := by
      rw [norm_mul, norm_neg, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, h2] at h
    linarith
  rcases eq_or_ne ‖w‖ 0 with hw0 | hw0
  · rw [hw0]
    simpa using mul_nonneg (hpos x) (hpos y)
  · have hw2 : 0 < ‖w‖ ^ (2 : ℕ) := by positivity
    rcases eq_or_lt_of_le (hpos y) with hb0 | hbpos
    · exfalso
      have hbz : b = 0 := hb.trans hb0.symm
      have h := key ((a + 1) / (2 * ‖w‖ ^ (2 : ℕ)))
      rw [hbz] at h
      have hrw2 : 2 * ((a + 1) / (2 * ‖w‖ ^ (2 : ℕ))) * ‖w‖ ^ (2 : ℕ) = a + 1 := by
        field_simp
      rw [hrw2] at h
      simp only [mul_zero, add_zero] at h
      linarith
    · have hbne : b ≠ 0 := ne_of_gt hbpos
      have h := key (1 / b)
      have e1 : 2 * (1 / b) * ‖w‖ ^ (2 : ℕ) = 2 * (‖w‖ ^ (2 : ℕ) / b) := by field_simp
      have e2 : (1 / b) ^ (2 : ℕ) * ‖w‖ ^ (2 : ℕ) * b = ‖w‖ ^ (2 : ℕ) / b := by
        field_simp
      rw [e1, e2] at h
      have hle : ‖w‖ ^ (2 : ℕ) / b ≤ a := by linarith
      rwa [div_le_iff₀ hbpos] at hle

/-- The square-root form of Cauchy--Schwarz. -/
theorem norm_le_sqrt (hpos : ∀ v : V, 0 ≤ (H v v).re) (x y : V) :
    ‖H x y‖ ≤ Real.sqrt ((H x x).re * (H y y).re) := by
  have h := hH.norm_sq_le hpos x y
  have hsq : Real.sqrt (‖H x y‖ ^ (2 : ℕ)) ≤ Real.sqrt ((H x x).re * (H y y).re) :=
    Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _)] at hsq

end IsHermitianForm

/-- **The Gaussian bound on the inverse Appell--Humbert factor.**  For a base point of bounded
form-size the inverse factor decays like `exp(−(π/4)·H(γ,γ))`, with a constant depending only on
the bound. -/
theorem norm_inv_appellHumbertFactor_le {H : V → V → ℂ} (hH : IsHermitianForm H)
    (hpos : ∀ v : V, 0 ≤ (H v v).re) {χ : V → ℂ} (hχ : ∀ γ, ‖χ γ‖ = 1)
    {C : ℝ} (hC : 0 ≤ C) {z : V} (hz : (H z z).re ≤ C ^ (2 : ℕ)) (γ : V) :
    ‖(appellHumbertFactor H χ γ z)⁻¹‖
      ≤ Real.exp (Real.pi * C ^ (2 : ℕ)) * Real.exp (-(Real.pi / 4) * (H γ γ).re) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set t : ℝ := (H γ γ).re with ht
  have ht0 : 0 ≤ t := hpos γ
  have hcs : ‖H z γ‖ ≤ Real.sqrt ((H z z).re * t) := hH.norm_le_sqrt hpos z γ
  have hbound : ‖H z γ‖ ≤ C * Real.sqrt t := by
    refine le_trans hcs ?_
    have h1 : (H z z).re * t ≤ C ^ (2 : ℕ) * t := mul_le_mul_of_nonneg_right hz ht0
    refine le_trans (Real.sqrt_le_sqrt h1) (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC]
  have hre : -(H z γ).re ≤ C * Real.sqrt t := by
    refine le_trans ?_ hbound
    refine le_trans (neg_le_abs _) ?_
    exact Complex.abs_re_le_norm _
  have hsqrt : Real.sqrt t ^ (2 : ℕ) = t := Real.sq_sqrt ht0
  have hkey : C * Real.sqrt t ≤ C ^ (2 : ℕ) + t / 4 := by
    nlinarith [sq_nonneg (C - Real.sqrt t / 2), Real.sqrt_nonneg t]
  have hexp : -(Real.pi * (H z γ).re + Real.pi / 2 * t)
      ≤ Real.pi * C ^ (2 : ℕ) + -(Real.pi / 4) * t := by
    have h1 : Real.pi * (-(H z γ).re) ≤ Real.pi * (C * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hre (le_of_lt hpi)
    have h2 : Real.pi * (C * Real.sqrt t) ≤ Real.pi * (C ^ (2 : ℕ) + t / 4) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt hpi)
    nlinarith
  rw [norm_inv, norm_appellHumbertFactor hH hχ, ← Real.exp_neg, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp

end GaloisForLFunctions.HTGeometry
