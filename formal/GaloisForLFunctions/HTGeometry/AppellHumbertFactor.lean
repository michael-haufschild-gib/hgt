import GaloisForLFunctions.HTGeometry.GaussianDecayVanishing

/-!
# The Appell--Humbert factor and its normalised modulus

For a Hermitian form `H` and a semicharacter `chi` the canonical factor of automorphy is

`e (gamma, z) = chi gamma * exp (pi H (z, gamma) + (pi/2) H (gamma, gamma))`.

Two facts are proved here.

* `appellHumbertFactor_isMulTwoCocycle` -- it is a factor of automorphy.  The exponents differ by
  `(pi/2) (H (g, g') - H (g', g)) = pi i Im H (g, g')`, which is exactly what the semicharacter law
  cancels.
* `norm_thetaNorm_add` -- for a function transforming by that factor, the **normalised modulus**
  `|theta z| exp (-(pi/2) Re H (z,z))` is invariant under the period group.  Every term involving
  the base point cancels; only `Re H (z, gamma)` appears, twice with opposite signs.

The second is the source of the Gaussian factor: along a direction where `H` is negative the
normalised modulus is unchanged while `exp ((pi/2) Re H (z,z))` decays like a Gaussian, so a bounded
normalised modulus forces the function to vanish on that line.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A Hermitian form: additive and complex-homogeneous in the first argument, conjugate symmetric. -/
structure IsHermitianForm (H : V → V → ℂ) : Prop where
  add_left : ∀ x y z : V, H (x + y) z = H x z + H y z
  smul_left : ∀ (a : ℂ) (x y : V), H (a • x) y = a * H x y
  symm : ∀ x y : V, H y x = star (H x y)

namespace IsHermitianForm

variable {H : V → V → ℂ} (hH : IsHermitianForm H)

include hH

theorem add_right (x y z : V) : H x (y + z) = H x y + H x z := by
  rw [hH.symm (y + z) x, hH.add_left, star_add, hH.symm x y, hH.symm x z, star_star, star_star]

theorem self_im (x : V) : (H x x).im = 0 := by
  have h := hH.symm x x
  rw [Complex.star_def, Complex.ext_iff] at h
  have := h.2
  simp only [Complex.conj_im] at this
  linarith

theorem re_symm (x y : V) : (H y x).re = (H x y).re := by
  rw [hH.symm, Complex.star_def, Complex.conj_re]

theorem sub_symm (x y : V) : H x y - H y x = ((2 * (H x y).im : ℝ) : ℂ) * Complex.I := by
  rw [hH.symm x y, Complex.star_def]
  exact Complex.sub_conj _

end IsHermitianForm

/-- The Appell--Humbert factor of a Hermitian form and a semicharacter. -/
noncomputable def appellHumbertFactor (H : V → V → ℂ) (χ : V → ℂ) (γ z : V) : ℂ :=
  χ γ * Complex.exp ((Real.pi : ℂ) * H z γ + ((Real.pi : ℂ) / 2) * H γ γ)

/-- **The Appell--Humbert factor is a factor of automorphy.** -/
theorem appellHumbertFactor_isMulTwoCocycle {H : V → V → ℂ} (hH : IsHermitianForm H) {χ : V → ℂ}
    (hχ : ∀ γ γ' : V, χ (γ + γ')
      = χ γ * χ γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H γ γ').im : ℝ))) ) :
    IsMulTwoCocycle (appellHumbertFactor H χ) := by
  intro γ γ' z
  have e1 : H z (γ + γ') = H z γ + H z γ' := hH.add_right z γ γ'
  have e2 : H (γ + γ') (γ + γ') = H γ γ + H γ γ' + (H γ' γ + H γ' γ') := by
    rw [hH.add_left, hH.add_right, hH.add_right]
  have e3 : H (z + γ') γ = H z γ + H γ' γ := hH.add_left z γ' γ
  have hsub : H γ γ' - H γ' γ = ((2 * (H γ γ').im : ℝ) : ℂ) * Complex.I := hH.sub_symm γ γ'
  have hexp : (Real.pi : ℂ) * H z (γ + γ') + ((Real.pi : ℂ) / 2) * H (γ + γ') (γ + γ')
      = ((Real.pi : ℂ) * H (z + γ') γ + ((Real.pi : ℂ) / 2) * H γ γ)
        + ((Real.pi : ℂ) * H z γ' + ((Real.pi : ℂ) / 2) * H γ' γ')
        + ((Real.pi : ℂ) * Complex.I * ((H γ γ').im : ℝ)) := by
    rw [e1, e2, e3]
    push_cast at hsub ⊢
    linear_combination ((Real.pi : ℂ) / 2) * hsub
  have hne : Complex.exp ((Real.pi : ℂ) * Complex.I * ((H γ γ').im : ℝ)) ≠ 0 :=
    Complex.exp_ne_zero _
  simp only [appellHumbertFactor, hχ γ γ', hexp, Complex.exp_add, Complex.exp_neg]
  field_simp

/-- The modulus of the Appell--Humbert factor, for a unitary semicharacter. -/
theorem norm_appellHumbertFactor {H : V → V → ℂ} (hH : IsHermitianForm H) {χ : V → ℂ}
    (hχ : ∀ γ, ‖χ γ‖ = 1) (γ z : V) :
    ‖appellHumbertFactor H χ γ z‖
      = Real.exp (Real.pi * (H z γ).re + (Real.pi / 2) * (H γ γ).re) := by
  rw [appellHumbertFactor, norm_mul, hχ, one_mul, Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re, hH.self_im]

/-- The normalised modulus of a function. -/
noncomputable def thetaNorm (H : V → V → ℂ) (θ : V → ℂ) (z : V) : ℝ :=
  ‖θ z‖ * Real.exp (-(Real.pi / 2) * (H z z).re)

/-- **The normalised modulus is invariant under the period group.** -/
theorem thetaNorm_add {H : V → V → ℂ} (hH : IsHermitianForm H) {χ : V → ℂ}
    (hχ : ∀ γ, ‖χ γ‖ = 1) {θ : V → ℂ}
    (hθ : ∀ γ z : V, θ (z + γ) = appellHumbertFactor H χ γ z * θ z) (γ z : V) :
    thetaNorm H θ (z + γ) = thetaNorm H θ z := by
  have hre : (H (z + γ) (z + γ)).re
      = (H z z).re + 2 * (H z γ).re + (H γ γ).re := by
    rw [hH.add_left, hH.add_right, hH.add_right]
    simp only [Complex.add_re]
    have := hH.re_symm z γ
    linarith
  have hexpid : Real.exp (Real.pi * (H z γ).re + Real.pi / 2 * (H γ γ).re)
      * Real.exp (-(Real.pi / 2) * ((H z z).re + 2 * (H z γ).re + (H γ γ).re))
      = Real.exp (-(Real.pi / 2) * (H z z).re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaNorm, thetaNorm, hθ, norm_mul, norm_appellHumbertFactor hH hχ, hre]
  linear_combination ‖θ z‖ * hexpid

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Along a complex line the Hermitian form is the squared modulus times its value. -/
theorem hermitianForm_smul_self {H : W → W → ℂ} (hH : IsHermitianForm H) (s : ℂ) (v : W) :
    (H (s • v) (s • v)).re = ‖s‖ ^ (2 : ℕ) * (H v v).re := by
  have hreal : star (H v v) = H v v := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]
    exact hH.self_im v
  have h1 : H (s • v) (s • v) = s * H v (s • v) := hH.smul_left s v (s • v)
  have h2 : H v (s • v) = star (H (s • v) v) := hH.symm _ _
  have h3 : H (s • v) v = s * H v v := hH.smul_left s v v
  have h4 : H (s • v) (s • v) = ((Complex.normSq s : ℝ) : ℂ) * H v v := by
    rw [h1, h2, h3, star_mul, hreal, Complex.star_def,
      show s * (H v v * (starRingEnd ℂ) s) = (s * (starRingEnd ℂ) s) * H v v by ring,
      Complex.mul_conj]
  rw [h4, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

/-- **A negative direction of the Hermitian form kills a bounded theta function on that line.**
Along a direction where `H` is negative the normalised modulus is unchanged while the exponential
factor decays like a Gaussian, so the function must vanish on the whole complex line. -/
theorem eq_zero_along_line_of_neg_of_thetaNorm_bounded {H : W → W → ℂ} (hH : IsHermitianForm H)
    {θ : W → ℂ} (hdiff : Differentiable ℂ θ) {M : ℝ} (hbdd : ∀ z, thetaNorm H θ z ≤ M)
    {v : W} (hv : (H v v).re < 0) (t : ℂ) :
    θ (t • v) = 0 := by
  have ha : 0 < -(Real.pi / 2) * (H v v).re := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  refine eq_zero_of_gaussian_decay_along_line (C := M) hdiff v ha (fun s => ?_) t
  have hb := hbdd (s • v)
  rw [thetaNorm, hermitianForm_smul_self hH] at hb
  have hexp : (0 : ℝ) < Real.exp (-(Real.pi / 2) * (‖s‖ ^ (2 : ℕ) * (H v v).re)) := Real.exp_pos _
  rw [← le_div_iff₀ hexp] at hb
  refine hb.trans_eq ?_
  rw [div_eq_mul_inv, ← Real.exp_neg,
    show -(-(Real.pi / 2) * (‖s‖ ^ (2 : ℕ) * (H v v).re))
      = -(-(Real.pi / 2) * (H v v).re) * ‖s‖ ^ (2 : ℕ) from by ring]

end Normed

end GaloisForLFunctions.HTGeometry
