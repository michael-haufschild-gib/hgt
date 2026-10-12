import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv


/-!
# GHS and Lebowitz inequalities do not see Lee–Yang

Riemann's measure `Φ(u)du` satisfies two ferromagnetic inequalities unconditionally:
- GHS: the magnetization `(ξ'/ξ)(½ + w)` is concave on `[0, ∞)` (`concaveOn_xiRealLogDeriv`);
- Lebowitz: the fourth cumulant is negative.

The Lee–Yang property for `Φ` is RH. This module shows that the two inequalities together do not
imply the Lee–Yang property. They also do not imply the real-axis sign law `ZZ'' < 0` at critical
points.

**Countermodel** (`ferromagnetic_inequalities_leeYang_blind`). The even positive measure
`δ₀ + (3/8)(δ₁ + δ₋₁)` has characteristic function `Z(t) = 1 + (3/4)cos t` and field-axis partition
function `1 + (3/4)cosh y`. It satisfies the following.
* GHS (`concaveOn_ferroMag`): `m(y) = (3/4)sinh y/(1 + (3/4)cosh y)` is concave on `[0, ∞)`. Its
  derivative is `(3/4)(c + 3/4)/(1 + (3/4)c)²` with `c = cosh y`, which decreases in `c ≥ 1`.
* Lebowitz (`ferro_lebowitz`): `μ₂ = μ₄ = 3/7`, so `μ₄ − 3μ₂² = −6/49 < 0`.
* Not Lee–Yang (`exists_ferroZC_nonreal_zero`): `Z(π + iy) = 0` where `cosh y = 4/3`.
* Real-axis sign failure (`ferroZ_signFailure`): `Z'(π) = 0` and `Z(π)Z''(π) = 3/16 > 0`.

Gaussian smoothing (`ferro_gaussian_smoothing`) adds `εy` to the magnetization and keeps the zero
set, so the smooth Gaussian mixtures satisfy GHS and fail Lee–Yang as well.
-/

open Real Set

noncomputable section

namespace RHTower.FerroBlind

/-- The even probability-type measure `δ₀ + (3/8)(δ₁ + δ₋₁)` through its characteristic function
`Z(t) = 1 + (3/4) cos t`. -/
def ferroZ (t : ℝ) : ℝ := 1 + 3 / 4 * Real.cos t

/-- Its complex extension. -/
def ferroZC (z : ℂ) : ℂ := 1 + 3 / 4 * Complex.cos z

/-- The field-axis partition function `Z(iy) = 1 + (3/4) cosh y`. -/
def ferroPart (y : ℝ) : ℝ := 1 + 3 / 4 * Real.cosh y

/-- The magnetization `m(y) = (log Z(iy))'`. -/
def ferroMag (y : ℝ) : ℝ := 3 / 4 * Real.sinh y / ferroPart y

theorem ferroPart_pos (y : ℝ) : 0 < ferroPart y := by
  unfold ferroPart; nlinarith [Real.one_le_cosh y]

theorem ferroZC_ofReal (t : ℝ) : ferroZC t = ferroZ t := by
  simp [ferroZC, ferroZ]

theorem ferroZC_mul_I (y : ℝ) : ferroZC ((y : ℂ) * Complex.I) = ferroPart y := by
  simp [ferroZC, ferroPart, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- `m` is the logarithmic derivative of the field-axis partition function. -/
theorem hasDerivAt_log_ferroPart (y : ℝ) :
    HasDerivAt (fun y => Real.log (ferroPart y)) (ferroMag y) y := by
  have h : HasDerivAt ferroPart (3 / 4 * Real.sinh y) y := by
    have := ((Real.hasDerivAt_cosh y).const_mul (3 / 4 : ℝ)).const_add 1
    exact this
  have := h.log (ferroPart_pos y).ne'
  simpa [ferroMag] using this

theorem hasDerivAt_ferroMag (y : ℝ) :
    HasDerivAt ferroMag (3 / 4 * (Real.cosh y + 3 / 4) / ferroPart y ^ 2) y := by
  have h1 : HasDerivAt (fun y => 3 / 4 * Real.sinh y) (3 / 4 * Real.cosh y) y :=
    (Real.hasDerivAt_sinh y).const_mul _
  have h2 : HasDerivAt ferroPart (3 / 4 * Real.sinh y) y := by
    have := ((Real.hasDerivAt_cosh y).const_mul (3 / 4 : ℝ)).const_add 1
    exact this
  have h3 := h1.div h2 (ferroPart_pos y).ne'
  refine h3.congr_deriv ?_
  have hc := Real.cosh_sq y
  unfold ferroPart
  field_simp
  nlinarith [hc]

/-- **GHS.** The magnetization is concave on `[0, ∞)`. -/
theorem concaveOn_ferroMag : ConcaveOn ℝ (Ici 0) ferroMag := by
  have hd : ∀ y, deriv ferroMag y = 3 / 4 * (Real.cosh y + 3 / 4) / ferroPart y ^ 2 :=
    fun y => (hasDerivAt_ferroMag y).deriv
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    (fun y _ => (hasDerivAt_ferroMag y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_ferroMag y).differentiableAt.differentiableWithinAt) ?_
  intro a ha b hb hab
  rw [interior_Ici] at ha hb
  rw [hd, hd]
  have hca : Real.cosh a ≤ Real.cosh b := by
    rw [Real.cosh_le_cosh, abs_of_pos ha, abs_of_pos hb]; exact hab
  have h1a := Real.one_le_cosh a
  set c₁ := Real.cosh a
  set c₂ := Real.cosh b
  have hp1 : 0 < ferroPart a := ferroPart_pos a
  have hp2 : 0 < ferroPart b := ferroPart_pos b
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [ferroPart]
  change 3 / 4 * (c₂ + 3 / 4) * (1 + 3 / 4 * c₁) ^ 2 ≤ 3 / 4 * (c₁ + 3 / 4) * (1 + 3 / 4 * c₂) ^ 2
  have hP : (0 : ℝ) ≤ 36 * c₁ * c₂ + 27 * (c₁ + c₂) + 8 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hca) hP]

/-- **Lebowitz.** The normalized fourth cumulant `μ₄ − 3μ₂²` is negative: `μ₂ = μ₄ = 3/7`. -/
theorem ferro_lebowitz :
    let w : Fin 3 → ℝ := ![1, 3 / 8, 3 / 8]
    let u : Fin 3 → ℝ := ![0, 1, -1]
    let M : ℕ → ℝ := fun k => (∑ i, w i * u i ^ k) / ∑ i, w i
    M 4 - 3 * M 2 ^ 2 < 0 := by
  simp [Fin.sum_univ_three]
  norm_num

/-- The characteristic function of the measure: `Z(t) = Σ wᵢ cos(t uᵢ)`. -/
theorem ferroZ_eq_sum (t : ℝ) :
    ferroZ t = 1 * Real.cos (t * 0) + 3 / 8 * Real.cos (t * 1) + 3 / 8 * Real.cos (t * (-1)) := by
  simp [ferroZ, Real.cos_neg]; ring

/-- **Lee–Yang fails.** `Z` has a non-real zero, at `π + iy` with `cosh y = 4/3`. -/
theorem exists_ferroZC_nonreal_zero : ∃ z : ℂ, z.im ≠ 0 ∧ ferroZC z = 0 := by
  have hcont : ContinuousOn Real.cosh (Icc 0 2) := Real.continuous_cosh.continuousOn
  have h2 : (4 : ℝ) / 3 ≤ Real.cosh 2 := by
    rw [Real.cosh_eq]
    have := Real.add_one_le_exp 2
    have := Real.exp_pos (-2)
    linarith
  obtain ⟨y, hy, hcy⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hcont
    ⟨by rw [Real.cosh_zero]; norm_num, h2⟩
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [Real.cosh_zero] at hcy; norm_num at hcy
  refine ⟨(Real.pi : ℂ) + (y : ℂ) * Complex.I, by simpa using hy0, ?_⟩
  rw [ferroZC, Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi, ← Complex.ofReal_cosh, hcy]
  push_cast
  ring

/-- **The real-axis sign law fails.** `t = π` is a critical point of `Z` with `Z(π)Z''(π) > 0`:
a positive local minimum of `Z`. -/
theorem ferroZ_signFailure :
    deriv ferroZ Real.pi = 0 ∧ ferroZ Real.pi ≠ 0 ∧
      0 < ferroZ Real.pi * deriv (deriv ferroZ) Real.pi := by
  have hd : deriv ferroZ = fun t => -(3 / 4 * Real.sin t) := by
    funext t
    have := ((Real.hasDerivAt_cos t).const_mul (3 / 4 : ℝ)).const_add 1
    rw [show ferroZ = fun t => 1 + 3 / 4 * Real.cos t from rfl, this.deriv]; ring
  have hdd : deriv (deriv ferroZ) = fun t => -(3 / 4 * Real.cos t) := by
    rw [hd]; funext t
    have := ((Real.hasDerivAt_sin t).const_mul (3 / 4 : ℝ)).neg
    exact (this : HasDerivAt (fun t => -(3 / 4 * Real.sin t)) _ t).deriv
  refine ⟨by rw [hd]; simp, by simp [ferroZ]; norm_num, ?_⟩
  rw [hdd]; simp [ferroZ]; norm_num

/-- **Gaussian smoothing keeps everything.** For `ε ≥ 0`, multiplying `Z` by `e^{−εz²/2}` (adding an
independent centred Gaussian of variance `ε`) adds `εy` to the magnetization, so GHS persists, and
leaves the zero set unchanged, so the non-real zero persists. -/
theorem ferro_gaussian_smoothing {ε : ℝ} (hε : 0 ≤ ε) :
    ConcaveOn ℝ (Ici 0) (fun y => ferroMag y + ε * y) ∧
      ∃ z : ℂ, z.im ≠ 0 ∧ ferroZC z * Complex.exp (-(ε : ℂ) * z ^ 2 / 2) = 0 := by
  refine ⟨concaveOn_ferroMag.add ((concaveOn_id (convex_Ici (0 : ℝ))).smul hε), ?_⟩
  obtain ⟨z, hz, h0⟩ := exists_ferroZC_nonreal_zero
  exact ⟨z, hz, by rw [h0, zero_mul]⟩

/-- **GHS and Lebowitz do not give Lee–Yang or the real-axis sign law.** One explicit even positive
measure satisfies both inequalities, while its characteristic function has a non-real zero and a
positive local minimum. -/
theorem ferromagnetic_inequalities_leeYang_blind :
    ConcaveOn ℝ (Ici 0) ferroMag ∧
      (let w : Fin 3 → ℝ := ![1, 3 / 8, 3 / 8]
       let u : Fin 3 → ℝ := ![0, 1, -1]
       let M : ℕ → ℝ := fun k => (∑ i, w i * u i ^ k) / ∑ i, w i
       M 4 - 3 * M 2 ^ 2 < 0) ∧
      (∃ z : ℂ, z.im ≠ 0 ∧ ferroZC z = 0) ∧
      (deriv ferroZ Real.pi = 0 ∧ ferroZ Real.pi ≠ 0 ∧
        0 < ferroZ Real.pi * deriv (deriv ferroZ) Real.pi) :=
  ⟨concaveOn_ferroMag, ferro_lebowitz, exists_ferroZC_nonreal_zero, ferroZ_signFailure⟩

end RHTower.FerroBlind
