/-
# Fejér majorant for Bourgain's first-spacing count

A centered interval character integral gives a nonnegative Fejér kernel.
Jordan's inequality supplies an explicit lower bound on every near pair.
Tensorizing in four coordinates turns the sharp first-spacing count into a
positive finite Fejér energy, without assuming a spacing estimate.
-/
import GaloisForLFunctions.RHTower.BourgainA6Rescaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace RHTower

noncomputable section

def bourgainIntervalCharacterIntegral (X d : ℝ) : ℂ :=
  ∫ z in (-X / 2)..(X / 2), bourgainUnitCharacter (d * z)

theorem bourgainIntervalCharacterIntegral_eq
    (X d : ℝ) :
    bourgainIntervalCharacterIntegral X d =
      (X * Real.sinc (Real.pi * X * d) : ℝ) := by
  by_cases hd : d = 0
  · subst d
    simp [bourgainIntervalCharacterIntegral, bourgainUnitCharacter]
    ring
  by_cases hX : X = 0
  · subst X
    simp [bourgainIntervalCharacterIntegral]
  have hc :
      2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hd)
  unfold bourgainIntervalCharacterIntegral bourgainUnitCharacter
  have hfun :
      (fun z : ℝ =>
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((d * z : ℝ) : ℂ))) =
        fun z : ℝ =>
          Complex.exp
            ((2 * (Real.pi : ℂ) * Complex.I * (d : ℂ)) * (z : ℂ)) := by
    funext z
    congr 1
    push_cast
    ring
  rw [hfun]
  rw [integral_exp_mul_complex hc]
  rw [show
      (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ)) *
          ((X / 2 : ℝ) : ℂ) =
        Complex.I * ((Real.pi * X * d : ℝ) : ℂ) by
    push_cast
    ring]
  rw [show
      (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ)) *
          ((-X / 2 : ℝ) : ℂ) =
        Complex.I * ((-(Real.pi * X * d) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [mul_comm Complex.I ((Real.pi * X * d : ℝ) : ℂ),
    mul_comm Complex.I ((-(Real.pi * X * d) : ℝ) : ℂ),
    Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  rw [Real.sinc_of_ne_zero]
  · push_cast
    field_simp [Real.pi_ne_zero, hX, hd]
    ring
  · exact mul_ne_zero (mul_ne_zero Real.pi_ne_zero hX) hd

/-- Nonnegative one-dimensional Fejér kernel associated with a centered
interval of length `X`. -/
def bourgainFejerKernel (X d : ℝ) : ℝ :=
  ‖bourgainIntervalCharacterIntegral X d‖ ^ (2 : ℕ)

theorem bourgainFejerKernel_nonneg
    (X d : ℝ) :
    0 ≤ bourgainFejerKernel X d := by
  unfold bourgainFejerKernel
  positivity

theorem bourgainFejerKernel_near_lower
    {X d : ℝ} (hX : 0 < X)
    (hd : |d| < 1 / (2 * X)) :
    (2 * X / Real.pi) ^ (2 : ℕ) ≤
      bourgainFejerKernel X d := by
  have hu :
      |Real.pi * X * d| ≤ Real.pi / 2 := by
    have hscaled : X * |d| < 1 / 2 := by
      calc
        X * |d| < X * (1 / (2 * X)) :=
          mul_lt_mul_of_pos_left hd hX
        _ = 1 / 2 := by field_simp [hX.ne']
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hX]
    nlinarith [Real.pi_pos]
  have hsinc :
      2 / Real.pi ≤ |Real.sinc (Real.pi * X * d)| := by
    by_cases hud : Real.pi * X * d = 0
    · rw [hud, Real.sinc_zero, abs_one]
      exact (div_le_one Real.pi_pos).2 Real.two_le_pi
    · rw [Real.sinc_of_ne_zero hud, abs_div]
      have hu0 : 0 < |Real.pi * X * d| := abs_pos.mpr hud
      have hjordan :=
        Real.mul_abs_le_abs_sin hu
      exact (le_div_iff₀ hu0).2 (by
        simpa [mul_assoc] using hjordan)
  rw [bourgainFejerKernel, bourgainIntervalCharacterIntegral_eq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hX]
  exact pow_le_pow_left₀ (by positivity)
    (by
      calc
        2 * X / Real.pi = X * (2 / Real.pi) := by ring
        _ ≤ X * |Real.sinc (Real.pi * X * d)| :=
          mul_le_mul_of_nonneg_left hsinc hX.le)
    2

/-- Tensor product of the four one-dimensional Fejér kernels. -/
def bourgainProductFejerKernel
    (X u v : BourgainPhaseSpace) : ℝ :=
  ∏ j : Fin 4, bourgainFejerKernel (X j) (u j - v j)

def bourgainFejerNearConstant
    (X : BourgainPhaseSpace) : ℝ :=
  ∏ j : Fin 4, (2 * X j / Real.pi) ^ (2 : ℕ)

def bourgainFejerSpacingEnergy
    (H : ℕ) (X : BourgainPhaseSpace) : ℝ :=
  ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
    bourgainProductFejerKernel X
      (bourgainSixfoldMoment h) (bourgainSixfoldMoment h')

theorem bourgainProductFejerKernel_nonneg
    (X u v : BourgainPhaseSpace) :
    0 ≤ bourgainProductFejerKernel X u v := by
  exact Finset.prod_nonneg fun j hj =>
    bourgainFejerKernel_nonneg (X j) (u j - v j)

theorem bourgainFejerNearConstant_nonneg
    (X : BourgainPhaseSpace) :
    0 ≤ bourgainFejerNearConstant X := by
  exact Finset.prod_nonneg fun j hj => sq_nonneg _

theorem bourgainFejerNearConstant_le_kernel_of_nearPair
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) {h h' : Fin 6 → Fin H}
    (hnear : BourgainNearPair X h h') :
    bourgainFejerNearConstant X ≤
      bourgainProductFejerKernel X
        (bourgainSixfoldMoment h) (bourgainSixfoldMoment h') := by
  apply Finset.prod_le_prod
  · intro j hj
    positivity
  · intro j hj
    exact bourgainFejerKernel_near_lower (hX j) (hnear j)

/-- Fejér-kernel majorant for Bourgain's sharp first-spacing count. -/
theorem bourgainFejerNearConstant_mul_firstSpacingCount_le
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) :
    bourgainFejerNearConstant X *
        (bourgainFirstSpacingCount H X : ℝ) ≤
      bourgainFejerSpacingEnergy H X := by
  classical
  let U : Finset (Fin 6 → Fin H) := Finset.univ
  let P : Finset ((Fin 6 → Fin H) × (Fin 6 → Fin H)) := U.product U
  have hcount :
      (bourgainFirstSpacingCount H X : ℝ) =
        ∑ p ∈ P,
          if BourgainNearPair X p.1 p.2 then (1 : ℝ) else 0 := by
    simp [bourgainFirstSpacingCount, P, U, Finset.sum_boole]
  have hterm
      (p : (Fin 6 → Fin H) × (Fin 6 → Fin H)) (hp : p ∈ P) :
      (if BourgainNearPair X p.1 p.2
        then bourgainFejerNearConstant X else 0) ≤
        bourgainProductFejerKernel X
          (bourgainSixfoldMoment p.1)
          (bourgainSixfoldMoment p.2) := by
    split_ifs with hnear
    · exact
        bourgainFejerNearConstant_le_kernel_of_nearPair hX hnear
    · exact
        bourgainProductFejerKernel_nonneg X
          (bourgainSixfoldMoment p.1)
          (bourgainSixfoldMoment p.2)
  calc
    bourgainFejerNearConstant X *
        (bourgainFirstSpacingCount H X : ℝ) =
        ∑ p ∈ P,
          if BourgainNearPair X p.1 p.2
          then bourgainFejerNearConstant X else 0 := by
      rw [hcount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    _ ≤ ∑ p ∈ P,
        bourgainProductFejerKernel X
          (bourgainSixfoldMoment p.1)
          (bourgainSixfoldMoment p.2) :=
      Finset.sum_le_sum hterm
    _ = bourgainFejerSpacingEnergy H X := by
      change
        (∑ p ∈ U ×ˢ U,
          bourgainProductFejerKernel X
            (bourgainSixfoldMoment p.1)
            (bourgainSixfoldMoment p.2)) =
          ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
            bourgainProductFejerKernel X
              (bourgainSixfoldMoment h)
              (bourgainSixfoldMoment h')
      rw [Finset.sum_product]

end

end RHTower
