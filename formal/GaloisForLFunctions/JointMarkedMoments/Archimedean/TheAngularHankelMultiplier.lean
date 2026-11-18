import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The angular Hankel multiplier

For the complex constituent with inducing exponents `±1/6`, angular mode `m ∈ ℤ` and radial
parameter `τ ∈ ℝ`, the normalized multiplier is
`K_{m,τ}(t) = Γ(1/3 + |m|/2 + s)Γ(2/3 + |m|/2 + s) / (Γ(1/3 + |m|/2 − s)Γ(2/3 + |m|/2 − s))`,
`s = t + iτ` (eq. (58)).

* `tateFactor_mul`: with the complex Tate factor
  `G_m(s) = i^{|m|}(2π)^{1−2s}Γ(s + |m|/2)/Γ(1 − s + |m|/2)`,
  `G_m(1/2 + s − 1/6) G_m(1/2 + s + 1/6) = (−1)^{|m|} (2π)^{−4s} K_{m,τ}(t)`.
* `hankelMultiplier_mul_reflect`: `K_{m,τ}(t) K_{−m,−τ}(−t) = 1` off the poles.
* `differentiableOn_hankelMultiplier`: `K_{m,τ}` is holomorphic on `Re t > −1/3`; the numerator
  arguments have positive real part there and `1/Γ` is entire.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Complex

noncomputable section

/-- Half the angular mode, `|m|/2`. -/
def halfMode (m : ℤ) : ℂ := ((|m| : ℤ) : ℂ) / 2

/-- The Gamma ratio `Γ(1/3 + |m|/2 + s)Γ(2/3 + |m|/2 + s)/(Γ(1/3 + |m|/2 − s)Γ(2/3 + |m|/2 − s))`. -/
def hankelRatio (m : ℤ) (s : ℂ) : ℂ :=
  Gamma (1 / 3 + halfMode m + s) * Gamma (2 / 3 + halfMode m + s) /
    (Gamma (1 / 3 + halfMode m - s) * Gamma (2 / 3 + halfMode m - s))

/-- The angular Hankel multiplier `K_{m,τ}(t)` of (58). -/
def hankelMultiplier (m : ℤ) (τ : ℝ) (t : ℂ) : ℂ := hankelRatio m (t + τ * I)

/-- The complex Tate factor `G_m(s) = i^{|m|}(2π)^{1−2s}Γ(s + |m|/2)/Γ(1 − s + |m|/2)`. -/
def tateFactor (m : ℤ) (s : ℂ) : ℂ :=
  I ^ m.natAbs * (2 * (Real.pi : ℂ)) ^ (1 - 2 * s) * Gamma (s + halfMode m) / Gamma (1 - s + halfMode m)

theorem halfMode_neg (m : ℤ) : halfMode (-m) = halfMode m := by
  unfold halfMode; rw [abs_neg]

/-- The two inducing characters multiply to the multiplier:
`G_m(1/2 + s − 1/6) G_m(1/2 + s + 1/6) = (−1)^{|m|}(2π)^{−4s} K`, `s = t + iτ`. -/
theorem tateFactor_mul (m : ℤ) (τ : ℝ) (t : ℂ) :
    tateFactor m (1 / 2 + (t + τ * I) - 1 / 6) * tateFactor m (1 / 2 + (t + τ * I) + 1 / 6) =
      (-1) ^ m.natAbs * (2 * (Real.pi : ℂ)) ^ (-4 * (t + τ * I)) * hankelMultiplier m τ t := by
  unfold tateFactor hankelMultiplier hankelRatio
  generalize t + (τ : ℂ) * I = s
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have hcpow : (2 * (Real.pi : ℂ)) ^ (1 - 2 * (1 / 2 + s - 1 / 6)) * (2 * (Real.pi : ℂ)) ^ (1 - 2 * (1 / 2 + s + 1 / 6)) =
      (2 * (Real.pi : ℂ)) ^ (-4 * s) := by
    rw [← cpow_add _ _ h2π]; congr 1; ring
  have hI : I ^ m.natAbs * I ^ m.natAbs = (-1) ^ m.natAbs := by
    rw [← mul_pow, I_mul_I]
  have g1 : Gamma (1 / 2 + s - 1 / 6 + halfMode m) = Gamma (1 / 3 + halfMode m + s) := by
    congr 1; ring
  have g2 : Gamma (1 - (1 / 2 + s - 1 / 6) + halfMode m) = Gamma (2 / 3 + halfMode m - s) := by
    congr 1; ring
  have g3 : Gamma (1 / 2 + s + 1 / 6 + halfMode m) = Gamma (2 / 3 + halfMode m + s) := by
    congr 1; ring
  have g4 : Gamma (1 - (1 / 2 + s + 1 / 6) + halfMode m) = Gamma (1 / 3 + halfMode m - s) := by
    congr 1; ring
  rw [g1, g2, g3, g4, ← hcpow, ← hI]
  ring

/-- Reflecting `(m, τ, t) ↦ (−m, −τ, −t)` inverts the multiplier. -/
theorem hankelMultiplier_reflect (m : ℤ) (τ : ℝ) (t : ℂ) :
    hankelMultiplier (-m) (-τ) (-t) = (hankelMultiplier m τ t)⁻¹ := by
  unfold hankelMultiplier hankelRatio
  rw [halfMode_neg, show -t + ((-τ : ℝ) : ℂ) * I = -(t + τ * I) by push_cast; ring]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  rw [inv_div]

/-- `K_{m,τ}(t) K_{−m,−τ}(−t) = 1` wherever the four Gamma values are finite and nonzero. -/
theorem hankelMultiplier_mul_reflect (m : ℤ) (τ : ℝ) (t : ℂ)
    (h1 : ∀ n : ℕ, 1 / 3 + halfMode m + (t + τ * I) ≠ -n)
    (h2 : ∀ n : ℕ, 2 / 3 + halfMode m + (t + τ * I) ≠ -n)
    (h3 : ∀ n : ℕ, 1 / 3 + halfMode m - (t + τ * I) ≠ -n)
    (h4 : ∀ n : ℕ, 2 / 3 + halfMode m - (t + τ * I) ≠ -n) :
    hankelMultiplier m τ t * hankelMultiplier (-m) (-τ) (-t) = 1 := by
  rw [hankelMultiplier_reflect]
  apply mul_inv_cancel₀
  unfold hankelMultiplier hankelRatio
  exact div_ne_zero (mul_ne_zero (Gamma_ne_zero h1) (Gamma_ne_zero h2))
    (mul_ne_zero (Gamma_ne_zero h3) (Gamma_ne_zero h4))

theorem halfMode_re_nonneg (m : ℤ) : 0 ≤ (halfMode m).re := by
  unfold halfMode
  rw [div_re]
  simp only [intCast_re, intCast_im]
  have : (0 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg m
  have h2 : normSq (2 : ℂ) = 4 := by norm_num [normSq_apply]
  simp only [re_ofNat, im_ofNat, h2]
  positivity

/-- `K_{m,τ}` is holomorphic on `Re t > −1/3`. -/
theorem differentiableOn_hankelMultiplier (m : ℤ) (τ : ℝ) :
    DifferentiableOn ℂ (hankelMultiplier m τ) {t : ℂ | -1 / 3 < t.re} := by
  intro t ht
  have hm := halfMode_re_nonneg m
  have hre1 : 0 < (1 / 3 + halfMode m + (t + τ * I)).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    norm_num
    simp only [Set.mem_setOf_eq] at ht
    linarith
  have hre2 : 0 < (2 / 3 + halfMode m + (t + τ * I)).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    norm_num
    simp only [Set.mem_setOf_eq] at ht
    linarith
  have hnp : ∀ {z : ℂ}, 0 < z.re → ∀ n : ℕ, z ≠ -n := by
    intro z hz n h
    rw [h] at hz
    simp at hz
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlin : Differentiable ℂ (fun t : ℂ => t + τ * I) := by fun_prop
  have dA : DifferentiableAt ℂ (fun t : ℂ => Gamma (1 / 3 + halfMode m + (t + τ * I))) t :=
    (differentiableAt_Gamma _ (hnp hre1)).comp t (by fun_prop)
  have dB : DifferentiableAt ℂ (fun t : ℂ => Gamma (2 / 3 + halfMode m + (t + τ * I))) t :=
    (differentiableAt_Gamma _ (hnp hre2)).comp t (by fun_prop)
  have dC : DifferentiableAt ℂ (fun t : ℂ => (Gamma (1 / 3 + halfMode m - (t + τ * I)))⁻¹) t :=
    (differentiable_one_div_Gamma.differentiableAt).comp t (by fun_prop)
  have dD : DifferentiableAt ℂ (fun t : ℂ => (Gamma (2 / 3 + halfMode m - (t + τ * I)))⁻¹) t :=
    (differentiable_one_div_Gamma.differentiableAt).comp t (by fun_prop)
  have heq : hankelMultiplier m τ = fun t : ℂ =>
      Gamma (1 / 3 + halfMode m + (t + τ * I)) * Gamma (2 / 3 + halfMode m + (t + τ * I)) *
        (Gamma (1 / 3 + halfMode m - (t + τ * I)))⁻¹ *
          (Gamma (2 / 3 + halfMode m - (t + τ * I)))⁻¹ := by
    funext t
    unfold hankelMultiplier hankelRatio
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [heq]
  exact (((dA.mul dB).mul dC).mul dD).differentiableWithinAt

end

end GaloisForLFunctions.JointMarkedMoments
