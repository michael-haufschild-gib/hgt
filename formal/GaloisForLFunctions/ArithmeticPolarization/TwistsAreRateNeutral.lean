import GaloisForLFunctions.ArithmeticPolarization.TwistedSectorsCollideQuartets

/-!
# Twists are rate neutral

A base, in the sense of the frontier (B1.9), is a structure whose loss does not scale with the
amplification. Harmonic twists `n^{−ikγ}` are the amplification class of the positive completions
of elliptic sectors. They neither gain nor lose:

* **Twisted orbit correlations** (`W_translate_twist`): translating a twisted test is a phase times
  the twist of the translate, so Weil's orbit correlation of a twisted test is `e^{iγt}` times the
  orbit correlation of the shifted configuration `Z − iγ`.
* **Rate neutrality** (`twisted_growth_iff`): a growth bound `C e^{Lt}` holds for the twisted orbit
  correlations of `Z` iff it holds for the orbit correlations of `Z − iγ`, and the shift preserves
  every real part (`shiftConfig_re`): the depth spectrum, hence every growth exponent, is
  unchanged. Twisting moves ordinates (and collides one of them) but is not an amplification.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- Translation `f(· − t)`. -/
def translate (t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => f (u - t)

/-- Translating a twisted test is a phase times twisting the translate. -/
theorem translate_twist (γ t : ℝ) (f : ℝ → ℂ) :
    translate t (twist γ f) = fun u => Complex.exp (γ * I * t) * twist γ (translate t f) u := by
  funext u
  simp only [translate, twist, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem paperFT_const_mul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    paperFT (fun u => c * f u) z = c * paperFT f z := by
  rw [paperFT, paperFT, ← MeasureTheory.integral_const_mul]
  congr 1; funext u; ring

/-- Weil's form is linear in its first test. -/
theorem W_const_mul_left (Z : Zeta23.ZeroConfig) (c : ℂ) (f g : ℝ → ℂ) :
    Z.W (fun u => c * f u) g = c * Z.W f g := by
  rw [Zeta23.ZeroConfig.W, Zeta23.ZeroConfig.W, ← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  simp only [Zeta23.ZeroConfig.Wsummand, paperFT_const_mul]
  ring

/-- **The twisted orbit correlation** is a phase times the orbit correlation of `Z − iγ`. -/
theorem W_translate_twist (Z : Zeta23.ZeroConfig) (γ t : ℝ) (f : ℝ → ℂ) :
    Z.W (translate t (twist γ f)) (twist γ f) =
      Complex.exp (γ * I * t) * (shiftConfig Z γ).W (translate t f) f := by
  rw [translate_twist, W_const_mul_left, W_twist]

/-- The shift preserves real parts: `Z − iγ` has the depth spectrum of `Z`. -/
theorem shiftConfig_re (Z : Zeta23.ZeroConfig) (γ : ℝ) :
    Complex.re '' (shiftConfig Z γ).carrier = Complex.re '' Z.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩; exact ⟨ρ, hρ, by simp⟩
  · rintro ⟨ρ, hρ, rfl⟩; exact ⟨ρ - γ * I, ⟨ρ, hρ, rfl⟩, by simp⟩

/-- **Rate neutrality.** A growth bound `C e^{Lt}` on the twisted orbit correlations of `Z` is the
same bound on the orbit correlations of `Z − iγ`. -/
theorem twisted_growth_iff (Z : Zeta23.ZeroConfig) (γ L : ℝ) (f : ℝ → ℂ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖Z.W (translate t (twist γ f)) (twist γ f)‖ ≤ C * Real.exp (L * t)) ↔
      (∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
        ‖(shiftConfig Z γ).W (translate t f) f‖ ≤ C * Real.exp (L * t)) := by
  have hn : ∀ t : ℝ, ‖Z.W (translate t (twist γ f)) (twist γ f)‖ =
      ‖(shiftConfig Z γ).W (translate t f) f‖ := by
    intro t
    rw [W_translate_twist, norm_mul, Complex.norm_exp]
    simp
  simp_rw [hn]

end GaloisForLFunctions.ArithmeticPolarization
