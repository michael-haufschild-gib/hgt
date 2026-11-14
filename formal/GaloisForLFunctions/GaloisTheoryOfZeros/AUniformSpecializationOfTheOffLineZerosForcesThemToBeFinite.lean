import GaloisForLFunctions.GaloisTheoryOfZeros.TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness

/-!
# A uniform specialization of the off-line zeros forces them to be finite

Every zero of ξ continues to the zeros of `H_t` for small real `t > 0`, and on every finite window
the arithmetic group acts on the continuations as heat monodromy, with a time `t₀` that depends
on the window. A uniform time is obstructed by the off-line zeros: for `t > 0` the heat family
has only finitely many nonreal zeros (Ki–Kim–Lee).

* **No uniform specialization** (`finite_offLine_of_uniform`). If on a common interval
  `0 < t < t₀` the off-line zeros of ξ have continuations `w_ρ(t)` that are nonreal zeros of
  `H_t`, distinct for distinct zeros, then only finitely many zeros of ξ are off the line.

So a specialization from the time `0` that is uniform in the window and keeps off-line zeros
apart and off the real axis exists only if the off-line zeros are finite in number; on finite
windows it always exists.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower RHTower.DeBruijn
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- **No uniform specialization.** A family of continuations of the off-line zeros that, on one
interval of positive times, consists of nonreal zeros of `H_t` and separates the zeros forces the
off-line zeros to be finite. -/
theorem finite_offLine_of_uniform {t₀ : ℝ} (ht₀ : 0 < t₀) (w : XiDivisorSupport → ℝ → ℂ)
    (hzero : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≠ 1 / 2 → ∀ t, 0 < t → t < t₀ →
      complexHeat (t : ℂ) (w ρ t) = 0 ∧ (w ρ t).im ≠ 0)
    (hinj : ∀ t, 0 < t → t < t₀ →
      Set.InjOn (fun ρ => w ρ t) {ρ : XiDivisorSupport | (ρ : ℂ).re ≠ 1 / 2}) :
    {ρ : XiDivisorSupport | (ρ : ℂ).re ≠ 1 / 2}.Finite := by
  have ht : 0 < t₀ / 2 := half_pos ht₀
  have ht' : t₀ / 2 < t₀ := half_lt_self ht₀
  refine Set.Finite.of_finite_image ((riemannHeat_nonreal_zeros_finite ht).subset ?_)
    (hinj _ ht ht')
  rintro _ ⟨ρ, hρ, rfl⟩
  obtain ⟨h0, him⟩ := hzero ρ hρ _ ht ht'
  exact ⟨by rw [← complexHeat_ofReal]; exact h0, him⟩

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.finite_offLine_of_uniform
