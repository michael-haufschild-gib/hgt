/-
# Hurwitz N=2 spine — the `z = log x` substitution glue

The descent runs in the coordinate `z = log x` (`x = a + n`), where the exponent filtration
(`ExponentFiltration.coeffs_zero_of_exp_periodic_combo`) applies: the singular term `x^{-(s+k)}` becomes
`exp(-(s+k)·z)` and the regular part `R(x) = R(e^z)` becomes `2πi`-periodic. This file supplies the two
substitution facts that bridge the Hurwitz-zeta local expansion to the exp-form the filtration consumes.

* `comp_exp_periodic` — `R(e^z)` is `2πi`-periodic (`e^{z+2πi} = e^z`).
* `cexp_cpow_strip` — on the strip `Im z ∈ (-π, π]`, `(e^z)^w = e^{w·z}` (so `x^{-(s+k)} = e^{-(s+k)z}`).
-/
import GaloisForLFunctions.Hurwitz.ExponentFiltration

open Complex

namespace HurwitzSpine

/-- **The regular part is `2πi`-periodic in `z = log x`.** `R(e^{z+2πi}) = R(e^z)` since `e^{2πi} = 1`.
This is the `H` (periodic) input of `coeffs_zero_of_exp_periodic_combo`. -/
theorem comp_exp_periodic (R : ℂ → ℂ) (z : ℂ) :
    R (Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I)) = R (Complex.exp z) := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Singular term in `z = log x`.** On the strip `Im z ∈ (-π, π]`, `(e^z)^w = e^{w·z}`; applied with
`z = log x` and `w = -(s+k)`, the Hurwitz singular term `x^{-(s+k)}` is `e^{-(s+k)·log x}`, the
exponential the filtration separates. -/
theorem cexp_cpow_strip {z : ℂ} (h1 : -Real.pi < z.im) (h2 : z.im ≤ Real.pi) (w : ℂ) :
    (Complex.exp z) ^ w = Complex.exp (w * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero z), Complex.log_exp h1 h2, mul_comm]

/-- **Exponent filtration on a `2πi`-invariant open region.** The Hurwitz relation holds only on a left
half-plane in `z = log x` (`x → 0`), not all `z`; this is the region version of
`coeffs_zero_of_exp_periodic_combo`. The shift `z ↦ z + 2πi` stays in the region (`2πi`-invariance) and
fixes the periodic `H`, so the shift-difference is a pure exponential combination vanishing on the open
region; `expLin_eq_zero_on_open` collapses it, and `β_k ∉ ℤ` removes the scalar. -/
theorem coeffs_zero_of_exp_periodic_combo_on_open {K : ℕ} {β : Fin K → ℂ}
    (hβ : Function.Injective β)
    (hβint : ∀ k, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) ≠ 1) {c : Fin K → ℂ}
    {H : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUinv : ∀ z ∈ U, z + 2 * (Real.pi : ℂ) * Complex.I ∈ U)
    (hper : ∀ z, H (z + 2 * (Real.pi : ℂ) * Complex.I) = H z)
    (h : ∀ z ∈ U, ∑ k, c k * Complex.exp (β k * z) + H z = 0) : c = 0 := by
  have hexp : ∀ (k : Fin K) (z : ℂ), Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) * Complex.exp (β k * z) := by
    intro k z
    rw [show β k * (z + 2 * (Real.pi : ℂ) * Complex.I)
          = β k * z + 2 * (Real.pi : ℂ) * Complex.I * β k from by ring, Complex.exp_add]
    ring
  have hdiff : ∀ z ∈ U, ∑ k, (c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1))
      * Complex.exp (β k * z) = 0 := by
    intro z hz
    have h1 := h (z + 2 * (Real.pi : ℂ) * Complex.I) (hUinv z hz)
    rw [hper z] at h1
    have h2 := h z hz
    have key : ∑ k, c k * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I))
        = ∑ k, c k * Complex.exp (β k * z) := by linear_combination h1 - h2
    rw [show (0 : ℂ) = (∑ k, c k * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I)))
          - ∑ k, c k * Complex.exp (β k * z) from by rw [key]; ring,
        ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [hexp k z]; ring)
  have hcd : (fun k => c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1)) = 0 :=
    HurwitzExp.expLin_eq_zero_on_open hβ hUo hUne hdiff
  funext k
  have := congrFun hcd k
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (hβint k))

end HurwitzSpine
