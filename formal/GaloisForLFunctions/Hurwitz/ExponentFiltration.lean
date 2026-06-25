/-
# Exponent filtration: separating singular exponents from the periodic regular part

In the `z = log x` coordinate the Hurwitz local data becomes clean:

* the singular term `x^{-s-k} = exp(β_k z)` with `β_k = -s-k` picks up `exp(2πi β_k) = exp(-2πi s)`
  under the monodromy loop `x ↦ e^{2πi} x`, i.e. the **shift** `z ↦ z + 2πi`;
* the regular part `R(x) = R(e^z)` is automatically **2πi-periodic** in `z`.

So a single shift-difference of the relation annihilates the regular part, leaving a pure exponential
combination `∑_k c_k (exp(2πi β_k) - 1) exp(β_k z) = 0`, which `expLin_linearIndependent` (distinct
`β_k`) collapses to `c_k (exp(2πi β_k) - 1) = 0`; with `β_k ∉ ℤ` (`exp(2πi β_k) ≠ 1`) every `c_k = 0`.

This is the exponent-filtration core of the Hurwitz quadratic descent — separating the non-integer
singular exponents from the integer-frequency (periodic) regular germ — built purely on the
`ExpIndependence` core, no Hurwitz zeta yet.
-/
import GaloisForLFunctions.Hurwitz.ExpIndependence

open Complex

namespace HurwitzExp

/-- **Exponent filtration / singular-vs-regular separation.** If a finite sum of singular exponentials
`∑_k c_k exp(β_k z)` (distinct `β_k`, none an integer so `exp(2πi β_k) ≠ 1`) plus a `2πi`-periodic
regular part `H` vanishes identically, then every singular coefficient `c_k = 0`. Proof: the shift
`z ↦ z + 2πi` fixes `H` and multiplies `exp(β_k z)` by `exp(2πi β_k)`, so the shift-difference is the
pure combination `∑_k c_k (exp(2πi β_k) - 1) exp(β_k z) = 0`; `expLin_linearIndependent` gives
`c_k (exp(2πi β_k) - 1) = 0`, hence `c_k = 0`. -/
theorem coeffs_zero_of_exp_periodic_combo {K : ℕ} {β : Fin K → ℂ} (hβ : Function.Injective β)
    (hβint : ∀ k, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) ≠ 1) {c : Fin K → ℂ}
    {H : ℂ → ℂ} (hper : ∀ z, H (z + 2 * (Real.pi : ℂ) * Complex.I) = H z)
    (h : ∀ z, ∑ k, c k * Complex.exp (β k * z) + H z = 0) : c = 0 := by
  have hexp : ∀ (k : Fin K) (z : ℂ), Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) * Complex.exp (β k * z) := by
    intro k z
    rw [show β k * (z + 2 * (Real.pi : ℂ) * Complex.I)
          = β k * z + 2 * (Real.pi : ℂ) * Complex.I * β k from by ring, Complex.exp_add]
    ring
  -- the shift-difference kills H, leaving a pure exponential combination
  have hdiff : ∀ z, ∑ k, (c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1))
      * Complex.exp (β k * z) = 0 := by
    intro z
    have h1 := h (z + 2 * (Real.pi : ℂ) * Complex.I)
    rw [hper z] at h1
    have h2 := h z
    have key : ∑ k, c k * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I))
        = ∑ k, c k * Complex.exp (β k * z) := by linear_combination h1 - h2
    rw [show (0 : ℂ) = (∑ k, c k * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I)))
          - ∑ k, c k * Complex.exp (β k * z) from by rw [key]; ring,
        ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [hexp k z]; ring)
  -- expLin collapses the pure combination, then β_k ∉ ℤ removes the scalar
  have hLI := expLin_linearIndependent hβ
  rw [Fintype.linearIndependent_iff] at hLI
  have hd : ∀ k, c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1) = 0 := by
    intro k
    refine hLI (fun k => c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1)) ?_ k
    funext z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hdiff z
  funext k
  exact (mul_eq_zero.mp (hd k)).resolve_right (sub_ne_zero.mpr (hβint k))

end HurwitzExp
