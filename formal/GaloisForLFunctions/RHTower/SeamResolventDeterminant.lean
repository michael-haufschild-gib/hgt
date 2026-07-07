/-
The seam resolvent-determinant identity: `tr((z·1 − Θ)⁻¹) = (det(z·1 − Θ))'/det(z·1 − Θ)`.

The seam construction's determinant step (`sdet(s − Θ_Δ) = C·ξ`) integrates the resolvent-flux identity
`Str((s − Θ_Δ)⁻¹) = ξ'/ξ`.  Its finite/spectral core is Jacobi's formula: the trace of the resolvent is
the logarithmic derivative of the characteristic determinant.  For a generator presented by its
eigenvalue family `t : n → ℂ` (the seam model presents `Θ_Δ` by its spectrum — the ξ-zeros — exactly
as `CarrierPickKernel` models the carrier `m(z) = Σ_i (t_i − z)⁻¹`), the generator is `diagonal t` and:

* `det_res` — `det(z·1 − diagonal t) = ∏_i (z − t_i)`: the characteristic determinant is the product
  over the spectrum (the finite "`ξ`").
* `trace_inv_res` — `tr((z·1 − diagonal t)⁻¹) = Σ_i (z − t_i)⁻¹`: the resolvent trace is the sum of
  simple poles at the spectrum (the finite resolvent/Pick face).
* `resolvent_trace_eq_logDeriv_det` — **Jacobi**: `tr((z·1 − diagonal t)⁻¹) =
  logDeriv (det(·1 − diagonal t)) z`.  Both sides are `Σ_i (z − t_i)⁻¹`; the determinant side via
  `logDeriv_prod` on `∏_i (w − t_i)`.
* `carrier_eq_neg_logDeriv_det` — the Pick carrier `m(z) = Σ_i (t_i − z)⁻¹` is
  `−logDeriv(det(·1 − diagonal t)) z`: the finite `−Ξ'/Ξ`, i.e. the finite shadow of the seam-flux
  cochain `−ξ'/ξ`.

This is the bridge that turns `Str((s − Θ_Δ)⁻¹) = ξ'/ξ` into `sdet(s − Θ_Δ) = C·ξ` by integration:
`logDeriv det = tr(resolvent)`, so if the resolvent trace is `ξ'/ξ` then `det` and `ξ` have equal
logarithmic derivative, hence agree up to a constant.  Here it is proved unconditionally for every
finite spectral truncation `diagonal t`.
-/
import GaloisForLFunctions.RHTower.SeamFluxCompletion
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

namespace RHTower

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The scalar matrix is diagonal: `z·1 = diagonal (fun _ => z)`. -/
theorem smul_one_eq_diagonal (z : ℂ) : z • (1 : Matrix n n ℂ) = diagonal (fun _ => z) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]; congr 1; ext i; simp

omit [Fintype n] in
/-- The resolvent argument in spectral form: `z·1 − diagonal t = diagonal (fun i => z − t_i)`. -/
theorem smul_one_sub_diagonal (z : ℂ) (t : n → ℂ) :
    z • (1 : Matrix n n ℂ) - diagonal t = diagonal (fun i => z - t i) := by
  rw [smul_one_eq_diagonal, ← Matrix.diagonal_sub]

/-- **The characteristic determinant is the product over the spectrum.**
`det(z·1 − diagonal t) = ∏_i (z − t_i)` — the finite "`ξ`". -/
theorem det_smul_one_sub_diagonal (z : ℂ) (t : n → ℂ) :
    (z • (1 : Matrix n n ℂ) - diagonal t).det = ∏ i, (z - t i) := by
  rw [smul_one_sub_diagonal, Matrix.det_diagonal]

/-- The resolvent in spectral form: `(z·1 − diagonal t)⁻¹ = diagonal (fun i => (z − t_i)⁻¹)` off the
spectrum. -/
theorem inv_smul_one_sub_diagonal (z : ℂ) (t : n → ℂ) (hz : ∀ i, z - t i ≠ 0) :
    (z • (1 : Matrix n n ℂ) - diagonal t)⁻¹ = diagonal (fun i => (z - t i)⁻¹) := by
  rw [smul_one_sub_diagonal]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal,
    show (fun i => (z - t i) * (z - t i)⁻¹) = (fun _ => (1 : ℂ)) from
      funext fun i => mul_inv_cancel₀ (hz i), Matrix.diagonal_one]

/-- **The resolvent trace is the sum of simple poles at the spectrum.**
`tr((z·1 − diagonal t)⁻¹) = Σ_i (z − t_i)⁻¹` — the finite resolvent/Pick face. -/
theorem trace_inv_smul_one_sub_diagonal (z : ℂ) (t : n → ℂ) (hz : ∀ i, z - t i ≠ 0) :
    (z • (1 : Matrix n n ℂ) - diagonal t)⁻¹.trace = ∑ i, (z - t i)⁻¹ := by
  rw [inv_smul_one_sub_diagonal z t hz, Matrix.trace_diagonal]

omit [DecidableEq n] in
/-- The logarithmic derivative of the characteristic product is the resolvent trace:
`logDeriv (∏_i (· − t_i)) z = Σ_i (z − t_i)⁻¹`, via `logDeriv_prod` on the simple factors
`logDeriv(w − t_i) = (z − t_i)⁻¹`. -/
theorem logDeriv_charProd (z : ℂ) (t : n → ℂ) (hz : ∀ i, z - t i ≠ 0) :
    logDeriv (fun w => ∏ i, (w - t i)) z = ∑ i, (z - t i)⁻¹ := by
  rw [logDeriv_prod (fun i _ => hz i) (fun i _ => by fun_prop)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logDeriv_apply, show deriv (fun w => w - t i) z = 1 from by simp, one_div]

/-- **Jacobi's formula, spectral form.**  The resolvent trace equals the logarithmic derivative of the
characteristic determinant:
`tr((z·1 − diagonal t)⁻¹) = logDeriv (fun w => det(w·1 − diagonal t)) z`.  Both sides are
`Σ_i (z − t_i)⁻¹`.  This is the finite core of the seam resolvent-flux identity
`Str((s − Θ_Δ)⁻¹) = (sdet(s − Θ_Δ))'/sdet(s − Θ_Δ)`. -/
theorem resolvent_trace_eq_logDeriv_det (z : ℂ) (t : n → ℂ) (hz : ∀ i, z - t i ≠ 0) :
    (z • (1 : Matrix n n ℂ) - diagonal t)⁻¹.trace
      = logDeriv (fun w => (w • (1 : Matrix n n ℂ) - diagonal t).det) z := by
  rw [trace_inv_smul_one_sub_diagonal z t hz,
    show (fun w => (w • (1 : Matrix n n ℂ) - diagonal t).det) = (fun w => ∏ i, (w - t i)) from
      funext fun w => det_smul_one_sub_diagonal w t,
    logDeriv_charProd z t hz]

/-- **The Pick carrier is minus the logarithmic derivative of the determinant.**
`Σ_i (t_i − z)⁻¹ = −logDeriv (fun w => det(w·1 − diagonal t)) z`.  The finite carrier
`m(z) = Σ_i (t_i − z)⁻¹` (`CarrierPickKernel`) is the finite `−Ξ'/Ξ` — the finite shadow of the
seam-flux cochain `−ξ'/ξ = seamFluxCochain`.  The Herglotz/Pick positivity of `m` (a real spectrum
`t`) is thus the finite realization of the seam's spectral face. -/
theorem carrier_eq_neg_logDeriv_det (z : ℂ) (t : n → ℂ) (hz : ∀ i, z - t i ≠ 0) :
    ∑ i, (t i - z)⁻¹ = -logDeriv (fun w => (w • (1 : Matrix n n ℂ) - diagonal t).det) z := by
  rw [← resolvent_trace_eq_logDeriv_det z t hz, trace_inv_smul_one_sub_diagonal z t hz,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show t i - z = -(z - t i) from by ring, neg_inv]

end RHTower
