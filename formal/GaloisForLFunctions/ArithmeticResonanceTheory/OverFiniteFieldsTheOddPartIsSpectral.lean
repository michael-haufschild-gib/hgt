import Mathlib

/-!
# Over a finite field the odd part is spectral

Calibration of the resonance–spectrum dictionary. A curve over `𝔽_q` has the finite virtual
realization `Z(s) = det(1 − q^{−s} F) / ((1 − q^{−s})(1 − q^{1−s}))`, with odd part the Frobenius
`F` on `H¹`, a `2g × 2g` matrix, and lengths `k log q`.

* **Zeros are spectral** (`det_one_sub_cpow_smul_eq_zero_iff`): the odd determinant vanishes at `s`
  exactly when `q^s` is an eigenvalue of `F`. The resonances of the curve are the spectrum of a
  finite-dimensional operator; no positivity is involved.
* **Zeros sit on vertical progressions** (`cpow_add_period`): `q^s` is periodic with period
  `2πi / log q`, so every zero `s` comes with `s + 2πik/log q`. A finite odd part never produces zeros
  on a real progression, which is why the trivial zeros of `ζ` exclude one
  (`riemannZeta_ne_virtualRealization`).
* **RH is unitarity** (`re_eq_half_of_norm_eigenvalue`): if every eigenvalue has modulus `q^{1/2}`,
  every zero has `Re s = 1/2`, because `|q^s| = q^{Re s}`.
-/

open Matrix Complex

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The zeros of the odd determinant are the spectrum of `F`.** For `q > 0`,
`det(1 − q^{−s} F) = 0` iff `q^s` is an eigenvalue of `F`. -/
theorem det_one_sub_cpow_smul_eq_zero_iff (F : Matrix n n ℂ) {q : ℝ} (hq : 0 < q) (s : ℂ) :
    (1 - (q : ℂ) ^ (-s) • F).det = 0 ↔ ∃ v : n → ℂ, v ≠ 0 ∧ F *ᵥ v = (q : ℂ) ^ s • v := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hTinv : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ hq0, add_neg_cancel, cpow_zero]
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, sub_eq_zero]
  constructor
  · intro h
    calc F *ᵥ v = ((q : ℂ) ^ s * (q : ℂ) ^ (-s)) • (F *ᵥ v) := by rw [hTinv, one_smul]
      _ = (q : ℂ) ^ s • ((q : ℂ) ^ (-s) • (F *ᵥ v)) := by rw [mul_smul]
      _ = (q : ℂ) ^ s • v := by rw [← h]
  · intro h
    rw [h, smul_smul, mul_comm, hTinv, one_smul]

/-- `q^s` is periodic with period `2πi / log q`. -/
theorem cpow_add_period {q : ℝ} (hq : 1 < q) (s : ℂ) (k : ℤ) :
    (q : ℂ) ^ (s + 2 * Real.pi * I * k / Real.log q) = (q : ℂ) ^ s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have hlog : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  rw [cpow_def_of_ne_zero hq0, cpow_def_of_ne_zero hq0, ← ofReal_log (zero_lt_one.trans hq).le,
    mul_add, Complex.exp_add]
  have : (Real.log q : ℂ) * (2 * Real.pi * I * k / Real.log q) = k * (2 * Real.pi * I) := by
    field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **RH is unitarity.** If `q^s` is an eigenvalue of modulus `q^{1/2}`, then `Re s = 1/2`. -/
theorem re_eq_half_of_norm_eigenvalue {q : ℝ} (hq : 1 < q) {s : ℂ}
    (hnorm : ‖(q : ℂ) ^ s‖ = q ^ (1 / 2 : ℝ)) : s.re = 1 / 2 := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  rw [norm_cpow_eq_rpow_re_of_pos hq0] at hnorm
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · exact absurd hnorm (Real.rpow_lt_rpow_of_exponent_lt hq h).ne
  · exact h
  · exact absurd hnorm (Real.rpow_lt_rpow_of_exponent_lt hq h).ne'

end GaloisForLFunctions.ArithmeticResonanceTheory
