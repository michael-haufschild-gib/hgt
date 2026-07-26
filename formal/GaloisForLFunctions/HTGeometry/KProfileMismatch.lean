import Mathlib

/-!
# A Gaussian profile cannot match a reciprocal-square-root profile

Two one-parameter families of moduli occur when a mean value `T⁻¹∫₀^T exp(i k φ(t)) dt` is evaluated
in two ways.  A phase of the form `C log t + D` produces the modulus `(1 + 4π²k²C²)^(-1/2)`, which
decays **polynomially** in `k`; an Euler product of averaged exponentials produces `exp(-k²E)` with
`E` the total energy, which decays **super-exponentially** once `E > 0`.

The two therefore disagree for all large `k`:

```text
√(1 + 4π²k²C²) ≤ 1 + 2π|C|k < 1 + k²E ≤ exp (k²E)      whenever  2π|C| < kE .
```

Neither the geometric nor the arithmetic side is used here; only the elementary fact that a
polynomial in `k` is eventually beaten by `exp (k²E)` for any positive `E`.  Consequently an identity
between the two profiles forces `E = 0`, and then `C = 0` as well since `exp 0 = 1` exceeds
`(1 + 4π²k²C²)^(-1/2)` for `C ≠ 0`.
-/

namespace HTGeometry

/-- `√(1 + a²) ≤ 1 + a` for `a ≥ 0`. -/
theorem sqrt_one_add_sq_le {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (1 + a ^ 2) ≤ 1 + a := by
  have h1 : (1 : ℝ) + a ^ 2 ≤ (1 + a) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) ≤ 1 + a := by linarith
  calc Real.sqrt (1 + a ^ 2) ≤ Real.sqrt ((1 + a) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = 1 + a := Real.sqrt_sq h2

/-- **Profile mismatch.**  For positive energy `E`, the Gaussian profile `exp (k²E)` exceeds the
reciprocal of the logarithmic-phase profile as soon as `k E > 2π|C|`. -/
theorem sqrt_lt_exp_of_energy_pos {E C k : ℝ} (hk : 0 < k)
    (hkgt : 2 * Real.pi * |C| < k * E) :
    Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2) < Real.exp (k ^ 2 * E) := by
  have hA : (0 : ℝ) ≤ 2 * Real.pi * |C| * k := by positivity
  have hrw : 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2 = (2 * Real.pi * |C| * k) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have h1 : Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2) ≤ 1 + 2 * Real.pi * |C| * k := by
    rw [hrw]
    exact sqrt_one_add_sq_le hA
  have h2 : 1 + 2 * Real.pi * |C| * k < 1 + k ^ 2 * E := by
    have := mul_lt_mul_of_pos_right hkgt hk
    nlinarith [this]
  have h3 : 1 + k ^ 2 * E ≤ Real.exp (k ^ 2 * E) := by
    have := Real.add_one_le_exp (k ^ 2 * E)
    linarith
  linarith

/-- The same statement in the form the two evaluations are compared in: the Euler-product modulus
`exp (-k²E)` is strictly smaller than the logarithmic-phase modulus `(1 + 4π²k²C²)^(-1/2)`. -/
theorem exp_neg_lt_inv_sqrt {E C k : ℝ} (hk : 0 < k)
    (hkgt : 2 * Real.pi * |C| < k * E) :
    Real.exp (-(k ^ 2 * E)) < (Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2))⁻¹ := by
  have hpos : (0 : ℝ) < Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := sqrt_lt_exp_of_energy_pos hk hkgt
  have hexp : (0 : ℝ) < Real.exp (k ^ 2 * E) := Real.exp_pos _
  rw [Real.exp_neg, inv_lt_inv₀ hexp hpos]
  exact hmain

/-- At zero energy the Euler product has modulus `1`, which already exceeds the logarithmic-phase
modulus unless the logarithmic coefficient vanishes. -/
theorem inv_sqrt_lt_one_of_ne_zero {C k : ℝ} (hC : C ≠ 0) (hk : k ≠ 0) :
    (Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2))⁻¹ < 1 := by
  have hgt : (1 : ℝ) < 1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2 := by
    have h1 : (0 : ℝ) < 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2 := by positivity
    linarith
  have hs : (1 : ℝ) < Real.sqrt (1 + 4 * Real.pi ^ 2 * k ^ 2 * C ^ 2) := by
    have := Real.sqrt_lt_sqrt (by norm_num) hgt
    simpa using this
  rw [inv_lt_one₀ (by linarith)]
  exact hs

end HTGeometry
