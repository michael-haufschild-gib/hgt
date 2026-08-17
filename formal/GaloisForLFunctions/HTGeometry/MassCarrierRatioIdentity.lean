import GaloisForLFunctions.HTGeometry.MassShellRootFactorization
import GaloisForLFunctions.HTGeometry.BesselK1PoincareForm

/-!
# The carrier against its deep-time profile, at every order

Substituting the Poincaré form of the order-one Schläfli asymptotic into the massive radiation
carrier writes the carrier as its deep-time profile times an explicit distortion -- a root ratio, a
root-of-root ratio, the exponential of the root defect and the Poincaré polynomial at the shell
argument -- plus the carrier weight of the Poincaré remainder.

The identity is exact at every order; only the last term is an error.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section CarrierRatio

variable {a : ℝ} {t : ℂ}

/-- The Poincaré polynomial of `K_1` evaluated at the shell argument. -/
def shellPoincareSum (a : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ) * (((a : ℂ) * z)⁻¹) ^ k

/-- The Poincaré remainder of `K_1` at the shell argument. -/
def shellPoincareRemainder (a : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  _root_.HTGeometry.besselK1C ((a : ℂ) * z)
    - Complex.exp (-((a : ℂ) * z)) * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)
      * shellPoincareSum a z n

/-- The distortion of the carrier against its deep-time profile, at order `n`. -/
def carrierDistortion (a : ℝ) (t z : ℂ) (n : ℕ) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ) * (t / z) * (_root_.HTGeometry.csqrt t / _root_.HTGeometry.csqrt z)
    * Complex.exp (-((a : ℂ) * (z - t))) * shellPoincareSum a z n

/-- **The carrier at every order.** -/
theorem massBesselCarrier_eq_distortion (ha : 0 < a) (ht : 0 < t.re) (x : ℝ)
    (hz : 0 < (_root_.HTGeometry.massBesselRoot t x).re) (n : ℕ) :
    _root_.HTGeometry.massBesselCarrier a t x
      = _root_.HTGeometry.massBesselLeading a t
          * carrierDistortion a t (_root_.HTGeometry.massBesselRoot t x) n
        + 2 * (a : ℂ) * t
            * shellPoincareRemainder a (_root_.HTGeometry.massBesselRoot t x) n
            / _root_.HTGeometry.massBesselRoot t x := by
  set z : ℂ := _root_.HTGeometry.massBesselRoot t x with hzdef
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hcsz : _root_.HTGeometry.csqrt z ≠ 0 := _root_.HTGeometry.csqrt_ne_zero hz
  have hcst : _root_.HTGeometry.csqrt t ≠ 0 := _root_.HTGeometry.csqrt_ne_zero ht
  have hlead := _root_.HTGeometry.two_mul_besselLeading_eq ha hz
  have hexp : Complex.exp (-((a : ℂ) * t)) * Complex.exp (-((a : ℂ) * (z - t)))
      = Complex.exp (-((a : ℂ) * z)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hK : _root_.HTGeometry.besselK1C ((a : ℂ) * z)
      = Complex.exp (-((a : ℂ) * z)) * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)
          * shellPoincareSum a z n
        + shellPoincareRemainder a z n := by
    rw [shellPoincareRemainder]
    ring
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2c : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs2
  have hlead2 : 2 * (a : ℂ) * (Complex.exp (-((a : ℂ) * z))
        * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ))
      = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ)
        * Complex.exp (-((a : ℂ) * z)) / _root_.HTGeometry.csqrt z := by
    have h : ((Real.sqrt 2 : ℝ) : ℂ) * (2 * (a : ℂ) * (Complex.exp (-((a : ℂ) * z))
        * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)))
        = ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ)
          * Complex.exp (-((a : ℂ) * z)) / _root_.HTGeometry.csqrt z) := by
      rw [hlead]
    rw [Complex.ofReal_inv] at h
    field_simp at h ⊢
    linear_combination h
  have hmain : 2 * (a : ℂ) * t
      * (Complex.exp (-((a : ℂ) * z)) * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)
        * shellPoincareSum a z n) / z
      = _root_.HTGeometry.massBesselLeading a t * carrierDistortion a t z n := by
    rw [carrierDistortion, _root_.HTGeometry.massBesselLeading]
    calc (2 : ℂ) * (a : ℂ) * t
          * (Complex.exp (-((a : ℂ) * z)) * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)
            * shellPoincareSum a z n) / z
        = (t * shellPoincareSum a z n / z)
            * (2 * (a : ℂ) * (Complex.exp (-((a : ℂ) * z))
              * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ))) := by ring
      _ = (t * shellPoincareSum a z n / z)
            * (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ)
              * Complex.exp (-((a : ℂ) * z)) / _root_.HTGeometry.csqrt z) := by rw [hlead2]
      _ = ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * Complex.exp (-((a : ℂ) * t))
            / _root_.HTGeometry.csqrt t
          * (((Real.sqrt 2 : ℝ) : ℂ) * (t / z)
            * (_root_.HTGeometry.csqrt t / _root_.HTGeometry.csqrt z)
            * Complex.exp (-((a : ℂ) * (z - t))) * shellPoincareSum a z n) := by
          rw [← hexp]
          field_simp
  rw [_root_.HTGeometry.massBesselCarrier, hK]
  rw [← hmain]
  ring

end CarrierRatio

end

end GaloisForLFunctions.HTGeometry
