import GaloisForLFunctions.RHTower.XiBoundaryPoissonDensity
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszMarkovTransform
import GaloisForLFunctions.HTGeometry.HalfLineTransportDistance

/-!
# The tail-Laplace conjugation and the offset-free prime weights

The finite exponential packet of a safe node/coefficient system has two presentations,
`f (y) = exp (-a y) g_a (y)`, and the Laplace transforms of `g_a` on `(0, ∞)` and on `(x, ∞)`
reproduce the two resolvent sums of the Cauchy-loss inequality.  Integrating the subtracted
`x`-variable first leaves the complementary factor `exp (-2 a min (y, z))`, which factors as
`exp (-a y) exp (-a z) exp (a |y - z|)`: the inverse Poisson conjugation.

On the prime side the same conjugation multiplies the atom weight `-Λ(n) n^{-1/2-a} / 2` at
`u = ± log n` by `exp (a |± log n|) = n^a`, leaving the offset-free critical weight
`-Λ(n) n^{-1/2} / 2`.
-/

noncomputable section

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ### Equations (5)-(7): the tail-Laplace conjugation -/

/-- The shifted exponential packet `g_a` of `(5)`. -/
def shiftedExpPacket {n : ℕ} (a : ℝ) (c w : Fin n → ℂ) (y : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (-((w j - (a : ℂ)) * (y : ℂ)))

/-- The unshifted exponential packet `f` of `(5)`. -/
def expPacket {n : ℕ} (c w : Fin n → ℂ) (y : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (-(w j * (y : ℂ)))

/-- **Equation (5).**  The two packets differ by the exponential tilt of the offset. -/
theorem expPacket_eq_tilt {n : ℕ} (a : ℝ) (c w : Fin n → ℂ) (y : ℝ) :
    expPacket c w y = Complex.exp (-((a : ℂ) * (y : ℂ))) * shiftedExpPacket a c w y := by
  rw [expPacket, shiftedExpPacket, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_comm (Complex.exp (-((a : ℂ) * (y : ℂ)))) (c j), mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

theorem re_node_shift {a : ℝ} {w : ℂ} (hw : a < w.re) (t : ℝ) :
    0 < (w - (a : ℂ) - Complex.I * (t : ℂ)).re := by
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
  linarith

/-- **Equation (6).**  The Laplace transform of the shifted packet on the half line is the
resolvent sum of the Cauchy-loss inequality. -/
theorem laplace_shiftedExpPacket {n : ℕ} {a : ℝ} {c w : Fin n → ℂ}
    (hw : ∀ j, a < (w j).re) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ),
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) * shiftedExpPacket a c w y)
      = ∑ j, c j / (w j - (a : ℂ) - Complex.I * (t : ℂ)) := by
  have hcongr : ∀ y : ℝ,
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) * shiftedExpPacket a c w y
        = ∑ j, c j * Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (y : ℂ))) := by
    intro y
    rw [shiftedExpPacket, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, mul_comm (Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) (c j), mul_assoc,
      ← Complex.exp_add]
    congr 2
    ring
  have hint : ∀ j : Fin n, IntegrableOn
      (fun y : ℝ => c j * Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (y : ℂ))))
      (Ioi (0 : ℝ)) :=
    fun j => (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul_shift (re_node_shift (hw j) t)
      (le_refl (0 : ℝ))).const_mul _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => hcongr y),
    MeasureTheory.integral_finsetSum _ (fun j _ => hint j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul_shift (re_node_shift (hw j) t) (0 : ℝ)]
  simp [div_eq_mul_inv]

/-- **Equation (7).**  The tail Laplace transform reproduces the damped resolvent sum. -/
theorem laplace_tail_shiftedExpPacket {n : ℕ} {a : ℝ} {c w : Fin n → ℂ}
    (hw : ∀ j, a < (w j).re) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ)))
        * ∫ y in Ioi x, Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) * shiftedExpPacket a c w y
      = ∑ j, c j * Complex.exp (-(w j * (x : ℂ)))
          / (w j - (a : ℂ) - Complex.I * (t : ℂ)) := by
  have hcongr : ∀ y : ℝ,
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) * shiftedExpPacket a c w y
        = ∑ j, c j * Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (y : ℂ))) := by
    intro y
    rw [shiftedExpPacket, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, mul_comm (Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) (c j), mul_assoc,
      ← Complex.exp_add]
    congr 2
    ring
  have hint : ∀ j : Fin n, IntegrableOn
      (fun y : ℝ => c j * Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (y : ℂ))))
      (Ioi x) :=
    fun j => (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul_shift (re_node_shift (hw j) t) hx).const_mul _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => hcongr y),
    MeasureTheory.integral_finsetSum _ (fun j _ => hint j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul_shift (re_node_shift (hw j) t) x]
  have hden : w j - (a : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have := re_node_shift (hw j) t
    rw [h, Complex.zero_re] at this
    exact absurd this (lt_irrefl 0)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hexp : Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ)))
      * Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))
      = Complex.exp (-(w j * (x : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ)))
        * (c j * (Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))
          * (w j - (a : ℂ) - Complex.I * (t : ℂ))⁻¹))
      = c j * (Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ)))
          * Complex.exp (-((w j - (a : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))))
        * (w j - (a : ℂ) - Complex.I * (t : ℂ))⁻¹ := by ring
    _ = c j * Complex.exp (-(w j * (x : ℂ)))
        * (w j - (a : ℂ) - Complex.I * (t : ℂ))⁻¹ := by rw [hexp]

/-! ### Equations (8)-(9): the minimum kernel and its inverse Poisson factor -/

/-- **Equation (8).**  Integrating the subtracted variable first leaves the minimum kernel. -/
theorem integral_min_exp {a : ℝ} (ha : a ≠ 0) (y z : ℝ) :
    2 * a * ∫ x in (0 : ℝ)..(min y z), Real.exp (-(2 * a * x))
      = 1 - Real.exp (-(2 * a * min y z)) := by
  have hne : (-(2 * a)) ≠ 0 := by
    simpa using ha
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun u : ℝ => Real.exp (-(2 * a * u)) / (-(2 * a)))
        (Real.exp (-(2 * a * x))) x := by
    intro x
    have hlin : HasDerivAt (fun u : ℝ => -(2 * a * u)) (-(2 * a)) x := by
      have h : HasDerivAt (fun u : ℝ => (-(2 * a)) * u) ((-(2 * a)) * 1) x :=
        (hasDerivAt_id x).const_mul (-(2 * a))
      simpa [neg_mul] using h
    have hexp := (Real.hasDerivAt_exp (-(2 * a * x))).comp x hlin
    have hval := hexp.div_const (-(2 * a))
    refine hval.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    ((Continuous.intervalIntegrable (by fun_prop) _ _)), mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- **Equation (9).**  The minimum kernel is the inverse Poisson conjugation of the tilt. -/
theorem exp_neg_two_mul_min (a y z : ℝ) :
    Real.exp (-(2 * a * min y z))
      = Real.exp (-(a * y)) * Real.exp (-(a * z)) * Real.exp (a * |y - z|) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have habs := abs_sub_eq_add_sub_two_min y z
  rw [habs]
  ring

/-! ### Equations (17)-(20): the offset-free prime weights -/

/-- **Equation (18).**  The atom weight of the prime power `n` in the boundary autocorrelation. -/
def primeAtomWeight (a : ℝ) (n : ℕ) : ℝ :=
  -(1 / 2) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 + a))

/-- **Equation (19).**  The inverse Poisson factor at the atom `± log n` is `n ^ a`. -/
theorem exp_mul_abs_log (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (a * |Real.log n|) = (n : ℝ) ^ a := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [abs_of_nonneg hlog, mul_comm, Real.exp_mul, Real.exp_log hn0]

/-- **Equation (20).**  De-Poissonizing the atom weight removes the safe offset exactly. -/
theorem primeAtomWeight_dePoissonized {a : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    primeAtomWeight a n * Real.exp (a * |Real.log n|)
      = -(1 / 2) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  rw [primeAtomWeight, exp_mul_abs_log a hn, mul_assoc, ← Real.rpow_add hn0]
  congr 2
  ring

/-- The de-Poissonized prime weight does not depend on the safe offset. -/
theorem primeAtomWeight_dePoissonized_offset_free {a b : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    primeAtomWeight a n * Real.exp (a * |Real.log n|)
      = primeAtomWeight b n * Real.exp (b * |Real.log n|) := by
  rw [primeAtomWeight_dePoissonized hn, primeAtomWeight_dePoissonized hn]

end RHTower
