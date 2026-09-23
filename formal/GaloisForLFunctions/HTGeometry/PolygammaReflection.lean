/-
Classical reflection value laws for the first polygamma derivative.

The digamma reflection identity is already banked in `DigammaBounds`.  Differentiating it on the
open nonintegral locus gives the trigamma reflection law.  This module keeps the full value
identity, including its exact pole exclusion, rather than exposing only a downstream bound.
-/
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.PolygammaMultiplication
import GaloisForLFunctions.HTGeometry.DigammaBounds

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open scoped Topology

private theorem sin_pi_mul_ne_zero_of_not_int {z : ℂ}
    (hz : ∀ m : ℤ, z ≠ (m : ℂ)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hc
  apply hz k
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hswap : ((Real.pi : ℝ) : ℂ) * z = ((Real.pi : ℝ) : ℂ) * (k : ℂ) := by
    rw [hc]
    ring
  exact mul_left_cancel₀ hpi hswap

private theorem digamma_reflection_eventuallyEq {z : ℂ}
    (hz : ∀ m : ℤ, z ≠ (m : ℂ)) :
    (fun w : ℂ => Complex.digamma w - Complex.digamma (1 - w)) =ᶠ[𝓝 z]
      (fun w : ℂ => -(Real.pi : ℂ) *
        (Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))) := by
  have hsin := sin_pi_mul_ne_zero_of_not_int hz
  have hsin_cont : ContinuousAt (fun w : ℂ =>
      Complex.sin ((Real.pi : ℂ) * w)) z := by
    fun_prop
  filter_upwards [hsin_cont.eventually_ne hsin] with w hw
  have hwz : ∀ k : ℤ, w ≠ (k : ℂ) := by
    intro k hwk
    apply hw
    rw [hwk]
    simpa [mul_comm] using Complex.sin_int_mul_pi k
  convert digamma_reflection hwz using 1
  ring

/-- **All-order polygamma reflection.**  Away from the integers, the reflected order-`n`
polygamma values are exactly the order-`n` derivative of the cotangent carrier:

`ψ⁽ⁿ⁾(z) - (-1)ⁿ ψ⁽ⁿ⁾(1-z) = -π Dⁿ cot(πz)`.

This includes the banked digamma reflection at `n = 0` and the trigamma reflection below at
`n = 1`. -/
theorem polygamma_reflection (n : ℕ) {z : ℂ}
    (hz : ∀ m : ℤ, z ≠ (m : ℂ)) :
    iteratedDeriv n Complex.digamma z -
        (-1 : ℂ) ^ n * iteratedDeriv n Complex.digamma (1 - z) =
      -(Real.pi : ℂ) * iteratedDeriv n
        (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) /
          Complex.sin ((Real.pi : ℂ) * w)) z := by
  have hzn : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hc
    exact hz (-(m : ℤ)) (by push_cast at hc ⊢; exact hc)
  have h1zn : ∀ m : ℕ, 1 - z ≠ -(m : ℂ) := by
    intro m hc
    apply hz ((m : ℤ) + 1)
    push_cast
    linear_combination -hc
  have hdz := GaloisForLFunctions.contDiffAt_digamma_n z hzn n
  have hd1z := GaloisForLFunctions.contDiffAt_digamma_n (1 - z) h1zn n
  have hcomp : ContDiffAt ℂ n (fun w : ℂ => Complex.digamma (1 - w)) z :=
    hd1z.comp z (contDiffAt_const.sub contDiffAt_id)
  have hd := (digamma_reflection_eventuallyEq hz).iteratedDeriv_eq (n := n)
  change iteratedDeriv n
      (Complex.digamma - fun w : ℂ => Complex.digamma (1 - w)) z = _ at hd
  rw [iteratedDeriv_sub hdz hcomp,
    congrFun (iteratedDeriv_comp_const_sub n Complex.digamma 1) z,
    iteratedDeriv_const_mul_field] at hd
  simpa [smul_eq_mul] using hd

/-- **Trigamma reflection.**  Away from the integers, the two reflected trigamma values add to
the exact cosecant-square carrier

`ψ'(z) + ψ'(1-z) = π² / sin(πz)²`.

This is the first differentiated member of `polygamma_reflection`. -/
theorem trigamma_reflection {z : ℂ} (hz : ∀ m : ℤ, z ≠ (m : ℂ)) :
    deriv Complex.digamma z + deriv Complex.digamma (1 - z) =
      (Real.pi : ℂ) ^ (2 : ℕ) / Complex.sin ((Real.pi : ℂ) * z) ^ (2 : ℕ) := by
  have hsin := sin_pi_mul_ne_zero_of_not_int hz
  have harg : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  have hcos : HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w))
      (-(Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ) * z)) z := by
    apply ((Complex.hasDerivAt_cos ((Real.pi : ℂ) * z)).comp z harg).congr_deriv
    ring
  have hsine : HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
      ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)) z := by
    apply ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z harg).congr_deriv
    ring
  have hcot : HasDerivAt
      (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) /
        Complex.sin ((Real.pi : ℂ) * w))
      (-(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) ^ (2 : ℕ)) z := by
    apply (hcos.div hsine hsin).congr_deriv
    field_simp
    rw [← Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z)]
    ring
  have h := polygamma_reflection 1 hz
  rw [show iteratedDeriv 1 Complex.digamma z = deriv Complex.digamma z by
        simp [iteratedDeriv_succ],
      show iteratedDeriv 1 Complex.digamma (1 - z) = deriv Complex.digamma (1 - z) by
        simp [iteratedDeriv_succ],
      show iteratedDeriv 1
          (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) /
            Complex.sin ((Real.pi : ℂ) * w)) z =
          -(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) ^ (2 : ℕ) by
        simp [iteratedDeriv_succ, hcot.deriv]] at h
  norm_num at h
  convert h using 1
  ring

/-- **Trigamma at the reflection centre.**  The fixed point `z = 1/2` of reflection turns the
two-value identity into the exact special value `ψ'(1/2) = π²/2`. -/
theorem trigamma_one_half :
    deriv Complex.digamma (1 / 2 : ℂ) = (Real.pi : ℂ) ^ (2 : ℕ) / 2 := by
  have h := trigamma_reflection (z := (1 / 2 : ℂ)) (by
    intro m hm
    have hmreal : (1 / 2 : ℝ) = (m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hmpos : (0 : ℤ) < m := by
      exact_mod_cast (show (0 : ℝ) < (m : ℝ) by rw [← hmreal]; norm_num)
    have hmlt : m < (1 : ℤ) := by
      exact_mod_cast (show (m : ℝ) < 1 by rw [← hmreal]; norm_num)
    omega)
  have harg : (Real.pi : ℂ) * (1 / 2 : ℂ) = (Real.pi : ℂ) / 2 := by ring
  rw [harg, Complex.sin_pi_div_two] at h
  norm_num at h ⊢
  linear_combination h / 2

/-- **Trigamma at one.**  Combining the reflection-centre value with the duplication value relation
gives the classical exact value `ψ'(1)=π²/6`. -/
theorem trigamma_one :
    deriv Complex.digamma 1 = (Real.pi : ℂ) ^ (2 : ℕ) / 6 := by
  have h := GaloisForLFunctions.polygamma_one_half_eq_mul_one 0
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  rw [trigamma_one_half] at h
  norm_num at h
  have h' : deriv Complex.digamma 1 = ((Real.pi : ℂ) ^ (2 : ℕ) / 2) / 3 := by
    apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).2
    simpa [mul_comm] using h.symm
  rw [h']
  ring

end RHTower
