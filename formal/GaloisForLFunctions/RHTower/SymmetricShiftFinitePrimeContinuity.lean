import GaloisForLFunctions.RHTower.SymmetricShiftFiniteEuler

/-!
# Finite-prime continuity of symmetric Euler shifts

Each fixed prime-power discrepancy coefficient tends to zero at collision.  Each fixed local factor
and every finite semilocal product likewise converges to the square of its unshifted value.  These
are the precise coordinatewise and finite-product continuity statements contrasted with the jump
of the global absolute-convergence abscissa.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Raw prime-power logarithmic discrepancy, defined also at the collision point. -/
def symmetricShiftEulerPrimePowerDiscrepancyRaw
    (p : Nat.Primes) (k : ℕ) (a : ℝ) : ℝ :=
  (p.1 : ℝ) ^ (a * (k + 1 : ℝ)) +
    (p.1 : ℝ) ^ (-(a * (k + 1 : ℝ))) - 2

/-- Every fixed prime-power logarithmic coefficient tends to its zero discrepancy at collision. -/
theorem tendsto_symmetricShiftEulerPrimePowerDiscrepancyRaw_zero
    (p : Nat.Primes) (k : ℕ) :
    Tendsto (symmetricShiftEulerPrimePowerDiscrepancyRaw p k) (𝓝 0) (𝓝 0) := by
  have hp : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hcont : Continuous (symmetricShiftEulerPrimePowerDiscrepancyRaw p k) := by
    unfold symmetricShiftEulerPrimePowerDiscrepancyRaw
    exact (((Real.continuous_const_rpow hp.ne').comp
        (continuous_id.mul continuous_const)).add
      ((Real.continuous_const_rpow hp.ne').comp
        (continuous_neg.comp (continuous_id.mul continuous_const)))).sub continuous_const
  have ht : Tendsto (symmetricShiftEulerPrimePowerDiscrepancyRaw p k)
      (𝓝 0) (𝓝 (symmetricShiftEulerPrimePowerDiscrepancyRaw p k 0)) :=
    hcont.continuousAt
  norm_num [symmetricShiftEulerPrimePowerDiscrepancyRaw] at ht
  exact ht

/-- Each fixed plus-shifted inverse Euler factor converges to its unshifted factor. -/
theorem tendsto_finiteEulerLocalFactorShiftedAdd_zero
    (p : Nat.Primes) (s : ℂ) :
    Tendsto (fun a : ℝ => finiteEulerLocalFactorShiftedAdd p a s)
      (𝓝 0) (𝓝 (finiteEulerLocalFactor p s)) := by
  have hp : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hcont : Continuous (fun a : ℝ => finiteEulerLocalFactorShiftedAdd p a s) := by
    unfold finiteEulerLocalFactorShiftedAdd
    exact continuous_const.sub
      (Complex.continuous_ofReal.comp
        ((Real.continuous_const_rpow hp.ne').comp continuous_neg) |>.mul continuous_const)
  have ht : Tendsto (fun a : ℝ => finiteEulerLocalFactorShiftedAdd p a s)
      (𝓝 0) (𝓝 (finiteEulerLocalFactorShiftedAdd p 0 s)) := hcont.continuousAt
  simpa [finiteEulerLocalFactorShiftedAdd, finiteEulerLocalFactor] using ht

/-- Each fixed minus-shifted inverse Euler factor converges to its unshifted factor. -/
theorem tendsto_finiteEulerLocalFactorShiftedSub_zero
    (p : Nat.Primes) (s : ℂ) :
    Tendsto (fun a : ℝ => finiteEulerLocalFactorShiftedSub p a s)
      (𝓝 0) (𝓝 (finiteEulerLocalFactor p s)) := by
  have hp : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hcont : Continuous (fun a : ℝ => finiteEulerLocalFactorShiftedSub p a s) := by
    unfold finiteEulerLocalFactorShiftedSub
    exact continuous_const.sub
      (Complex.continuous_ofReal.comp
        ((Real.continuous_const_rpow hp.ne').comp continuous_id) |>.mul continuous_const)
  have ht : Tendsto (fun a : ℝ => finiteEulerLocalFactorShiftedSub p a s)
      (𝓝 0) (𝓝 (finiteEulerLocalFactorShiftedSub p 0 s)) := hcont.continuousAt
  simpa [finiteEulerLocalFactorShiftedSub, finiteEulerLocalFactor] using ht

/-- A fixed paired local factor converges to the square of its unshifted value. -/
theorem tendsto_finiteEulerLocalFactor_symmetricShift_zero
    (p : Nat.Primes) (s : ℂ) :
    Tendsto
        (fun a : ℝ => finiteEulerLocalFactorShiftedAdd p a s *
          finiteEulerLocalFactorShiftedSub p a s)
      (𝓝 0) (𝓝 (finiteEulerLocalFactor p s ^ 2)) := by
  simpa [pow_two] using
    (tendsto_finiteEulerLocalFactorShiftedAdd_zero p s).mul
      (tendsto_finiteEulerLocalFactorShiftedSub_zero p s)

/-- Every finite semilocal Euler product is continuous through the collision parameter. -/
theorem tendsto_finiteEulerSemilocalProduct_symmetricShift_zero
    (S : Finset Nat.Primes) (s : ℂ) :
    Tendsto
        (fun a : ℝ => finiteEulerSemilocalProduct S (s + (a : ℂ)) *
          finiteEulerSemilocalProduct S (s - (a : ℂ)))
      (𝓝 0) (𝓝 (finiteEulerSemilocalProduct S s ^ 2)) := by
  have hcont : Continuous (fun a : ℝ =>
      finiteEulerSemilocalProduct S (s + (a : ℂ)) *
        finiteEulerSemilocalProduct S (s - (a : ℂ))) := by
    apply Continuous.mul
    · unfold finiteEulerSemilocalProduct
      exact continuous_finsetProd S fun p _ => by
        unfold finiteEulerLocalFactor
        fun_prop
    · unfold finiteEulerSemilocalProduct
      exact continuous_finsetProd S fun p _ => by
        unfold finiteEulerLocalFactor
        fun_prop
  have ht : Tendsto
      (fun a : ℝ => finiteEulerSemilocalProduct S (s + (a : ℂ)) *
        finiteEulerSemilocalProduct S (s - (a : ℂ)))
      (𝓝 0)
      (𝓝 (finiteEulerSemilocalProduct S (s + (0 : ℂ)) *
        finiteEulerSemilocalProduct S (s - (0 : ℂ)))) := hcont.continuousAt
  simpa [pow_two] using ht

end

end GaloisForLFunctions.RHTower
