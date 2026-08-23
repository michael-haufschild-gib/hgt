import GaloisForLFunctions.RHTower.SymmetricShiftEulerSlopes
import GaloisForLFunctions.RHTower.FiniteEulerGammaReflectionWeld

namespace GaloisForLFunctions.RHTower

open Complex

noncomputable section

/-- The inverse local Euler factor after the `s ↦ s + a` translate. -/
def finiteEulerLocalFactorShiftedAdd (p : Nat.Primes) (a : ℝ) (s : ℂ) : ℂ :=
  1 - (((p : ℝ) ^ (-a) : ℝ) : ℂ) * Complex.exp (-s * Real.log p)

/-- The inverse local Euler factor after the `s ↦ s - a` translate. -/
def finiteEulerLocalFactorShiftedSub (p : Nat.Primes) (a : ℝ) (s : ℂ) : ℂ :=
  1 - (((p : ℝ) ^ a : ℝ) : ℂ) * Complex.exp (-s * Real.log p)

/-- The plus-shifted finite Euler factor uses the `p^{-a}` reciprocal root. -/
theorem finiteEulerLocalFactorShiftedAdd_eq_symmetricShiftRoot (p : Nat.Primes) (a : ℝ) (s : ℂ) :
    finiteEulerLocalFactorShiftedAdd p a s =
      1 - (RHTower.symmetricShiftLocalRoots p a ⟨1, norm_one⟩).1 *
        Complex.exp (-s * Real.log p) := by
  simp [finiteEulerLocalFactorShiftedAdd, RHTower.symmetricShiftLocalRoots]

/-- The minus-shifted finite Euler factor uses the `p^a` reciprocal root. -/
theorem finiteEulerLocalFactorShiftedSub_eq_symmetricShiftRoot (p : Nat.Primes) (a : ℝ) (s : ℂ) :
    finiteEulerLocalFactorShiftedSub p a s =
      1 - (RHTower.symmetricShiftLocalRoots p a ⟨1, norm_one⟩).2 *
        Complex.exp (-s * Real.log p) := by
  simp [finiteEulerLocalFactorShiftedSub, RHTower.symmetricShiftLocalRoots]

/-- Translating the finite Euler factor by `+a` produces its exact `p^{-a}` root. -/
theorem finiteEulerLocalFactor_add_real (p : Nat.Primes) (a : ℝ) (s : ℂ) :
    finiteEulerLocalFactor p (s + (a : ℂ)) = finiteEulerLocalFactorShiftedAdd p a s := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast Nat.zero_lt_of_lt p.property.one_lt
  have hscale : Complex.exp (((-a * Real.log p : ℝ) : ℂ)) = ((p : ℝ) ^ (-a) : ℝ) := by
    rw [← Complex.ofReal_exp, Real.rpow_def_of_pos hp]
    congr 1
    ring_nf
  unfold finiteEulerLocalFactor finiteEulerLocalFactorShiftedAdd
  rw [show -(s + (a : ℂ)) * (Real.log p : ℂ) =
      ((-a * Real.log p : ℝ) : ℂ) + (-s * (Real.log p : ℂ)) by
        push_cast
        ring_nf,
    Complex.exp_add, hscale]

/-- Translating the finite Euler factor by `-a` produces its exact `p^a` root. -/
theorem finiteEulerLocalFactor_sub_real (p : Nat.Primes) (a : ℝ) (s : ℂ) :
    finiteEulerLocalFactor p (s - (a : ℂ)) = finiteEulerLocalFactorShiftedSub p a s := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast Nat.zero_lt_of_lt p.property.one_lt
  have hscale : Complex.exp (((a * Real.log p : ℝ) : ℂ)) = ((p : ℝ) ^ a : ℝ) := by
    rw [← Complex.ofReal_exp, Real.rpow_def_of_pos hp]
    congr 1
    ring_nf
  unfold finiteEulerLocalFactor finiteEulerLocalFactorShiftedSub
  rw [show -(s - (a : ℂ)) * (Real.log p : ℂ) =
      ((a * Real.log p : ℝ) : ℂ) + (-s * (Real.log p : ℂ)) by
        push_cast
        ring_nf,
    Complex.exp_add, hscale]

/-- A finite semilocal Euler product transports factorwise to the two exact shifted root packets. -/
theorem finiteEulerSemilocalProduct_symmetricShift (S : Finset Nat.Primes) (a : ℝ) (s : ℂ) :
    finiteEulerSemilocalProduct S (s + (a : ℂ)) *
        finiteEulerSemilocalProduct S (s - (a : ℂ)) =
      (∏ p ∈ S, finiteEulerLocalFactorShiftedAdd p a s) *
        ∏ p ∈ S, finiteEulerLocalFactorShiftedSub p a s := by
  unfold finiteEulerSemilocalProduct
  simp_rw [finiteEulerLocalFactor_add_real, finiteEulerLocalFactor_sub_real]

end

end GaloisForLFunctions.RHTower
