import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeNormalSubLogSquareClassification
import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqLower

/-!
# Soldering curvature of the marked Hedenmalm prime-normal character

The two centered half-characters form a flat rank-two prime bundle.  Its odd scalar soldering is
the Hedenmalm prime-normal sine symbol, but the odd-soldering kernel is not parallel.  The resulting
second fundamental form has size `log p / 2`; its cofinal squared norm is exactly the prime-log
moment at the log-square wall.

This module is a Route-N frontier theorem, not RH.  It proves that ordinary full-Jordan
sub-log-square descent cannot be imposed on the scalar soldered carrier: grade one already reaches
log-square size on every real spectral fibre.  A multiplicity-faithful covariant construction must
retain the marked rank-two carrier until after taking jets.
-/

open Complex

noncomputable section

namespace RHTower

/-- The positive half-density `p⁻¹ᐟ²`, written with `sqrt` for exact norm bookkeeping. -/
def hedenmalmPrimeHalfDensity (p : ℕ) : ℝ := (Real.sqrt (p : ℝ))⁻¹

/-- The two centered orientations of the normalized prime character. -/
def hedenmalmMarkedPrimeHalfCharacter (p : ℕ) (z : ℂ) : ℂ × ℂ :=
  let c : ℂ := (hedenmalmPrimeHalfDensity p : ℝ)
  let a : ℂ := ((Real.log p / 2 : ℝ) : ℂ)
  (c * Complex.exp (z * (Complex.I * a)),
    c * Complex.exp (z * (-Complex.I * a)))

/-- Infinitesimal generator of the two marked prime orientations. -/
def hedenmalmMarkedPrimeGenerator (p : ℕ) (v : ℂ × ℂ) : ℂ × ℂ :=
  let a : ℂ := ((Real.log p / 2 : ℝ) : ℂ)
  (v.1 * (Complex.I * a), v.2 * (-Complex.I * a))

/-- Covariant derivative value `d - Γₚv` in the marked prime frame. -/
def hedenmalmMarkedPrimeConnection (p : ℕ) (d v : ℂ × ℂ) : ℂ × ℂ :=
  (d.1 - (hedenmalmMarkedPrimeGenerator p v).1,
    d.2 - (hedenmalmMarkedPrimeGenerator p v).2)

/-- Even endpoint soldering. -/
def hedenmalmPrimeEvenSolder (v : ℂ × ℂ) : ℂ := v.1 + v.2

/-- Odd endpoint soldering; on the marked half-character this is the prime-normal sine symbol. -/
def hedenmalmPrimeOddSolder (v : ℂ × ℂ) : ℂ := -Complex.I * (v.1 - v.2)

/-- Generator of the odd-soldering kernel. -/
def hedenmalmPrimeOddSolderKernelVector : ℂ × ℂ := (1, 1)

/-- Euclidean squared energy of a marked two-component value. -/
def hedenmalmMarkedPrimeEnergy (v : ℂ × ℂ) : ℝ := ‖v.1‖ ^ (2 : ℕ) + ‖v.2‖ ^ (2 : ℕ)

theorem hasDerivAt_hedenmalmMarkedPrimeHalfCharacter_fst (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (hedenmalmMarkedPrimeHalfCharacter p w).1)
      (hedenmalmMarkedPrimeGenerator p (hedenmalmMarkedPrimeHalfCharacter p z)).1 z := by
  let c : ℂ := (hedenmalmPrimeHalfDensity p : ℝ)
  let a : ℂ := ((Real.log p / 2 : ℝ) : ℂ)
  have hlin : HasDerivAt (fun w : ℂ => w * (Complex.I * a)) (Complex.I * a) z := by
    simpa using (hasDerivAt_id z).mul_const (Complex.I * a)
  have hmul := hlin.cexp.const_mul c
  simpa only [hedenmalmMarkedPrimeHalfCharacter, hedenmalmMarkedPrimeGenerator,
    c, a, mul_assoc] using hmul

theorem hasDerivAt_hedenmalmMarkedPrimeHalfCharacter_snd (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (hedenmalmMarkedPrimeHalfCharacter p w).2)
      (hedenmalmMarkedPrimeGenerator p (hedenmalmMarkedPrimeHalfCharacter p z)).2 z := by
  let c : ℂ := (hedenmalmPrimeHalfDensity p : ℝ)
  let a : ℂ := ((Real.log p / 2 : ℝ) : ℂ)
  have hlin : HasDerivAt (fun w : ℂ => w * (-Complex.I * a)) (-Complex.I * a) z := by
    simpa using (hasDerivAt_id z).mul_const (-Complex.I * a)
  have hmul := hlin.cexp.const_mul c
  simpa only [hedenmalmMarkedPrimeHalfCharacter, hedenmalmMarkedPrimeGenerator,
    c, a, mul_assoc] using hmul

/-- The marked prime character is parallel for its canonical diagonal connection. -/
theorem hedenmalmMarkedPrimeConnection_character_eq_zero (p : ℕ) (z : ℂ) :
    hedenmalmMarkedPrimeConnection p
      (hedenmalmMarkedPrimeGenerator p (hedenmalmMarkedPrimeHalfCharacter p z))
      (hedenmalmMarkedPrimeHalfCharacter p z) = 0 := by
  ext <;> simp [hedenmalmMarkedPrimeConnection]

/-- Odd derivative is the even channel times the curvature `log p / 2`. -/
theorem hedenmalmPrimeOddSolder_generator (p : ℕ) (v : ℂ × ℂ) :
    hedenmalmPrimeOddSolder (hedenmalmMarkedPrimeGenerator p v) =
      ((Real.log p / 2 : ℝ) : ℂ) * hedenmalmPrimeEvenSolder v := by
  simp only [hedenmalmPrimeOddSolder, hedenmalmMarkedPrimeGenerator,
    hedenmalmPrimeEvenSolder]
  ring_nf
  simp

/-- Even derivative is minus the odd channel times the curvature `log p / 2`. -/
theorem hedenmalmPrimeEvenSolder_generator (p : ℕ) (v : ℂ × ℂ) :
    hedenmalmPrimeEvenSolder (hedenmalmMarkedPrimeGenerator p v) =
      -((Real.log p / 2 : ℝ) : ℂ) * hedenmalmPrimeOddSolder v := by
  simp only [hedenmalmPrimeOddSolder, hedenmalmMarkedPrimeGenerator,
    hedenmalmPrimeEvenSolder]
  ring_nf

theorem hedenmalmPrimeOddSolder_kernelVector_eq_zero :
    hedenmalmPrimeOddSolder hedenmalmPrimeOddSolderKernelVector = 0 := by
  simp [hedenmalmPrimeOddSolder, hedenmalmPrimeOddSolderKernelVector]

/-- **Connection non-descent.** For every actual prime, the marked generator sends a vector in the
odd-soldering kernel outside that kernel. Hence the flat marked connection does not descend to the
scalar odd quotient. -/
theorem hedenmalmPrimeOddSolder_connectionObstruction (p : Nat.Primes) :
    hedenmalmPrimeOddSolder
      (hedenmalmMarkedPrimeGenerator p.1 hedenmalmPrimeOddSolderKernelVector) ≠ 0 := by
  rw [show hedenmalmPrimeOddSolder
      (hedenmalmMarkedPrimeGenerator p.1 hedenmalmPrimeOddSolderKernelVector) =
        ((Real.log (p.1 : ℕ) : ℝ) : ℂ) by
    simp only [hedenmalmPrimeOddSolder, hedenmalmMarkedPrimeGenerator,
      hedenmalmPrimeOddSolderKernelVector]
    ring_nf
    simp]
  exact_mod_cast (Real.log_pos
    (by exact_mod_cast p.2.one_lt : (1 : ℝ) < (p.1 : ℕ))).ne'

/-- On every real spectral fibre, ordinary first marked jet energy is exactly
`(log p)²/(2p)`. -/
theorem hedenmalmMarkedPrime_firstJetEnergy_eq (p : Nat.Primes) (x : ℝ) :
    hedenmalmMarkedPrimeEnergy
      (hedenmalmMarkedPrimeGenerator p
        (hedenmalmMarkedPrimeHalfCharacter p (x : ℂ))) =
      Real.log (p : ℕ) ^ (2 : ℕ) / (2 * (p : ℕ)) := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
  have hlog0 : 0 ≤ Real.log ((p : ℕ) : ℝ) := (Real.log_pos hp1).le
  have hsqrt : Real.sqrt ((p : ℕ) : ℝ) ^ (2 : ℕ) = (p : ℕ) := Real.sq_sqrt hp0.le
  simp only [hedenmalmMarkedPrimeEnergy, hedenmalmMarkedPrimeGenerator,
    hedenmalmMarkedPrimeHalfCharacter, hedenmalmPrimeHalfDensity, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, norm_inv, Complex.norm_exp]
  simp only [neg_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, sub_self]
  norm_num
  rw [abs_of_nonneg hlog0, abs_of_nonneg (Real.sqrt_nonneg _)]
  field_simp
  nlinarith

/-- **Cofinal log-square curvature wall.** The ordinary first marked jet already has a uniform
log-square lower bound on every real spectral fibre. -/
theorem sum_hedenmalmMarkedPrime_firstJetEnergy_ge (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    Real.log N ^ (2 : ℕ) / 4 - (39 / 2 : ℝ) * Real.log N - 25 / 2 ≤
      ∑ p ∈ Nat.primesLE N,
        hedenmalmMarkedPrimeEnergy
          (hedenmalmMarkedPrimeGenerator p
            (hedenmalmMarkedPrimeHalfCharacter p (x : ℂ))) := by
  have hmain := Sieve.sum_prime_log_sq_div_ge N hN
  have hsum : (∑ p ∈ Nat.primesLE N,
      hedenmalmMarkedPrimeEnergy
        (hedenmalmMarkedPrimeGenerator p
          (hedenmalmMarkedPrimeHalfCharacter p (x : ℂ)))) =
      (1 / 2 : ℝ) *
        ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) ^ (2 : ℕ) / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [show hedenmalmMarkedPrimeEnergy
        (hedenmalmMarkedPrimeGenerator p
          (hedenmalmMarkedPrimeHalfCharacter p (x : ℂ))) =
          Real.log (p : ℕ) ^ (2 : ℕ) / (2 * (p : ℕ)) from
      hedenmalmMarkedPrime_firstJetEnergy_eq
        (⟨p, Nat.prime_of_mem_primesLE hp⟩ : Nat.Primes) x]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    field_simp
  rw [hsum]
  linarith

/-- The even/odd endpoint transform is a scaled unitary change of marked coordinates. -/
theorem hedenmalmPrime_evenOdd_energy_eq (v : ℂ × ℂ) :
    ‖hedenmalmPrimeEvenSolder v‖ ^ (2 : ℕ) + ‖hedenmalmPrimeOddSolder v‖ ^ (2 : ℕ) =
      2 * hedenmalmMarkedPrimeEnergy v := by
  simp only [hedenmalmPrimeEvenSolder, hedenmalmPrimeOddSolder,
    hedenmalmMarkedPrimeEnergy, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_I, one_mul, Complex.normSq_add, Complex.normSq_sub]
  ring

/-- **Radial-only marked energy.** The full marked endpoint doublet has no vertical-clock phase:
its pointwise energy depends only on `Im z`. -/
theorem hedenmalmMarkedPrime_energy_eq_cosh (p : Nat.Primes) (z : ℂ) :
    hedenmalmMarkedPrimeEnergy (hedenmalmMarkedPrimeHalfCharacter p.1 z) =
      2 / (p.1 : ℕ) * Real.cosh (z.im * Real.log (p.1 : ℕ)) := by
  have hp0 : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.pos
  have hsqrt : Real.sqrt ((p.1 : ℕ) : ℝ) ^ (2 : ℕ) = (p.1 : ℕ) := Real.sq_sqrt hp0.le
  have hshape :
      hedenmalmMarkedPrimeEnergy (hedenmalmMarkedPrimeHalfCharacter p.1 z) =
        (Real.sqrt ((p.1 : ℕ) : ℝ))⁻¹ ^ (2 : ℕ) *
            Real.exp (-(z.im * Real.log (p.1 : ℕ))) +
          (Real.sqrt ((p.1 : ℕ) : ℝ))⁻¹ ^ (2 : ℕ) *
            Real.exp (z.im * Real.log (p.1 : ℕ)) := by
    simp only [hedenmalmMarkedPrimeEnergy, hedenmalmMarkedPrimeHalfCharacter,
      hedenmalmPrimeHalfDensity, norm_mul, Complex.norm_real, norm_inv,
      Complex.norm_exp, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
      zero_mul, one_mul, zero_sub, neg_re, neg_im, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    congr 1 <;> ring_nf
    · rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
    · rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
  rw [hshape]
  have hc : (Real.sqrt ((p.1 : ℕ) : ℝ))⁻¹ ^ (2 : ℕ) = 1 / (p.1 : ℕ) := by
    rw [inv_pow, hsqrt]
    simp [div_eq_mul_inv]
  rw [hc]
  rw [Real.cosh_eq]
  ring

/-- Source-normal even/odd endpoint energy in its exact radial form. -/
theorem hedenmalmPrime_evenOdd_character_energy_eq_cosh (p : Nat.Primes) (z : ℂ) :
    ‖hedenmalmPrimeEvenSolder (hedenmalmMarkedPrimeHalfCharacter p.1 z)‖ ^ (2 : ℕ) +
        ‖hedenmalmPrimeOddSolder (hedenmalmMarkedPrimeHalfCharacter p.1 z)‖ ^ (2 : ℕ) =
      4 / (p.1 : ℕ) * Real.cosh (z.im * Real.log (p.1 : ℕ)) := by
  rw [hedenmalmPrime_evenOdd_energy_eq, hedenmalmMarkedPrime_energy_eq_cosh]
  ring

end RHTower
