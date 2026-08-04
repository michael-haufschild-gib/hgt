import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinSchattenWall

/-!
# Determinant transgression of the cofinal Gamma Bockstein

The signed cofinal Gamma Bockstein coefficient is exactly the positive Fisher density times the
difference of the physical degree-one rotation determinants in the two Gamma orientations.
Consequently a common nonzero corrected-determinant Stokes factor cannot change its vanishing
locus.  In particular, determinant-one `det2`/BV correction does not annihilate the Bockstein:
same-fibre determinant comparison is already equivalent to neutral grade.

This is an unconditional obstruction and a design law for the missing source boundary.  A valid
producer must create a genuinely orientation-sensitive source transgression before Xi
specialization; a common unimodular correction is insufficient.
-/

namespace RHTower

noncomputable section

/-- Signed real representative of the reflected-minus-forward cofinal Gamma Bockstein. -/
def primeGammaCofinalBocksteinCoefficient (t : ℝ) (p : Nat.Primes) : ℝ :=
  primeActivationOccupancyFisherTwist (-t) p -
    primeActivationOccupancyFisherTwist t p

/-- Determinant of the physical degree-one swap-scale rotation at prime `p` and grade `t`. -/
def primeGammaPhysicalRotationDeterminant (t : ℝ) (p : Nat.Primes) : ℝ :=
  -((p : ℝ) ^ t)

/-- Determinant of the untwisted cyclic source rotation. -/
def primeGammaSourceRotationDeterminant : ℝ := -1

/-- A common scalar corrected-determinant Stokes factor applied to both Gamma orientations. -/
def primeGammaCommonCorrectedRotationDeterminant
    (c t : ℝ) (p : Nat.Primes) : ℝ :=
  c * primeGammaPhysicalRotationDeterminant t p

/-- **Exact determinant transgression.**  The Bockstein coefficient is Fisher density times the
difference of the forward and reflected physical rotation determinants. -/
theorem primeGammaCofinalBocksteinCoefficient_eq_determinantTransgression
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p =
      primeActivationOccupancyFisherDensity p *
        (primeGammaPhysicalRotationDeterminant t p -
          primeGammaPhysicalRotationDeterminant (-t) p) := by
  simp only [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeGammaPhysicalRotationDeterminant]
  ring

/-- The two physical orientation determinants agree exactly at neutral grade. -/
theorem primeGammaPhysicalRotationDeterminant_eq_reflection_iff
    (t : ℝ) (p : Nat.Primes) :
    primeGammaPhysicalRotationDeterminant t p =
        primeGammaPhysicalRotationDeterminant (-t) p ↔
      t = 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  constructor
  · intro h
    have hpow : (p : ℝ) ^ t = (p : ℝ) ^ (-t) := by
      exact neg_injective h
    have hexp : t = -t :=
      (Real.strictMono_rpow_of_base_gt_one hp1).injective hpow
    linarith
  · rintro rfl
    rw [neg_zero]

/-- Either physical determinant equals the source determinant exactly at neutral grade. -/
theorem primeGammaPhysicalRotationDeterminant_eq_source_iff
    (t : ℝ) (p : Nat.Primes) :
    primeGammaPhysicalRotationDeterminant t p =
        primeGammaSourceRotationDeterminant ↔
      t = 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  constructor
  · intro h
    have hpow : (p : ℝ) ^ t = (p : ℝ) ^ (0 : ℝ) := by
      simpa [primeGammaPhysicalRotationDeterminant,
        primeGammaSourceRotationDeterminant] using h
    exact (Real.strictMono_rpow_of_base_gt_one hp1).injective hpow
  · rintro rfl
    simp [primeGammaPhysicalRotationDeterminant,
      primeGammaSourceRotationDeterminant]

/-- Pointwise Bockstein annihilation is exactly equality of physical orientation determinants. -/
theorem primeGammaCofinalBocksteinCoefficient_eq_zero_iff_determinants
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p = 0 ↔
      primeGammaPhysicalRotationDeterminant t p =
        primeGammaPhysicalRotationDeterminant (-t) p := by
  rw [primeGammaCofinalBocksteinCoefficient_eq_determinantTransgression]
  have hdensity : primeActivationOccupancyFisherDensity p ≠ 0 := by
    have hp0 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    have hden : (0 : ℝ) < ((p.1 : ℝ) + 1) ^ 2 := by positivity
    rw [primeActivationOccupancyFisherDensity_eq]
    exact ne_of_gt (div_pos hp0 hden)
  rw [mul_eq_zero, or_iff_right hdensity, sub_eq_zero]

/-- The signed pointwise Bockstein coefficient vanishes exactly at neutral grade. -/
theorem primeGammaCofinalBocksteinCoefficient_eq_zero_iff
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p = 0 ↔ t = 0 := by
  rw [primeGammaCofinalBocksteinCoefficient_eq_zero_iff_determinants,
    primeGammaPhysicalRotationDeterminant_eq_reflection_iff]

/-- The absolute representative used by the Schatten wall is the magnitude of the determinant
transgression. -/
theorem primeGammaCofinalBocksteinMagnitude_eq_abs_determinantTransgression
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinMagnitude t p =
      |primeActivationOccupancyFisherDensity p *
        (primeGammaPhysicalRotationDeterminant t p -
          primeGammaPhysicalRotationDeterminant (-t) p)| := by
  rw [← primeGammaCofinalBocksteinCoefficient_eq_determinantTransgression]
  rfl

/-- **Common-correction no-go.**  Multiplying both orientations by any one nonzero corrected
determinant factor preserves the exact Bockstein vanishing locus. -/
theorem primeGammaCommonCorrectedRotationDeterminant_eq_reflection_iff
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) (p : Nat.Primes) :
    primeGammaCommonCorrectedRotationDeterminant c t p =
        primeGammaCommonCorrectedRotationDeterminant c (-t) p ↔
      t = 0 := by
  constructor
  · intro h
    apply (primeGammaPhysicalRotationDeterminant_eq_reflection_iff t p).mp
    exact mul_left_cancel₀ hc h
  · rintro rfl
    rw [neg_zero]

/-- Determinant-one `det2`/BV Stokes correction annihilates the determinant transgression iff the
uncorrected Bockstein already vanishes. -/
theorem primeGammaDeterminantOneStokesCorrection_eq_iff_bockstein_eq_zero
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCommonCorrectedRotationDeterminant 1 t p =
        primeGammaCommonCorrectedRotationDeterminant 1 (-t) p ↔
      primeGammaCofinalBocksteinCoefficient t p = 0 := by
  rw [primeGammaCommonCorrectedRotationDeterminant_eq_reflection_iff one_ne_zero,
    primeGammaCofinalBocksteinCoefficient_eq_zero_iff]

/-- Comparing both physical orientations with the fixed cyclic source determinant is exactly
Bockstein annihilation, not an independent consequence of determinant-one correction. -/
theorem primeGammaBothPhysicalDeterminants_eq_source_iff_bockstein_eq_zero
    (t : ℝ) (p : Nat.Primes) :
    (primeGammaPhysicalRotationDeterminant t p =
          primeGammaSourceRotationDeterminant ∧
        primeGammaPhysicalRotationDeterminant (-t) p =
          primeGammaSourceRotationDeterminant) ↔
      primeGammaCofinalBocksteinCoefficient t p = 0 := by
  rw [primeGammaPhysicalRotationDeterminant_eq_source_iff,
    primeGammaPhysicalRotationDeterminant_eq_source_iff,
    primeGammaCofinalBocksteinCoefficient_eq_zero_iff]
  constructor
  · rintro ⟨ht, _⟩
    exact ht
  · rintro rfl
    exact ⟨rfl, neg_zero⟩

end

end RHTower
