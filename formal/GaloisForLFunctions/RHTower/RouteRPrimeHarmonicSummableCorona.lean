import GaloisForLFunctions.HTGeometry.ChronometricUnboundedPulseModel
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic
import GaloisForLFunctions.RHTower.RouteRCriticalWallOrientedHarmonicQuantization

/-!
# Prime-harmonic summable corona

Bounded prime tails carry pointwise Hadamard multiplication.  Absolutely summable tails form an
ideal, so the quotient retains first-order completion defects while erasing trace-class changes.
The universal Route-R harmonic carrier is nonzero in this quotient, but its square is zero because
the reciprocal-prime square is summable.

Thus the first-wall completion defect is a literal nonzero nilpotent, not a metaphor.  Every
reduced multiplicative receiver erases it.  Combined with oriented harmonic quantization, every
non-neutral first-wall class is one of the two Roos orientations of this same square-zero carrier.
This is an obstruction theorem: it does not assert a faithful reduced landing.
-/

open GaloisForLFunctions.HTGeometry
open scoped BoundedContinuousFunction

namespace RHTower

noncomputable section

/-- Bounded complex prime tails. -/
abbrev RouteRBoundedTraceSequence := BoundedSeq

/-- Absolutely summable bounded tails form an ideal for pointwise multiplication. -/
def routeRSummableBoundedTailIdeal : Ideal RouteRBoundedTraceSequence where
  carrier := {a | Summable (fun n => ‖a n‖)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    refine Summable.of_norm_bounded (ha.add hb) fun n => ?_
    simpa using norm_add_le (a n) (b n)
  smul_mem' := by
    intro a b hb
    refine Summable.of_norm_bounded (hb.mul_left ‖a‖) fun n => ?_
    simpa [smul_eq_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg ((a • b) n))] using
        mul_le_mul_of_nonneg_right (a.norm_coe_le_norm n) (norm_nonneg (b n))

/-- Bounded prime tails modulo absolutely summable changes. -/
abbrev RouteRSummableHadamardCorona :=
  RouteRBoundedTraceSequence ⧸ routeRSummableBoundedTailIdeal

/-- Class of a bounded prime tail in the summable Hadamard corona. -/
def routeRSummableHadamardClass (a : RouteRBoundedTraceSequence) :
    RouteRSummableHadamardCorona :=
  Ideal.Quotient.mk routeRSummableBoundedTailIdeal a

/-- Enumerated prime-harmonic sequence as a bounded pointwise multiplier. -/
def routeRPrimeHarmonicBoundedTraceSequence : RouteRBoundedTraceSequence :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    routeRPrimeHarmonicTraceSequence continuous_of_discreteTopology 1 (fun n => by
      rw [routeRPrimeHarmonicTraceSequence, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact inv_le_one_of_one_le₀ (by
        exact_mod_cast (nthPrimeEquiv n).2.one_le))

@[simp] theorem routeRPrimeHarmonicBoundedTraceSequence_apply (n : ℕ) :
    routeRPrimeHarmonicBoundedTraceSequence n = routeRPrimeHarmonicTraceSequence n :=
  rfl

/-- Universal first-wall harmonic class survives modulo `ell^(1 : ℕ)`. -/
theorem routeRPrimeHarmonicSummableHadamardClass_ne_zero :
    routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ≠ 0 := by
  intro hzero
  have hmem : routeRPrimeHarmonicBoundedTraceSequence ∈
      routeRSummableBoundedTailIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hnorm : Summable (fun n => ‖routeRPrimeHarmonicTraceSequence n‖) := by
    simpa [routeRSummableBoundedTailIdeal] using hmem
  exact not_summable_routeRPrimeHarmonicTraceSequence
    (summable_norm_iff.mp hnorm)

/-- Square of the universal harmonic representative is absolutely summable. -/
theorem summable_norm_routeRPrimeHarmonicTraceSequence_sq :
    Summable (fun n => ‖routeRPrimeHarmonicTraceSequence n ^ (2 : ℕ)‖) := by
  have hp : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ)⁻¹ ^ (2 : ℕ))) := by
    have h := summable_primeSquareRecip.mul_left (1 / 2 : ℝ)
    simpa [mul_assoc] using h
  have hn : Summable (fun n => (((nthPrimeEquiv n).1 : ℝ)⁻¹ ^ (2 : ℕ))) :=
    nthPrimeEquiv.summable_iff.mpr hp
  refine hn.congr fun n => ?_
  rw [routeRPrimeHarmonicTraceSequence, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

/-- Universal off-line carrier is a literal nonzero square-zero element after quotienting by
absolutely summable tails. -/
theorem routeRPrimeHarmonicSummableHadamardClass_sq_zero :
    routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ^ (2 : ℕ) = 0 := by
  rw [pow_two]
  change Ideal.Quotient.mk routeRSummableBoundedTailIdeal
    (routeRPrimeHarmonicBoundedTraceSequence *
      routeRPrimeHarmonicBoundedTraceSequence) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change Summable (fun n =>
    ‖routeRPrimeHarmonicBoundedTraceSequence n *
      routeRPrimeHarmonicBoundedTraceSequence n‖)
  simpa [pow_two] using summable_norm_routeRPrimeHarmonicTraceSequence_sq

/-- Every reduced multiplicative receiver erases the universal first-wall class. -/
theorem routeRPrimeHarmonicSummableHadamardClass_map_eq_zero
    {S : Type*} [CommRing S] [IsReduced S]
    (phi : RouteRSummableHadamardCorona →+* S) :
    phi (routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence) = 0 := by
  exact ((show IsNilpotent
      (routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence) from
        ⟨2, routeRPrimeHarmonicSummableHadamardClass_sq_zero⟩).map phi).eq_zero

/-- At every non-neutral grade, Route-R first-wall Roos class is one of two orientations of the
same nonzero square-zero summable-corona carrier. -/
theorem routeRPrimeGammaCriticalWall_has_oriented_squareZeroCarrier
    {t : ℝ} (ht : t ≠ 0) :
    (routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) =
        routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence ∨
      routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) =
        -routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence) ∧
    routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ≠ 0 ∧
    routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ^ (2 : ℕ) = 0 := by
  constructor
  · rcases lt_or_gt_of_ne ht with htneg | htpos
    · exact Or.inl (routeRPrimeGammaCriticalWallTailRoosClass_eq_harmonic_of_neg htneg)
    · exact Or.inr (routeRPrimeGammaCriticalWallTailRoosClass_eq_neg_harmonic_of_pos htpos)
  · exact ⟨routeRPrimeHarmonicSummableHadamardClass_ne_zero,
      routeRPrimeHarmonicSummableHadamardClass_sq_zero⟩

end

end RHTower
