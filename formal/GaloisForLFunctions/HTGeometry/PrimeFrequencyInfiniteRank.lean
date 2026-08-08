import GaloisForLFunctions.HTGeometry.ArchimedeanCorank

/-!
# Infinite prime-frequency rank and the differential-transcendence criterion (eq. 6, 30–32)

A Dirichlet series satisfying an algebraic differential equation has a finitely generated exponent
module: all but finitely many of its exponents are integral combinations of the first few.  Its
contrapositive is a differential-transcendence criterion — an object whose frequency module is not
finitely generated satisfies no algebraic differential equation.

For the Riemann zeta function the frequency module contains `{log p : p prime}`, whose full `ℚ`-span
has rank equal to the (infinite) cardinality of the primes — already recorded in `ArchimedeanCorank`
as `primeLogFullSpan_rank`.  This file upgrades that to genuine non-finite-generation over `ℚ`, and
records the modus-tollens step separately from it, as a hypothesis-parametric statement: the
finite-phase implication is an input, not a conclusion of this file.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **The prime-log frequency module has infinite rational rank.**  `span_ℚ {log p : p prime}` is not
finitely generated: its `ℚ`-dimension is the cardinality of the primes. -/
theorem primeLogFullSpan_not_finite : ¬ Module.Finite ℚ primeLogFullSpan := by
  intro h
  have hrank : Module.rank ℚ primeLogFullSpan < Cardinal.aleph0 :=
    Module.rank_lt_aleph0 ℚ _
  rw [primeLogFullSpan_rank] at hrank
  exact absurd hrank (not_lt.mpr (Cardinal.aleph0_le_mk Nat.Primes))

/-- **Modus tollens against non-finite generation.**  For any proposition `P` whose truth would force
the prime-log module to be finitely generated over `ℚ`, `P` is false.  The mathematical content is
entirely in `primeLogFullSpan_not_finite`; the finite-generation implication itself is a hypothesis
of this statement and is proved nowhere in this file. -/
theorem prime_frequency_forces_transcendence {DAoverGammaField : Prop}
    (finitePhase : DAoverGammaField → Module.Finite ℚ primeLogFullSpan) :
    ¬ DAoverGammaField :=
  fun h => primeLogFullSpan_not_finite (finitePhase h)

end

end GaloisForLFunctions
