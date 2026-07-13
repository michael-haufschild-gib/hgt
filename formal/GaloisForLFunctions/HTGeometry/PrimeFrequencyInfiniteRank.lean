import GaloisForLFunctions.RHTower.ArchimedeanCorank

/-!
# Infinite prime-frequency rank and the differential-transcendence criterion (eq. 6, 30–32)

The finite-phase theorem forces a *finite* rational Bohr-frequency rank on any recurrent object that
is differentially algebraic over the Gamma field.  Its contrapositive is the frequency criterion: an
object whose frequency module has infinite rational rank is differentially transcendental over the
Gamma field.

For the Riemann zeta function the frequency module contains `{log p : p prime}`, whose full `ℚ`-span
has rank equal to the (infinite) cardinality of the primes — already recorded in `ArchimedeanCorank`
as `primeLogFullSpan_rank`.  This file upgrades that to genuine non-finite-generation and states the
resulting criterion (eq. 32), with the finite-phase conclusion supplied as the explicit interface it
is: the theorem whose unconditional proof needs the Bohr-hull / Pontryagin / covering-dimension
infrastructure still under construction.
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

/-- **Frequency criterion (contrapositive of finite-phase, eq. 6 / 32).**  Suppose an object's
differential algebraicity over the Gamma field forces its Bohr-frequency module to be the finitely
generated (finite-rank) module `finitePhase h`.  Since the prime-log frequency module is *not*
finitely generated, no object carrying it as its frequency module — the completed zeta source among
them — can be differentially algebraic over the Gamma field.  This is exactly the shape of the zeta
consequence eq. (32): `Γ` and `ζ` are differentially algebraically independent over `C(s)`. -/
theorem prime_frequency_forces_transcendence {DAoverGammaField : Prop}
    (finitePhase : DAoverGammaField → Module.Finite ℚ primeLogFullSpan) :
    ¬ DAoverGammaField :=
  fun h => primeLogFullSpan_not_finite (finitePhase h)

end

end GaloisForLFunctions
