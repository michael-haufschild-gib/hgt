import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheHassePrincipleWithHeights
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex

/-!
# Effective Arithmetic Hodge Theory of the multiplicative group of `ℚ`

Umbrella for the effective chapter of the arithmetic Hodge theory of `ℚ_{>0}`: finite sections of
the Weil kernel and what they carry.

* **Heights.** The height filtration `κ_T` of the index, its Riemann–von Mangoldt bound, Nyquist
  separation and its sharp constant, towers of scale `< π/T` and an explicit tower in `⟨2, 3⟩`
  certifying every right zero of ordinate at most `T`, and the blind primes at height `T`.
* **Schedules.** Weil's form on real tests as a polarized quadratic form, its two-sided continuity
  under synthesis errors, Gram-matrix convergence, and the theorem that the explicit Gevrey and
  Denjoy–Carleman schedules `(log log N)^α/N`, `α > 1`, reach the index `κ(K_ζ)`.

See `EffectiveArithmeticHodgeTheory/README.md`.
-/
