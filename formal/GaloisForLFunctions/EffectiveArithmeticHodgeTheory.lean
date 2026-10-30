import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheHassePrincipleWithHeights
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.IndexCarriersOfFiniteSpectra
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheBezoutTheoremOfTheMultiplicativeGroup
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheRiemannRochTheoremOfTheMultiplicativeGroup
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.ApproximateVanishingIsAlmostDivisibility
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.SmallIntegerAuxiliariesAreDivisible
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheTwistTowerCollapsesOverTheIntegers
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TwinsAreSeenByEveryLargeSection

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
* **Carriers.** Families carrying a finite spectrum read the index of its exponential sums; a
  window of `|S|` steps of a separating element and a box of side `|S|` in two jointly separating
  commuting elements carry it; on `ℚ_{>0}` two primes always do.
* **Bézout.** The Frobenius progressions `2πiℤ/log p` are the points of `𝔾_m(ℚ)`: a nonzero
  Dirichlet polynomial of length `N` vanishing to order `m_p` along them has `∏ p^{m_p} ≤ N`,
  attained by the Euler factors; the zero estimate of arithmetic Stepanov.
* **Riemann–Roch.** The sections of length `N` vanishing to orders `m_p` along the progressions form
  a space of dimension `⌊N/∏p^{m_p}⌋`; multiplication by the Euler factor and the tower quotient
  are inverse isomorphisms between consecutive divisors.
* **Approximate Bézout.** Values at most `ε` on `N²p log p` consecutive points of the progression of
  `p` force every `p`-tower sum to be `√2 ε`-small in `ℓ²`: the roots `e^{−2πi log n/log p}` are
  `4/(Np log p)`-separated by integrality, and the mean square on a stretch sees the diagonal.
* **Integer auxiliaries.** For integer coefficients, smallness below `1/√2` on a long stretch of a
  progression is vanishing on all of it, order by order: the zero estimate for `ℤ[Γ]`.
* **Selectivity in sections.** A bounded twin that fails Weil positivity is seen by every large
  section of a Gevrey schedule; under RH every large section separates `ζ` from its Liouville twin.
* **Parity.** The twist tower of the Liouville character collapses over `ℤ`: its base-change levels
  above the first live on proper prime powers and lie in the square-root class.

See `EffectiveArithmeticHodgeTheory/README.md`.
-/
