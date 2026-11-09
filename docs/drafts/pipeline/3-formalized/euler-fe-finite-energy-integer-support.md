# Finite energy forces integer support and preserves residues

- **ID:** euler-fe-finite-energy-integer-support
- **Stage:** 3-formalized
- **Programme:** Euler–FE transport theory.

## Exact statement

For a countable Beurling system with finite inverse-3/2 moment, a measurable,
polynomially bounded `L²` defect in the actual Riemann theta identity forces every
generalized-integer norm to be a natural number. The pole coefficient is real.
At every height, the defect contributes zero radial residue.
For an ordered integer spectrum beginning at one, the residue is half its first
atomic mass. If that first mass is one and every mass is at least one, every mass
equals one and the spectrum is exactly `λ_n=n+1`.
For a Beurling system this determines the ordinary integer counting measure,
unique generalized integers of every positive integer norm, equality with ζ on
`Re s>1`, and a norm-preserving bijection of prime labels with rational primes.

## Proof

Write `J_g=ℒψ_g` for the proved half-line Laplace representation. Cauchy–Schwarz
against `exp(-εu)` gives

    |εJ_g(ε+iy)| ≤ ‖ψ_g‖₂ √(2ε)/2 → 0,

uniformly in `y`. The actual partial-fraction/Laplace identity on the positive real
axis has real atomic and dual terms. Its imaginary part, multiplied by `ε`,
therefore gives `Im β/π=0` in the limit. This reduces the theta law to a real pole.

Reality of the same identity gives `Re J_g(ε-iy)=Re J_g(ε+iy)`. The strong `L²`
boundary limit has an almost-everywhere convergent subsequence. Apply it at `y`
and `-y`, using invariance of Lebesgue measure under reflection, to obtain
`Re Bg(-y)=Re Bg(y)` almost everywhere.

The finite-energy tent transport theorem makes `Re Bg=0` almost everywhere on
`(0,1)`. Evenness gives the negative gap too. Thus its pairing with the origin
tent `max(1-|y|,0)` vanishes; the point `y=0` is null and the endpoints carry zero
tent weight. Strong Hardy convergence passes the origin Fejér defect to twice
this zero pairing.

In the actual origin Fejér identity, the atomic Poisson term tends to zero because
the measure is supported on `[1,∞)`. The polar term also tends to zero. The dual
term tends to twice

    ∫ sinc²(πu) dν(u).

Consequently this integral is zero. Its summands over generalized integers are
nonnegative and summable under the inverse-square moment. Each vanishes, forcing
`sin(π‖x‖)=0`. Since every norm is at least one, every norm is a positive integer.

For integer frequencies, the Abel cosine means at zero and one coincide exactly.
The zero-height limit is `β/π`; the limit at the first atom is `a₀/(2π)`, because
the defect contributes no residue. Thus `2β=a₀`. At any atom, positivity and
`cos≤1` give `a_m≤2β`. If `a₀=1` and `a_m≥1`, every mass equals one.

Every positive integer must occur: if `k` were missing, integer spacing would
give a uniform relative separation of `k` from the spectrum, so its atomic Abel
limit would be zero. Integer periodicity identifies this Abel mean with the
zero-height mean, whose limit is `1/(2π)>0`. Strict ordering then gives `λ_n=n+1`.

The Beurling specialization needs no nonempty-label premise. With no prime labels,
only the unit atom remains. Embed it in the integer spectrum with mass one at the
first atom and zero elsewhere. The pole identity gives `2β=1`, whereas its finite
exponential dual has zero radial residue and gives `β=0`, a contradiction.

The inverse-3/2 moment makes every bounded norm fibre finite. Enumerate the
distinct norms increasingly and weight each by its fibre cardinality. Their first
mass is one, since only the empty prime multiset has norm one; every mass is at
least one. Reindexing the absolutely convergent theta series supplies the same
actual theta law. The spectrum theorem gives all positive integers with unit
fibre cardinalities. Hence the norm map identifies generalized integers with
positive integers bijectively. Multiplicativity identifies the indecomposable
generators with rational primes, and reindexing the Dirichlet series gives ζ.

For the original Hamburger strip formulation, the established contour inversion
produces precisely this theta law. The radial-residue argument makes its possibly
complex pole real. The preceding classification then applies without additional
alignment, recurrence or size hypotheses.

The classification also gives an infinite-energy obstruction: a nonclassical
prime system in the same strip class must satisfy `∫⁻ ‖g(t)‖ₑ² = ∞`.
Otherwise measurability and finite square energy give `g∈L²`, contradicting
the norm-preserving rational-prime classification.

## Lean formalization

- `FiniteEnergyDefectsHaveNoBoundaryResidues.lean`: uniform residue bound, zero
  radial residue, real pole coefficient.
- `FiniteEnergyDefectsForceIntegerSupport.lean`: almost-everywhere boundary
  symmetry, origin Fejér limit, zero sinc-squared integral, integer norms.
- `FiniteEnergyDefectsPreserveAtomicResidues.lean`: actual atomic Abel limits,
  integer-support pole identity, unit multiplicities, and full lattice filling.
- `FiniteEnergyFunctionalEquationsDetermineThePrimes.lean`: nonempty prime labels,
  rational-prime classification from the actual theta law, and its original
  Hamburger strip specialization.

All four modules pass direct `lake --old env lean` checks. Terminal declarations
`beurlingSystem_rigidity_of_finiteEnergy_theta_defect`,
`beurlingSystem_rigidity_of_finiteEnergy_defect`, and
`nonclassical_beurling_defect_energy_eq_top` have transitive axiom lists containing
only `propext`, `Classical.choice`, and `Quot.sound`. None proves height replication
for ζ.
