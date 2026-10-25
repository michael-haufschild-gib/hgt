# Full Wiener annihilation in the actual cofactor module

- **ID:** biarithmetic-full-wiener-annihilation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), A1–A2.
- **Statement:** For every subcritical damping, either the actual receiver is admitted, or its complex paid ideal annihilates every completed actual common cofactor-limit module. Every such module has nonempty Bohr hull contained in the source obstruction hull.

## Dependency-closed proof

Let `v=A_epsilon` be the actual centered divisor prefix, with `v(0)=0`, and let
`E_T=||v||_T^2`. The corpus proves that either the receiver is admitted or `E_T` tends to
infinity. Its exact pronic dilation bound is `||v(floor(./j))||_T<=sqrt(E_T/j)`.
Take any actual common cofinal subsequence along which every normalized signed covariance converges:

`K_T(j,k)=<v(floor(./j)),v(floor(./k))>_T/E_T -> K(j,k)`.

The packet inequalities give a complex Hilbert realization with total vectors `delta_j`,
unit vector `delta_1`, and commuting operators `V_p delta_j=delta_(pj)` satisfying
`||V_p||<=1/sqrt(p)`. The absolute coefficient series
`pi(a)=sum_j a(j)V_j` therefore defines a contractive unital representation of the critical
Wiener algebra. These are actual source constructions, already supplied by ADR and AOT.

Fix a real critical Wiener kernel `g` whose convolution with the actual source is paid.
The exact convolution identity and the critical-kernel mean correction show that
`P_g(n)=sum_(j<=n)g(j)v(floor(n/j))` has pronic norm bounded by a constant `C_g`, uniformly
in the horizon. This estimate concerns the full kernel; it makes no claim about payment of
its truncations.

For every fixed `k`, Cauchy–Schwarz now gives

`|<P_g,v(floor(./k))>_T/E_T| <= C_g/(sqrt(k)*sqrt(E_T)) -> 0`.

At each horizon this pairing is exactly `sum_j g(j)K_T(j,k)`: all terms with `j>T` vanish
because `v(0)=0`. The uniform majorant is

`|g(j)K_T(j,k)| <= |g(j)|/(sqrt(j)*sqrt(k))`.

It is summable by critical Wiener membership. Dominated convergence along the common
subsequence proves `sum_j g(j)K(j,k)=0` for every `k`.

For a complex kernel `a` in the paid ideal, its real and imaginary components both satisfy
this argument by the definition of that ideal. The norm-convergent operator series then gives
`<delta_k,pi(a)delta_1>=sum_j a(j)K(j,k)=0` for every `k`. Totality forces
`pi(a)delta_1=0`. Commutativity gives `pi(a)delta_j=V_j pi(a)delta_1=0`, and continuity plus
totality gives `pi(a)=0`. Thus `paidIdeal <= ker(pi)`.

The annihilator is closed and proper: continuity gives closedness, and its unit acts on the
nonzero receiver vector. The commutative Banach-algebra character theorem supplies a maximal
ideal containing it, hence a point of its Bohr hull. Ideal inclusion reverses hull inclusion,
so every such module character lies in the source obstruction hull.

The argument applies to every `ActualCofactorLimit epsilon`, whose kernel is the limit of
an actual common Gram subsequence. The chosen limit is constructed by the corpus, so the
class is nonempty without an extra source premise. The programme states the universal
alternative explicitly: either admission holds, or the inclusion and nonempty subhull hold
for every actual realization.

## Inputs and scope

- ADR `RepairingKernelsVanishOnEscape`: full repairing-action bound and normalized disappearance.
- ADR `TheCofactorLimitCarriesACyclicDilationAction`: actual positive Gram realization, dilation,
  cyclicity, and contraction.
- AOT `BoundedMultiplicativeSequencesActOnWienerAlgebras`: absolute Wiener integration.
- ADR `TheCofactorLimitIsAWienerModule`: actual representation, annihilator, and nonempty hull.
- ADR `WienerCovariancesFollowTheCommonCofactorLimit`: exact finite and full covariance series.
- ADR `PaidWienerKernelsAnnihilateTheCofactorLimit`: full comparison for every actual realization.
- Mathlib Tannery theorem: a summable single-series majorant permits the covariance limit.

This is the missing full-kernel source/module comparison, not a new cancellation estimate or
a claim that the actual receiver escapes. It does not identify the paid ideal with the module
annihilator, prove spectral synthesis, compute the golden module, or exclude white noise.
The result uses the actual source through its full convolution payment bound; the functional
analysis thereafter is general. The usual ideal/representation machinery is classical.

## Verification

- [x] Dependency-closed paper proof; no assumption that paid truncations are dense.
- [x] Full-kernel source norm bound already formalized and audited in this programme.
- [x] Natural-index covariance extension, finite-horizon series identity, dominated limit.
- [x] Complex Wiener series and totality comparison.
- [x] Actual paid-ideal inclusion and Bohr-hull inclusion.
- [x] Direct leaf check and main-declaration transitive axiom audit.

`BiarithmeticGeometry/FullWienerAnnihilation.lean` now reuses the ADR covariance and
annihilation foundations. Its four public interfaces include
`admits_or_all_actual_annihilators` and `admits_or_all_actual_moduleHulls`, together with
the chosen-module specializations. The interface scratch audit and direct repository
check both passed. All four transitive audits report only `propext`, `Classical.choice`,
and `Quot.sound`. No duplicate local covariance or completion implementation remains.
