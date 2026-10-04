# BAG full weighted rational cubic and critical tested boundary

- **ID:** BAG-C28.56ac.
- **Stage:** 3-formalized; production and public-theorem axiom audits passed.
- **Route:** BAG actual rational source to the complete arithmetic boundary.
- **Namespace:** RHTower.BAGTrace.
- **Leaves:** ChiRamanujanWeightedRationalTrace; ChiRamanujanRationalCriticalBoundary.

## Exact statements

Let Gamma_sigma(a,b) be the ACTUAL rationalCubic from C28.56ab, with literal
mu(den)/RamanujanDenominator coefficients and weights a^(-sigma)b^(-sigma).
For every sigma>1 and imaginary alpha,beta the complete unordered sum

    sum_(a,b positive rational) Gamma_sigma(a,b)*a^(-alpha)*b^(-beta)

equals the full six-zeta expression from C28.56y. Its exact absolute mass is
the balanced mass zeta(sigma)^2*product_p(1+4p^(-sigma)), independent of the
imaginary frequencies. Both rational axes have the exact two-zeta transforms.
Literal removal of a=1 and b=1 therefore gives Z-D(beta)-D(alpha)+1.

For EVERY integrable complex frequency test Phi and epsilon>0, the series
of actual termwise integrals

    sum_(a!=1,b!=1) integral_(u,v)
      Gamma_(1+epsilon)(a,b)*a^(-iu)*b^(-iv)*Phi(u,v)

is an unconditional HasSum, with value integral(cubicConnectedKernel Phi epsilon).
No interchange or summability premise is assumed. For EVERY fixed smooth
compact Phi, as epsilon tends to zero from the right, this full tested
rational series tends to cubicCriticalBoundaryValue Phi R: both symmetric
finite parts, the negative pi^2 intersection mass, negative twice the mixed
product-PV action, and the ordinary test integral.

## Dependency-closed proof and source identification

Positivity of the rational base removes complex-power branch ambiguity.
The explicit prime-valuation equivalence identifies a rational character
with its finite prime-character product. Each weighted local factor is
exactly the balanced factor times the two characters. Their norms are one,
so the full norm sum is the already-proved balanced absolute mass.

On each finite prime set the support cutoff HasSum is the existing
weightedTrace. Actual absolute convergence and Tannery identify its full
sum with the six-zeta cutoff limit. The same argument applies to the square
energy axis: its actual summable majorant is the balanced energy. It yields
the full two-zeta transform. These arguments keep every prime, valuation
sector and imaginary frequency. Literal inclusion-exclusion removes both
rational axes and restores their common origin once.

Uniqueness of the existing finite-prime limits identifies this exact rational
sum with cubicConnectedKernel. Each individual frequency character is
continuous. For an integrable test, the bound

    norm(Gamma_off(a,b)*characters*Phi(u,v))
       = abs(Gamma_off(a,b))*norm(Phi(u,v))

is summable in (a,b), and its sum is integrable in (u,v). Series dominated
convergence proves the actual HasSum of integrals. The compact-test boundary
from C28.56aa then applies to this sum, with no additional arithmetic premise.

## Audits

Production35695 (WeightedRationalTrace) and production85951
(RationalCriticalBoundary) exited0 without diagnostics, each using
lake --old env lean on the leaf with explicit olean output. Both leaves wired
into RHTower. Axiom61723 exited0: all27 public theorems depend only on propext,
Classical.choice and Quot.sound. Index93281 exited0; all27 public names occur
in LEAN_API. Lint51208 exited1 with exactly15 unrelated unreachable modules,
no new-leaf/proof-debt/freshness error. No full/umbrella build.

## Frontier assessment

This closes frequency-weighted rational/tested identification, including
termwise rational-series integration for each positive damping. It does not
identify a rational arithmetic axis with a physical prime contraction,
prove convergence of the finite-prime integral net, supply a noncompact
critical-test theorem, or justify growing profiles and coupled limits.

Actual global source control is now closed in C28.56ad for EVERY joint
derivative, uniformly through damping one. Next mathematical conjecture:
complete Schwartz boundary and uniform test-seminorm control, retaining all
reflected finite parts and moving intersection source
(P1 bag-global-cubic-source-growth, C28.56ae).
Physical near-resonances, growing moments, moving cofactors and positive
common-height self-return remain open. RH remains unproved.
