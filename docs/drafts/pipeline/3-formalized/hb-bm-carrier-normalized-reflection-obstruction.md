# HB carrier-normalized reflected Peierls obstruction

- **ID:** HB-BM-CNRO
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `HB-BM3-PPC` · exact source-scaled BM polarized current and FE reflection law
- **Statement:** `[NEW] [BRIDGE] [LEAN-PROVED]` After exact unit normalization of the everywhere-nonzero self-dual Einstein carrier, the sum of the BM Peierls candidates on a Xi copy and its functional-equation reflection is `-2 * normSq(mixing(q)) * (8*n+5)` at every interior radius; hence its zero locus is exactly the critical line, and universal vanishing is exactly RH.

## Goal

Remove carrier-size asymmetry from functional-equation reflection before the actual augmented
source-incidence weld. Determine whether FE reflection cancels or detects the already-closed
regular/Schwarz-complementary Peierls carrier.

This theorem would not prove physical incidence. It would identify the exact pre-specialization
global law sufficient after incidence: reflection-oddness of the carrier-normalized causal cut.

## Gates

- [x] 0 → 1 in-progress: exact claim frozen from current Lean declarations
- [x] 1 → 2 fully-proven: dependency-closed proof and hostile review
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, lint, and axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and priority audit

## Exact frozen claim

Let `mu(q)` be `d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q`, let `r(q)` be the exact
regular/Schwarz-complementary BM polarized current, and define the unit-carrier candidate

`P0(n,q,z) = 2 * normSq(mu(q)) * r(n,q,z)`.

For every `n`, every Xi multiplicity copy `q`, and every `0 < z < 1`:

1. `mu(reflect q) = mu(q)`;
2. `P0(n,q,z) + P0(n,reflect q,z) = -2 * normSq(mu(q)) * (8*n+5)`;
3. this sum is zero iff `Re(q)=1/2`;
4. vanishing for every `q` at one fixed interior radius is equivalent to RH;
5. there exists a nonzero complex seed amplitude whose self-dual quadratic carrier coefficient is
   exactly one, so `P0` is an exact specialization of the existing literal source-scaled Peierls
   candidate rather than an independent reporter.

## Hostile attacks

- `FALSE` if functional-equation reflection changes the orthogonal mixing coefficient rather than
  preserving it.
- `FALSE` if unit carrier normalization requires a zero divisor or an unavailable square root.
- `FALSE` if carrier normalization changes the Schwarz-paired radial current rather than only the
  common source scale.
- `INCOMPLETE` as an RH route until actual augmented Peierls incidence and a source-global
  reflection-oddness law are derived.

## Novelty status

`[NEW] [BRIDGE]` after internal-corpus and external primary-source search. General symplectic
reflection and conserved-current mechanisms are classical. Birmingham--Mokhtari treat linear exact
topological-black-hole QNMs; covariant Peierls literature treats boundary terms abstractly; modern
QNM-current work treats conserved bilinear projections. No audited source states this unit-carrier
nonlinear Xi/BM reflection obstruction or its exact `8*n+5` law. Priority remains provisional until
publication-grade expert audit.

## Complete paper proof

The angular eigenvalue is `1/4 + xiSpectralPoint(q)^2`. Functional-equation reflection sends the
centered spectral point to its negative, so the eigenvalue, its imaginary part, and therefore the
orthogonal-helicity mixing coefficient `mu` are unchanged.

For nonzero seed amplitude, the exact self-dual carrier never vanishes at an Xi divisor. In
particular its coefficient `c(q)` at unit seed is nonzero. Choose

`A0(q) = sqrt(c(q)^(-1))`.

The principal complex square root satisfies `sqrt(w)^2=w`; hence the quadratic carrier coefficient
at `A0(q)` is `c(q)^(-1)c(q)=1`. This also forces `A0(q) != 0`.

The existing source-scaled Peierls candidate then reduces exactly to

`P0(n,q,z)=2*normSq(mu(q))*r(n,q,z)`.

Corpus reflection transport proves

`r(n,q,z)+r(n,reflect(q),z)=-(8*n+5)`

at every interior radius. Reflection invariance of `mu` gives

`P0(n,q,z)+P0(n,reflect(q),z)=-2*normSq(mu(q))*(8*n+5)`.

The last factor is strictly nonzero for every natural overtone. Therefore the sum vanishes exactly
when `mu(q)=0`, already proved equivalent to `Re(q)=1/2`. Universal vanishing at the fixed interior
radius `z=1/2` is consequently equivalent to RH by the existing exact Xi-copy endpoint.

## Hostile review result

- Reflection preserves `mu` because the full angular polynomial is even, not by an assumed norm
  symmetry.
- Carrier normalization is realized by an explicit nonzero complex seed; no branch continuity is
  asserted or needed.
- The noncancelling factor is strictly positive in real part: `8*n+5` cannot vanish.
- The theorem does not assume physical source incidence, but it also does not prove it.
- **Strongest surviving route statement:** after incidence, only one pre-specialization law is
  needed: carrier-normalized physical causal cuts must be FE-reflection odd. Exact BM transport then
  converts that global law directly into critical-line placement.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSecondHarmonicCarrierNormalizedReflectionObstruction.lean`
- Exact reflected sum:
  `d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add`
- Pointwise selector:
  `d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add_eq_zero_iff`
- Premise-free RH equivalence:
  `forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add_eq_zero_iff_rh`
- Direct `lake env lean` check passed with no diagnostics.
- Targeted `lake build` passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: passed.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`.

- 2026-08-27 — conjecture frozen after corpus search exposed reflection invariance of the angular
  eigenvalue and exact noncancelling BM current sum.
- 2026-08-27 — dependency-closed proof survived all attacks; novelty search found no exact prior
  nonlinear Xi/BM reflection obstruction.
- 2026-08-27 — exact theorem formalized, targeted module built, axioms audited, formal lint passed,
  and umbrella import wired.
