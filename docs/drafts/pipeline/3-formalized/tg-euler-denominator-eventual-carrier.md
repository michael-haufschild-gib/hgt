# TG C9.11i — eventual Euler carrier and moving-domain admission

- **Stage:** 3-formalized
- **Type:** PROVED eventual rigidity and nonzero finite-family survivor
- **Route:** TG, actual cofinal source admission after denominator clearing.

## Hard target

C9.11h proves the exact finite gap law and that the common carrier over **all**
finite prime sets is zero, with nonzero simultaneous carriers at every finite
stage. Strengthen this to genuine eventual admission, without assuming that the
original vector has a positive Fourier gap or belongs to the initial Sonin space:

For b>0 and every even L² vector f,

`(∃ S₀, ∀ S ⊇ S₀, A_S f ∈ K_b) iff f=0`.

This closes the possible escape of discarding finitely many initial stages. It
does not rule out stage-dependent vectors, graded carriers, or a relative class.

## Corpus evidence and paper proof

- `CCMEulerDenominatorCarrier`: exact gap propagation for the actual physical
  factors, full finite carrier classification, all-stage common-core rigidity,
  nonzero survivor at each finite stage. Its leaf audit has passed.
- `HardyTitchmarshEulerConcrete.evenPrimeLocalFactor_isUnit`: each actual factor
  is boundedly invertible. Finite products therefore remain injective; no uniform
  inverse bound is needed.
- `CCMFiniteEulerDenominator`: literal Mellin polynomial representation of A_S,
  giving the insertion identity `A_(insert v S)=A_v A_S` when v∉S by scalar
  product insertion and Mellin injectivity.
- `SoninEvenCarrier.evenCentralSoninDilationCorner_not_isCompactOperator`:
  supplies actual nonzero vectors in every positive-aperture even Sonin carrier.

Given S₀ from eventual admission, put g=A_S₀ f. Then g∈K_b. For every prime
outside S₀, insertion gives A_p g∈K_b. C9.11h's one-factor sharp law forces the
Fourier gap of g to include p*b for every such prime. Genuine primes outside a
finite set are unbounded, so cutoff exhaustion gives g=0. Finite-product
injectivity gives f=0. The converse is immediate.

The positive survivor must also be retained: **every finite collection of stage
conditions has a nonzero simultaneous solution**, obtained from a Sonin carrier
whose aperture exceeds b and every P_S*b in the collection. Thus the obstruction
is specifically the infinite cofinal intersection, not any finite stage.

## Next geometric question forced by this obstruction

The exact finite survivor has physical gap b and Fourier gap P_S*b. Dilation by
1/sqrt(P_S) should identify it with K_(sqrt(P_S)*b). That unitary identification
is not yet formalized. A viable TG cofinal construction must carry these moving
domains and the resulting aperture transitions through its four-leg relative
class. It must then prove matrix-complete cubic Hardy-index compatibility and
the strict sub-unit law. None of those conclusions follows from common-core
rigidity.

## Log

- 2026-10-02: deep corpus search for finite Euler insertion, injectivity and
  cofinal Sonin carriers was partial and returned no applicable cofinal carrier
  theorem. Direct source inspection verifies the actual one-factor unit theorem
  and the full finite Mellin representation; no literature-based assumption used.
- C9.11i has a dependency-closed paper argument above, pending exact Lean API
  checks and formalization. C9.11h already removes the empty-stage variant; do
  not count another proof of that weaker variant as new frontier progress.

## Verified outcome — 2026-10-02

`CCMEulerEventualCarrier` proves actual prime insertion, finite Euler
invertibility, the exact eventual-admission iff-zero theorem without any initial
gap or carrier premise, and the nonzero finite-family survivor. All four public
theorems pass the foreground final leaf audit with `lake --old env lean ... -o ...`;
all four axiom queries return only `propext`, `Classical.choice`, `Quot.sound`.
The leaf is umbrella-wired, with default heartbeats and no full build.

The proof uses g=A_S₀f, primes outside S₀, and the previously proved sharp gap
law. It does not assume a uniform Euler inverse or a convergence topology.
For the finite-family survivor, choose c greater than b and all P_S*b in the
family, then take a nonzero actual vector in K_c.

Next conjecture `tg-euler-moving-carrier-radical`: the canonical nonzero
simultaneous carrier may annihilate J_S itself, and its Euler image may annihilate
δ_S. If true, this repair discards the relative current before any cubic character
is formed. The exact source kernel and its complementary boundary must be retained.
Moving-domain relative admission, the Hardy-index comparison and sub-unit law
remain unproved; this result neither proves nor falsifies RH.
