# Liouville-weld finite-blind area-clock universality law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target: `GaloisForLFunctions.RHTower.LiouvilleWeldFiniteBlindAreaClockUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`TranscendentalRateObject` proves that the powers of the explicit Liouville constant form an
infinite `ℤ`-independent rate family, that their weld classes remain independent, and that their
Mahler self-similarity selects the unique clock `0`.

`WeldFiniteChargeBlindAreaReadoutUniversalityLaw` independently proves that every finite-valued
charge kills the complete real weld-class line while one canonical oriented-area scalar recovers
that line faithfully.

No corpus theorem applies the finite-blind/area-faithful observer dichotomy to the
transcendence-generated Liouville packet or joins it to the Mahler clock.

## Statement

Map a finitely supported integer polynomial `c` in the Liouville powers to the weld-line class whose
conversion scalar is `∑ n, c n • liouvilleConst ^ n`. Then:

1. its native cohomology class is exactly the corresponding integer sum of Liouville weld classes;
2. every additive observation in every finite abelian group is zero on every packet;
3. canonical oriented-area readout returns the exact Liouville polynomial;
4. the packet map is injective, hence a single real readout distinguishes the full infinite-rank
   transcendental weld packet although all finite observers collapse it;
5. the same packet's Mahler self-similarity has a unique coherent clock and fixes `0`.

## Dependency-closed proof

Expand `weldClassHom.rangeRestrict` and use additivity to identify the packet's native cohomology
class. Apply `weldClassLine_finiteCharge_invisible` for arbitrary finite targets and
`weldClassAreaReadout_rangeRestrict` for exact scalar recovery. If two packets agree, applying area
readout makes their Liouville-polynomial scalars equal; injectivity of finite-support linear
combination follows from `liouvilleRateObject.rate_indep`, so their coefficient packets agree.
Finally apply `liouvilleObject_has_clock` and `liouvilleObject_clock_at_zero`.

No numerical computation, functional equation, prime factorization, or extra analytic premise is
used.

## Novelty audit

Corpus audit: exact theorem search found the two source mechanisms but no theorem composing
Liouville transcendental independence, arbitrary finite-charge blindness, scalar area recovery,
and Mahler clock selection.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

Dependency-flattened exact proof check passed:
`lake env lean /private/tmp/law489_scratch.lean`.

The source module is wired into `GaloisForLFunctions.RHTower`; its direct exact check and final
umbrella audit remain pending because the imported finite-charge/area module has no cached `.olean`
until final module build.
