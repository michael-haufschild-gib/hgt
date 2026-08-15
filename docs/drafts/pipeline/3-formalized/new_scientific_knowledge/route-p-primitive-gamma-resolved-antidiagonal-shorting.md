# Route P primitive Gamma-resolved antidiagonal shorting

- **ID:** `route-p-primitive-gamma-resolved-antidiagonal-shorting`
- **Stage:** 3-formalized
- **Label:** `P-G191`
- **Source:** P-G190 double-Green flux, Attack 31 Gamma coorientation no-go, resolved Calderón--Witt boundary
- **Statement:** Off the balanced section and away from the cell diagonal, the kernel of the
  physical two-channel Gamma reporter is exactly the universal antidiagonal. The square root of
  the P-G190 pair flux supplies a canonical nonzero vector in that forced kernel, with positive
  globally summable retained energy and nonzero pre-cooriented orientation signal.

## Conjecture loop

Attack 31 proved that the positive symmetric weight `J_i J_j` cannot short physical Gamma
coorientation. Two candidate pivots were tested.

`C191-A`: use the Big-Witt reciprocal horizon itself as the missing sign. This fails: its
coefficients are positive and symmetric, so Attack 31 applies verbatim.

`C191-B`: retain the two ordered Calderón--Witt channels before their codiagonal. This survives,
but the useful result is stronger than the existence of one alternating vector: physical
coorientation forces the entire shorting sector.

## Exact kernel classification

Write the reflection-odd Gamma exterior as `O_a(i,j)` and its physical coorientation as

```text
E_a(i,j)=(height(j)-height(i)) O_a(i,j).
```

Both factors reverse under cell exchange, hence

```text
E_a(j,i)=E_a(i,j).                                             (1)
```

For a resolved coefficient pair `z=(x,y)`, define the physical reporter

```text
R_(a;i,j)(z)=x E_a(i,j)+y E_a(j,i).                            (2)
```

Lean proves the exact factorization

```text
R_(a;i,j)(z)=E_a(i,j) codiagonal(z).                           (3)
```

If `a != 0` and `i != j`, Gamma height injectivity and the previously proved source detection
law give `E_a(i,j) != 0`. Therefore

```text
ker R_(a;i,j)
 = ker codiagonal
 = range antidiagonal
 = {(x,-x) : x in R}.                                         (4)
```

Thus signed incidence is not free design space. Rank two is minimal and the relative sign is
forced: every physical shorting pair is antidiagonal.

## Canonical flux realization

Let `Q_i` be P-G190's positive summable double-Green flux and set

```text
A_ij = sqrt(Q_i Q_j),
W_ij = (A_ij,-A_ij).                                           (5)
```

Lean proves `A_ij>0`, so `W_ij` is nonzero, and

```text
R_(a;i,j)(W_ij)=0,                                             (6)
energy(W_ij)=A_ij^2+(-A_ij)^2=2 Q_i Q_j>0.                    (7)
```

The energy family over all ordered cell pairs is summable. This reconciles P-G189's square-root
Wold singularity with Attack 31: cancellation occurs in a hidden rank-two amplitude, while its
quadratic energy remains positive and trace-finite.

The shorting does not discard orientation data. Before physical coorientation, antisymmetry of
`O` gives

```text
x O_a(i,j)+(-x) O_a(j,i)=2x O_a(i,j),                          (8)
```

which is nonzero for `W_ij` when `a != 0` and `i != j`. Coorientation converts the same resolved
pair from an orientation detector into an exact hidden current.

## Big-picture principle

The positive-cone obstruction and the resolved-boundary construction are two faces of one
universal law:

```text
antisymmetric geometric carrier * antisymmetric physical orientation
  = symmetric observable;
kernel of symmetric two-channel observation
  = antidiagonal hidden current;
quadratic norm of hidden current
  = positive trace-class energy.
```

This identifies where scalarization loses the needed source sign. The sign must live in the
resolved ordered-channel amplitude before physical codiagonal observation; it cannot be recovered
from any positive scalar pair kernel afterward.

## Hostile novelty audit

The corpus already had the universal algebraic identity
`ker(codiagonal)=range(antidiagonal)` and concrete resolved Calderón--Witt self-cups. It also had
Attack 31's positive cooriented no-go. P-G191's new content is their coefficient-faithful coupling
to the actual Gamma exterior and P-G190 current:

- symmetry and nonvanishing of the physical Gamma pair exterior;
- exact factorization `(3)` and complete kernel classification `(4)`;
- canonical nonzero square-root flux vector `(5)`;
- exact shorting with positive globally summable retained energy `(6)`--`(7)`;
- simultaneous nonvanishing of the pre-cooriented orientation signal `(8)`.

P-G191 does not construct a source map whose residues reproduce every entry of the completed Xi
zero Gram matrix. Calling `(6)` the final Route P shorting theorem would be theatre. P-G192 later
falsifies the naive next step: lifting the quadratic source into this antidiagonal and using its
codiagonal vanishing cannot control matrix trace, because the hidden Wold energy stays strictly
positive. The surviving producer must retain the antidiagonal as an energy-carrying colligation
output rather than quotienting it away.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaResolvedAntidiagonalShorting.lean
```

Capstones:

- `ker_routePPrimitiveGammaCoorientedResolvedReporter_eq_range_antidiagonal`;
- `routePPrimitiveGammaResolvedWoldCurrent_ne_zero`;
- `routePPrimitiveGammaCoorientedResolvedReporter_woldCurrent`;
- `routePPrimitiveGammaResolvedWoldCurrent_energy`;
- `routePPrimitiveGammaResolvedWoldCurrent_uncooriented_ne_zero`;
- `summable_routePPrimitiveGammaResolvedWoldCurrent_energy`.

Verification:

- `/tmp/pg191.lean`: `lake env lean /tmp/pg191.lean` passed cleanly;
- exact leaf build passed; no umbrella build run;
- `/tmp/pg191_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] positive reciprocal-horizon conjecture falsified
- [x] physical coorientation symmetry proved
- [x] reporter factorization proved
- [x] full off-critical shorting kernel classified
- [x] canonical nonzero double-Green flux vector built
- [x] exact shorting and retained-energy identity proved
- [x] global pair-energy summability proved
- [x] pre-cooriented orientation survival proved
- [x] scratch verification
- [x] exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [x] naive antidiagonal lift audited and retired by P-G192 trace-blindness theorem
- [ ] retain antidiagonal energy in matrix-complete pole--Gamma colligation
- [ ] recover and dominate completed two-variable zero Gram matrix before scalarization
- [ ] unconditional RH
