# Shifted-Hankel square-half-density boundary escape

- **ID:** `shifted-hankel-square-half-density-boundary-escape`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper + Lean 4) / EXACT CROSS-ROUTE CLASSIFIER / NOT RH PROOF
- **Source:** `rh-current-frontier-map.md`; shifted reciprocal Hankel, Route-L half-density,
  Route-U positive-axis boundary, source-horizontal polar properness
- **Statement:** Möbius mass-shift preserves the multiplicity-exact Xi trace term only on the
  square-half-density carrier. Polynomial pullback instead acquires an odd complex cocycle, and
  every preserved witness escapes into the moving positive-axis pole with exact retained charge.

## Goal

Test whether source reflection or Möbius shifting can funnel every negative trace-Hankel witness
into the unconditionally positive centered analytic-tail cone. Replace the failed conjecture by
the exact covariant carrier and identify the source theorem that would have to control it.

## Gates

- [x] 0 → 1 in-progress: source-pure question, hostile failures, exact survivor, literature audit
- [x] dependency-closed paper proof below
- [ ] 1 → 2 fully-proven: external novelty classification and standalone audit
- [x] Lean formalization complete; pipeline remains Stage 1 until external novelty gate closes
- [ ] RH

## Heavy conjecture loop

### C0 — polynomial reversal funnels residual witnesses into the positive cone

**Conjecture.** Translate a negative central Hankel polynomial by

```text
T_y(z)=z/(1+yz)
```

and clear its denominator. For large `y`, all translated atoms are close to the positive real
axis, so the transformed polynomial should enter the centered analytic-tail cone without changing
the sign of its trace value.

**Failure.** If `p` has clearing degree `d` and

```text
P_(y,d)(w)=(1-yw)^d p(w/(1-yw)),
```

then at `w=T_y(z)` one has

```text
w P_(y,d)(w)^2 = z p(z)^2 / (1+yz)^(2d+1).                 (1)
```

The odd complex cocycle rotates the trace summand. Ordinary polynomial reversal is not
sign-covariant. Scalar multiplication does not remove an atom-dependent phase.

### C1 — source unitarity makes the translated witness uniformly harmless

**Conjecture.** Replace polynomial pullback by the norm-covariant half-density action. Global
source unitarity should bound every translated witness and contradict source-horizontal polar
properness.

**Failure.** Critical prime/Weil transport is unbounded on ambient multiplicative `L2`. The orbit
can retain constant Hilbert norm while escaping its graph domain through a boundary pole. This is
the strict-edge/critical-graph-norm wall already isolated in Routes L and T, not a consequence of
ambient unitarity.

### C2 — the two source unipotents are unitary on one divisor fibre

**Conjecture.** Put forward and reciprocal prime transports on one coefficient-faithful source
carrier. Their commutator has divisor eigenvalue `p^(2t)`; unitarity would force `t=0`.

**Failure.** Burnol Cartier zero-transfer is globally isometric but its two fixed heads have
strictly reciprocal norms off line. Tail mass compensates the head mismatch. Source involution
identifies orientation-dependent fibres, not both actions on one fixed fibre. External
Connes--Consani analysis finds the same local obstruction: the local scattering factors are
unimodular on the boundary but are not bounded inner functions in the required half-plane.

### C3 — use the unique trace-covariant carrier

**Pivot and theorem.** For a function `F` of the squared test value define

```text
(S_y F)(w) = F(w/(1-yw))/(1-yw).                           (2)
```

Then, wherever denominators are nonzero,

```text
S_u(S_y F)=S_(y+u)F,                                      (3)
T_y(z) (S_y F)(T_y(z)) = z F(z).                          (4)
```

For `F=p^2`, (4) preserves every Xi-copy trace summand, hence every prime label already encoded in
the source moments and every divisor-multiplicity copy. Formula (2) is the square of the unique
weight-one-half pullback required by the quadratic trace. It is rational, not polynomial.

At the shifted atom `w=T_y(z)`, its boundary coordinate is exact:

```text
1-yw = 1/(1+yz),                                          (5)
w/(1-yw)=z.                                               (6)
```

For the monomial square `F(z)=z^(2d)`, therefore,

```text
(S_y F)(w)=w^(2d)/(1-yw)^(2d+1).                          (7)
```

Every fixed-degree witness has an odd pole at `w=1/y`. Under the rescaling `x=yw`, this pole is
fixed at `x=1`, while every Xi atom approaches it through the exact distance (5). The missing
horizontal information is not lost: it is stored in the complex boundary charge `1+yz`.

## Paper proof

Let `D=1+yz` and `w=z/D`. Then

```text
1-yw = 1-yz/D = (D-yz)/D = 1/D,
w/(1-yw) = (z/D)/(1/D) = z.
```

Substitution in (2) gives

```text
w (S_y F)(w) = (z/D) F(z)/(1/D) = zF(z),
```

proving (4). Applying the same two fractional-linear identities twice gives (3). Substitution into
the denominator-cleared polynomial gives (1), and substituting `F(z)=z^(2d)` gives (7). For Xi
copies, `Re z>0` and `y>=0` imply `D!=0`, so all identities are unconditional on the actual source
spectrum.

## No-go closure

- **Exact killing mechanism:** polynomial transport pays the atom-dependent odd cocycle (1);
  trace-covariant transport removes it only by admitting the boundary pole (7).
- **Strongest positive survivor:** exact square-half-density semigroup and termwise trace
  invariance, with a complete classification of where a negative witness can hide under large
  shift: the fixed rescaled pole `x=1`.
- **New insight:** centered analytic-tail positivity and shifted-Hankel positivity are not separated
  by coefficient estimates in the bulk. They are separated by a boundary-domain question. Route
  U's selected positive-axis admission, Route T's critical graph norm, Route L's strict-edge
  landing, and source-horizontal polar properness are four presentations of control of this same
  square-half-density pole charge.
- **Remaining producer:** prove from the prime--Gamma source, before zero scalarization, that the
  rescaled square-half-density boundary charge is tight/admitted in both reflection orientations.
  Any theorem controlling only polynomial coefficients, ambient `L2`, finite moments, or one
  orientation misses the pole and cannot close RH.
- **Status:** dependency-closed paper theorem and unconditional Lean formalization. RH remains open.

## External boundary

Connes--Consani, *The Scaling Hamiltonian* (arXiv:1910.14368), supplies the external boundary:
critical half-density symmetrization and semilocal trace formulas are classical, while the local
scattering factors fail the bounded-inner condition needed for the naive positivity argument.
Burnol's Sonine/co-Poisson work supplies classical spectral-evaluation context. Neither source
states the Xi shifted-reciprocal square-half-density covariance (1)--(7) or its cross-route boundary
classification. Novelty claim is restricted to that corpus-specific synthesis.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/XiShiftedTraceHalfDensityBoundaryEscape.lean`

Main declarations:

- `mobiusSquareHalfDensityTransport_add`;
- `reciprocalMassShift_mul_squareHalfDensityTransport`;
- `xiShiftedSquareHalfDensityTraceTerm_eq_zeroShift`;
- `xiShiftedSquareHalfDensityTraceHankel_eq_zeroShift`;
- `xiShifted_denominatorClearedPolynomialTrace_eq_oddCocycle`;
- `mobiusSquareHalfDensityTransport_evenMonomial`.

Targeted verification:

```text
lake env lean GaloisForLFunctions/RHTower/XiShiftedTraceHalfDensityBoundaryEscape.lean
lake build GaloisForLFunctions.RHTower.XiShiftedTraceHalfDensityBoundaryEscape
```

Both passed. `#print axioms` for the five capstones reports only `propext`, `Classical.choice`, and
`Quot.sound`. No umbrella build was run. RHTower import is wired.

## Log

- 2026-08-11 — C0, C1, C2 falsified against exact corpus theorems; C3 paper-proved; boundary-pole
  survivor frozen for Lean formalization.
- 2026-08-11 — C3 formalized unconditionally; leaf check, target build, axiom audit, and umbrella
  wiring completed without an umbrella build.
