# Deninger Big-Witt cross-pair strict descent and singular one-leg trace

- **ID:** `deninger-big-witt-cross-pair-strict-gamma-bv-singular-trace`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION + EXACT COMPARISON + SHARP NO-GO
- **Route:** L
- **RH used:** no
- **Xi-zero location used:** no
- **Added axiom used:** no
- **Computation used:** no
- **Parents:** `deninger-big-witt-frobenius-cross-pair-coherent-compensator.md`, `DeningerBigWittFrobeniusStrictGreenBoundaryDescent.lean`

## New frontier statement

Write the four-label Frobenius coefficient as

```text
C_(p,q;r,t) = ghost_1(F_2 Cross(L_pq,R_rt))
            = -2 L_pq R_rt,
L_pq = (a_p-a_q)/(pq),
R_rt = conjugate(a_r-a_t).
```

For every fixed left edge `(p,q)`, every coefficient `C_(p,q;r,t)` has two
literal realizations:

1. its scalar multiple of the actual ordered `(p,q)` Calderón--Witt Gamma
   witness;
2. an ordinary-integer degree-`pq` Hochschild Green chain with weight
   `-2(a_p-a_q)R_rt`.

The normalized incidence coordinate and BV ground boundary readout are both
exactly `C_(p,q;r,t)`. Actual Gamma reflection-boundary and co-Poisson
transport preserve this coefficient and multiply it by their genuine modular
exterior.

The complete finite right-edge fiber vanishes sourcewise:

```text
sum_(r,t in S^2) C_(p,q;r,t) = 0,
sum_(r,t in S^2) GammaSource_(p,q;r,t) = 0,
sum_(r,t in S^2) BVChain_(p,q;r,t) = 0.
```

Its diagonal is exactly the physical pair source. Therefore its off-diagonal
complement is exactly the negative physical source in both actual carriers.
The existing BV ground reader sees the same sign:

```text
ground(offDiagonal_(p,q)) = - physicalCoefficient_(p,q).
```

Hence invisibility under that reader is equivalent to physical vanishing; it
cannot be obtained formally from the coherent decomposition alone.

## Singular one-leg transport

Let `I` be the actual ordered cross-prime packet index and `H = ell^2(I,C)`
the existing Calderón packet Hilbert space. Finite packets admit a faithful
linear inclusion

```text
j : C^(I)_fin -> H
```

and an algebraic one-leg trace

```text
Sigma(c) = sum_i c_i.
```

For the finite right-leg packet `R_S`, Lean proves the non-tautological
factorization

```text
FiberCoefficient_(p,q)(S) = (-2 L_pq) Sigma(R_S).
```

Thus coherent cancellation uses exactly `Sigma`, not an unspecified scalar
map. But `Sigma` has no continuous extension to `H`. More sharply, there are
uniform averaging packets `u_N` with

```text
norm(j u_N)^2 = 1/(N+1),
Sigma(u_N) = 1.
```

Therefore `j u_N -> 0` while `Sigma(u_N) -> 1`; `Sigma` is sequentially
nonclosable relative to the actual Hilbert admission.

## Exact singular graph and coherent-source exclusion

The graph completion of `(j,Sigma)` is now constructed rather than invoked:

```text
G = ell^2(I,C) direct-sum C,
c |-> (j(c), Sigma(c)).
```

Finite labelled packets are dense in `G`; uniform averages converge to the
nonzero vertical generator `(0,1)`. But this generic saturation is not an
arithmetic source theorem. Every complete coherent right-leg fibre has trace
zero, so continuity of the graph trace gives the strict closure separation

```text
closure { graph(R_S) : coherent finite fibres R_S }
  subset ker(graphTrace),
(0,1) notin closure { graph(R_S) }.
```

Thus arbitrary averaging packets cannot lawfully replace coherent Frobenius
fibres. The minimal source-level survivor is explicit: puncture one selected
ordered edge `i=(r,t)` before coherent summation. Its trace is exactly
`-R_rt`, selected edge plus punctured complement reconstructs the coherent
fibre, and the continuous fixed-left graph readout satisfies

```text
GraphReadout_(p,q)(punctured_(r,t) R_S) = -C_(p,q;r,t).
```

This is a label-faithful selected singular compensator. It does not provide
the still-missing canonical Xi/Green rule selecting `(r,t)` or prove physical
annihilation.

## Prime-harmonic arithmetic source and Gamma boundary

The vertical graph generator now has a canonical Big-Witt source. Fix the
ordered row from prime two to every later prime. Its literal raw coefficients
are `1/(2q)`. Euler divergence sends finite row trace to infinity, while the
existing square-summable all-cross-prime horizon uniformly bounds ambient
`ell^2` norm. Normalizing each finite row by its own trace therefore gives
actual labelled packets with trace one, ambient limit zero, and graph limit
`(0,1)`.

Multiplying these packets by any completed-Xi provenance coefficient gives
the corresponding vertical fibre. On every retained coordinate, undoing the
finite normalization recovers exactly the existing raw all-cross-prime Xi
incidence comparison. For completed Green provenance this constructs the
source Green vertical vector without a generic Hilbert averaging substitute.

The actual normalized Gamma defect is a continuous readout on this vertical
sector. For reflected-Gaussian provenance its value vanishes exactly when
`Re(s)=1/2`; proof compares with actual all-cross-prime Gamma admission at the
literal nonzero `(2,3)` raw coefficient. This identifies exact physical
boundary carried by the constructed source. It does not prove that boundary
vanishes at completed-Xi zeros.

## Proof architecture

1. Use the arbitrary-ring Frobenius ghost-shift theorem and the universal
   Teichmüller cross-effect identity to obtain `C=-2LR`.
2. Use normalized independence of actual Calderón Gamma witnesses to recover
   `C` at the left-edge coordinate.
3. Insert reciprocal ordinary degree `1/(pq)` through the existing BV Green
   boundary; the chosen chain weight reconstructs `C` exactly.
4. Factor every fixed-left finite fiber by the antisymmetric right-leg sum.
5. Construct algebraic finite-packet admission and coordinate summation.
6. On normalized finite indicators, compute Hilbert norm one and trace
   `sqrt(card)`, excluding every bounded extension.
7. On uniform averages, prove Hilbert norm tends to zero while trace is one,
   excluding sequential closability.
8. Prove trivial joint annihilator of ambient admission and trace, hence full
   graph saturation.
9. Use continuity of graph trace to separate closure of coherent right-leg
   fibres from vertical singular generator.
10. Puncture one selected edge and prove exact reconstruction and negative
    four-label Frobenius readout.
11. Normalize the literal prime-two Big-Witt row by its divergent finite
    trace; use uniform horizon norm control to obtain the vertical graph
    generator from arithmetic packets.
12. Weight by completed Xi Green provenance and recover raw incidence on each
    retained coordinate after undoing finite normalization.
13. Pair graph trace with actual normalized Gamma defect and compare through
    the nonzero `(2,3)` coefficient, proving reflected-Gaussian readout
    vanishes exactly on the critical line.

## Anti-theatre audit

This does **not** prove RH and does **not** call a scalar zero a new boundary.
The first leaf explicitly records that current one-edge Calderón transport
forgets the right label. The second leaf then identifies the exact functional
needed to restore the right-leg contraction and proves that the standard
completed carrier cannot support it continuously or as a closable graph.

Finite antisymmetric cancellation and noncontinuity of the all-ones row on
`ell^2` are classical separately. Literature checked includes Deninger--Mellit
on Witt-vector algebra, Blumberg--Gerhardt--Hill--Lawson on Witt vectors and
twisted Hochschild homology, and Deninger-style dynamical/cohomological zeta
formalism. No located source joins the concrete four-label Big-Witt
coefficient, actual Calderón Gamma witness, ordinary BV Green chain, and the
proved nonclosable one-leg trace. Novelty claim is this exact Route-L
identification and obstruction, not the component lemmas in isolation.

## Exact surviving frontier

Prove an unconditional source Green--Stokes identity that annihilates the
explicit actual-Gamma readout on every completed-Xi zero. Source construction,
Xi/Green coefficient transport, retained-coordinate incidence, and physical
Gamma boundary comparison are now formalized. What remains is not selection,
completion, or target identification: it is the new analytic theorem forcing
the resulting nontrivial boundary scalar to vanish without assuming RH, a
zero-location premise, or vanishing of the four-label coefficient.

## Lean certificates

```text
formal/GaloisForLFunctions/RHTower/
  DeningerBigWittFrobeniusCrossPairStrictGammaBVDescent.lean
  DeningerBigWittFrobeniusCrossPairSingularOneLegTrace.lean
  DeningerBigWittFrobeniusCrossPairSingularOneLegGraphCompletion.lean
  DeningerBigWittCrossPrimeHarmonicSingularGraphSource.lean
```

Capstones:

- `deningerBigWittCrossPairFrobeniusStrictDescent`;
- `deningerBigWittCrossPairFrobeniusAllFiberIncidenceSource_zero`;
- `deningerBigWittCrossPairFrobeniusAllFiberBVGreenChain_zero`;
- `deningerBigWittCrossPairFrobeniusOffDiagonalStrictDescent`;
- `deningerBigWittCrossPairFrobenius_groundReadout_invisibility_iff_physical_zero`;
- `deningerBigWittCrossPairFrobeniusFiberCoefficient_eq_singularOneLegContraction`;
- `deningerBigWittCrossPairAlgebraicOneLegTrace_noContinuousExtension`;
- `deningerBigWittCrossPairAlgebraicOneLegTrace_not_closable`;
- `deningerBigWittCrossPairFiniteOneLegGraph_closure_eq_top`;
- `deningerBigWittCrossPairOneLegGraphSingularVector_not_mem_coherent_closure`;
- `deningerBigWittCrossPairOneLegGraphFiberReadout_selectedPuncturedRightLegPacket`;
- `tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_primeTwoRightEdgeNormalizedPacket`;
- `deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket_coordinate_eq_rawComparison`;
- `tendsto_deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket_graph`;
- `deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout_reflectedGaussian_eq_zero_iff`.

## Verification

- direct `lake env lean` on all four leaves: pass;
- exact leaf-only `lake build` on all four leaves: pass;
- umbrella imports wired; umbrella not built;
- capstone axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden declaration scan: pass;
- no stale Lean process.
