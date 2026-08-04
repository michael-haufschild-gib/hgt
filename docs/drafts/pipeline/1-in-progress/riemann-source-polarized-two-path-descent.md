# Riemann source-polarized two-path descent

- **ID:** `riemann-source-polarized-two-path-descent`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** `[CONJECTURE]` The literal rational-adelic cyclic source admits a divisor-independent,
  source-pointed singular comparison whose two degree-two face-collapse paths specialize
  coefficient-faithfully to the direct and two-step BV--Wold transports on the exact
  `(2,0),(2,1),(2,2)` prime-depth simplex and retain a nonzero ordinary-prime top-conormal line.

## Public sentence

An off-line zero makes two ways of collapsing the same arithmetic triangle disagree; the source
should not be allowed to give two answers to one simplicial face identity.

## Goal

Replace routewise annihilation by source coherence.  Route charts need not kill the horizontal
Green defect separately.  They must be local realizations of one pre-divisor arithmetic object,
and their overlap maps must respect the source's exact face identities.  The already formalized
Route-R curvature then turns coherence itself into a critical-line selector.

## Exact internal frontier

- `[CORPUS]` `primeDepthBVWoldConnection(i,j)=m_i lambda_j-m_j lambda_i` is sign-indefinite,
  is not a vertex coboundary, and has exact witness curvature `-log(2)/8` in
  `formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldCurvedSourceDifferential.lean`.
- `[CORPUS]` For `T_a(i,j)=exp(a theta(i,j))`,

  ```text
  T_a(i0,i1) T_a(i1,i2) = T_a(i0,i2)  iff  a=0,
  ```

  where `i0=(2,0)`, `i1=(2,1)`, and `i2=(2,2)`; see
  `primeDepthBVWoldTransport_witness_flat_iff`.
- `[CORPUS]` At a Xi divisor copy `rho`, `a_rho=2 Re(rho)-1`, so witness flatness is equivalent
  to `Re(rho)=1/2`; see `primeDepthBVWoldXiTransport_witness_flat_iff`.
- `[CORPUS]` The rational-adelic cyclic bar, its face identities, a trace-one ordinary-prime
  degree-one atom, and a pre-divisor ordered physical comparison exist.  The measured physical
  paracyclic defect has residue `(delta_n(rho)-1)c_rho`; see
  `MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`.
- `[CORPUS]` Generic serial/parallel observation calculus is complete:
  `eq_zero_of_sourcePointed_parallelConservativeFactorizations`,
  `completeObservationDescentLaw`, and the relative-admission naturality laws.  These are
  detectors, not arithmetic producers.
- `[LOCAL-RESEARCH]` Route L lacks source-null-homology/singular Green--BV boundary
  compatibility.  Route R lacks the graded variable-ideal singular Cartier comparison to the
  fixed same-fibre conormal.  C1 lacks its singular boundary/intersection pairing.  CCM-FU lacks
  a cofinal noncompact Ward incidence.  Route E lacks a source-predeclared physical relation.
  These are Stage-1 open cores in `rh-current-frontier-map.md`, not completed hypotheses.

## External frontier

- `[LITERATURE]` Connes--Consani organize critical zeros as sheaf cohomology on the Scaling Site
  and separately retain an all-zero prolate/Laplacian realization; they do not construct the
  source-polarized two-path comparison here:
  <https://arxiv.org/abs/2207.10419>.
- `[LITERATURE]` Connes--Consani--Marcolli identify RH with positivity of a trace pairing on an
  adelic class-space cyclic-homology cokernel; the positive intersection pairing remains the
  source-bearing step: <https://arxiv.org/abs/math/0703392>.
- `[LITERATURE]` Hedenmalm constructs a theta differential-operator pair and makes the missing
  inner-product/self-adjointness structure explicit: <https://arxiv.org/abs/2606.17494>.
- `[LITERATURE]` Suzuki's screw-function framework leaves the cofinal self-adjoint limit as a
  conjecture: <https://arxiv.org/abs/2606.09096>.
- `[LITERATURE]` Cellular-sheaf Hodge/Laplacian theory already supplies generic local-to-global
  consistency and harmonic representatives: <https://arxiv.org/abs/1808.01513>.  Therefore
  “put the routes in a sheaf” is `[REDISCOVERED]`; only an exact arithmetic comparison with the
  displayed curvature could change the RH frontier.
- `[NOVELTY UNVERIFIED]` No located primary source gives the exact rational-adelic
  cyclic-face/BV--Wold transport comparison.  This is not a priority claim; MathSciNet/zbMATH
  ancestry and independent expert review remain absent.

## Frozen conjecture: `SOURCE-POLARIZED-TWO-PATH-DESCENT`

Let

```text
i0=(2,0), i1=(2,1), i2=(2,2),
a_rho=2 Re(rho)-1,
T_rho(i,j)=exp(a_rho theta(i,j)).
```

Construct before divisor specialization:

1. a degree-two rational-adelic cyclic source simplex `sigma_2` with an ordinary-prime
   trace-one pointing;
2. a singular, source-graded target `L_src` over the Wold ideal, Gamma determinant, BV first
   trace, and co-Poisson source point;
3. source face comparisons and a top-conormal pointing `v_src` such that `v_src` is non-torsion
   and every construction is independent of Xi divisor data;
4. for every later Xi divisor specialization `rho`, coefficient-faithful identifications under
   which the two source-equal face composites act on `v_rho` as

   ```text
   T_rho(i0,i1) T_rho(i1,i2) v_rho
   and
   T_rho(i0,i2) v_rho,
   ```

   with `v_rho != 0`.

The equality of the composites must be inherited from a literal cyclic/simplicial face identity,
not imposed after inspecting `rho`.  “Singular” means the comparison may use a variable ideal,
locally finite source grade, noncompact cofinal target, or closed relation, but it must preserve
ordinary-prime, depth, multiplicity, and divisor provenance until the displayed specialization.

## Conditional implication, not accepted proof

If the conjectured comparison exists, face naturality gives

```text
(T_rho(i0,i1) T_rho(i1,i2) - T_rho(i0,i2)) v_rho = 0.
```

Non-torsion/non-erasure of `v_rho` gives transport flatness.  The corpus theorem
`primeDepthBVWoldXiTransport_witness_flat_iff` gives `Re(rho)=1/2`.  Quantifying over all divisor
copies yields RH.

This is only a conditional chain.  No claim is `[PAPER-PROVED]` while the source comparison is
unconstructed.

## Conjecture-distance gate

- **Ontological reversal:** horizontal displacement is not a vector each route must annihilate;
  it is the obstruction to gluing route realizations of one arithmetic source simplex.
- **Compression:** one coherence defect simultaneously explains Route L's failed strict boundary,
  Route R's curved prime/depth differential, C1's missing singular pairing, CCM-FU's escaping
  cofinal incidence, and Route E's missing predeclared adjacency.
- **Risky consequence:** any finite regular approximation of the comparison must expose a
  nonzero two-path defect off line with normalized scalar
  `exp(-a_rho log(2)/8)-1`; it cannot converge coefficient-faithfully to a strict comparison in
  a fixed Hilbert, finite-Rees, scalar-distributional, or product-topology category.
- **Not “known theory plus positivity”:** no positivity or self-adjointness premise occurs.  The
  selector is source coherence against an already nonflat arithmetic connection.

## Hostile attack and relentless interrogation

### Killed precursor: route-sheaf Hodge annihilation

`[REDISCOVERED] [CIRCULAR]` Putting route outputs in a cellular sheaf and assuming the defect record
is both exact and coexact merely imports standard Hodge theory; the source-specific coexactness is
the missing RH-bearing statement.  It supplies no arithmetic producer.

**Exact why:** generic Hodge decomposition sees only a chosen complex and inner product.  Existing
regular, positive, and invariant completions erase the reflection-odd coordinate, while choosing
an adjoint that retains it is precisely C1/Route-R same-fibre identification.

**Stronger conjecture from the failure:** use an exact source face identity against the already
computed nonzero Route-R curvature.  Coherence is fixed before a Hilbert structure and predicts a
specific scalar failure, rather than assuming harmonic vanishing.

### Current hostile verdict

`SURVIVES PRELIMINARY ATTACK` as a conjecture, with severe caveats:

- not killed by the finite-Rees, positive-cone, scalar-frequency, product-topology, matroid, or
  ordinary-`L2` no-gos because it explicitly requires a pre-scalar singular graded comparison;
- not established by generic cyclic identities: a coefficient-faithful physical face comparison
  is exactly `[OPEN CORE]`;
- not an RH proof, and existence must not be packaged as an abstract structure whose only
  inhabitant is obtained from `Re(rho)=1/2`;
- likely false if demanded in the ordinary cyclic target: the formalized paracyclic defect and
  minimal-boundary saturation rule that category out.

## `[OPEN CORE]`

`SINGULAR-DEGREE-TWO-FACE-COMPARISON`: construct the divisor-independent degree-two source
comparison and prove face naturality plus non-torsion on the trace-one ordinary-prime simplex.
First attack must decide the smallest viable target category.  Ordinary cyclic modules, fixed
Hilbert completions, finite Rees order, scalar distributions after frequency separation, and
product-topology closed relations are already excluded.

## Route-shadow map

| Corpus route | Shadow in proposed source simplex |
|---|---|
| R | nonseparable BV--Wold connection and exact two-path curvature |
| L | literal rational-adelic cyclic source, physical comparison, and Green--BV boundary |
| C1 / CCM class space | singular recipient and Real/Clifford intersection orientation |
| CCM-FU | noncompact cofinal realization needed to retain escaping source pointing |
| E | source-predeclared squarefree incidence supplying physical face adjacency |
| D2 / G | continued high-frequency and meromorphic overlap charts testing face naturality |
| N / O | source domain and whole-ground exhaustion preventing hidden complement directions |
| P / Q | all-order completed moments and theta-boundary saturation testing uniqueness of the target grade |

This table is a conjectural role assignment, not evidence that those maps exist.

## Gates

- [x] internal route and failed-mechanism audit
- [x] external RH and sheaf/Hodge parent audit
- [x] exact falsifiable conjecture frozen
- [x] precursor killed for a specific circularity/rediscovery reason
- [ ] construct the singular degree-two comparison
- [ ] complete hostile paper proof with no open dependency
- [ ] move to Stage 2 only after proof closure
- [ ] formalize exact theorem unconditionally, wire umbrella, and pass targeted gates
- [ ] complete exact novelty/significance audit

## Log

- 2026-08-04 — froze `SOURCE-POLARIZED-TWO-PATH-DESCENT` after corpus/external audit.  No Lean
  infrastructure authorized: exact source comparison remains open.
