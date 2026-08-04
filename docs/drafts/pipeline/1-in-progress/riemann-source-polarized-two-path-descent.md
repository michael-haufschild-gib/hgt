# Riemann source-polarized two-path descent

- **ID:** `riemann-source-polarized-two-path-descent`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** `[CONJECTURE]` The literal rational-adelic cyclic source admits a
  divisor-independent, source-pointed singular para-`S` comparison whose target differential
  square is the direct-versus-two-step BV--Wold transport defect on the exact
  `(2,0),(2,1),(2,2)` prime-depth simplex and whose periodicity image of the ordinary-prime
  pointing is nonzero.

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
- `[LITERATURE]` Ponge's para-`S` modules satisfy the exact curvature law
  `d^2=(1-T)S` and his perturbation lemmas lift Hochschild deformation retracts to para-`S`
  deformation retracts: <https://arxiv.org/abs/1810.04835>.  This is the closest parent mechanism,
  not the missing arithmetic comparison.
- `[LITERATURE]` Getzler's 2026 paracyclic Dold--Kan theorem characterizes cyclicity by identity
  Dwyer--Kan monodromy on normalized chains: <https://arxiv.org/abs/2602.08158>.
- `[NOVELTY UNVERIFIED]` No located primary source gives the exact rational-adelic
  cyclic-face/BV--Wold transport comparison.  This is not a priority claim; MathSciNet/zbMATH
  ancestry and independent expert review remain absent.

## Frozen conjecture: `SOURCE-POLARIZED-PARA-S-DESCENT`

Let

```text
i0=(2,0), i1=(2,1), i2=(2,2),
a_rho=2 Re(rho)-1,
T_rho(i,j)=exp(a_rho theta(i,j)).
```

Construct before divisor specialization:

1. a degree-two rational-adelic cyclic source simplex `sigma_2` with an ordinary-prime
   trace-one pointing;
2. an honest source `S`-module `C_src` obtained from the cyclic bar and a singular, source-graded
   para-`S` target `P_src` over the Wold ideal, Gamma determinant, BV first trace, and co-Poisson
   source point;
3. a source-pointed para-`S` morphism `F_src : C_src -> P_src` fixed independently of Xi divisor
   data, with `S(F_src(sigma_2))` non-torsion and nonzero on the trace-one ordinary-prime pointing;
4. for every later Xi divisor specialization `rho`, coefficient-faithful identifications under
   which the target differential square on that pointing is

   ```text
   (T_rho(i0,i1) T_rho(i1,i2) - T_rho(i0,i2)) v_rho,
   ```

   with `v_rho != 0`.

   and whose normalized target monodromy is

   ```text
   M_rho = T_rho(i0,i2) /
     (T_rho(i0,i1) T_rho(i1,i2)).
   ```

   Thus the target identity is literally `d^2=(1-M_rho)S` after taking
   `S=T_rho(i0,i1)T_rho(i1,i2)` on the retained line.

The morphism must inherit source `d^2=0` from literal cyclic/simplicial identities, not impose
flatness after inspecting `rho`.  “Singular” means the comparison may use a variable ideal,
locally finite source grade, noncompact cofinal target, or closed relation, but it must preserve
ordinary-prime, depth, multiplicity, and divisor provenance until the displayed specialization.

## Conditional implication, not accepted proof

If the conjectured comparison exists, the source is an honest `S`-module, hence
`d^2 sigma_2=0`.  Intertwining of the differential gives

```text
(1-M_rho) S(v_rho) = 0.
```

Non-torsion/non-erasure of `S(v_rho)` gives `M_rho=1`, hence transport flatness.  The corpus theorem
`primeDepthBVWoldXiTransport_witness_flat_iff` gives `Re(rho)=1/2`.  Quantifying over all divisor
copies yields RH.

This is only a conditional chain.  No claim is `[PAPER-PROVED]` while the source comparison is
unconstructed.

## Conjecture-distance gate

- **Ontological reversal:** horizontal displacement is not a vector each route must annihilate;
  it is target monodromy/curvature measuring failure of one cyclic arithmetic source to descend
  through all route realizations.
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

**Stronger conjecture from the failure:** use the exact para-`S` identity `d^2=(1-T)S` to identify
Route-R curvature and Route-L paracyclic monodromy as two shadows of one source descent defect.
Coherence is fixed before a Hilbert structure and predicts a specific scalar failure, rather than
assuming harmonic vanishing.

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

`SINGULAR-SOURCE-PARA-S-RETRACT`: construct a divisor-independent Hochschild deformation retract
from the rational-adelic cyclic source to the joint physical target, verify the hypotheses needed
to lift it by the paracyclic perturbation lemma, and prove that the lifted periodicity image of the
trace-one ordinary-prime simplex is non-torsion.  First attack must decide the smallest viable
target category.  Ordinary cyclic modules, fixed Hilbert completions, finite Rees order, scalar
distributions after frequency separation, and product-topology closed relations are already
excluded.

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

- 2026-08-04 — froze `SOURCE-POLARIZED-TWO-PATH-DESCENT` after corpus/external audit.
- 2026-08-04 — external paracyclic audit exposed `d^2=(1-T)S` as the exact parent identity;
  strengthened active claim to `SOURCE-POLARIZED-PARA-S-DESCENT`.  No Lean infrastructure
  authorized: exact source comparison remains open.

## 2026-08-04 decisive hostile verdict: para-`S` merger retired

`[FAILED AS AN RH ROUTE] [POSITIVE SURVIVOR FOUND]`

The conjectured target square is not an uncorrected source obstruction.  The corpus already
constructs, independently from that square, the graded-`det_2` anomaly

```text
A_a(i,j,k) = exp(-a Area(i,j,k))
```

and proves

```text
T_a(i,j) T_a(j,k) A_a(i,j,k) = T_a(i,k).
```

Thus the proposed para-`S` periodicity leg is already present: it is the unconditional
counterboundary in `PrimeDepthBVWoldGradedDet2ScalarDescentBoundary.lean`.  Demanding that this
correction vanish is not inherited source exactness; on the actual Xi conormal it is equivalent to
RH.  The earlier non-torsion requirement therefore hid the desired conclusion.

The failure is stronger than circularity.  Route R's correction and Route L's monodromy are
finite-isogenous, so parallelizing their zero tests cannot shrink the common radical.

## Positive survivor: primewise monodromy--anomaly isogeny atlas law

Let `p` be any ordinary prime, put `b_p = 1-p^{-1}`, and use the three same-prime depth cells
`(p,0),(p,1),(p,2)`.  For centered real rate `a`, let

```text
A_p(a) := primeDepthBVWoldGradedDet2Anomaly a (p,0) (p,1) (p,2).
```

Then:

1. **All-prime triangle law**

   ```text
   Area_p = -(1-p^{-1})^3 log p.
   ```

2. **Monodromy--anomaly isogeny law**.  For `a_s=2 Re(s)-1` and Route L mate gain
   `delta_p(s)=exp(a_s log p)`,

   ```text
   A_p(a_s)^(p^3) = delta_p(s)^((p-1)^3).
   ```

3. **Dyadic atlas transition**

   ```text
   A_2(a_s)^8 = delta_2(s).
   ```

4. **Same-radical consequence**

   ```text
   A_2(a_s)=1  iff  delta_2(s)=1  iff  Re(s)=1/2.
   ```

5. **Cyclotomic amplification of the cofinal Route-L/CCM defect**.  At clock `2`, the already
   constructed cofinal source-homology readout can be rewritten

   ```text
   (delta_2(s)-1) * jet * trace
     = (A_2(a_s)^8-1) * jet * trace
     = (A_2(a_s)-1)(1+A_2(a_s)+...+A_2(a_s)^7) * jet * trace.
   ```

   Since `A_2(a_s)>0`, the cyclotomic multiplier is strictly positive.  Route L/CCM's physical
   paracyclic defect and Route R/graded-`det_2`'s triangle anomaly therefore have exactly the same
   vanishing radical before any Xi quantification.

### Paper proof

Write `q=p` as a positive real, `b=1-q^{-1}`, `m_e=bq^{-e}`, and
`lambda_e=(e+1)log q`.  Direct expansion gives

```text
theta_01 = b log(q) (2-q^{-1}),
theta_12 = b log(q) (3q^{-1}-2q^{-2}),
theta_20 = b log(q) (q^{-2}-3).
```

Adding yields

```text
b log(q)(-1+2q^{-1}-q^{-2}) = -b^3 log(q),
```

proving (1).  By definition of the independently constructed anomaly,

```text
A_p(a)=exp(a b^3 log p).
```

Hence

```text
A_p(a_s)^(p^3)
 = exp(a_s p^3 ((p-1)/p)^3 log p)
 = exp(a_s (p-1)^3 log p)
 = delta_p(s)^((p-1)^3),
```

which proves (2); `p=2` proves (3).  Positivity of the real exponential and injectivity of
`exp` prove (4).  The geometric factorization `x^8-1=(x-1)sum_{k=0}^7 x^k`, with every summand
positive at `x=A_2(a_s)`, proves (5).

No RH assumption, divisor vanishing, analytic continuation, limiting interchange, positivity
selection, or unconstructed comparison occurs in this proof.

## Revised cross-route merger verdict

Parallel source atlases must first be quotiented by **source isogeny classes of observations**.
Route labels do not certify independence.  R curvature, graded-`det_2` counterboundary, L
paracyclic monodromy, and CCM cofinal Bockstein are four cochain-degree presentations of one
positive horizontal character.  Their serial composition enlarges radicals; their naive parallel
product merely repeats the same radical.

A genuine Frankenstein route must glue **transition laws between primitive isogeny classes**, not
stack equivalent vanishing tests.  Missing transverse class must retain information not generated
by the positive character `s |-> p^(2 Re(s)-1)` under powers, nonzero scalar multiplication,
completion, or boundary passage.  Candidate sources are now sharply restricted to orientation
phase, singular Cartier provenance, or noncompact cofinal incidence before scalarization.

### Updated gates

- [x] para-`S` conjecture killed by explicit corpus counterboundary
- [x] positive survivor dependency-closed on paper
- [x] all-prime theorem and dyadic same-radical consequence isolated
- [ ] formalize survivor unconditionally and wire umbrella
- [ ] re-audit exact external/internal novelty after formalization

- 2026-08-04 — retired `SOURCE-POLARIZED-PARA-S-DESCENT`: its missing periodicity leg is the
  existing graded-`det_2` anomaly, while its non-torsion clause is RH-bearing.  Extracted the
  all-prime monodromy--anomaly isogeny law as positive survivor.
