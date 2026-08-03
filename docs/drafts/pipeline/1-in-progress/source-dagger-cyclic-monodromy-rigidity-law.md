# Source--dagger cyclic monodromy rigidity law

- **ID:** `source-dagger-cyclic-monodromy-rigidity-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM (paper) / RH PRODUCER CONJECTURE
- **Scientific status:** `[UNIVERSAL CONSUMER PROVED HERE] [SOURCE LANDING OPEN] [NOT RH]`
- **Statement:** A nonzero atom transported equivariantly from a cyclic source into a
  source-inverse/analytic-dagger paracyclic boundary must lie in the trivial-monodromy sector. For
  the Riemann top conormal, that monodromy is `q^(2 Re rho - 1)`, so an atomically faithful global
  landing forces `Re rho = 1/2`.

## Goal

Replace the dead regular Meyer comparison and the terminal scalar/cyclic readers by one
source-first chain identity which still carries horizontal orientation.

The route is not:

```text
construct a cyclic trace;
show a completed scalar is positive;
identify two pointwise boundary values;
assume a unitary divisor character.
```

It is:

```text
actual cyclic source atom
  -> singular top-conormal boundary atom
  -> mixed source-inverse/analytic-dagger rotation
  -> paracyclic monodromy
  -> retained source cyclicity forces monodromy one.
```

The only RH-bearing construction is the global, atomically faithful, mixed-rotation-equivariant
landing. The rigidity after that landing is unconditional.

## 1. Universal retained-cyclicity theorem `[PROVED HERE]`

Let `C` be a set with a degree-one cyclic rotation `t`, so

```text
t(t(c)) = c.                                                (1)
```

Let `V` be a complex vector space and let `T` be a target rotation whose square is scalar
monodromy:

```text
T(T(v)) = delta * v.                                        (2)
```

Suppose `L : C -> V` intertwines the two rotations:

```text
L(t(c)) = T(L(c)).                                          (3)
```

Then every retained atom `L(c) != 0` satisfies

```text
delta = 1.                                                  (4)
```

### Proof

Apply `(3)` twice and use `(1)`:

```text
L(c) = L(t(t(c))) = T(T(L(c))) = delta * L(c).
```

Since `L(c)` is nonzero, scalar cancellation gives `delta=1`. No norm, trace, positivity,
compactness, spectral theorem, or finite-dimensionality is used.

This is the smallest useful form of the law. In degree `n`, the same argument replaces `(1)` by
`t^(n+1)=1` and `(2)` by the full paracyclic monodromy.

## 2. Riemann mixed rotation

Fix an integer clock `q>1` and a spectral parameter `s`. The centered half-density character is

```text
lambda_q(s) = q^(1/2-s).                                    (5)
```

Source inversion and analytic adjunction are different off the critical line. On a two-legged
boundary packet their mixed rotation has the form

```text
T_s(x,y)
  = (lambda_q(s)^(-1) y, conjugate(lambda_q(s))^(-1) x).
                                                               (6)
```

Therefore

```text
T_s^2
  = |lambda_q(s)|^(-2) id
  = q^(2 Re(s)-1) id.                                      (7)
```

The scalar in `(7)` is already present in the corpus as all of the following:

- half-density mate gain;
- source-inverse/analytic-adjoint fracture;
- reflected shell entropy;
- Wold--Poisson transverse rate;
- Hellinger finite-Rees/all-orders-flat type split;
- Deninger one-sided framed curvature;
- Gamma/Calderon--Witt mate curvature;
- weight-one Frobenius--Hodge commutator.

Thus these are not separate obstructions. They are coordinate shadows of one paracyclic
monodromy.

If a nonzero cyclic source atom lands equivariantly at an Xi divisor point `rho`, `(4)` and `(7)`
give

```text
q^(2 Re(rho)-1) = 1.
```

Since `q>1`,

```text
Re(rho)=1/2.                                               (8)
```

One fixed clock is enough. Multiplicity is retained by landing the top conormal rather than the
reduced scalar divisor.

## 3. Exact source and target now available

Recent formal source work supplies most of the typed ingredients.

### Cyclic source

The source is the cyclic bar construction of the minimally unitized, finite-support rational CCM
adelic crossed product. Current modules construct:

- the actual nonunital crossed-product multiplication and its minimal unitization;
- cyclic-bar faces, degeneracies, and rotation on tensor powers;
- the face--face relations now being completed;
- a degreewise Real structure commuting with source cyclic rotation;
- algebraic and closed cyclic cokernels carrying the Real structure.

This source exists before Xi divisor evaluation.

### Singular top-conormal target

The target is not the regular Meyer boundary. It is the singular Cartier principal-parts/top-
conormal boundary assembled from:

- the source exceptional section generating the Xi Cartier quotient globally;
- the unique coherent ramified top-conormal power sector;
- literal top-residue adjunction and coefficient-faithful finite-stage cocones;
- the forced failure-nerve inverse-square metric;
- multiplicity-exact singular Cartier renormalization;
- the actual Gamma/Calderon--Witt boundary coefficient.

The finite source map and finite target landing exist. What is not yet constructed is their
global mixed cyclic comparison through the singular cofinal boundary.

## 4. The successor theorem to construct

`[OPEN CORE] [GLOBAL_ATOMIC_SOURCE_DAGGER_CYCLIC_LANDING]`

Construct, before selecting a zero, a morphism from the actual Real cyclic CCM source into the
singular Cartier Gamma/co-Poisson boundary such that its degree-one component satisfies:

1. **One fixed source atom.** A canonical clock/top-conormal bar atom `theta_q` is defined from
   the ordinary-prime source and obeys `t_1^2(theta_q)=theta_q`.
2. **Mixed rotation.** Boundary rotation uses source inverse on one leg and analytic dagger on
   the other. Its fibre at `rho` is exactly `(6)`, not the purely algebraic reciprocal swap.
3. **Equivariance before localization.** The global landing intertwines source rotation with the
   mixed boundary rotation. No fibrewise correction or zero-dependent gauge is permitted.
4. **Atomic non-erasure.** At every Xi divisor stalk, the landed top-conormal atom is nonzero and
   retains the complete multiplicity filtration.
5. **Singular strictness.** The landing is defined in a topology strictly finer than product
   observation and has the beyond-all-finite-Rees order forced by the corpus's no-sewing laws.
6. **Actual Gamma/co-Poisson provenance.** The mixed rotation agrees with the already constructed
   one-sided framed curvature and actual degree-six Gamma boundary, rather than being defined from
   desired monodromy.

Clauses 1--6 and the theorem of Section 1 imply RH.

## 5. Why this succeeds where the previous route fails

### Literal Meyer--Poisson sewing

The regular pointwise comparison is dead: the relevant Gaussian is not in the literal boundary
kernel off line, and complete regular comparisons either erase cofinal Xi trace or become
maximally vertical. The new target is explicitly singular and top-conormal.

### Cyclic scalar readers

Completed Euler clock plus Gamma--Jacobi tail loss generates every finite matrix algebra. A cyclic
scalar reader is therefore an ordinary trace and erases the pointed orientation. The new law is
chain-level and uses the retained atom before any trace.

### Reflection/Tate parity

Free reflected pairs are boundaries and parity loses even seam deposits. The new invariant is the
positive real monodromy `q^(2 Re rho-1)`, not orbit parity.

### Positive/Hilbert completion

Finite positive packets and Hilbert completions either lose the divisor atom or forget the
all-orders-flat distinction. The new theorem needs no positivity and predicts the singularity of
the correct landing.

### Green covariance

The total Green map is covariant because its Riesz and Hodge defects cancel antidiagonally. Mixed
cyclic rotation retains the ordered two-leg provenance before that codiagonal, so its square reads
the uncancelled monodromy.

### Hedenmalm two-ended gluing

Vertical source gluing conserves the independent horizontal defect. Cyclic monodromy attacks that
horizontal defect directly; it does not ask vertical gluing to annihilate it.

## 6. Universal shadow law

The proposed public law is:

> **A faithful cyclic source cannot acquire modular drift under descent.** Whenever an atomic
> source relation with finite cyclic order survives in a boundary realization, the target
> paracyclic monodromy is trivial on that atom. Apparent drift can occur only by atomic erasure,
> loss of cyclic equivariance, or singular failure of descent.

This explains the corpus in one sentence:

- finite source theorems succeed because cyclic/order data are retained;
- scalarized consumers see only monodromy-invariant shadows;
- product-topology completions erase atoms by maximal verticality;
- finite-Rees transports cannot cross the modular type split;
- Gamma/co-Poisson curvature is the measured failure of cyclic descent;
- the critical line is the trivial-monodromy locus;
- four-unit Ward positivity is a downstream consumer after atomic cyclic descent, not the
  producer;
- Hedenmalm, Wold--Poisson, Sonin/Calkin, Rees, Hodge, and Cartier constructions are different
  observations of the same retained-or-erased cyclic atom.

## 7. Hostile audit

1. **Every algebra has a cyclic bar complex.** Correct. Source cyclicity alone proves nothing.
   Load-bearing content is mixed source-inverse/analytic-dagger equivariance plus nonzero Cartier
   landing.
2. **A purely algebraic target swap squares to one for every `s`.** Correct. Such a swap forgets
   analytic adjunction and is rejected by clause 2.
3. **KMS/twisted cyclic systems allow nontrivial modular flow.** Correct. They are paracyclic. The
   theorem constrains only the nonzero image of a genuinely cyclic source atom.
4. **The landing could choose the invariant subspace fibrewise.** Forbidden. It must be one global
   source morphism before divisor specialization.
5. **The atom could vanish at off-line zeros.** This is the main falsifier. Atomic non-erasure must
   follow from the source exceptional section, top-residue faithfulness, and singular Cartier
   landing.
6. **Closed cyclic completion could become maximally vertical.** Correct. The landing must retain
   one output-informative top-conormal atom in a nonproduct topology.
7. **Ordinary Real cyclicity may not produce the mixed dagger.** Correct. A Real-Brauer or
   source-duality comparison may be necessary. Proving a purely complex cyclic morphism is
   insufficient.
8. **Symmetric local Frobenius algebra is insufficient.** Correct. Every local Xi Artin algebra is
   symmetric. The analytic mixed rotation and its positive modular monodromy are essential.
9. **Generalized-prime countermodel.** If an off-line generalized-prime system supports clauses
   1--6 with literal ordinary-source provenance, the route is false.
10. **Equivalence theatre.** Defining the target rotation only after requiring `T^2=1`, or defining
    the landing from critical zeros, is exactly RH and is forbidden.

## 8. Near-term construction order

1. Complete the actual cyclic bar module and its Real structure on the rational CCM source.
2. Define the singular top-conormal boundary as a paracyclic object; compute degree-one mixed
   rotation directly from source inverse and Gamma analytic dagger.
3. Prove its square is the existing half-density mate gain and its curvature is the already
   formalized one-sided framed/Gamma boundary coefficient.
4. Construct the global degree-one landing of `theta_q` from the source exceptional section and
   rational-Witt top-conormal cocone.
5. Prove rotation equivariance on the dense finite source core.
6. Prove closed singular extension and atomic non-erasure at every Cartier stalk.
7. Apply retained-cyclicity rigidity to obtain RH.

Steps 1--3 are structural and locally testable. Step 4 is the first genuinely arithmetic bridge.
Step 6 is the decisive cofinal theorem.

## Gates

- [x] 0 → 1: universal law, exact consumer proof, source/target, falsifiers, and kill conditions
  frozen
- [x] previous regular Meyer, scalar cyclic, parity, positive-completion, and homogeneous-cycle
  routes excluded
- [x] exact current corpus ingredients identified
- [ ] construct actual source degree-one cyclic atom
- [ ] construct mixed paracyclic target and identify monodromy with mate gain
- [ ] construct global source-first landing
- [ ] prove atomic non-erasure and singular strictness
- [ ] derive RH
- [ ] formalize each dependency-closed theorem

## Log

- 2026-08-03 — Frozen after the literal Meyer comparison, scalar cyclic reader, Blaschke product,
  reflection-Tate, regular completion, Green codiagonal, vertical-gluing, diagonal weighting, and
  fixed-carrier homogeneous-cycle attacks were all closed. The surviving invariant is the
  degree-one cyclic identity before source-inverse/analytic-dagger descent; its target defect is
  exactly the already computed Riemann modular character.

## 2026-08-03 boundary-defect correction

The strict landing in Sections 4 and 8 is overdetermined and is no longer the open core. For an
arbitrary linear landing `L`, define `D = T L - L t`. The exact identity

```text
T D + D t = T^2 L - L t^2
```

implies, when `t^2 = 1` and `T^2 = delta id`, that

```text
(delta - 1) L = T D + D t.
```

Consequences:

1. strict equivariance `D = 0` forces `L = 0` whenever `delta != 1`; singular topology,
   unboundedness, and nonclosability do not evade this algebraic obstruction for a single-valued
   landing on a rotation-stable domain;
2. strict equivariance is stronger than needed: if `D` lands in a `T`-stable boundary submodule
   `B` and one physical atom satisfies `L(theta_q) notin B`, then `delta = 1`;
3. the existing nonzero top-conormal vector does not yet prove the required nonzero quotient class.

Revised open core:

```text
[GLOBAL_ARITHMETIC_BOUNDARY_CLASS_LAW]
construct source-defined B;
prove physical source-dagger defect lies in B;
prove physical top conormal does not lie in B.
```

At every Xi divisor fibre these three clauses imply `q^(2 Re rho - 1) = 1`, hence RH. The strict
landing route is obstructed; the surviving route is homological, not topological.

Formal support:

- `formal/GaloisForLFunctions/HTGeometry/CyclicParacyclicBoundaryDefectLaw.lean`
- `formal/GaloisForLFunctions/RHTower/SourceDaggerCyclicBoundaryDefectLaw.lean`

## 2026-08-03 maximal-boundary closure

The boundary itself is no longer an open construction. Define the canonical minimal stable defect
boundary

```text
B_min = range(D) + range(T D).
```

When `T^2 = delta id`, `B_min` is `T`-stable, contains the defect, and is contained in every other
stable defect boundary. Therefore an atom survives any admissible quotient iff it survives
`V / B_min`. Away from `delta = 1`, the entire range of `L` lies in `B_min`; if `L` is surjective,
`B_min = V`.

For the literal two-leg landing scaled by the first nonzero physical Möbius--theta jet,

```text
B_min(rho) = 0       if Re rho = 1/2,
B_min(rho) = C^2     if Re rho != 1/2.
```

The canonical source atom class is nonzero iff `Re rho = 1/2`, and global class survival is
equivalent to RH. Thus boundary choice, topology, and singular completion are closed as possible
sources of the missing theorem. Revised open core:

```text
[INDEPENDENT_ARITHMETIC_CLASS_SURVIVAL]
compare literal cyclic arithmetic source with physical Möbius--theta two-leg landing;
construct a pre-divisor source residue annihilating B_min;
prove it detects the canonical physical class.
```

The corpus currently contains the literal cyclic CCM source and the physical Möbius--theta landing
as separate producers, but no comparison between them and no residue with the two required
properties. Any global proof of this source residue statement is exactly RH-bearing, not a smaller
boundary-construction lemma.

Formal support:

- `formal/GaloisForLFunctions/RHTower/MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`

## 2026-08-03 literal comparison and residue-transgression closure

The literal comparison is now constructed. Let `A` be the minimal unitization of the rational
adelic CCM crossed product and use its genuine degree-one cyclic bar `A ⊗ A`. For every ordinary
prime `p`, the source atom with scaling labels `p` and `p⁻¹`, Gaussian real coefficient, and
integral finite-adele Bruhat coefficient satisfies the independent source identity

```text
epsilon_0^1(u_p) = 1.
```

The pre-divisor ordered comparison and cyclic residue are

```text
C(x) = (epsilon_0^1(x), 0),
Res(z_0,z_1) = z_0 + z_1.
```

For every independent jet grade `k`, physical rung `m`, and spectral point `w`, the comparison
lands through the actual Möbius--theta transform and converges cofinally to
`XiC^(k)(w) C(x)`. Only after construction is `k` specialized to divisor multiplicity. Lower
grades have zero residue and the first nonzero grade is detected, without any unitary Jordan or
simplicity premise.

The decisive exact law is

```text
Res(D_{n,rho} x) = (delta_n(rho) - 1) c_rho epsilon_0^1(x).
```

Thus the source residue kills the untwisted cyclic comparison defect, while analytic dagger
twisting transgresses it by precisely monodromy minus one. On `u_p`, both source factors outside
`delta-1` are nonzero. The constructed residue annihilates the physical `B_min(rho)` iff
`Re rho = 1/2`; global annihilation iff RH. This closes source construction, literal comparison,
ordinary-prime detection, multiplicity filtering, and residue construction.

Revised open core:

```text
[PHYSICAL_DEFECT_SOURCE_NULL_HOMOLOGY]
prove, before divisor specialization, that the physical analytic-dagger defect is a literal
cyclic boundary (or otherwise has zero literal source residue).
```

This is not an infrastructure lemma. The transgression formula and trace-one prime cycle prove it
is exactly RH-bearing.

Formal support:

- `formal/GaloisForLFunctions/RHTower/MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`
  (`ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one`,
  `tendsto_ccmMobiusThetaFilteredTwoLegLanding_primeCycle_at_divisor`,
  `ccmMobiusThetaXiJetTwoLegResidue_ne_zero_at_supportMultiplicity`,
  `ccmMobiusThetaTwoLegParacyclicDefect_residue`,
  `ccmMobiusThetaSourceResidueAnnihilatesMinimalBoundary_iff`,
  `ccmMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary_iff_riemannHypothesis`)
