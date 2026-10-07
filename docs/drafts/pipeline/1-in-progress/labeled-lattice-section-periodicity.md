# Translation rigidity of labeled lattice sections

- **ID:** labeled-lattice-section-periodicity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** xi-marked-joint-monodromy.md, C2; periodic-lattice-branched-sections.md
- **Statement C2-P:** Every nonrational meromorphic map V:C -> P1 satisfying the reciprocal and conjugate reciprocal symmetries, whose complete fibers over the three cube roots of unity are simple and separately contained in their labeled integer classes, has a nonzero translation period.

## Exact statement and purpose

Put omega=exp(2*pi*i/3). Require, as identities of sphere-valued maps,
V(-w)=1/V(w) and V(conj w)=1/conj(V(w)). For j=0,1,2 require
V(w)=omega^j => w belongs to j+3*Z and the local degree at w is one.
Rational maps are excluded from C2-P, not from the parent C2 classification.
Nonconstant rational degree-one and degree-three examples already exist.

C2-P competes with an explicit nonperiodic admissible meromorphic section.
Neither outcome is assumed. A period, if obtained, still needs a separate
descent argument before differential algebraicity follows. This card does
not assert the parent C2, nor any conclusion about the actual Xi section.

**[OPEN CORE]** Produce a period from the complete-fiber restrictions and
symmetries, or construct a counterexample satisfying every restriction.
Inclusion of fibers in a periodic set does not assert periodicity of fibers
or of the map. Interpolation at integers does not control additional fibers.

## Gates

The dilation-compatible subclass is now closed by a separate sufficient criterion. For an entire homogeneous pair F, let S be the origin fiber. If S-S is closed discrete, dilation by lambda preserves equality of fibers, lambda^(-n)->0, and S contains a nonzero regular return tau, then `(lambda-1)*tau` is a nonzero period. Regularity at the origin is deduced. Integer containment of S supplies the topological hypotheses. Both the projective theorem and integer-fiber specialization are Lean-certified in `HTGeometry/DiscreteFiberDilationPeriod.lean`; see [proof card](../3-formalized/discrete-fiber-difference-dilation-rigidity.md). This does not produce a dilation action for arbitrary C2-P sections or Xi. Verdict BRIDGE; significant novelty unverified.

- [x] Exact candidate, parent relationship, competing failure mechanism.
- [x] Multiplicative reciprocal repair of the cosine model excluded: `G(w)/G(-w)` has a genuine off-real 1-fiber at `6*i*sqrt(5)`. Full coincidence equation `4*w²=9*n²*(1-81*n²)` is Lean-certified. See [closed repair card](../5-failed/cosine-reciprocal-symmetrization.md). This refutes that repair, not C2-P.
- [x] Entire class of regular positive-diagonal rational norm-one repairs excluded: infinitely many genuine nonreal holomorphic 1-fibers, via pairwise distinct cosine diagonal coordinates and finite polynomial zero sets. Both leaves built and axiom-audited; [formalized card](../3-formalized/rational-cosine-diagonal-repair.md). Negative sign and cancelled basepoints are still live.
- [x] Product-divisor basepoint repair passes the infinite 1-fiber and aperiodicity tests but fails both other marked fibers: infinitely many genuine nonreal points, via two analytic submersions and exact discrete specialization. [Formal survivor](../3-formalized/cosine-product-corner-unfolding.md). The broader [algebraic-component classification](cosine-algebraic-fiber-rigidity.md) remains a conjecture.
- [x] First internal and external hostile audit.
- [ ] Dependency-closed proof or fully checked counterexample.
- [ ] Formalization of a significant dependency-closed result.

## Internal audit, 2026-10-07

Deep search: `meromorphic three labeled integer fibers rational periodic rigidity`.
Inspected all 20 candidate statements, all 20 source-argument statements,
and the proposed ingredient set. Results partial: decomposition deadline;
inventory complete at snapshot, compiler freshness incomplete, background
refresh ongoing. Existing rank-three period and constant-increment rigidity
theorems assume periods/increments; they do not produce the first period.
The proposed ingredient set therefore does not close this core. No claim
of corpus-wide absence follows. Forbidden spectral, positivity, and bound
arguments appearing among irrelevant hits are not imported.

## External hostile audit, 2026-10-07

Zhong, Meng, Yuan, *Meromorphic solutions of first-order differential equations
with rational exponential coefficients*, arXiv:2609.10219v1 (9 September 2026),
https://arxiv.org/html/2609.10219v1, Example 7.6 supplies an entire cosine of
a square root with three finite exponential fiber sets but no period.
Its two extremal cosine fibers are ramified away from the origin, and two
values share an exponential image. It does not satisfy the present simple,
separately labeled fibers or reciprocal symmetry. Its counting/growth proof
is outside the permitted methods and is not used. The paper's main theorem
assumes a first-order rational differential equation, which is unavailable
here; importing that premise would assume the sought rigidity.

**Verdict:** SURVIVES PRELIMINARY ATTACK. Novelty and significance remain
unverified; this verdict is not evidence that C2-P is true.

## Exact attacks to pursue

1. Square-root descent: audit complete regular cosine fibers and residue
   classes, including whether an affine square coordinate can support all
   three labels. Ordinary even descent loses the required involution.
2. Infinite real dessins: classify allowed continuation across the real
   line without assuming prescribed vertex positions are uniformizable.
3. Section geometry: use the affine modification
   `(v^3-1)*x=2*v^3-3*r*v+1`, r=exp(-2*pi*i*w/3), retaining the exceptional
   fibers and the v=infinity chart. No finite-dimensional ODE is assumed.

## No-go closure

Not retired. No killing theorem or positive survivor yet.

## Exact square-root attack: labels and simplicity do not force a period

The following paper calculation is a counterexample to C2-P with only the
symmetry V(-w)=1/V(w) removed. It is not a counterexample to C2-P itself.
It refines the classical square-root-cosine construction; significant
scientific novelty is not established.

Define the entire function

```
T(w) = cos(2*pi*sqrt((w+1/12)/27)),
```

where the expression denotes the even cosine power series in its square
root, hence a single-valued entire function. Put A_k=cos(pi*k/9) for
k=1,5,7. These three constants are distinct and real. For an algebraic
distinctness check, eta=exp(pi*i/9) has order 18, and equality of
eta^k+eta^(-k) and eta^l+eta^(-l) forces k=+/-l modulo 18.
Let

```
L(x) = (x-A_1)*(A_7-A_5) / ((x-A_5)*(A_7-A_1)),
M(x) = (omega*L(x)+1)/(omega^2*L(x)+1),
V(w) = M(T(w)).
```

All rational expressions are interpreted on P1. The map M is a Mobius
transformation sending A_1,A_7,A_5 to 1,omega,omega^2, respectively.
Real coefficients of L and conjugation exchanging omega and omega^2 give
M(conj x)=1/conj(M(x)); thus V has the required conjugate reciprocity.

The complete cosine fibers, obtained by solving the quadratic equation
for its exponential, are exactly

```
T(w)=A_k <=> w=((18*n+k)^2-1)/12 for some integer n,
k in {1,5,7}.
```

The apparently second sign is absorbed by n -> -n and squaring.
Equivalently the points are `27*n^2+3*k*n+(k^2-1)/12`.
Consequently the three labeled fibers belong to 0+3Z, 1+3Z, 2+3Z,
respectively. Every such point is simple: the cosine derivative vanishes
only when its exponential is +/-1, whereas eta^k is neither; the square
coordinate is unramified there because 18*n+k is nonzero. The branch
point w=-1/12 maps to T=1, which is none of these three constants.

The first fiber is infinite: equality of two squares (18*n+1)^2 and
(18*m+1)^2 implies n=m, since the alternative 18*(n+m)=-2 is impossible.
Therefore V is not rational.

There is no nonzero complex period. If p were a period, V(0)=1 would
force p in 3Z. Write p as a nonzero integer and use V(n*p)=1 for every
integer n. Then 1+12*n*p would be an integer square for every n.
Choose a prime q not dividing 12*p. Solve
`1+12*n*p = q (mod q^2)`, possible since 12*p is invertible modulo q^2.
The left side cannot be a square: divisibility of a square by q implies
divisibility by q^2. This is a contradiction. This argument uses exact
divisibility, not growth or a counting estimate.

Finally V(30)=1, from n=1,k=1. If V(-30)=1, an integer square would equal
-359, which is 5 modulo 7; squares modulo 7 are 0,1,2,4. Hence V(-30)
is not 1 and the missing reciprocal symmetry demonstrably fails.

**What survives:** full labeled simplicity plus conjugate reciprocity
still permits nonperiodic maps. The remaining involution must carry
essential information in any proof of C2-P. Multiplying this V by
1/V(-w) restores an involution but does not preserve the complete three
fibers; no such repair is asserted. Paper proof only, not yet Lean.

The arithmetic construction extends to any integer m>=2. Set
`T_m(w)=cos(2*pi*sqrt((w+1/(4*m))/m^3))` and
`a_j=cos(pi*(1+2*m*j)/m^2)` for j=0,...,m-1. Its complete fiber is

```
w=m^3*n^2+m*(1+2*m*j)*n+j+m*j^2, n in Z.
```

Every fiber is simple and lies in j+mZ. The a_j are distinct: equality
of the exponential pairs requires j=l modulo m, or
1+m*(j+l)=0 modulo m^2; the latter is impossible modulo m.
The j=0 fiber is infinite, and a nonzero period would make every
1+4*m*n*p an integer square, excluded by the same prime-square
divisibility argument. Thus no finite number of separately labeled
regular fibers alone forces a period. This generalization is paper-only;
it remains a refinement of a classical construction, not a novelty claim.

### Stronger exact replacement for the nonperiodicity argument

For m=3 and `w_n=((18*n+1)^2-1)/12`, differentiation through the
quadratic cover gives the exact jet identity

```
T'(w_n)*(18*n+1) = -(2*pi/3)*sin(pi/9) = T'(0),
T'(0) != 0.
```

If p is a period, T(p)=T(0) forces p=w_n by the complete fiber formula.
Differentiating T(w+p)=T(w) at w=0 gives T'(p)=T'(0). Substitution in
the jet identity gives n=0, hence p=0. This local differential argument
uses the ramification coordinate itself, without inequalities, arithmetic
counting, or prime selection. Mobius postcomposition preserves periods.
It is the preferred Lean proof of nonperiodicity. For general m, the
corresponding factor is `2*m^2*n+1`; the same argument applies.

## Formalization in progress

`HTGeometry/LabeledCosineDescent.lean` now verifies the quadratic-cover
descent, complete fibers, simple orders, distinct labels, an injective
infinite fiber, real structure, and absence of nonzero periods. Final
`exists_entire_nonperiodic_labeled_fibers` has no hypotheses. Nonperiodicity
uses the exact jet identity, not the modular alternative. Direct Lean audit
passes without warnings; targeted `--old` build passes (3388 jobs). Four
axiom audits use only propext, Classical.choice, Quot.sound. The leaf is
wired into HTGeometry, without an umbrella build.

`HTGeometry/LabeledCosineMobius.lean` now verifies the cube-root
normalization, complete simple fibers, absence of projective translation
periods (retaining poles), and homogeneous conjugate reciprocity. The final
`nonperiodic_cube_root_model` has no hypotheses. It also includes an
injective infinite 1-fiber and failure of reciprocal reflection: 30 is in
the 1-fiber and -30 is not. The latter uses an exact finite-field
contradiction (a putative square is 5 in F_7; cubing and Fermat's identity
force its root to vanish), not a sign argument about a negative square.
Direct Lean audit passes without warnings; the targeted `--old` build
passes (3399 jobs). Both leaves are wired once into HTGeometry. No full
or umbrella build, heartbeat change, numerical experiment, or commit ran.
The arbitrary-m extension and centered-cover set lemma remain paper-only.
Eight exported theorem axiom checks (four per leaf) report only propext,
Classical.choice, Quot.sound. The final model includes every required
property except reciprocal reflection, whose failure it explicitly proves.

Global `lint --check-generated` remains failing outside these leaves.
The final run reports nine unreachable modules:
`RHTower.WeilConeBoundaryMobiusAveraging`,
`RHTower.WeilNullPotentialSummableSideWitness`,
`HTGeometry.ApertureConeCalculus`, `HTGeometry.ApertureConeWinding`,
`HTGeometry.ApertureLogTranslation`, `HTGeometry.ApertureOpenHistoryIdeal`,
`HTGeometry.BoundaryCoronaCStarAlgebra`,
`HTGeometry.IntegerPolynomialRelationReduction`, and
`HTGeometry.TernaryTranslatedPowers`. It also reports API/overview freshness
drift after concurrent additions despite a preceding index refresh.
The generated reports are refreshed again after that run; no global-clean
claim follows. No error names either new cosine leaf. Scoped diff checks
pass. Unrelated modules are untouched.

Cycle audit: significant scientific novelty remains unverified. The
classical cosine family was used to falsify the weaker candidate with
complete fibers and exact first jets; this is a bridge, not an RH proof.
No actual Xi premise was discharged. No step was declined for effort,
and no numerical experiment was used. The next research target stays the
full reciprocal global-section problem; the two paper-only extensions
above are not substitutes for it. C2-P, C2, and RH remain open.

## Next hostile test: reflection on a centered quadratic cover

An elementary geometric obstruction limits a possible repair. Let E be a
nonempty subset of the real axis, invariant under negation, and set
S={u in C : u^2 in E}. Then S has no nonzero translation stabilizer.
Indeed S is invariant under multiplication by i, so a period p also gives
the period i*p. Choose u in S. All squares at u, u+p, u-p, u+i*p,
u+p+i*p are real. Their second difference gives Im(p^2)=0; their mixed
difference gives Re(p^2)=0. Thus p^2=0 and p=0. This is exact polynomial
geometry, with no metric estimate.

Applied to the complete 1-fiber of a reciprocal map, this excludes
obtaining an admissible map by centered quadratic descent of a periodic
meromorphic function. It does not handle shifted branch points or
arbitrary sections. It is an elementary bridge, not significant new
science; no claim that this settles C2-P is made. Lean status: not started.

Additional corpus audits: the affine-modification query and centered-cover
query returned partial results (reranking deadlines; the latter also
reported a disconnected worker). All 20 candidate and 20 source statements
in each were inspected. Suggested ingredient sets concerned unrelated
affine pullbacks or finite-fiber estimates, not the open rigidity claim.
Inventories were complete at their snapshots; compiler freshness was
incomplete and background refresh ongoing. No absence claim follows.

## Log

- 2026-10-07 — Created after the Lean-certified periodic infinite-branching
  counterexample refuted rational-Schwarzian rigidity. RH remains open.
