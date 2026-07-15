# Derived self-dual clock-splitting stack

- **ID:** `derived-self-dual-clock-splitting-stack`
- **Stage:** 1-in-progress
- **Type:** MEDAL-SCALE CONJECTURE / UNIFIED HT OBSTRUCTION OBJECT
- **Scientific status:** `[CONJECTURE] [FINITE-STAGE ACYCLICITY PROVED] [NOT AN RH RESULT]`
- **Parent theorems:**
  `../2-fully-proven/new_scientific_knowledge/hypertranscendental-clock-incompressibility.md`,
  `../2-fully-proven/new_scientific_knowledge/differential-variational-building-balance-law.md`
- **Statement:** The universal positive linearized object of a hypertranscendental realization is
  its capacity field: the building-valued clock-capacity path descended over the source realization
  groupoid modulo bounded congruence.  The derived stack of filtration-tame, global, positive, and
  self-dual splittings is the stack of admissible trivializations of that field.  The familiar
  obstruction modes are conjecturally conservative representations of this one object.

## 1. Why the obstruction object has a splitting stack

Let `K/C` be a finite-rank free HT field and let `rho` be a realization of its finite jet
observables in an ambient algebraic, analytic, spectral, or boundary object `A`.  Linearization
gives a completed differential cotangent comparison

```text
Theta_rho : A tensorhat_K M_K  ->  M_A,                              (1)
```

where `M_K` is the torsion-free Kahler--Ore module of `K/C`.  A cone of `(1)` is not yet the right
object: for a harmless free transverse extension it contains the transverse cotangent directions.
The actual reconstruction question is whether the intrinsic summand of `(1)` admits a compatible
right inverse.

On a parameter or continuation domain `U`, write the comparison in local frames as

```text
P_U : V_A|U -> V_K|U.                                                   (2)
```

The variance convention is chosen so that a reconstruction is a right inverse.  Define

```text
Spl_rho(U)={Q_U : P_U Q_U=I}.                                          (3)
```

The raw sheaf `(3)` is then cut down by the conditions forced by the realization:

1. **clock-tame:** the operator orders of `Q_U` are uniformly controlled by the observable
   filtration;
2. **continuation-compatible:** the local splittings glue across overlaps;
3. **monodromy-equivariant:** continuation around a loop returns the same splitting up to the
   prescribed source symmetry;
4. **positive:** the induced source pairing has the required positive cone;
5. **self-dual:** reflection/adjunction fixes the splitting.

The resulting derived moduli object is the **self-dual clock-splitting stack**

```text
SHT(rho)=R Spl_rho^(tame,+,sd).                                        (4)
```

Hypertranscendence is constrained not by one equation or one flow, but by the existence and
topology of the compatible reconstruction stack `(4)`.

## 2. Finite-stage acyclicity theorem

### Theorem A: local splitting space is affine

Let `P` be any full-row-rank matrix over a field or skew field.  Then the space of right inverses
is nonempty.  If `Q_0` is one right inverse, every right inverse is uniquely

```text
Q=Q_0+H,                         P H=0.                                (5)
```

Thus `Spl(P)` is an affine torsor over `ker(H |-> P H)`.  In particular, a single finite free
differential embedding has no pointwise algebraic splitting obstruction.

### Proof

Full row rank gives `Q_0` with `P Q_0=I`.  If `P Q=I`, then

```text
P(Q-Q_0)=0.
```

Conversely every `Q_0+H` with `PH=0` is a right inverse.  Uniqueness of `H=Q-Q_0` is immediate.
The exact kernel-perturbation equivalence is Lean-verified as
`matrix_rightInverse_iff_kernelPerturbation` in
`formal/GaloisForLFunctions/HTGeometry/AlgebraicIndependentLinearForms.lean`.

### Theorem B: finite immersion cannot create a global clock obstruction

For a fixed embedding of finite-rank free differential fields, the Frechet comparison has full row
rank over the rational pseudodifferential skew field.  It therefore has `(5)`, and any two induced
clock gauges differ by fixed two-sided overhead.  Consequently their translation lengths and full
normalized Cartan spectra agree.

This is the proved clock-incompressibility theorem.  It is the decisive no-go:

```text
no universal HT obstruction exists at one finite free differential stage.              (6)
```

The positive successor is that every genuine obstruction is a failure to choose the affine local
splittings `(5)` *compatibly* with at least one of the five structures defining `(4)`.

### Theorem C: surjective splitting towers have no completion obstruction

Let `S_m` be nonempty finite-stage splitting spaces and let

```text
r_m:S_(m+1)->S_m
```

be their restriction maps.  If every `r_m` is surjective, then there is a compatible sequence
`q_m in S_m` with `r_m(q_(m+1))=q_m` for every `m`.

Choose `q_0`.  Having chosen `q_m`, surjectivity supplies `q_(m+1)` above it; dependent recursion
constructs the tower.  This is Lean-verified as `exists_compatible_of_surjective_tower` in
`formal/GaloisForLFunctions/HTGeometry/AlgebraicIndependentLinearForms.lean`.

Therefore a completion/continuation obstruction is impossible under the Mittag--Leffler lifting
condition.  Its positive certificate is an explicit scale at which some finite splitting does not
lift, or an eventual failure of surjectivity in the pro-system.

## 3. Unified-obstruction conjecture

**[CONJECTURE: SPLITTING-STACK COMPLETENESS.]** For every source-defined realization `rho` of a
finitely generated HT field, all persistent reconstruction obstructions factor functorially
through `(4)`.  More precisely:

```text
spectral incompleteness       = rank/cokernel support of the splitting stack,
continuation failure          = absence of a global section,
monodromy                     = nontrivial descent class of the affine splitting torsor,
positivity failure            = emptiness of its positive fixed substack,
noncanonical boundary data    = noncontractibility of its tame self-dual section space. (7)
```

The five outputs in `(7)` are not asserted to be automatically equivalent.  The conjecture is that
for a valid unified realization they are conservative functors of one object: two chains describe
the same obstruction exactly when their comparison functors identify the same class or support in
`SHT(rho)`.

## 4. The three boundary strata

Clock incompressibility proves that `(4)` can be nontrivial only at the boundary of the finite-free
immersion category.  Once a realization is presented by a tower of admissible splitting spaces,
the following trichotomy is exact.

### Theorem D: abstract boundary trichotomy

Exactly one of the following reductions occurs.

1. No finite-rank splitting tower represents all source observables: rank boundary.
2. A finite tower exists, but some admissible splitting space `S_m` is empty: map/structure
   boundary.
3. Every `S_m` is nonempty, but there is no compatible global splitting: by Theorem C, some
   restriction `S_(m+1)->S_m` is not surjective, giving the completion boundary.

If none occurs, every stage is nonempty and every restriction is surjective, so Theorem C constructs
a compatible global admissible splitting.  There is then no obstruction of type `(4)`.

The theorem is conditional only on having a source-defined splitting-tower presentation.  The
medal-scale completeness conjecture is that every persistent HT realization obstruction has such a
presentation and that the presentation is conservative.

### Theorem E: finite-dimensional affine towers have no completion obstruction

Let `(S_n)` be a countable inverse tower of nonempty finite-dimensional affine spaces over a field,
with affine restriction maps.  For fixed `n`, the images of all later stages in `S_n` form a
descending chain of nonempty affine subspaces.  Their dimensions cannot decrease indefinitely, and
an inclusion of nonempty affine subspaces of the same finite dimension is equality.  Hence the
images stabilize: the tower is Mittag--Leffler.  The standard nonempty Mittag--Leffler inverse-limit
theorem then gives

```text
lim_n S_n != empty.
```

Therefore a purely algebraic finite-dimensional affine splitting tower cannot carry a completion
obstruction, even when its original one-step restrictions are not surjective.  The positive
successor is forced: completion obstruction requires infinite dimension, failure of closedness or
tameness, or a non-affine positivity/self-duality cut.

This is standard inverse-limit parent theory, not a novelty claim; the relevant general
Mittag--Leffler nonemptiness theorem is Stacks Project, Tag 0597.

### Theorem F: the direct-sum/product clock horizon

The completion boundary is nonempty in infinite rank.  Let `k^(N)` be the algebraic direct sum of
countably many clock coordinates.  At scale `n`, define

```text
S_n={v in k^(N) : v_0=...=v_(n-1)=1}.                                 (8)
```

Every `S_n` is a nonempty affine space.  The restriction `S_(n+1)->S_n` preserves the underlying
finitely supported vector.  A compatible sequence would therefore be one finitely supported vector
whose every coordinate is `1`, which is impossible.  Hence

```text
lim_m S_m = empty                 inside k^(N).                         (9)
```

In the product completion `k^N`, however, there is exactly one compatible point:

```text
1_boundary=(1,1,1,...).                                                (10)
```

This is an exact realization of the founding phrase: every finite algebraic clock constraint is
soluble, all solutions fail to assemble in the algebraic source, and completion adds one thin
boundary observable satisfying the entire infinite packet.  The no-compatible theorem and the
unique product-boundary theorem are Lean-verified as
`finitePrefixOneSplitting_no_compatible` and
`existsUnique_productCompletion_unitBoundary` in
`formal/GaloisForLFunctions/HTGeometry/AlgebraicIndependentLinearForms.lean`.

This model is not claimed as externally new linear algebra.  Its role is stronger and cleaner: it
proves that the completion stratum proposed by `(4)` is mathematically inhabited and identifies the
minimal mechanism--direct sum versus product--that any analytic HT realization must enrich rather
than merely rename.

### Theorem G: normalization forces a persistent self-dual modular defect

Let the unique product boundary `(10)` be made normal in a positive diagonal clock completion

```text
H_w={a : sum_n w_n |a_n|^2 < infinity},       w_n>0.
```

Then `1_boundary in H_w` exactly when `sum_n w_n<infinity`.  For every such weight and every cutoff
`N`, some `n>=N` satisfies `w_(n+1)!=w_n`; moreover no bounded positive change of metric can make
the reweighted clock stationary.  For a two-sided reflection-symmetric weight, the modular ratio

```text
Delta_w(n)=w_(n+1)/w_n
```

obeys

```text
Delta_w(-n-1)=Delta_w(n)^(-1).                                (11)
```

Thus the positive completion does not erase the completion obstruction.  It converts the missing
algebraic boundary into a normal state carrying a persistent anti-self-dual modular anomaly.
Moreover, the modular ratio determines every nowhere-zero two-sided weight up to scale and every
positive total-mass-one weight uniquely.  It is therefore a complete invariant of the normalized
positive diagonal completion, not merely an obstruction witness.  The five exact kernels are
Lean-verified in
`formal/GaloisForLFunctions/HTGeometry/AlgebraicIndependentLinearForms.lean`; the proof and external
novelty gate are in
`../2-fully-proven/new_scientific_knowledge/hypertranscendental-clock-normalization-symmetry-anomaly.md`.

Theorem G supplies the diagonal boundary chart.  The modular-corona class is not the universal
object; it is one coordinate representation of the capacity field.  The stack `(4)` is the derived
stack of admissible trivializations of that field.

### Theorem H: exact symmetry condenses the boundary into one spectral line

The diagonal modular anomaly has a rigid non-diagonal escape.  Let a total two-sided clock orbit
`u_(n+1)=Uu_n` live in a positive Hilbert completion with `U` unitary.  If a normal vector `b`
realizes the complete boundary packet

```text
<u_n,b>=1             for every n in Z,
```

then `Ub=b`; `b` is the unique vector with that response; and every fixed vector of `U` is a scalar
multiple of `b`.  Hence the fixed spectral sector is exactly the canonical boundary line.  The
forward clock orbit cannot be Bessel, since its first `N` responses against `b` already have squared
sum `N`.

This is the strong positive successor to the diagonal no-go.  A normal positive boundary can keep
exact clock symmetry, but only by condensing into a simple zero-frequency spectral atom and giving
up stable Bessel observability.  The general object is therefore a pointed measured clock
compactification: its free sector carries the modular cocycle and its fixed boundary sector carries
the spectral atom.  The new Lean kernels and the external novelty gate are in
`../2-fully-proven/new_scientific_knowledge/hypertranscendental-clock-modular-spectral-alternative.md`.

### Theorem I: arbitrary positive clocks have a canonical capacity-innovation path

Let `G_N` be the strictly positive Gram matrix of the first `N+1` realized clock modes and `C_N`
its coherent canonical inverse-Cholesky frame.  For the unit boundary packet define

```text
eta_N=(C_N 1)_N,
kappa_N=||C_N 1||^2.
```

Then

```text
kappa_(N+1)=kappa_N+|eta_(N+1)|^2,
kappa_N=sum_(n<=N)|eta_n|^2.
```

The minimum squared norm of a vector realizing the first `N+1` unit responses is exactly
`kappa_N`.  In the Hilbert completion, the complete boundary is normal exactly when
`eta in ell^2`, equivalently `sup_N kappa_N<infinity`; its squared norm is that supremum.  A Bessel
clock forces `kappa_N>=(N+1)/B`, so stable observability places the boundary in the rigged dual
rather than the Hilbert space.

For an `r`-packet of boundary observables, `eta_N in C^r` and the capacity is a positive matrix path

```text
K_(N+1)=K_N+eta_(N+1)^*eta_(N+1).
```

Every increment is positive semidefinite of rank at most one.  This matrix curvature law is
Lean-verified; it is the finite-rank building-valued object anticipated by the conjecture.  The
paper proof, formal kernels, and external novelty gate are in
`../2-fully-proven/new_scientific_knowledge/hypertranscendental-clock-capacity-innovation-theorem.md`.

Theorems G and H are now normal-form consequences of Theorem I.  In diagonal coordinates the
innovation distribution is recorded by the persistent modular ratio.  Under exact unitary shift
symmetry, square-summability condenses into the unique fixed spectral line.

### Theorem J: capacity freedom forces a covariant capacity field

Hypertranscendence and positivity alone impose no scalar capacity-growth law.  Every nondecreasing
positive scalar path occurs as the unit-boundary capacity of a coherent positive Gram clock.
Conversely, bounded response-intertwining equivalences make minimum-response norms and their
squared capacities `Theta`-equivalent.  For finite response packets, coordinate change by `R`
obeys the exact congruence law

```text
K_N(tR)=R^*K_N(t)R.
```

Therefore a scalar innovation sequence is not the intrinsic object.  The intrinsic object is the
bounded-congruence class of the positive matrix path descended over the realization/coordinate
groupoid: the **hypertranscendental capacity field**.  The modular-corona and spectral-atom
descriptions are boundary charts of this field; the splitting stack is its derived positive
self-dual trivialization object.

The complete paper proof, external novelty gate, and Lean kernels are in
`../2-fully-proven/new_scientific_knowledge/hypertranscendental-capacity-field-realization-covariance.md`.

### Rank boundary

The source tail is not finitely differentially generated or the completed cotangent module is not
perfect.  No finite matrix `P` controls all observables.  This is the natural home of infinite
clock capacity that cannot be represented by one finite building.

### Map boundary

The realization is a quotient, specialization, or rank-degenerate comparison.  The local matrix
loses full row rank; the right-inverse torsor becomes empty.  Its degeneracy support is a genuine
spectral locus.

### Completion boundary

Every finite stage splits algebraically, but no family of splittings is uniformly clock-tame or
compatible under inverse limit.  Derived completion

```text
R lim_m Spl(P_m)                                                       (12)
```

retains the higher inverse-limit and descent classes discarded by an ordinary limit.  This is the
only remaining place for a continuation or noncanonical-boundary obstruction when all finite
comparisons are exact.  Theorem C further forces such an obstruction to appear as failure of the
surjective lifting condition (or of the clock-tame subspaces to remain nonempty).

**[CONJECTURE]** Every persistent HT realization obstruction is represented conservatively by a
splitting tower to which Theorem D applies, and the three strata glue functorially into `(4)`.  A
counterexample is a fourth phase and would itself be a significant new classification result.

## 5. Self-dual degeneracy spectrum

Suppose the realization has a reflection involution `iota` and a compatible adjoint pairing.  The
self-dual substack is the homotopy fixed object

```text
SHT(rho)^sd = SHT(rho)^(h iota).                                      (13)
```

Define its degeneracy spectrum by

```text
Sigma_sd(rho) = support of the derived failure of a tame positive section of (13).      (14)
```

At a regular parameter, the affine splitting torsor has a tame positive self-dual section and the
fiber of `(14)` is empty.  At a degeneracy, a local rank drops, a descent class appears, a tame
right inverse blows up, or the positive fixed locus becomes empty.  These are four presentations
of one derived fiber of `(13)`.

**[CONJECTURE; NOT AN RH RESULT.]** For a source-first completed-zeta realization, the critical
zeros are the common self-dual degeneracy spectrum only if

```text
{rho}=a construction independent of the zeros,
reflection=the functional-equation involution,
Sigma_sd(rho)=the zero divisor with multiplicity,
and every obstruction chain factors conservatively through (13).      (15)
```

Equation `(15)` is a research program and a falsifiable representation theorem, not a claim that RH
or even the identification has been proved.

## 6. Connection with the founding conjecture

The statement

```text
hypertranscendence is infinite algebraic clock capacity concentrated on a thin constraint boundary
```

now has a precise candidate meaning:

```text
infinite capacity = the pro-system of free finite jet packets,
finite rigidity   = affine and asymptotically incompressible local splitting spaces,
thin boundary     = the modular-corona class whose admissible trivialization stack degenerates.
                                                                            (16)
```

The clock is a filtration of observables.  The boundary is the failure of compatible observation,
not a moment in time.

## 7. External novelty gate

The novelty gate is only against external literature.

Parent theories include:

- cotangent complexes and transitivity triangles in Andre--Quillen theory,
  https://stacks.math.columbia.edu/tag/08P6;
- Andre--Quillen cohomology for algebras over operads, which supplies a general derived framework
  for algebraic theories with operators, https://arxiv.org/abs/0806.4405;
- derived completion as a derived inverse limit, https://stacks.math.columbia.edu/tag/0A0E;
- Frechet-Jacobian inclusion maps of differential modules in G. Mari Beffa,
  https://www.numdam.org/item/BSMF_1999__127_3_363_0/;
- differential substitutions and their Frechet chain rule,
  https://arxiv.org/abs/2301.04475 and https://arxiv.org/abs/solv-int/9509006;
- affine buildings and their boundary geometry,
  https://doi.org/10.2140/iig.2023.20.471.

These theories make the ingredients legitimate; they do not make `(4)`, `(7)`, or `(13)` an
external theorem.  Targeted searches located no construction of a tame positive self-dual
splitting stack for differential-field realizations, no finite-immersion acyclicity/boundary
trichotomy in this setting, and no theorem identifying spectral, continuation, positivity,
monodromy, and boundary-condition defects as conservative images of such a stack.

External novelty is therefore **provisional**.  Operadic Andre--Quillen theory, D-module
deformation theory, integrable-systems reduction, derived completion, and analytic Fredholm theory
all require specialist review before any priority claim.

## 8. Significance and anti-theatre gate

- `[PASS]` The object is forced by the proved no-go: local finite embeddings always split, so only
  compatibility of splittings can carry an obstruction.
- `[PASS]` It gives one exact object with five testable realization functors, rather than declaring
  five metaphors equivalent.
- `[PASS]` Rank, map, and completion failures form an exact conditional trichotomy inside one
  moduli problem.
- `[PASS]` It predicts a source-defined multiplicity-bearing degeneracy support.
- `[PASS]` It has decisive finite-stage and surjective-tower no-go theorems with Lean kernels.
- `[PASS]` Its modular-corona refinement is a complete invariant of normalized positive diagonal
  completions and is provably nontrivial under bounded positive gauges.
- `[PASS]` The exactly symmetric non-diagonal escape is classified: one canonical boundary
  eigenline and unavoidable Bessel failure.
- `[FAIL until proved]` Existence of `(4)` in a usable category, completeness of `(7)`,
  conservativity of the splitting-tower presentation, and any zeta realization remain open.
- `[FAIL if redressed]` Calling an arbitrary cotangent complex, Fredholm determinant, or sheaf of
  boundary conditions `SHT` does not instantiate the conjecture.
- `[MEDAL-SCALE VERDICT]` A proof of splitting-stack completeness plus a nontrivial arithmetic
  realization satisfying `(15)` would create the requested new field.  The definition and local
  acyclicity theorem alone do not.

## 9. Attack and falsifiers

1. Construct `SHT(rho)` first for inverse systems of finite-dimensional valued differential
   modules, where derived limits and affine torsors are explicit.
2. Prove the rank/map/completion stratification and a descent spectral sequence for its homotopy
   groups.
3. Add reflection and positivity; determine when homotopy fixed splittings exist.
4. Prove conservativity for two genuinely different realizations, not two notations for one map.
5. Only then test completed-zeta data.

Falsifiers:

- a persistent obstruction for a fixed finite free differential embedding;
- a global obstruction with a uniformly tame compatible right inverse at every scale;
- two obstruction chains with identical classes in `(4)` but inequivalent multiplicity spectra;
- a self-dual degeneracy spectrum whose support depends on a choice of local splitting;
- a fourth boundary phase outside rank, map, and completion.

Every no-go has a positive successor:

- failure of the trichotomy produces a new fourth phase;
- failure of positivity equivalence isolates a genuinely order-theoretic obstruction not detected
  by derived descent;
- failure of monodromy conservativity produces a higher nonabelian splitting invariant;
- failure of the zeta identification still leaves a general HT realization theory with its own
  classification theorem.

## Gates

- [x] 0 -> 1: object, finite theorem, conjectures, parent theories, attack, and falsifiers stated
- [ ] 1 -> 2: construct the stack and prove conservative splitting-tower completeness and descent
- [ ] 2 -> 3: formalize finite inverse systems, torsor descent, and the self-dual fixed object
- [ ] 3 -> 4: specialist novelty validation and a nontrivial analytic/arithmetic realization

## Log

- 2026-07-15 -- opened after finite-embedding incompressibility killed any pointwise conductor as
  the growing universal obstruction; replaced it with the compatibility stack of affine local
  splittings.
