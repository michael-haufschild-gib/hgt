# Hypertranscendental differential pseudodivisors and finite-depth noncompression

- **ID:** `hypertranscendental-differential-pseudodivisor-prolongation`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT THEOREM / CONJECTURAL CROSS-FAMILY LOCALIZATION THEORY
- **Scientific status:** `[TRIPTIC THEOREM PROVED FROM EXISTING PARENTS]`
  `[ALGEBRAIC NONCOMPRESSION LEAN-FORMALIZED] [GENERAL PRINCIPLE CONJECTURAL]`
  `[NOVELTY PROVISIONAL] [SIGNIFICANCE HIGH IF CROSS-FAMILY] [NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/triptic-orbit-residue-reciprocity.md`
  - `../2-fully-proven/new_scientific_knowledge/irrational-elliptic-gamma-pointed-bi-anomaly-fracture.md`
  - `hypertranscendental-capacity-descent-postnikov-tower.md`
  - `hypertranscendental-normalization-horizon-uniformization.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/DifferentialOrbitMarkerLocalization.lean`
- **Statement:** In the irrational triptic HT quotient, the ordinary orbit divisor is the
  degree-zero quotient of a free differential pseudodivisor.  Every fixed finite
  principal-part depth misses an explicit nonzero HT class, while the cofinal all-order marker is
  complete modulo DA.  Gamma proves that this is only the **singular chart** of the obstruction
  object: the full source fibre is an extension by regular normalization inertia.  Reconstruction
  requires a transverse selector on that regular sector, not more data derived from the source.

## Decisive source correction

A bare source, even with one regular pointing, does not canonically reconstruct its solution.
The pair

```text
Gamma(z),  exp(2 pi i z) Gamma(z)
```

has the same unit-shift source and pointing, and periodic gauges can preserve every prescribed
finite jet.  For reporters `R_r`, the maximal reconstruction theorem is

```text
Obs_R injective
  iff K^S intersect intersection_r ker R_r = {0}.           (1)
```

Therefore no divisor, gerbe, completion, transport, or polarization obtained only by
postprocessing the same forgotten source can manufacture a preferred germ.  The object below does
not try to do so.  It classifies a pointed **DA-relative class** on the source-effectively
normalized stratum, and retains its residual common kernel as inertia.

## The exact triptic differential thickening `[PROVED]`

For the irrational triptic class, put

```text
Q={F meromorphic : Delta_1 F=0, Delta_tau Delta_sigma F is constant},
M_DA=Q intersect Mer_DA,
G=C/(Z+Z tau+Z sigma).
```

The triptic orbit-residue theorem gives an isomorphism of differential translation modules

```text
R_trip : Q/M_DA  ~=  A:=C[delta][G].                        (2)
```

The basis element `[g]` is one orbit point on the thin rank-three quotient.  Its differential
prolongation is

```text
C[delta][g]={P(delta)[g] : P in C[delta]}.                  (3)
```

Thus one support atom carries an unbounded free differential tower.  This is an exact realization
of

```text
infinite differential-algebraic capacity
concentrated on a finitely supported constraint boundary.   (4)
```

No evolution or time variable is involved.  The capacity is the free action of the differential
operator algebra on a thin orbit marker.

## Ordinary divisor as the degree-zero shadow `[PROVED]`

Let

```text
epsilon_0 : C[delta][G] -> C[G],
epsilon_0(sum_g P_g(delta)[g])=sum_g P_g(0)[g].              (5)
```

Then multiplication by `delta` and `(5)` form the exact sequence

```text
0 -> A --delta--> A --epsilon_0--> C[G] -> 0.               (6)
```

Transport through `(2)` gives

```text
0 -> delta(Q/M_DA) -> Q/M_DA -> C[G] -> 0.                 (7)
```

On a logarithmic derivative, the degree-zero coefficient is the simple residue and hence the
ordinary zero/pole multiplicity.  For the standard elliptic-gamma wedge, the FHRZ pseudodivisor of
the meromorphic gerbe section maps under `dlog` to the degree-zero theta boundary atom.  This is a
pointed standard-frame comparison; it is not yet a global identification of the FHRZ gerbe with
the full module `(2)`.

Equation `(7)` is the decisive no-go and positive successor:

```text
[NO-GO]
An ordinary divisor, pseudodivisor, or unpointed gerbe class is conservative for Q/M_DA.

[POSITIVE]
Its information loss is exact and one-generated: the invisible fibre is precisely the
differential prolongation ideal delta A.  The full invariant is the minimal all-order
differential thickening of the divisor shadow in this class.                 (8)
```

## Finite-depth noncompression `[PROVED; ALGEBRA LEAN-FORMALIZED]`

For `n>=0`, let

```text
J_<n : A -> (direct sum_(0<=k<n) C[G])
```

retain only the coefficients of `1,delta,...,delta^(n-1)`.  Coefficientwise polynomial division
gives

```text
ker J_<n = delta^n A.                                      (9)
```

Consequently, for every finite depth `n` and every `g in G`,

```text
delta^n[g] != 0 in A,       J_<n(delta^n[g])=0.             (10)
```

Via `(2)`, the analytic representative `delta^n Psi_g` is hypertranscendental modulo DA and is
invisible to every boundary reporter which retains only principal-part orders below `n+1`.
Nevertheless every element of `A` has finite support and finite polynomial degree, so every
nonzero class is detected at some finite depth:

```text
intersection_n ker J_<n = {0},
but ker J_<n != {0} for every fixed n.                      (11)
```

This is nonuniform cofinal conservativity.  No universal finite principal-part depth classifies
the triptic HT quotient, but the full tower does, and every individual class appears at a finite
stage.

The Lean theorem is slightly stronger at marker level.  An additive coefficient reporter can only
enlarge translation stabilizers; an injective reporter preserves them exactly; and two reporters
recover the exact stabilizer whenever their paired coefficient map is injective.  For polynomial
labels Lean proves:

```text
ker(polynomialJetReporter n)=X^n C[X];
every finite depth kills the aperiodic atom X^n[x];
every nonzero finite marker is detected at some finite depth;
the all-coefficient reporter preserves the exact stabilizer;
ker(divisorShadow)=image(X-shift).                          (12)
```

Thus the common-kernel theorem `(1)` and the triptic principal-part tower are instances of one
exact information-loss law rather than an analogy.

The same Lean module proves the regular complement used by the Barnes test:

```text
entire + periods (1,tau), Im(tau)>0  -> constant;
the same hypotheses + one value 1   -> identically 1.      (12a)
```

These are `analyticOnNhd_constant_of_period_one_tau` and
`analyticOnNhd_eq_one_of_period_one_tau_of_pointed`.

## `[CONJECTURE -- REGULAR-SINGULAR DIFFERENTIAL DESCENT PRINCIPLE]`

For every source-localizable regular constrained HT class, after quotienting the admissible DA
gauge, there is a presentation-invariant source-face object

```text
PDiff_S([F])
```

The Barnes derived-fracture theorem sharpens the status of this object.  `PDiff_S` is the
marker-level shadow of a DA-relative characteristic module, not by itself the full topology.  The
full invariant must retain its differential Rees filtration and minimal source-face resolution;
otherwise it cannot distinguish unbounded capacity from homological fracture amplitude.

with the following properties.

1. It is a finitely supported sheaf or cosheaf of modules over the source differential-operator
   algebra; finite support is measured on source-orbit or source-face quotients, not on the
   analytic plane.
2. Its ordinary divisor or topological charge is the degree-zero Koszul/augmentation shadow.
3. Higher differential principal parts are genuine prolongation layers, not decorations; their
   cofinal family is conservative on the DA-relative class.
4. Typed face restrictions satisfy an integrability/descent law.  Failure of this law is the
   continuation or production obstruction; residual common kernels are normalization inertia.
5. Polarization, spectral completion, monodromy, and integral realization are functors of the
   same differential pseudodivisor object.  They need not be individually conservative, but a
   specified family must satisfy the common-kernel and stable-range gates.
6. The singular object classifies the HT/DA superselection class only modulo its regular
   source-fixed inertia `G_reg`.  The full obstruction datum is the extension

   ```text
   0 -> G_reg -> G_source -> PDiff_S -> 0
   ```

   together with a transverse normalization on `G_reg` and the compatibility class gluing the two
   sectors.  It does not and cannot canonically choose an analytic representative from a bare
   source.

The conjecture says what constrains this class of hypertranscendental functions: not an additional
finite differential equation, but the coupling of a thin singular characteristic boundary carrying
an infinite differential prolongation to a regular normalization fibre.  Global integrability,
descent, orientation, and stable realization are properties of this coupling, not of either factor
alone.

## Where to look next

The next theorem must not be another categorical wrapper.

### 1. Unit-shift Gamma test `[SINGULAR SECTOR PASSED; FULL RECONSTRUCTION FAILED]`

The singular differential marker of `dlog Gamma` is the free `C[delta]` prolongation of the unit
pole orbit modulo DA.  But even the **all-order** principal-part tower is nonconservative on the
full source fibre.  If `p` is entire, nowhere zero, and `1`-periodic, then

```text
F(z)=Gamma(z),                 G(z)=p(z)Gamma(z)
dlog G-dlog F=p'(z)/p(z).
```

The difference is entire, so every singular principal-part reporter agrees.  The special choice
`p(z)=exp(2 pi i z)` gives the pointed counterexample in the source correction.  More generally,

`h_n(z)=(exp(2 pi i(z-1))-1)^(n+1)`

produces a nontrivial periodic gauge preserving the pointing and every jet through order `n`.
Thus neither finite normalization nor complete singular localization reconstructs Gamma from its
bare source.

The positive theorem is exact.  On global unit-shift solutions, the kernel of the full principal-
part reporter on logarithmic gauge derivatives is precisely the regular periodic unit sector:

```text
G_reg={p'/p : p entire, nowhere zero, 1-periodic}.
```

Indeed, equality of all principal parts makes `p'/p` entire; then `p` has neither zeros nor poles.
Every such unit has the form

`p(z)=exp(2 pi i m z+h(z))`,  `m in Z`, `h` entire and `1`-periodic,

so its logarithmic derivative is `2 pi i m+h'`.  Therefore the full singular marker becomes
injective exactly after quotienting this regular inertia, and any transverse normalization `R`
completes reconstruction exactly when `R|G_reg` is injective.  This is the common-kernel theorem
applied after the singular quotient, not an appeal to a canonical Gamma representative.

The nonlinear Bohr--Mollerup/cofinal convexity horizon is a genuinely independent transverse
normalization and kills this regular sector on its admissible stratum.  The still-open comparison
problem is to express that selector as a natural gluing law with the singular differential module,
without storing the Gamma germ itself.

### 2. Barnes nontriptic test `[PASSED FOR THE DA-RELATIVE SINGULAR MODULE]`

For rationally independent Barnes periods, the full constant-coefficient differential-translation
annihilator is

```text
Ann_DA^diff(Psi_N)=(prod_j(T_j-1))
```

inside `C[delta,T_1^(+-1),...,T_N^(+-1)]`.  Hence the cyclic HT/DA module is

```text
C[delta,T_1^(+-1),...,T_N^(+-1)]/(prod_j(T_j-1))
  ~= (C[T_1^(+-1),...,T_N^(+-1)]/(prod_j(T_j-1)))[delta].
```

This is a free differential cylinder over the reduced union of source faces `T_j=1`.  It is not an
elliptic-gerbe restatement: `N=1` recovers the Gamma `C[delta]` atom, and arbitrary `N` gives a
squarefree reducible characteristic boundary.  The proof uses the Barnes ladder plus differential
algebraic independence of scaled-digamma translates to exclude hidden mixed differential-
translation cancellations.

The full alternating complex of restrictions to intersections of these source faces is exact.
Thus compatible face data glue uniquely modulo the Barnes annihilator and there is no higher
singular kinematic cohomology, despite unbounded differential capacity on every component.  This
proves that capacity depth and descent-obstruction height are independent axes of the HT object.

The derived restriction is even sharper.  Writing the characteristic product as `p_j x_j`, the
two factor multiplications form an exact matrix factorization on the Barnes module.  Restriction
to every nonempty face `S` is `[B_S -> B_S]` with zero differential, so its only Tor groups are two
identical copies of `B_S` in degrees zero and one.  Deeper faces do not create deeper fracture.
This normal-crossing algebra is Lean-formalized in `NormalCrossingFaceMatrixFactorization.lean`.

The regular sector has a sharp rank transition.  If two rationally independent periods are
collinear, their subgroup is nondiscrete and every fixed meromorphic gauge is constant.  If they
span a lattice, equality of full logarithmic principal parts makes the gauge an entire nowhere-zero
doubly periodic function, hence constant.  One regular pointing then kills the scalar.  Therefore
for Barnes rank at least two, the source, full singular marker, and one pointing are jointly
conservative on the top meromorphic fibre.  This is a genuine positive reconstruction theorem;
rank-one Gamma is the exceptional nonconservative phase.

### 3. Stable realization test

Complete the differential pseudodivisor in a source-forced bornology and compute whether its
reporter is exact-blind, approximate-blind, or stably conservative.  The compact-source
observability wall proves that a compact finite-window realization cannot be stably conservative
on an infinite-dimensional prolongation.  A positive theorem must construct either a natural
noncompact transverse channel or a nonlinear cofinal selector.

## Novelty gate

The following are parent mathematics and are not novelty claims:

- the polynomial exact sequence `0 -> X C[X] -> C[X] -> C -> 0`;
- principal parts, residues, divisors, jet bundles, logarithmic jet differentials, and `D`-modules;
- orbital and panorbital residues as complete summability obstructions on one elliptic curve;
- parameterized difference Galois criteria for hypertranscendence;
- the FHRZ gamma gerbe, its meromorphic section, and its pseudodivisor realization;
- common-kernel conservativity and stabilizer monotonicity under postprocessing.

Primary threats checked include Felder--Henriques--Rossi--Zhu,
`https://arxiv.org/abs/math/0601337`; Arreche--Babbitt,
`https://arxiv.org/abs/2508.18247`; Adamczewski--Dreyfus--Hardouin,
`https://arxiv.org/abs/1910.01874`; and Campana--Darondeau--Demailly--Rousseau on logarithmic and
orbifold jet differentials, `https://arxiv.org/abs/2109.00764`.

The current algebraic Lean theorems are a bridge, not new science by themselves.  The triptic
finite-depth noncompression theorem is a substantive corollary of the candidate-new reciprocity
and completeness theorem, and belongs in that paper.  It does not yet warrant a separate paper.

The candidate-new general content is the source-presentation-invariant differential
pseudodivisor construction, a cross-family descent theorem, and a comparison proving that two
independently built obstruction receivers are conservative images of it.  Targeted searches found
the ingredients separately but no theorem with those properties.  This is provisional absence
evidence, not a priority certificate.

## Anti-theatre and Fields gate

Kill or demote the principle if any of the following occurs.

1. `PDiff_S` is just the principal-parts sheaf or a standard `D`-module with new terminology.
2. The construction stores the target germ or divisor and then claims to reconstruct it from the
   source.
3. The Barnes test produces no natural object beyond classical multiple-gamma divisor formulas.
4. The comparison with a second receiver is only equality of dimensions, supports, or zero sets.
5. Presentation changes alter the prolongation filtration or its descent class.
6. A finite principal-part reporter is claimed complete despite the explicit classes `(10)`.

Every kill has a positive successor: identify the exact quotient retained by the parent theory,
compute its residual prolongation kernel, and state the maximal source-effectively normalized
stratum on which it is conservative.

```text
Current verdict:
  triptic noncompression = strong paper-level consequence, not Fields-scale alone;
  Barnes characteristic module + exact face factorization = candidate-new paper theorem;
  presentation-invariant characteristic-resolution field = Fields-scale target;
  terminology without the Gamma/Barnes comparison theorem = theatre.        (13)
```

## RH pressure test only

A proposed RH obstruction object which factors through one fixed finite principal-part depth
cannot be conservative on an unbounded differential prolongation.  This does not show that any
particular RH proof fails, and it says nothing about the location of zeta zeros.

The research hypothesis is narrower: if the completed-zeta source has a source-pure differential
pseudodivisor realization, then spectral incompleteness, continuation failure, positivity failure,
monodromy, and noncanonical boundary conditions may be different truncations or realizations of
its self-dual descent defect.  The critical zeros could be its common degeneracy spectrum only
after that source-pure object and jointly conservative realization maps are constructed without
using the zero divisor as input.

## Gates

- [x] bare-source reconstruction no-go incorporated
- [x] ordinary divisor/gerbe finite-information no-go isolated
- [x] exact positive differential-prolongation sequence proved in the triptic quotient
- [x] finite-depth noncompression and cofinal detection proved
- [x] algebraic stabilizer and kernel laws Lean-formalized
- [x] FHRZ, orbital-residue, parameterized-Galois, and jet-differential parents identified
- [x] standalone-paper overclaim rejected
- [x] construct and compute the DA-relative unit-shift Gamma singular module
- [x] prove the full Gamma principal-part tower is blind exactly to regular periodic unit inertia
- [ ] glue the Gamma singular module to the nonlinear normalization horizon
- [x] pass the Barnes nontriptic singular-module test
- [x] compute and Lean-formalize the exact Barnes two-periodic derived face fracture
- [x] compute the Barnes regular inertia and prove its rank-two pointed collapse
- [ ] prove presentation invariance under source changes
- [ ] construct two independently defined conservative realization functors
- [ ] complete independent specialist novelty audit
