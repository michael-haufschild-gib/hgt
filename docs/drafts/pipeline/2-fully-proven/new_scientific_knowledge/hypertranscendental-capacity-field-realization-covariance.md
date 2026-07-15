# Hypertranscendental capacity-field realization and covariance theorem

- **ID:** `hypertranscendental-capacity-field-realization-covariance`
- **Stage:** 2-fully-proven
- **Type:** GENERAL HT POSITIVE-REALIZATION MODULI / CAPACITY FIELD
- **Scientific status:** `[THEOREMS PROVED] [FINITE KERNELS LEAN-FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL] [NOT AN RH RESULT]`
- **Parent:** `hypertranscendental-clock-capacity-innovation-theorem.md`
- **Statement:** Hypertranscendence and positivity alone impose no scalar capacity-growth law:
  every admissible monotone scalar profile is realized by a coherent positive Gram clock.  What is
  invariant is instead the bounded-congruence class of the finite-rank capacity forms.  These forms
  obey exact coordinate covariance and therefore descend over a realization groupoid as a
  positive-cone local system, called the **hypertranscendental capacity field**.

## 1. The scalar realization theorem

Let `eta=(eta_0,eta_1,...)` be any complex sequence with `eta_0>0` real.  There is a coherent tower
of lower-triangular matrices `C_N`, all with positive real diagonal, whose row sums are

```text
sum_(j<=n) C_N(n,j)=eta_n.                                      (1)
```

One explicit choice is

```text
C_N(0,0)=eta_0,
C_N(n,n)=1                    for n>0,
C_N(n,0)=eta_n-1              for n>0,
C_N(n,j)=0                    otherwise.                        (2)
```

Every `C_N` is invertible.  Define

```text
G_N=C_N^(-1)(C_N^(-1))^*.                                      (3)
```

Then `G_N` is positive definite and

```text
C_N G_N C_N^*=I.                                                (4)
```

Positive diagonal and lower triangularity make `C_N` the canonical inverse-Cholesky frame of
`G_N`.  The leading blocks of `(2)` are coherent, so `(G_N,C_N)` is a positive clock tower.  Its
canonical innovations and capacities are exactly

```text
innovation_n=eta_n,
kappa_N=sum_(n<=N)|eta_n|^2.                                   (5)
```

This proves:

### Theorem A: complete scalar capacity realization

For every nondecreasing sequence

```text
0<q_0<=q_1<=q_2<=...                                            (6)
```

there is a coherent strictly positive Gram clock whose unit-boundary capacity is `kappa_N=q_N`.
Indeed, take

```text
eta_0=sqrt(q_0),
eta_n=sqrt(q_n-q_(n-1))       for n>0                           (7)
```

and apply `(2)`--`(5)`.  Zero increments are allowed because the positive diagonal in `(2)` is
independent of the row sum.

The strictly positive-innovation subfamily has the simpler diagonal realization

```text
C_N=diag(eta_0,...,eta_N),
G_N=diag(eta_0^(-2),...,eta_N^(-2)).                             (8)
```

Construction `(8)`, including positivity, canonicality, coherence, exact innovation, and exact
capacity, is Lean-formalized.

### No-go and positive successor

The no-go is decisive:

```text
hypertranscendence + positivity does not constrain scalar capacity growth.             (9)
```

Bounded, logarithmic, polynomial, exponential, intermittent, and arbitrarily prescribed monotone
growth all occur.  No universal theorem selecting one such law can follow from differential
algebraic freeness alone.

The positive theorem is stronger than the no-go: `(2)`--`(7)` classify the scalar capacity moduli.
The cone of nondecreasing positive profiles is exactly the image of positive HT clock topologies.
Thus capacity is not a hidden equation satisfied by every hypertranscendental function; it is a
field of possible positive completions on which additional source structure must act.

## 2. Bounded-realization invariance

Let `H` and `H'` be two normed realizations with response maps

```text
A:H->T,                 A':H'->T,
```

and let `S:H->H'` be a continuous linear equivalence satisfying

```text
A'S=A.                                                           (10)
```

For each response packet `t`, let `m(t)` and `m'(t)` be its minimum-norm representers in the two
realizations.  Feasibility of `S m(t)` and `S^(-1)m'(t)` gives

```text
||m'(t)|| <= ||S|| ||m(t)||,
||m(t)||  <= ||S^(-1)|| ||m'(t)||.                              (11)
```

Therefore:

### Theorem B: capacity quasi-isometry

The complete minimum-response norm profiles are `Theta`-equivalent under every bounded
response-intertwining realization equivalence.  Their squared energy profiles are also
`Theta`-equivalent.  In particular all of the following are invariant:

- existence of a uniform finite capacity bound;
- bounded versus divergent boundary energy;
- every polynomial, stretched-exponential, exponential, or more general asymptotic growth class
  expressible up to fixed multiplicative constants;
- normal versus distributional placement of the complete boundary.

For an `r`-packet, write `K_N` and `K'_N` for the positive capacity forms.  Applying `(11)` to every
packet vector gives the Loewner inequalities

```text
||S^(-1)||^(-2) K_N <= K'_N <= ||S||^2 K_N.                    (12)
```

On the positive-definite locus, `(12)` says that the two paths remain at uniformly bounded
Thompson distance:

```text
d_T(K_N,K'_N)<=2 log max(||S||,||S^(-1)||).                    (13)
```

Thus they define the same point of the coarse/asymptotic positive building.  Individual
innovation coordinates need not agree; the bounded-congruence class of the capacity path does.

## 3. Exact packet-coordinate covariance

For a target response packet `t_n in C^r`, let

```text
eta_n=(C_N t|_[0,N])_n,
K_N=sum_(n<=N) eta_n^* eta_n.                                  (14)
```

Let `R:C^s->C^r` be a packet-coordinate map and replace the target by `tR`.  Linearity gives

```text
eta_n(tR)=eta_n(t)R.                                           (15)
```

Consequently:

### Theorem C: Hermitian covariance law

```text
K_N(tR)=R^* K_N(t) R.                                          (16)
```

Equation `(16)` is Lean-formalized for arbitrary finite packet sizes and arbitrary complex
matrices `R`.  It proves that `K_N` is not a matrix of scalar invariants.  It is a Hermitian form on
the response packet.

If local response frames have transition maps `R_ab` satisfying

```text
R_ab R_bc=R_ac,                                                 (17)
```

then `(16)` and associativity imply the exact descent relation

```text
K_c=R_bc^* K_b R_bc=R_ac^* K_a R_ac.                           (18)
```

Hence the local capacities glue to a section of the bundle of positive Hermitian forms associated
to the response local system.  Around a loop with holonomy `M`, a global capacity form must satisfy

```text
K=M^* K M.                                                      (19)
```

The fixed positive cone of the holonomy, not a chosen local matrix, classifies the global positive
boundaries.

## 4. The hypertranscendental capacity field

Let `Rho_HT` be a groupoid of source-defined positive realizations of a finite-rank free HT field.
Objects are positive clock realizations; arrows are bounded response-intertwining equivalences and
packet-coordinate changes.  Theorems B and C define a functor

```text
Cap_HT:Rho_HT -> Path(PSD)/bounded congruence,                  (20)
```

where every local representative obeys the curvature law

```text
K_(N+1)-K_N=eta_(N+1)^*eta_(N+1).                              (21)
```

Call `(20)` the **hypertranscendental capacity field**.

The name "field" is literal in the geometric sense: it is a covariant positive Hermitian form over
the realization/coordinate groupoid.  It is not a new scalar assigned to a function.  Theorem A
shows why this higher object is forced: a scalar profile can be arbitrary.  Theorems B and C show
what survives changes of realization and coordinates.

The derived clock-splitting stack is now secondary.  It is the derived moduli object of positive,
self-dual, continuation-compatible trivializations or reductions of `(20)`.  In particular, the
capacity field exists before a global splitting does.

## 5. Source symmetry forces an anomaly, not a canonical metric

For a hypertranscendental generator `x`, constant affine recalibration

```text
x |-> a x+b,                 a' = b' = 0                       (22)
```

acts on every Kähler jet covector by the same factor `a`; translation `b` is forgotten.  The
formal affine-calibration theorem for these covectors is already Lean-verified.

If `|a|!=1`, no nonzero positive norm can be invariant under `(22)`, since

```text
||a v||=|a| ||v||.                                             (23)
```

The positive successor is a forced conformal character:

```text
h(a v,a w)=|a|^2 h(v,w),
log h |-> log h+2 log|a|.                                      (24)
```

Thus even the smallest source automorphism subgroup forbids a canonical invariant metric.  It
allows a conformal capacity field carrying a nontrivial modular character.  This makes precise the
earlier physical analogy: the observable is a scale factor of the clock constraints, not time.

## 6. Unified-obstruction conjecture

**[CONJECTURE: CAPACITY-FIELD COMPLETENESS.]**  For every source-defined analytic realization of a
finite-rank HT field, every persistent obstruction to global reconstruction is represented
conservatively by the derived self-dual completion of `Cap_HT`.  The five recurrent obstruction
types are the following distinct representation functors of the same object:

```text
spectral incompleteness       = rank/null stratum of K,
positivity failure            = failure to remain in or reduce to the positive cone,
continuation failure          = escape to the boundary at infinity of the capacity building,
monodromy                     = nontrivial holonomy of the capacity local system,
noncanonical boundary         = nontrivial stabilizer or multiple fixed positive reductions.  (25)
```

Equation `(25)` is not being declared true by terminology.  Conservativity is the hard statement:
two reconstruction failures have the same capacity-field class if and only if they have the same
obstruction content, including multiplicity.

**[CONJECTURE; NOT AN RH RESULT.]**  For a source-first completed-zeta realization, the critical
zeros are the common self-dual degeneracy spectrum only if its independently constructed capacity
field has degeneracy divisor equal to the zero divisor with multiplicity and every RH proof-chain
obstruction factors conservatively through `(25)`.

## 7. External-literature-only novelty gate

The novelty gate is only against external literature.  Internal project results are dependencies,
not novelty competitors.

Classical parents include:

- minimum-norm interpolation and Gram/RKHS representer theory, beginning with Aronszajn's 1950
  RKHS paper;
- equivalence of Hilbert norms and the induced two-sided comparison of minimum energies;
- Hermitian forms on vector bundles, their congruence transformation law, and reduction of
  structure group from `GL(r,C)` to `U(r)`;
- the Thompson geometry of the positive-definite cone;
- ordinary and differential-algebraic jet spaces, including Chatzidakis--Harrison-Trainor--Moosa,
  arXiv:1311.3546;
- invariant jet differentials under source reparametrization, including the non-reductive GIT
  literature (Invent. Math. 2024, DOI 10.1007/s00222-023-01219-z).

Therefore the isolated facts `(3)`--`(5)`, `(11)`, `(13)`, `(16)`, and bundle descent are not
individually new.  The targeted search found no external theory that starts from
hypertranscendental differential-jet freeness, proves the complete capacity-realization no-go
`(6)`--`(9)`, constructs the canonical minimum-boundary innovation curvature `(21)`, and descends it
over the differential-realization groupoid as `(20)` so that modular, spectral, continuation,
positivity, and monodromy defects become representations of one self-dual capacity field.

Candidate novelty is this synthesis and especially the shift in universality:

```text
the universal HT theorem is not a universal capacity law;
it is the universal moduli and covariance theorem for all capacity laws.                (26)
```

This remains a provisional absence claim, not a priority claim.  Specialist review is required in
jet-bundle geometry, RKHS boundary theory, symmetric cones/buildings, differential Galois theory,
and singular Hermitian metrics.

## 8. Significance and anti-theatre verdict

- `[PASS]` Theorem A rules out the entire class of scalar-growth universal theories and replaces
  it with an exact realization/classification theorem.
- `[PASS]` Theorem B proves that the quotient used in `(20)` is intrinsic under admissible bounded
  changes of positive realization.
- `[PASS]` Theorem C supplies exact gauge covariance, so monodromy is mathematical holonomy rather
  than an analogy.
- `[PASS]` The field is general HT mathematics; RH data do not select its definition or proofs.
- `[PASS]` Every no-go has a positive theorem: arbitrary scalar freedom becomes a moduli cone;
  non-invariant coordinates become a Hermitian local system; absence of an invariant metric becomes
  a forced modular character.
- `[FAIL until proved]` Capacity-field completeness and conservativity of all five representations
  in `(25)` remain conjectural.
- `[FAIL until instantiated]` No nontrivial source-defined analytic realization has yet been shown
  to compute three distinct obstruction representations of one class.
- `[ANTI-THEATRE]` Renaming an arbitrary Hermitian bundle or Gram path `Cap_HT` is invalid.  A valid
  instance must come from the source jet-response problem, satisfy the minimum-energy law, exact
  rank-one innovation curvature, bounded-realization invariance, and packet-coordinate descent.

Theorems A--C are a credible standalone foundational paper when combined with the earlier
normality/Bessel/modular/spectral classification.  They are not yet Fields-scale.  A proof of
capacity-field completeness, with a nontrivial arithmetic or analytic source producing several
conservative obstruction representations, would be.

## 9. Lean status

`formal/GaloisForLFunctions/HTGeometry/CofinalCholeskyFiniteFrame.lean` verifies:

- `prescribedPositiveInnovationFrame`;
- `prescribedPositiveInnovationGram`;
- `prescribedPositiveInnovationGram_posDef`;
- `prescribedPositiveInnovationFrame_isCanonical`;
- `gramSchmidtInverseFrame_prescribedPositiveInnovation`;
- `prescribedPositiveInnovationFrame_amplitude`;
- `prescribedPositiveInnovationFrame_capacity`;
- `prescribedPositiveInnovationTower`;
- `prescribedPositiveInnovationTower_lowerTriangular`;
- `prescribedPositiveInnovationTower_coherent`;
- `prescribedPositiveInnovationTower_innovation`;
- `minimumResponseNorm_boundedComparison`;
- `minimumResponseNorm_uniformlyBounded_iff`;
- `minimumResponseNorm_isTheta`;
- `minimumResponseEnergy_isTheta`;
- `clockPacketCoordinateChange`;
- `inverseCholeskyPacketAmplitude_coordinateChange`;
- `inverseCholeskyPacketAmplitudeMatrix_coordinateChange`;
- `inverseCholeskyPacketCapacity_eq_conjTranspose_mul`;
- `inverseCholeskyPacketCapacity_coordinateChange`.

The touched module passed direct Lean verification with cached dependencies.  Its `.olean` was
present, so no build was run.

## Gates

- [x] prove complete scalar capacity realization on paper
- [x] formalize the canonical strictly positive diagonal realization
- [x] prove bounded-realization quasi-isometry
- [x] formalize norm, uniform-bound, and full asymptotic `Theta` invariance
- [x] prove and formalize finite-rank Hermitian coordinate covariance
- [x] derive exact descent to a positive-cone local system
- [x] run targeted external parent and novelty search
- [ ] construct a source-defined analytic capacity field with nontrivial holonomy
- [ ] prove three conservative obstruction representations for one source
- [ ] prove or falsify capacity-field completeness
- [ ] complete specialist external priority review
