# Squarefree coface constraints have a codimension-two reconstructing boundary complex

- **ID:** `multiple-elliptic-gamma-codimension-two-boundary-reconstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM / ABSTRACT CONSTRAINT ALGEBRA / CONDITIONAL HT ARCHITECTURE TEST
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED ALGEBRAIC CORE] [MEG APPLICATION OPEN]`
- **Parents:**
  - `../new_scientific_knowledge/all-order-multiple-elliptic-gamma-structural-differential-matroid.md`
  - `../new_scientific_knowledge/multiple-elliptic-gamma-transverse-constraint-depth.md`
  - `../../1-in-progress/source-anomaly-boundary-colligation-field.md`
- **Statement:** For every `r >= 1`, the localized squarefree coface ideal `I_r` is reconstructed by
  a length-two perfect boundary complex. Its Betti ranks are `(1,r+1,r)`, its maximal boundary
  minors are exactly the `r+1` squarefree face generators, and it has no higher syzygies. Applying
  this complex to the genuine multiple elliptic-gamma differential matroid is conditional on the
  still-open nonlinear order-one atomicity and all-order exact-matroid identification.

## 1. The exact constraint ring

Put `n=r+1`, let `F=C(delta)`, and write

```text
A=F[t_0^(+-1),...,t_r^(+-1)],
x_i=t_i-1,
m_i=product_(j != i)x_j,
I_r=(m_0,...,m_r).
```

Equivalently, `A` is the localization of `F[x_0,...,x_r]` obtained by inverting every
`1+x_i`. Everything proved below is an unconditional theorem about `I_r` and `A/I_r`. The
proposed identification of `I_r` with the complete structural annihilator of the genuine multiple
elliptic-gamma family is not an input to the Lean theorem and remains open: the current
elliptic-gamma code proves `C[delta]`-linear freeness of separated bottom defects, not their
nonlinear `DifferentialIndependent` property.

The theorem below therefore concerns the complete dependence algebra of the abstract squarefree
coface model. Its analytic special-function interpretation is conditional.

## 2. Boundary matrix

Let `H_r:A^r -> A^(r+1)` be

```text
H_r(b_1,...,b_r)
  =(-x_0 sum_(i=1)^r b_i, x_1 b_1,...,x_r b_r).          (1)
```

Let `M_r:A^(r+1)->A` be

```text
M_r(a_0,...,a_r)=sum_(i=0)^r a_i m_i.                    (2)
```

Since `x_i m_i=product_j x_j` for every `i`, equations `(1)` and `(2)` give

```text
M_r H_r=0.                                                (3)
```

The columns of `H_r` are the elementary boundary seams

```text
x_i e_i-x_0 e_0,          1<=i<=r.                       (4)
```

## 3. Complete syzygy theorem `[PROVED]`

The sequence

```text
0 -> A^r --H_r--> A^(r+1) --M_r--> A -> A/I_r -> 0       (5)
```

is exact.

### Proof

The image of `M_r` is `I_r`, and `(3)` gives `im(H_r) subset ker(M_r)`. Suppose

```text
sum_(i=0)^r a_i m_i=0.                                   (6)
```

Fix `i>=1` and reduce `(6)` modulo `(x_i)`. Every `m_j` with `j != i` vanishes, while `m_i`
does not. The quotient `A/(x_i)` is a domain: it is the corresponding Laurent localization of a
polynomial ring in the remaining variables. Hence `a_i m_i=0` in that quotient forces

```text
a_i=x_i b_i                                               (7)
```

for some `b_i in A`. Substituting `(7)` in `(6)` and using `x_i m_i=x_0m_0` gives

```text
m_0(a_0+x_0 sum_(i=1)^r b_i)=0.
```

The ring `A` is a domain and `m_0 != 0`, so

```text
a_0=-x_0 sum_(i=1)^r b_i.
```

Thus `(a_0,...,a_r)=H_r(b_1,...,b_r)`, proving exactness at `A^(r+1)`. Finally,
`H_r(b)=0` gives `x_i b_i=0` in every coordinate `i>=1`; the domain property gives `b_i=0`.
Therefore `H_r` is injective. `QED`

## 4. Reconstruction by maximal minors `[PROVED]`

Delete row zero of the `(r+1) by r` matrix of `H_r`. The remaining matrix is diagonal, so its
determinant is

```text
product_(i=1)^r x_i=m_0.                                 (8)
```

If row `k>=1` is deleted, expansion in column `k` leaves `-x_0` times the diagonal product over
`i != 0,k`. Hence that maximal minor is

```text
unit * x_0 product_(i != 0,k)x_i=unit * m_k.             (9)
```

Consequently the maximal minors of `H_r` generate exactly `I_r`. The boundary map reconstructs
the full abstract squarefree coface ideal. If the open analytic theorem later identifies `I_r`
with the exact elliptic-gamma structural annihilator, this same matrix will reconstruct that
annihilator and its associated linear matroid.

This is a genuine object-level statement about the algebraic model. The boundary matrix is not
merely compatible with the chosen generators; its maximal minors recover all of `I_r`.

## 5. Homological depth `[PROVED]`

Localize at the maximal ideal `(x_0,...,x_r)`. Every entry of `H_r` and `M_r` lies in that maximal
ideal, so `(5)` is minimal there. Therefore the local Betti ranks are

```text
beta_0=1,       beta_1=r+1,       beta_2=r,               (10)
beta_j=0 for j>2.                                         (11)
```

In particular `A/I_r` has projective dimension exactly two. Equivalently, the squarefree
constraint is perfect of codimension two. This also follows from the prime decomposition

```text
I_r=intersection_(a<b)(x_a,x_b)
```

together with `(5)`.

## 6. Architecture consequence

The abstract squarefree coface hierarchy falsifies the algebraic principle

```text
more face directions => higher homological amplitude.                      (12)
```

There are arbitrarily many face directions in the algebraic model, but its resolved constraint
object has no homology above degree two. The corresponding claim for the complete actual
elliptic-gamma dependence object remains conditional on the missing exact-matroid theorem.

**Positive replacement.** The relevant measure of thinness is not the number of jet observables,
the number of face constraints, or the visible depth of the hierarchy. It is the amplitude and
rank profile of the minimal source-boundary complex. For this family the amplitude is uniformly
two, while the boundary multiplicity grows linearly as `(r+1,r)`.

This separates two axes:

```text
coface multiplicity:      arbitrarily many squarefree generators;
constraint complexity:    perfect boundary amplitude two.                 (13)
```

## 6a. Lean formalization

The formalization is split between
`formal/GaloisForLFunctions/HTGeometry/SquarefreeVeroneseIdeal.lean` and
`formal/GaloisForLFunctions/HTGeometry/CofaceBoundaryReconstruction.lean`. Together they contain:

- `cofaceMonomial`, `cofaceRelation`, and `cofaceBoundary`;
- `cofaceRelation_boundary`, proving `M_r H_r=0`;
- `cofaceRelation_eq_zero_iff`, proving that every face-monomial relation is a boundary;
- `cofaceBoundary_injective`, proving that the boundary presentation has no higher syzygy.
- `range_cofaceRelation`, proving that the image of `M_r` is exactly `I_r`;
- `cofaceBoundaryMaximalMinor_zero` and `cofaceBoundaryMaximalMinor_succ`, computing every signed
  maximal minor;
- `cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal`, proving that those minors reconstruct `I_r`;
- `cofaceOrigin_boundaryMatrix` and `cofaceOrigin_cofaceMonomial`, proving origin-minimality for
  every positive order;
- `cofaceBoundaryComplex_bettiRanks`, proving the free-rank profile `(1,r+1,r)`;
- `cofaceBoundaryResolutionCertificate`, packaging exactness, absence of higher syzygies,
  maximal-minor reconstruction, minimality, and the Betti ranks for every `r>0`.

The new module passed its exact targeted build when its cache artifact was absent, followed by a
direct Lean verification. After the final image theorem was added, the touched source again passed
direct Lean verification against cached dependencies. No full build was run.

## 7. Bold successor conjecture

**[CONJECTURE — PERFECT BOUNDARY RECONSTRUCTION]** A regular finite-source constrained
hypertranscendental germ has a source-canonical perfect boundary complex `C_x`, defined before any
degeneracy set, such that:

1. the Fitting supports of `C_x` are exactly its finite-observable differential-dependence strata;
2. the complete source anomaly and boundary self-symbol are the first differential and extension
   data of `C_x`;
3. source-equivalent analytic presentations yield quasi-isomorphic calibrated complexes;
4. the analytic source germ is reconstructed, up to source equivalence, from `C_x` together with
   its critical bornology, affine calibration, and polarization.

The theorem above proves the exact codimension-two algebraic model: `C_x` is `(5)`, its Fitting
ideal is `I_r`, and its first boundary map reconstructs the squarefree coface ideal. Showing that
this is the complete nonlinear structural matroid of an actual HT family is part of the conjectural
analytic realization step, not part of the Lean certificate.

This conjecture is substantially stronger than saying that a constraint has a resolution. It
asserts source-canonicity, analytic presentation invariance, and reconstruction of the constrained
HT germ. Those are the open parts capable of supporting a new Riemann--Hilbert-type theory.

## 8. Unified-obstruction interpretation `[CONJECTURE]`

For a reflected parameterized source, suppose `C_x` has a source-defined self-dual polarization.
Then the common obstruction object should be the derived moduli of polarized analytic
realizations of `C_x`:

1. continuation failure is failure to extend a realization;
2. boundary ambiguity is nonuniqueness of extensions;
3. monodromy is holonomy of the realization torsor;
4. spectral incompleteness is homology after analytic realization;
5. positivity failure is failure of the reflected Hermitian orientation.

The exact theorem prevents this from being pure vocabulary at the algebraic-model level: there is
a canonical finite complex whose maximal minors recover the entire squarefree coface ideal. Its
identification with the complete multiple-elliptic-gamma dependence ideal, the five-face
comparison, and analytic reconstruction remain conjectural.

## 9. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta source would have to produce a prime--archimedean perfect
boundary complex independently of `xi`, its zeros, or a zero-indexed operator. The different RH
proof chains could represent one object only if their complexes are source-matched realizations
preserving calibration, boundary maps, bornology, reflection, and polarization. Critical zeros
would then be the fixed-locus degeneracy support of that self-dual complex.

No such zeta complex or cross-chain equivalence is proved here.

## 10. Parent-theory and anti-theatre gate

- Hilbert--Burch resolutions, squarefree Veronese ideals, Fitting ideals, and perfect complexes are
  established commutative algebra. They are `[SEARCH]`, not discoveries.
- The exact sequence `(5)` is an explicit specialization of that parent theory.
- The candidate scientific content is conditional on an all-order multiple-elliptic-gamma
  exact-matroid theorem that is not yet proved: only then would the complete nonlinear
  differential dependence geometry of every order be reconstructed by this uniform
  codimension-two boundary complex.
- The Fields-level claim is the successor reconstruction correspondence, not the existence of a
  free resolution.

The formalized algebraic result is a Hilbert--Burch specialization and fails the novelty gate in
isolation. It could become a significant structural theorem only if the missing analytic
exact-matroid identification is proved and bounded boundary amplitude changes the expected
geometry of constrained HT sources beyond this hierarchy.

## Gates

- [x] generate and attack distinct state, curvature, and perfect-complex architectures
- [x] prove complete syzygy classification
- [x] prove reconstruction by maximal minors
- [x] prove uniform projective dimension two
- [x] state the exact higher-curvature no-go and positive successor
- [x] formalize the algebraic exact-complex theorem in Lean
- [ ] prove nonlinear differential independence of the actual bottom-face defects
- [ ] identify the genuine all-order multiple elliptic-gamma structural matroid with `A/I_r`
- [ ] run exact/equivalent/stronger/mechanism literature searches
- [ ] test a non-simplicial non-Gamma constrained HT source
- [ ] prove source-presentation invariance in one analytic class
- [ ] prove analytic-germ reconstruction in one nontrivial class
