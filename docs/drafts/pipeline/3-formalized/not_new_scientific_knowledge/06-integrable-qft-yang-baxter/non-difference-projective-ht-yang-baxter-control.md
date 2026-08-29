# A non-difference Yang--Baxter family carries intrinsic projective HT but violates positive-metric unitarity

- **ID:** `non-difference-projective-ht-yang-baxter-control`
- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** THEOREM / YANG--BAXTER CONTROL / PHYSICAL NO-GO BOUNDARY
- **Scientific status:** `[PROVED SPECIALIZATION] [NOT A RELATIVISTIC QFT] [NOT NEW AS A CONSTRUCTION]`
- **Scope:** general analytic hypertranscendental clocks in a regular `4 x 4` quantum
  Yang--Baxter family; no RH or distinguished special-function input
- **Parent:** `../needs-audit/projective-wigner-smith-nonabelian-ht-separation.md`
- **Statement:** The regular two-state Yang--Baxter equation admits a projectively HT family whose
  flip-removed channel operator is non-diagonalizable in every constant one-particle basis.  The
  associated braid operator has a nilpotent block that makes positive-metric Hilbert-space
  unitarity impossible, and the two
  independent spectral clocks cannot be reduced to a Lorentz rapidity difference.  Thus
  Yang--Baxter consistency does not obstruct intrinsically mixing projective HT; positivity and
  relativistic covariance do.

## Published arbitrary-function family

Corcoran--de Leeuw Model 1 is the regular quantum `R`-matrix

```text
R(u,v)=
  [1, delta G, delta F, A delta F delta G]
  [0,       0,       1,       A delta G]
  [0,       1,       0,       A delta F]
  [0,       0,       0,               1],                    (1)

delta X=X(u)-X(v).
```

Here `A` is constant and `F,G` are arbitrary analytic functions.  The cited classification proves
the spectral-parameter quantum Yang--Baxter equation and regularity

```text
R(u,u)=P,                                                     (2)
```

where `P` is the tensor flip.  It also proves algebraic braiding unitarity
`R_12(u,v)R_21(v,u)=I`.  That inversion identity is not positive-metric operator unitarity.

Choose `A=0`, choose an analytic HT germ `H` from the already established open general-HT family,
and specialize

```text
F=H,                         G(u)=u.                           (3)
```

No named special function is selected.  Equations `(1)`--`(3)` give

```text
R_H(u,v)=
  [1, u-v, H(u)-H(v), 0]
  [0,   0,           1, 0]
  [0,   1,           0, 0]
  [0,   0,           0, 1].                                  (4)
```

This is an exact specialization of a published arbitrary-function solution, not a newly found
Yang--Baxter matrix.

## Exact projective Kolchin content `[PROVED]`

Fix a regular value `v_0` and use the ordinary differential base `K=C(u)`, enlarged only by the
constant value `H(v_0)`.  The `(1,1)` entry of `(4)` is the constant pivot `1`.  Every entry ratio
belongs to `K<H(u)>`, while the `(1,3)` ratio is

```text
H(u)-H(v_0).                                                  (5)
```

It recovers `H(u)` over the declared base.  Therefore the anchored projective field is exactly

```text
P_(R_H,v_0)=K<H>,                 dtrdeg_K P_(R_H,v_0)=1.       (6)
```

Left multiplication by the constant flip only makes a constant rational recombination of matrix
entries, so the same equality holds for the associated braid family below.  Scalar normalization
cannot remove `(6)`.

## Quantum versus braid convention

The published matrix `(4)` satisfies the quantum Yang--Baxter equation.  Its associated
braid-form operator is

```text
check S_H(u,v)=P R_H(u,v)
              =I+(u-v)E_12+(H(u)-H(v))E_13
              =I+N_H(u,v).                                    (7)
```

For every pair,

```text
N_H(u,v)^2=0.                                                  (8)
```

This convention alignment also exposes a third physical mismatch: regularity of the published
quantum matrix gives `check S_H(u,u)=I`, whereas the Alazzawi--Lechner compact-local intertwiner
theorem requires the physical braid-form scattering matrix to satisfy `S(0)=-P`.  The present
control is not in that zero-rapidity sector.

## Intrinsic mixing without a diagonal basis `[PROVED]`

For a braid-form scattering matrix `S`, the flip-removed channel amplitude is `P S`.  Applied to
`check S_H`, it is precisely the published quantum matrix `R_H`.  Direct multiplication gives

```text
R_H(u,v)^2
  =I+((u-v)+(H(u)-H(v)))(E_12+E_13).                           (9)
```

The added matrix in `(9)` is square-zero and is generically nonzero because `H(u)+u` cannot be
constant when `H` is HT.  Thus `R_H^2` is a nontrivial unipotent matrix and is not diagonalizable.
If `R_H` were diagonalizable, its square would be diagonalizable, a contradiction.  A constant
one-particle gauge `U tensor U` acts on the flip-removed amplitude by similarity, so it cannot
make even one generic member diagonal, let alone the full family.  This is intrinsic channel
mixing in the exact sense excluded by the diagonal local-QFT control.

The associated braid operators `check S_H` happen to commute for different parameter pairs because
all products of the nilpotents in `(7)` vanish.  This is a second correction to loose terminology:
intrinsic mixing does not require a noncommuting braid-rapidity algebra.  Non-diagonalizability of
one flip-removed channel operator is already a basis-invariant certificate.

## The three physical failures are exact

### 1. No positive-metric Hilbert-space unitarity

A unitary operator on a finite-dimensional positive-definite complex inner-product space is
diagonalizable.  The generic braid operator `check S_H=I+N_H` in `(7)` is not.  Therefore no
positive-definite one-particle metric can make it unitary.  Multiplication by a nonzero scalar does
not remove its Jordan block.

This does not contradict the paper's braiding-unitarity identity: the latter is an algebraic
relation between `(u,v)` and `(v,u)`, not the adjoint relation required by a positive-metric
scattering theory.

### 2. No Lorentz difference form, even after reparametrization

Suppose a locally invertible analytic spectral coordinate `rho` made `(4)` a difference family.
Then there would be one-variable analytic functions `a,b` such that

```text
u-v       =a(rho(u)-rho(v)),
H(u)-H(v)=b(rho(u)-rho(v)).                                  (10)
```

Differentiating the first identity in `u` and `v` gives

```text
1=a'(rho(u)-rho(v))rho'(u)
 =a'(rho(u)-rho(v))rho'(v).                                  (11)
```

Thus `rho'` is locally constant and `rho` is affine.  The second identity then says
`H(u)-H(v)` depends only on `u-v`; differentiating while varying the second point forces `H'` to
be constant.  Hence `H` would be affine and therefore DA, contradicting its HT choice.

Massive `1+1`-dimensional Lorentz-invariant two-particle scattering depends on a rapidity
difference.  The published family therefore describes a legitimate non-difference integrable
spectral system, but it cannot be inserted as the desired relativistic factorizing S-matrix.
Crossing and compact-local reconstruction are not reached.

### 3. Wrong zero-rapidity sector for the compact-local theorem

Equation `(2)` implies `check S_H(u,u)=I`, not `-P`.  A scalar normalization changes this to a
scalar multiple of `I`, never to `-P` in dimension two.  Thus even apart from positivity and
Lorentz covariance, this regular quantum-`R` branch does not meet the fermionic zero-rapidity
hypothesis used by the known analytic intertwiner and modular-nuclearity theorem.

## Anti-theatre and novelty gate

1. **An arbitrary function in a Yang--Baxter matrix called a new construction.**  Rejected:
   Corcoran--de Leeuw already prove `(1)` for arbitrary `F,G`.
2. **Braiding unitarity called physical unitarity.**  Rejected by the nontrivial Jordan block in
   `(7)`.
3. **Two spectral clocks called a rapidity difference by reparametrization.**  Rejected by
   `(10)`--`(11)` and HT of `H`.
4. **Matrix entries called intrinsic mixing without a gauge test.**  The Jordan form of
   `check S_H` is not the relevant test; the flip-removed matrix `R_H` is itself
   non-diagonalizable by `(9)`
   and survives every constant `U tensor U` similarity.
5. **A failed physical model discarded as irrelevant.**  The control closes the algebraic
   Yang--Baxter gate and localizes the missing physics to positive-metric `*`-unitarity plus
   Lorentz difference/crossing, rather than integrability itself.

The specialization and its Yang--Baxter property are not new scientific knowledge.  The
projective-Kolchin and physical-boundary synthesis is a potentially useful diagnosis, but it is
not promoted as novel without an independent literature audit.

## Exact surviving core

The next construction problem is strictly smaller than “find an HT `R`-matrix”:

```text
projective HT + Yang--Baxter + intrinsic mixing                 [solved here]
+ Lorentz difference + positive-metric unitarity + crossing     [open]
+ physical zero-rapidity sector S(0)=-P                         [open]
+ compact-local reconstruction                                  [open].       (12)
```

The regular `4 x 4` difference-form classification is not by itself the physical no-go surface.
The complete nonregular classification now proves the fixed-basis two-state no-go on the distinct
adjacent flip-anchor surface in
`../needs-audit/two-state-fermionic-zero-intrinsic-mixing-rigidity.md`.  The positive-unitary,
intrinsically mixing `O(N)` matrix resolves the convention: its physical quantum zero is `-P`, but
its braid conversion has zero `-I`.  The exact theorem
`../needs-audit/fermionic-zero-braid-anchor-commutation-gate.md` proves that an adjacent family
anchored at `-P` becomes an identity-anchored quantum family and is pointwise locally
product-diagonal under positive unitarity.  The classification corollary upgrades this to one fixed
basis, but it still does not yield a no-go for the physical quantum lane or a move to at least three
internal states.

## Lean formalization

Formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/CorcoranDeLeeuwModelOne.lean`,
`formal/GaloisForLFunctions/HTGeometry/UnipotentDiagonalizationObstruction.lean`,
`formal/GaloisForLFunctions/HTGeometry/DifferenceFormReparametrisation.lean`,
`formal/GaloisForLFunctions/HTGeometry/SingleGeneratorDifferentialDegree.lean`, and
`formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveEntryField.lean`.

The Yang--Baxter property is **proved, not imported**.  `modelOneR A f g` is `(1)` over an
arbitrary commutative ring, with `f = delta F` and `g = delta G` free scalars and `A` free; the
identity is established for the whole family, so the published classification is no longer an
input to anything on this card.

- `modelOneBraid_adjacentBraid` proves the adjacent spectral braid equation for the braid form
  `R * P` at the three increment pairs produced by a common pair of clocks at three spectral
  points, which is exactly the non-difference substitution `f_1 + f_3 = f_(uw)`.
- `modelOneR_quantumYangBaxter` transports it to
  `R_12(u,v) R_13(u,w) R_23(v,w) = R_23(v,w) R_13(u,w) R_12(u,v)` on the literal three-particle
  legs, through the corpus's right-flip bridge `rightFlip_adjacentBraid_iff_quantumYangBaxter`.
- `modelOneR_regular` proves `(2)`, `R(u,u) = P`, and `modelOneBraid_regular` proves the braid
  anchor `check S(u,u) = 1`; `smul_one_ne_neg_flip` proves that no scalar multiple of the identity
  is `-P`, which is the exact zero-rapidity mismatch of the third physical failure.
- `modelOneR_braidingUnitarity` proves the algebraic inversion identity
  `R_12(u,v) R_21(v,u) = 1` for every `A`.
- `modelOneBraid_sub_one_sq` proves `(8)`, `N_H^2 = 0`, and `modelOneR_sq` proves `(9)`,
  `R_H^2 = 1 + (delta F + delta G)(E_12 + E_13)` with a square-zero, nonzero increment factor.
- `not_isDiagonalizableMatrix_modelOneR` proves the intrinsic-mixing statement: whenever
  `delta F + delta G` is nonzero, `R_H` is similar to no diagonal matrix at all, so in particular
  no constant one-particle gauge `U tensor U` diagonalizes it.  The mechanism is
  `eq_one_of_isDiagonalizableMatrix_of_sub_one_sq`: a diagonalizable matrix with `(M-1)^2 = 0`
  is the identity.
- `modelOneR_not_metric_isometry` proves the first physical failure, `Q`-unitarity is impossible
  for every positive-definite metric `Q`.  The route is elementary and uses no spectral theorem:
  the invariance identity at `M^2` and at `M^4` differ by exactly the quadratic term, forcing
  `K^dagger Q K = 0`, which positive definiteness forbids.
- `deriv_eq_of_difference_reparametrisation` proves `(10)`--`(11)` on any open set and without
  assuming that `H` is differentiable: the first identity forces `deriv rho` to take one common
  value, and the second transports that to `deriv H`.
  `not_exists_difference_reparametrisation_of_hypertranscendental` is the second physical failure:
  a hypertranscendental clock admits no analytic reparametrization to difference form, because a
  constant derivative makes `H` affine and hence differentially algebraic.
- `differentialAdjoin_pivotEntryFamily_modelOneR` proves `(5)`--`(6)`: after anchoring the second
  spectral parameter, the pivot-normalized entry family generates exactly `K<H>`, and
  `pivotEntryFamily_smul` proves that scalar normalization cannot remove it.
  `anchoredModelOne_projectiveField_degree` adds the degree statement
  `dtrdeg_K K<H> = 1` for a hypertranscendental increment, through the reusable
  `differentialTranscendenceDegree_differentialAdjoin_singleton_eq_one`.

Direct Lean checks and targeted leaf builds passed.  Axiom audit of every capstone above reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Primary literature

- L. Corcoran and M. de Leeuw, *All regular `4 x 4` solutions of the Yang--Baxter equation*,
  <https://arxiv.org/abs/2306.10423>.
- M. de Leeuw and C. Posch, *All `4 x 4` solutions of the Yang--Baxter equation*,
  <https://arxiv.org/abs/2411.18685>.

## Gates

- [x] published regular two-state quantum Yang--Baxter family
- [x] arbitrary analytic function specialized to an open-family HT clock
- [x] anchored projective differential transcendence degree one
- [x] no constant one-particle diagonal reduction
- [x] exact positive-metric unitarity obstruction
- [x] exact no-reparametrization-to-difference proof
- [x] quantum/braid convention and zero-rapidity mismatch isolated
- [x] construction novelty rejected
- [x] exact Lean theorems, targeted leaf builds, and axiom gate; the Yang--Baxter property is
  proved for the whole arbitrary-function family rather than imported
- [x] adjacent/quantum convention map and zero-anchor split proved
- [ ] physical quantum positive-unitary slice extracted from the exact `4 x 4` classification
- [ ] physical intrinsically mixing projective-HT S-matrix
- [ ] compact-local QFT reconstruction
