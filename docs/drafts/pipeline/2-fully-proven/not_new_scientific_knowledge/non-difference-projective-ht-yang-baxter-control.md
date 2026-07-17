# A non-difference Yang--Baxter family carries intrinsic projective HT but violates positive-metric unitarity

- **ID:** `non-difference-projective-ht-yang-baxter-control`
- **Stage:** 2-fully-proven / not_new_scientific_knowledge
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
A provisional attempt to transport a physical `S(0)=-P` family to an identity-anchored quantum
matrix has been downgraded to
`../../0-backlog/two-state-fermionic-zero-intrinsic-mixing-rigidity.md`.  The positive-unitary,
intrinsically mixing `O(N)` S-matrix with fermionic zero shows that the operator-algebraic
scattering / spin-chain quantum-`R` convention must be derived, not inferred from a tensor flip.
Until that benchmark is reproduced, neither the proposed two-state no-go nor a move to at least
three internal states is established.

## Lean boundary

No Lean edit is justified.  The Yang--Baxter theorem is imported from the published
classification; the remaining arguments are finite matrix specialization and analytic physical
gates.  Existing HTGeometry projective tomography already formalizes the reusable finite quotient
structure.  A wrapper around this unphysical control would add no new unconditional theorem
surface.

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
- [ ] physical convention map and positive-unitary slice extracted from the full nonregular `4 x 4` classification
- [ ] physical intrinsically mixing projective-HT S-matrix
- [ ] compact-local QFT reconstruction
