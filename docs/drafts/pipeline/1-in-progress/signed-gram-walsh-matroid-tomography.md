# Signed-Gram Walsh matroid tomography

- **ID:** `signed-gram-walsh-matroid-tomography`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / FINITE CONSTRAINT GEOMETRY
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED]`
- **Statement:** The determinant response of a finite coefficient Gram form over the complete
  source-orientation cube has Walsh coefficients equal to its weighted squared Pluecker
  coordinates; hence the response cube reconstructs the exposed representable matroid together
  with all basis masses.

## Finite candidate theorem

Let `P` be a finite source set, let `J` be a finite probe set of cardinality `m`, let
`C=(c_(p,j))` be a complex `P`-by-`J` matrix, and let `a_p>0`.  For
`epsilon in {+1,-1}^P`, put

```text
G_epsilon = C^* diag(epsilon_p a_p) C,
D(epsilon) = det(G_epsilon).
```

For an `m`-subset `B` of `P`, write

```text
mu_B = (prod_(p in B) a_p) |det(C_B)|^2,
chi_B(epsilon) = prod_(p in B) epsilon_p.
```

Cauchy--Binet gives the orientation expansion

```text
D(epsilon) = sum_(B subset P, |B|=m) mu_B chi_B(epsilon).   (1)
```

The Walsh inversion formula therefore gives

```text
mu_B = 2^(-|P|) sum_epsilon D(epsilon) chi_B(epsilon).      (2)
```

Thus the full signed determinant cube determines every weighted squared maximal minor.  In
particular it determines which `m`-subsets are bases of the row matroid of `C`, its total basis
mass, and whether `C` has full column rank.

## Geometric interpretation

The all-positive chamber sees only

```text
D(+1)=sum_B mu_B,
```

so it collapses the basis geometry to one scalar.  The complete orientation cube separates the
basis masses exactly.  Orientation and constraint geometry are therefore not independent
factors: the orientation response is a tomographic coordinate system for the constraint
matroid.

For an energy marking, apply the construction to the coefficient matrix restricted to an exposed
face.  Purity recovers the face cardinality, Gram rank recovers the visible dimension, and signed
determinant tomography recovers the complete maximal-basis geometry on that face.

## Product target

For tensor coefficient packets, the response matrices satisfy

```text
G_(epsilon tensor eta) = G_epsilon tensor G_eta.
```

The determinant obeys

```text
D_(A tensor B)(epsilon,eta)
  = D_A(epsilon)^(|J_B|) D_B(eta)^(|J_A|).                 (3)
```

Equation `(3)` is not itself a simple product of Walsh spectra because of the powers.  The target
is an exact convolution law for the recovered squared Pluecker masses, or a proof that exterior
powers give the canonical multiplicative formulation.

## HT significance

This law would refine finite HT constraint geometry from rank data to a complete weighted
representable matroid.  It identifies a positive requirement on any orientation-based universal
constraint carrier: it must expose a separating family of sign responses, or an equivalent
polarization, if it is to retain the basis geometry rather than only its total mass.

## RH audit

Applied to prime or zero coefficient packets, the theorem is a route constraint, not an RH
criterion.  A construction observing only the positive Gram determinant cannot recover which
source subsets support independent separating constraints.  An RH-facing route based on signed
metrics must canonically realize enough orientation responses to reconstruct the relevant
cofinal matroid, and must additionally prove that this matroid controls the Xi divisor.  The
second implication is presently open.

## Dual gate

- **Classical parent components:** Cauchy--Binet, Fourier--Walsh inversion, basis-generating
  polynomials of representable matroids, and determinantal measures.
- **Candidate residue:** the exact identification of a signed Gram determinant cube as complete
  weighted-matroid tomography, its exposed-boundary specialization, and a canonical cofinal HT
  formulation.
- **Retirement condition:** downgrade to `[BRIDGE]` if an equivalent determinant-hypercube
  recovery theorem is already standard in principal-minor, phase-retrieval, or determinantal
  point-process literature, or if no source-canonical orientation family exists in the HT
  application.

## Gates

- [x] exact finite formula isolated
- [x] local Walsh inversion infrastructure identified
- [ ] abstract Walsh coefficient recovery formalized
- [ ] Gram determinant expansion formalized
- [ ] weighted matroid reconstruction capstone formalized
- [ ] tensor/exterior product law settled
- [ ] primary-literature novelty audit completed
- [ ] exposed HT specialization completed
- [ ] pure-mathematical paper integration after novelty verdict
