# Quadratic circle free-orbit charge

- **ID:** `quadratic-circle-free-orbit-charge`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[POSITIVE NO-GO]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/QuadraticCircleFreeOrbitCharge.lean`
- **Successor route:** `../../1-in-progress/quadratic-reflection-anomaly-rh.md`

## Theorem

Fix a prime `p`.  The linear prime-log circle phase cancels on a signed reflection pair:

```text
[m log p] + [-m log p] = 0.                               (1)
```

Define the quadratic refinement

```text
q_p(m) = [m^2 log p].                                     (2)
```

Then

```text
q_p(m) + q_p(-m) = [2m^2 log p],                          (3)
```

and this phase is zero exactly when `m=0`.

More generally, for a finite list of free-reflection-orbit multiplicities `m_i in N`, define

```text
Q_p(m_1,...,m_r) = [2 sum_i m_i^2 log p].                 (4)
```

Then

```text
Q_p(m_1,...,m_r)=0  iff  every m_i=0.                     (5)
```

The proof uses nonnegativity of the integer sum of squares and the infinite order of `log p` modulo
`Z`.

At the actual Xi divisor, vanishing of the quadratic reflected-pair phase at every right-half zero
is therefore equivalent to RH.  This is still a target-side criterion; the new route is the source
construction and annihilation of that quadratic phase.

## Positive statement from linear reflection cancellation

Unpolarized linear holonomy is blind because reflected signed contributions cancel.  A quadratic
refinement converts the same pair into a positive local contribution.  Therefore a global
equivariant anomaly can avoid half-plane cancellation if it has all three properties:

1. free orbits contribute the sum of the two quadratic local terms;
2. fixed critical-line orbits carry a canonical localization correction and contribute zero;
3. distinct free orbits add orthogonally, without cross terms.

If a source theorem forced the resulting phase `(4)` to vanish on every finite window, `(5)` would
exclude all free reflection orbits.

## Polarization-symmetry no-go

For every function `q` on an abelian group, its polarization

```text
b_q(x,y)=q(x+y)-q(x)-q(y)
```

is symmetric.  If it is also antisymmetric, then every value is two-torsion.  The prime-log circle
phase `[log p]` is not two-torsion.  Therefore it cannot be obtained by taking a quadratic
refinement of the existing alternating weld commutator pairing.

The positive successor is narrower: the source must supply a separate **symmetric arithmetic
incidence pairing** with polarization `[2mn log p]`.  The alternating weld `H^2` class may enter as
adjacent data, but it cannot itself be the polarized bilinear form.

## Formal surface

- `reflectionPairQuadraticCircleCharge_eq`
- `reflectionPairQuadraticCircleCharge_eq_zero_iff`
- `xiReflectionPairQuadraticCircleCharge_eq_zero_iff`
- `riemannHypothesis_iff_xiReflectionPairQuadraticCircleCharges_zero`
- `freeOrbitQuadraticIndex_eq_zero_iff`
- `freeOrbitQuadraticCircleCharge_eq_zero_iff`
- `quadraticPolarization_comm`
- `two_nsmul_quadraticPolarization_eq_zero_of_antisymm`
- `no_primeCircle_antisymmetric_quadraticPolarization`

## Verification

`lake env lean GaloisForLFunctions/RHTower/QuadraticCircleFreeOrbitCharge.lean` passes on the
repository toolchain.

## Novelty and significance gate

The sum-of-squares and character-faithfulness algebra is standard.  No claim of new scientific
knowledge is made.  The unproved equivariant quadratic source anomaly would be the new RH-bearing
content.

## Gates

- [x] 0 -> 1: quadratic successor to linear cancellation stated
- [x] 1 -> 2: pair and finite-list faithfulness proved
- [x] 2 -> 3: algebraic consumer formalized and checked
- [ ] 3 -> 4: not promoted; source quadratic refinement is open
