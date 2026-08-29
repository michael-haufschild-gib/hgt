# Laguerre--Pólya and Jensen hyperbolicity blindness of a maximal HT power pro-field

- **ID:** `laguerre-polya-jensen-profield-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; real-rootedness; Jensen--Pólya boundary
- **Statement:** One functional-equation-even maximal-HT power pro-field has an order-one
  Laguerre--Pólya representative and representatives with exactly `k` off-real zero quartets for
  every `k>=1`; equivalently, the same pro-field realizes both complete Jensen hyperbolicity and
  failure of at least one Jensen polynomial.

## Goal

Test whether maximal translation hypertranscendence, even reflection symmetry, order-one growth,
and the complete algebraic power-normalization hierarchy can intrinsically select real-rootedness.
The theorem gives an exact negative answer inside a single family of real even entire functions.

## Setup

Choose `theta` in the comeager free set of the functional-equation-even canonical-product theorem in
`herglotz-full-translation-ht-krein-index-orthogonality.md`.  Its base function is

`E_theta(z)=prod_(j>=0) (1-z^2/Lambda_j(theta)^2)`,            (1)

where `Lambda_j(theta)>0`, `Lambda_j(theta)=j+1+O(1)`, and all zeros `+-Lambda_j(theta)` are
simple.  The product is real, even, entire of exact order one.  Its logarithmic derivative has a
differentially algebraically independent full complex translation orbit.  Consequently the orbit
of `E_theta` itself is differentially algebraically independent.

For `k>=1`, choose distinct positive zeros

`a_1,b_1,...,a_k,b_k`

and distinct nonreal points `t_1,...,t_k` in the upper half-plane with nonzero real parts, avoiding
all existing zeros and each other's sign/conjugation orbits.  Define

`E_(theta,k)(z)=E_theta(z) prod_(ell=1)^k`

` ((z^2-t_ell^2)(z^2-conj(t_ell)^2))`

` /((z^2-a_ell^2)(z^2-b_ell^2)).`                              (2)

The apparent poles cancel selected simple zeros of `E_theta`.  Thus (2) is real, even, entire of
exact order one.  It replaces `4k` real zeros by exactly the `k` off-real quartets

`{+-t_ell,+-conj(t_ell)}`.                                    (3)

For any nonzero meromorphic `F` and `N>=1`, put

`P_N(F)=C(z)<T_h(F^N):h in C>`.                               (4)

## Theorem `[PROVED HERE]`

1. `E_theta` belongs to the Laguerre--Pólya class.
2. For every `k>=1`, `E_(theta,k)` does not belong to the Laguerre--Pólya class and has exactly `k`
   nonreal sign/conjugation quartets.
3. The translate families of all `E_(theta,k)`, including `k=0`, are differentially algebraically
   independent over `C(z)` and generate the same differential-translation field.
4. For every `N>=1` and every `k>=0`,

   `P_N(E_(theta,k))=P_N(E_theta)`.                            (5)

   These termwise equalities preserve every divisibility transition, so the complete inverse power
   systems and all their intersections are identical.
5. With the classical Jensen polynomials `J_F^(d,n)` attached to the Taylor coefficients of a real
   entire `F`, every `J_(E_theta)^(d,n)` is hyperbolic, whereas for every `k>=1` at least one
   `J_(E_(theta,k))^(d,n)` is not hyperbolic.

Hence membership in the Laguerre--Pólya class, complete Jensen hyperbolicity, and the number of
off-real quartets are not invariants of the unpointed maximal-HT power pro-field, even after even
functional-equation symmetry and exact order one are imposed.

## Proof

### 1. The base function is Laguerre--Pólya

The finite partial products

`E_theta,J(z)=prod_(j=0)^J (1-z^2/Lambda_j(theta)^2)`           (6)

are real polynomials whose zeros are all real.  Since

`sum_j Lambda_j(theta)^(-2)<infinity`,                         (7)

the products (6) converge locally uniformly on `C` to `E_theta`.  The Laguerre--Pólya class is
exactly the locally uniform closure of the real-rooted real polynomials.  Therefore
`E_theta` belongs to that class.

### 2. Quartet surgery leaves the class

Cancellation in (2) is exact because the selected zeros of `E_theta` are simple.  The inserted
points in (3) are genuine nonreal zeros and no other zeros move.  Every nonzero function in the
Laguerre--Pólya class has only real zeros, as follows either from its canonical representation or
from Hurwitz's theorem applied to the approximating real-rooted polynomials.  Hence
`E_(theta,k)` is not Laguerre--Pólya for every `k>=1`.  The orbit-separation assumptions on the
`t_ell` make the `k` quartets in (3) distinct, proving the exact count.

### 3. Maximal HT and all power levels are unchanged

Write

`E_(theta,k)=R_k E_theta`, `R_k in C(z)^*`.                    (8)

For each translation `h`, both `T_h(R_k)` and its inverse lie in `C(z)`.  Thus

`C(z)<T_h(E_(theta,k)):h in C>`

` =C(z)<T_h(E_theta):h in C>`.                                (9)

The base orbit is differentially algebraically independent because its logarithmic derivatives
form the independent orbit proved in the parent Herglotz theorem and lie in its generated field.
Multiplying each member by an invertible base-field element preserves every differential-algebraic
relation in both directions, so every surgically modified orbit is independent as well.

For every positive integer `N`,

`T_h(E_(theta,k)^N)=T_h(R_k^N) T_h(E_theta^N)`.                (10)

Again the first factor is invertible in `C(z)`.  Equation (10) proves (5) generator by generator.
Because the fields are equal inside the same ambient meromorphic differential field, all transition
maps and intersections are identical, not merely abstractly isomorphic.

### 4. Jensen hyperbolicity changes

Write a real entire function as

`F(z)=sum_(r>=0) gamma_r z^r/r!`

and define

`J_F^(d,n)(X)=sum_(j=0)^d binom(d,j) gamma_(n+j) X^j`.          (11)

Jensen's theorem says that a real entire function is Laguerre--Pólya exactly when all polynomials
(11) are hyperbolic.  Section 1 therefore makes every `J_(E_theta)^(d,n)` hyperbolic.  Section 2 and
the converse direction of Jensen's theorem imply that, for each `k>=1`, some pair `(d,n)` gives a
nonhyperbolic `J_(E_(theta,k))^(d,n)`.  This proves all assertions. `QED`

## Law extracted

**Pólya gauge-blindness law.**  Rational functional-equation-symmetric divisor surgery preserves a
maximal translation differential matroid and the full algebraic power pro-field termwise, while it
can cross the boundary of the Laguerre--Pólya class and add any prescribed finite number of
off-real symmetry quartets.  Infinite Jensen hyperbolicity is therefore analytic divisor data, not
an invariant of the unpointed HT normalization tower.

The theorem includes the infinite hierarchy, not merely a finite Jensen prefix: the base passes
every Jensen polynomial and each modified representative fails at least one, while all power levels
remain equal.

## RH-route consequence

The theorem rules out the implementation claim that the Pólya--Jensen RH selector, de
Bruijn--Newman real-rooted phase, or a Jensen-section hyperbolicity certificate can be reconstructed
canonically from:

1. an unpointed maximal-HT full translation field;
2. its differential matroid;
3. every algebraic power-normalization field simultaneously;
4. the complete inverse system and its stable intersection;
5. those data together with scalar evenness and exact order-one growth.

Those objects are identical while complete Jensen hyperbolicity changes.  This does **not** refute
the Pólya--Jensen equivalence to RH.  The actual xi function supplies a distinguished Taylor center,
canonical Hadamard normalization, theta/Euler source, and a pointed entire representative.  Any
viable Jensen proof must use such a marking or another structure not recoverable from the unpointed
HT power pro-field.

## Parent-theory and novelty verdict

- `[SEARCH]` The Laguerre--Pólya class as the local-uniform closure of real-rooted polynomials and
  Jensen's characterization by hyperbolic Jensen polynomials are classical.
- `[SEARCH]` Griffin--Ono--Rolen--Thorner--Tripp--Wagner state the Pólya equivalence for xi and study
  its Jensen polynomials: `https://arxiv.org/abs/1910.01227`.
- `[SEARCH]` Wagner surveys the Jensen--Pólya program for L-functions:
  `https://arxiv.org/abs/1905.11269`.
- `[BRIDGE]` Exact quartet surgery and maximal translation HT come from the separate Herglotz
  canonical-product theorem; power-level invariance is rational gauge.

The combined result is a useful exact route boundary, but after erasing project vocabulary its proof
is a direct assembly of classical Laguerre--Pólya/Jensen theory with rational multiplication.  It
fails the parent-theory and anti-theatre novelty gates and is not new scientific knowledge.

## Lean status (2026-08-29)

**Complete and unconditional.**  Capstone:
`GaloisForLFunctions.HTGeometry.exists_powerNormalizationProfield_laguerrePolyaJensenBlindness`
(`formal/GaloisForLFunctions/HTGeometry/LaguerrePolyaJensenProfieldBlindness.lean`).  For every
strict divisibility ladder `D` it produces one `θ` such that the even surgery family
`kreinEvenSurgeryFunction θ k` satisfies, at every `k`:

- entire, even, Schwarz-real, order-one envelope;
- the exact divisor: the zeros are the unselected `±Λ_n(θ)` together with the `4k` points
  `±t_i, ±conj(t_i)`, whose `k` quartets are distinct (`EvenSurgeryPoleSeparated`) and off-real
  (`0 < im t_i`);
- equality of every algebraic power-translation level with the base, of the complete inverse system
  along `D`, and of its logarithmic-residue intersection;
- maximal translation differential independence of the logarithmic-derivative translate family;
- `k = 0` is Laguerre--Pólya and **every** Jensen polynomial `J^d` of its real Taylor coefficients
  splits over `ℝ`; every `k ≥ 1` is **not** Laguerre--Pólya and **some** Jensen polynomial fails to
  split.

The classical Jensen/Laguerre--Pólya input was built from scratch rather than assumed:

| Layer | Module | Content |
|---|---|---|
| Laguerre shift | `HTGeometry/LaguerreShiftSplits.lean` | `splits_laguerreShift` (`p ↦ p' − βp` preserves real-rootedness) via the exponential gauge, Rolle, the multiplicity drop, and `natDegree_ne_card_roots_succ` |
| Reversal | `HTGeometry/SplitsReflect.lean` | `Splits.reflect`: coefficient reversal preserves splitting over any field |
| Hermite--Poulain | `HTGeometry/HermitePoulain.lean` | `diffOpApply` in `Module.End ℝ ℝ[X]` and `splits_diffOpApply` |
| Jensen algebra | `HTGeometry/JensenPolynomialSplits.lean` | `jensenReverse`, `jensenPoly`, `diffOpApply_X_pow`, `splits_jensenPoly_of_splits` |
| Hurwitz | `HTGeometry/HurwitzClosedZeroLocus.lean` | sphere-domination zero planting and `zero_mem_closed_of_tendstoLocallyUniformly` |
| Limits | `HTGeometry/RealRootedCoefficientLimit.lean` | `splits_of_tendsto_coeff`: real-rootedness is closed under bounded-degree coefficient limits |
| Jensen limits | `HTGeometry/JensenPolynomialLimit.lean` | `splits_jensenPoly_of_tendsto_coeff` |
| The class | `HTGeometry/LaguerrePolyaClass.lean` | `LaguerrePolya`, `splits_jensenPoly_of_laguerrePolya`, `im_eq_zero_of_laguerrePolya` |
| Base function | `HTGeometry/EvenCanonicalProductLaguerrePolya.lean` | `laguerrePolya_movingEvenCanonicalProduct` |
| Converse | `HTGeometry/JensenScaledWeight.lean`, `HTGeometry/LaguerrePolyaJensenConverse.lean` | `jensenWeight`, `splits_comp_C_mul_X`, `laguerrePolya_of_splits_jensenPoly` |
| Real coefficients | `HTGeometry/RealTaylorCoefficients.lean` | `realTaylorCoeff`, `exists_jensenPoly_not_splits_of_nonreal_zero` |

The pro-field half is the pre-existing
`HTGeometry.PowerNormalizationProfieldKreinBlindness.exists_powerNormalizationProfield_allEvenKreinIndex`
stack (with `MovingEvenCanonicalSurgery`, `EvenSurgeryPoleSeparationWitnesses`,
`KreinEscapePowerFieldInvariance`).

All declarations are axiom-clean: `propext`, `Classical.choice`, `Quot.sound`.

## Gates

- [x] 0 -> 1: exact real-rootedness selector and same-pro-field falsifying family isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: optional bridge publication/integration

## Log

- 2026-07-11 -- Proved exact Laguerre--Pólya/Jensen blindness using the functional-equation-even
  maximal-HT canonical product and rational off-real quartet surgery.
- 2026-07-11 -- Downgraded after parent-theory attack: the route consequence is exact, but the
  mechanism is classical Jensen theory plus rational gauge and is not new scientific knowledge.
- 2026-08-29 -- Formalized unconditionally in Lean 4 and promoted to stage 3: both directions of
  Jensen's theorem, the Laguerre--Pólya class, and the full pro-field blindness capstone.
