# A unitary pair-word twist has an automatic shrinking-tube Hardy bound

- **ID:** `unitary-pair-twist-hardy-exponential-bound`
- **Stage:** 2-fully-proven / not_new_scientific_knowledge
- **Type:** BRIDGE LEMMA / ANALYTIC TWIST ESTIMATE / MODULAR NUCLEARITY
- **Scientific status:** `[PROVED AS ROUTINE EXTENSION] [REDISCOVERED BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Scope:** finite-dimensional matrix factorizing QFT; no RH or distinguished special-function
  input
- **Parents:** `../needs-audit/identity-zero-componentwise-pauli-modular-nuclearity.md` and
  `scalar-cdd-invariance-of-intertwiner-property.md`
- **Statement:** On the Alazzawi--Lechner tubes of width `O(1/n)`, any collision-regular
  all-particle relative twist that is a bounded-multiplicity product of bounded holomorphic
  two-body factors, unitary on the real rapidity axis, automatically obeys the required
  `exp(O(n))` norm and inverse-norm bounds. Thus a pair-factorized twist does not face an
  independent `O(n^2)` conditioning obstruction. This is conditional infrastructure, not a
  theorem that standard factorizing `F`-matrices have such a pair-word form.

## Goal

The analytic intertwiner criterion for compact locality asks for all-particle multipliers `I_n`
on the tubes

```text
C_n=lambda_(pi/2)+(-kappa/(2n),kappa/(2n))^n              (1)
```

with both `||I_n||` and the central-boundary inverse norm bounded by a constant to the `n`th
power. If a relative twist admits a bounded-multiplicity word of `O(n^2)` two-body factors, a
uniform bound larger than one on each factor would give the fatal estimate `exp(O(n^2))`.

Known factorizing `F`-matrices need not have this form: type-A constructions commonly use
triangular products of multi-body partial `F`-matrices or block sums. The hypothesis below is a
specific ansatz whose applicability must be proved model by model.

The theorem below identifies the missing fact in that count. The factors are sampled only
`O(1/n)` away from the real axis, where unitarity gives norm exactly one. Three-lines
interpolation turns the loss per factor into `O(1/n)`, and the complete pair product costs only
`exp(O(n))`.

## Two-body strip lemma `[PROVED]`

Let `V` be a finite-dimensional Hilbert space, let `rho>0`, and let

```text
F : {z in C : |Im z|<rho} -> GL(V)                           (2)
```

be holomorphic. Assume that `F` and `F^(-1)` are bounded on the closed upper and lower
substrips under consideration, with bounds `M>=1` and `M_tilde>=1`, and that

```text
F(x) is unitary for every real x.                            (3)
```

Then, for `|y|<=rho`,

```text
||F(x+iy)||       <= M^(|y|/rho),
||F(x+iy)^(-1)|| <= M_tilde^(|y|/rho).                       (4)
```

### Proof

First take `0<=y<=rho`. For unit vectors `u,v`, the scalar function

```text
z |-> <u,F(z)v>                                             (5)
```

is holomorphic and bounded on the horizontal strip. Its boundary modulus is at most one on
`Im z=0` by `(3)` and at most `M` on `Im z=rho`. Hadamard's three-lines theorem gives

```text
|<u,F(x+iy)v>| <= M^(y/rho).                                (6)
```

Taking the supremum over `u,v` proves the first estimate for positive `y`; the lower strip gives
the negative case. The inverse is holomorphic by `(2)`, unitary on the real axis by `(3)`, and
the identical argument with its bound `M_tilde` proves the second estimate. If bounds are known
only on open strips, apply the statement on any fixed smaller closed substrip. No dimension
factor is introduced.

## All-particle pair-product theorem `[PROVED]`

Write a point of the tube `(1)` as

```text
zeta_j=theta_j+i(-pi/2+eta_j),
|eta_j|<kappa/(2n).                                         (7)
```

Hence every pair difference satisfies

```text
|Im(zeta_i-zeta_j)|=|eta_i-eta_j|<kappa/n.                  (8)
```

Suppose an analytic all-particle twist has an ordered factorization

```text
I_n(zeta)=product_(r=1)^(L_n)
  F_r(zeta_(i_r)-zeta_(j_r))^(i_r,j_r),                     (9)
```

where:

1. every `F_r` satisfies the two-body strip lemma with common `rho,M,M_tilde`;
2. every unordered pair `{i,j}` occurs at most `m` times in the word, with `m` independent of
   `n`;
3. `0<kappa<=rho`;
4. tensor-leg insertion preserves the two-body operator norm, as usual.

No commutativity of the factors is assumed. Submultiplicativity, `(4)`, and `(8)` give

```text
||I_n(zeta)||
 <= M^((1/rho) sum_r |eta_(i_r)-eta_(j_r)|)
 <= M^(m kappa (n-1)/(2 rho)).                              (10)
```

Indeed, there are `n(n-1)/2` unordered pairs and each contribution is below `kappa/n`.
Therefore

```text
||I_n(zeta)|| <= gamma^n,
gamma=M^(m kappa/(2 rho)).                                  (11)
```

The inverse of `(9)` is the reverse ordered product of the inverse pair factors. The same proof
gives

```text
||I_n(zeta)^(-1)|| <= gamma_tilde^n,
gamma_tilde=M_tilde^(m kappa/(2 rho)).                      (12)
```

On the central boundary `eta_1=...=eta_n=0`, every factor is unitary, so `I_n` itself is
unitary and the inverse norm is exactly one. Equation `(12)` is stronger than the
Alazzawi--Lechner central-boundary requirement when the factorization is valid throughout the
tube.

More generally, the same proof applies to any word with `L_n<=a n^2` factors whose arguments
have imaginary parts bounded by `b/n`; the conditioning exponent is at most
`ab log(M) n/rho`. The bounded pair-multiplicity form records the geometry relevant to
factorizing twists.

## Modular-nuclearity consequence

Assume in addition that `(9)` is holomorphic and invertible across every collision diagonal and
satisfies the relative cocycle equation

```text
I_n(theta) D_n^B(tau_k)
  =D_n^(B(0))(tau_k) I_n(theta)                             (13)
```

on the central boundary, or the equivalent Alazzawi--Lechner subspace-mapping condition. Then
`(11)`--`(12)` discharge the quantitative parts of their intertwiner property. If
`B(0)=-F`, their theorem gives modular nuclearity and compact-local observables. In the
right-flipped braid convention `B(0)=-I`, the componentwise Pauli theorem in the parent card
provides the same factorial summability once the corresponding quantitatively bounded relative
twist exists.

Ordinary existence is not part of this ansatz.  The abstract descent theorem
`fixed-particle-holomorphic-acyclicity-identity-zero-yang-baxter.md` produces a holomorphic
invertible relative frame for every fixed particle number, but gives neither a pair-word
factorization nor any bound in `(11)`--`(12)`.

Thus, within the pair-factorized class, the open problem is not a separate large-`n` norm
estimate. Within the pair-word ansatz, it is to construct a twist satisfying all five structural
gates:

```text
relative factorization to the constant zero anchor,
holomorphic invertibility through collision diagonals,
unitary real-axis normalization,
uniform fixed-strip bounds for every factor and its inverse,
bounded pair multiplicity independent of n.                (14)
```

The third gate is essential. A real-axis bound `||F(x)||<=c` with `c>1` produces `c^(O(n^2))`
before interpolation and does not imply `(11)`.

## Application to the `O(N)` problem

The rational `O(N)`/Brauer scattering matrix is the first serious target. Published work proves
regularity, the fermionic zero anchor, and quantitatively controlled analytic intertwiners through
particle number two.  Fixed-`n` holomorphic frames now exist abstractly at every particle number,
but their bounded Hardy control for `n>=3` remains open. Standard factorizing `F`-matrices are
known for several type-A and ice-rule
models, but the literature audit found no all-`n` factorizing `F`-matrix for the rational
`O(N)`/Brauer vector matrix and no collision-regular relative twist with the QFT Hardy
properties.

The lemma gives a conditional route: if a bounded-multiplicity Brauer pair word with `(14)`
exists, the required `exp(O(n))` conditioning follows automatically.  The three-body audit in
`../../5-failed/on-brauer-two-body-half-twist-pair-word.md` now proves that the published
two-particle half-phase cannot extend as any fixed one-copy-per-pair word, and that no universal
collision-normalized pair factor can satisfy both its two-body relative equation and reduced-word
coherence.  The Oka-descent frame proves that this is a factorization no-go, not a qualitative
nonexistence theorem. A surviving explicit construction must contain corrective/repeated factors
or genuine multi-body partial twists and requires a separate conditioning theorem.

## Hypertranscendental physics consequence

Regular scalar-unit CDD factors are neutral for existence of the intertwiner property and can be
handled by their own pair half-phases. Therefore a scalar HT clock can coexist with the relative
twist without changing the matrix obstruction. A genuinely mixing HT theory must instead supply
a projectively HT positive-unitary Yang--Baxter family and a collision-regular relative twist for
its noncentral cocycle.

The physical object exposed here is a **relative Hardy twist**: a quantitatively controlled
change of multiparticle exchange constraint, not a time-evolution flow. Its real-axis unitarity
is the zero-loss physical boundary condition; its small imaginary displacement measures the
analytic cost of sharpening wedge localization into compact locality.

## Anti-theatre and novelty gate

1. **Hadamard three-lines or the pair count called a new theorem.** Rejected. Alazzawi--Lechner
   Proposition 5.4 already combines the exact `O(n^2)` scalar pair product with the same `1/n`
   tubes and obtains `gamma^n`, including central-boundary unitarity. The operator-valued form
   `(10)`--`(12)` is the immediate matrix-coefficient three-lines and submultiplicativity
   extension; commutativity is not used in the norm estimate.
2. **An `O(N)` twist declared constructed.** Rejected. No algebraic Brauer twist satisfying
   `(13)` has been produced here.
3. **Any factorizing `F`-matrix declared sufficient.** Rejected. Generic-inhomogeneity formulas
   may be singular at collisions, may factorize to the identity instead of the required constant
   anchor, and need not admit unitary boundary normalization.
4. **`O(n^2)` factors declared harmless without zero loss.** Rejected. Unitarity in `(3)` is
   load-bearing.
5. **Scalar HT called nonabelian HT.** Rejected. Scalar dressings remain central and disappear
   from projective Wigner--Smith data.

Focused searches across factorizing `F`-matrices, Drinfeld twists, the `O(N)` intertwiner
problem, and analytic cocycles found no statement of the shrinking-tube conditioning theorem
`(10)`--`(12)` in this operator-word generality. That textual absence does not clear the novelty
gate: the extension is routine and the exact scalar mechanism is already published. The lemma is
kept only to prevent the incorrect claim that pair count alone forces `exp(O(n^2))` growth.

## Bold conjecture

`[CONJECTURE -- CORRECTED RELATIVE BRAUER HARDY TWIST]` For every `N>=3`, the fixed-particle
Oka-descent frames for the regular `O(N)` sigma-model braid cocycle can be replaced by an explicit
collision-regular relative Brauer construction built from genuine multiparticle partial twists,
or from bounded-multiplicity pair factors with nontrivial corrective/repeated terms.  It cannot
be the one-copy or reduced-word lift of the published two-particle half-phase.  The partial
factors and their inverses are bounded on fixed strips and unitary on the real axis, and the
resulting all-particle operators obey the required `exp(O(n))` Hardy bounds.

This is not the broader conjecture that every regular Yang--Baxter family has the intertwiner
property. It is tied to the Brauer algebra and is falsifiable at the first three-body twist
compatibility equation.

## Exact open core

1. The exact three-body equation is derived and the one-copy/reduced-word lift of the known
   two-particle factor is disproved.  Classify bounded-multiplicity words with corrective/repeated
   factors.
2. Construct the first explicit, quantitatively controlled three-body partial twist/associator
   or exhibit its nonzero Brauer/partial-index obstruction.  A nonconstructive holomorphic frame
   already exists.
3. Prove real-axis unitarizability without multiplying by a singular scalar normalization.
4. Only after 1--3, combine the twist with a projectively HT intrinsically mixing physical
   Yang--Baxter family; scalar HT dressing alone is a commuting-clock control.
5. Formalize the strip-to-`exp(O(n))` implication only together with an analytic-twist interface.
   The finite counting inequality alone would be wrapper theatre.

## Primary literature

- S. Alazzawi, *Deformations of Quantum Field Theories and the Construction of Interacting
  Models*, <https://arxiv.org/abs/1503.00897>, especially Lemma 3.28 and its correction of the
  earlier nonshrinking-tube estimate.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>, especially Proposition 4.5, Definition 5.2,
  Theorem 5.3, Proposition 5.4, and equations (5.13)--(5.15).
- J. M. Maillet and J. Sanchez de Santos, *Drinfel'd twists and algebraic Bethe ansatz*,
  <https://arxiv.org/abs/q-alg/9612012>.
- S. G. McAteer and M. Wheeler, *On factorizing F-matrices in `Y(sl_n)` and
  `U_q(sl_n-hat)` spin chains*, <https://arxiv.org/abs/1112.0839>.
- H. Pfeiffer, *Factorizing twists and the universal R-matrix of the Yangian `Y(sl_2)`*,
  <https://arxiv.org/abs/math-ph/0006032>.
- A. P. Isaev, A. I. Molev, and O. V. Ogievetsky, *A new fusion procedure for the Brauer
  algebra and evaluation homomorphisms*, <https://arxiv.org/abs/1101.1336>.

## Gates

- [x] corpus collision audit
- [x] primary intertwiner and factorizing-twist literature audit
- [x] two-body three-lines estimate proved
- [x] all-particle pair-count estimate proved without commutativity
- [x] inverse estimate and central-boundary unitarity proved
- [x] exact structural remainder isolated
- [x] independent operator-algebraic novelty audit; novelty rejected
- [x] `O(N)` three-body equation solved negatively for one-copy and reduced-word pair lifts
- [ ] corrective repeated-pair words classified
- [ ] all-particle relative Brauer Hardy twist
- [ ] compact-local intrinsically mixing projective-HT QFT
