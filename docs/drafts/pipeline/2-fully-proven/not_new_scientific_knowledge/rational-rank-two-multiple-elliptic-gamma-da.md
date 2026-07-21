# Rational-rank-two multiple elliptic Gamma is differentially algebraic

- **ID:** `rational-rank-two-multiple-elliptic-gamma-da`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FINITE-TWIST CLOSURE BRIDGE
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [REDISCOVERED/COROLLARY]`
  `[UNCONDITIONAL LEAN PROOF OPEN] [NOT AN RH RESULT]`
- **Primary sources:** Masaki Kato, *Differential Algebraicity of the Multiple Elliptic Gamma
  Function for a Rational Period* (2021), Theorem 1.1 and Propositions 2.1--2.2; the standard
  multiple-elliptic-Gamma multiplication formula obtained by residue decomposition of the
  generalized q-Pochhammer product.
- **Parent:**
  `../../1-in-progress/multiple-gamma-period-deletion-annihilator-law.md`
- **Statement:** A finite multiple-elliptic-Gamma period tuple in the upper half-plane is DA as
  soon as the rational span of the tuple together with the unit period has rank at most two.

> **2026-07-21 completion note.** This bridge is the DA half of the exact universal classification
> proved in `../../4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/`. The new
> complementary theorem proves HT for every augmented-rank-at-least-three tuple, so the two halves
> now exhaust all finite upper-half-plane period configurations.

## Exact theorem

Let `I` be finite and nonempty and let

```text
tau=(tau_i)_(i in I) in H^I.
```

Write `G_I(z;tau)` for the Nishizawa multiple elliptic Gamma function in the parity convention

```text
G_I(z;tau)
 = (Q/x; q)_infinity * (x; q)_infinity^((-1)^(|I|-1)),
x=e^(2*pi*i*z), q_i=e^(2*pi*i*tau_i), Q=product_i q_i.                    (1)
```

If

```text
rank_Q span_Q({1} union {tau_i : i in I}) <= 2,                            (2)
```

then `G_I(z;tau)` is differentially algebraic over `C(z)`. Consequently its logarithmic
derivative is differentially algebraic.

## Proof

### 1. Rank two gives a common contracting nome power

Condition `(2)` has rank exactly two, since every `tau_i` has positive imaginary part. Fix
`omega=tau_i0` for one label. Then

```text
tau_i=a_i+b_i*omega,  a_i,b_i in Q.                                       (3)
```

Taking imaginary parts shows `b_i>0`. Choose a positive integer `M` clearing all denominators in
`(3)`. Thus

```text
M*tau_i=A_i+B_i*omega,
A_i in Z, B_i in Z_{>0}.                                                   (4)
```

The integer offsets do not change the nomes:

```text
exp(2*pi*i*M*tau_i)=exp(2*pi*i*B_i*omega).                                 (5)
```

Hence the scaled period vector in `(4)` defines exactly the same multiple elliptic Gamma function
as the Kato-rational vector `(B_i*omega)_i`.

### 2. Multiplication formula removes the finite twists

For every positive integer `M`, residue decomposition of every multi-index gives the exact identity

```text
G_I(z;tau)
 = product_(k in {0,...,M-1}^I)
     G_I(z + sum_i k_i*tau_i; M*tau).                                     (6)
```

There is no normalization factor. For the backward q-Pochhammer product, write each index as
`n_i=M*l_i+k_i`. In the reflected forward product, use the reversed residue
`k_i -> M-1-k_i`; this turns the numerator of each scaled factor into the complete residue
decomposition of `Q/x`. Equivalently, `(6)` is the standard multiple-elliptic-Gamma
multiplication formula

```text
G_r(z|tau)=product_a G_r(z+a dot tau | M*tau+n)                            (7)
```

with an arbitrary integral vector `n`; take `n_i=-A_i` in `(4)`.

### 3. Kato closure

Every factor on the right of `(6)` has the rational period vector `(B_i*omega)_i`. Kato's
Theorem 1.1 makes it DA. Affine translations in `z` and finite products preserve differential
algebraicity, so `(6)` makes `G_I(z;tau)` DA. The quotient `G_I'/G_I` lies in the same
differential field and is DA. `QED`

## Consequence for the period-deletion ideal

For the logarithmic derivative `Psi_(r,tau)` and every structural deletion set `J`, hierarchy
descent gives

```text
x_J Psi_(r,tau)=Psi_(r-|J|, tau restricted to V\J)                        (8)
```

up to the standard DA normalization. If the residual rank `q_tau(J)<=2`, the theorem above makes
the right side DA. Therefore every generator of the rational deletion ideal is a DA annihilator:

```text
D_tau subset Ann_DA(Psi_(r,tau)).                                         (9)
```

Thus the evident inclusion in the deletion-annihilator programme is proved on paper. The exact
remaining conjectural content is the reverse inclusion.

## Hostile checks and scope

1. The twists in this theorem are finite root-of-unity phases multiplying contracting nomes. No
   nome lies on the unit circle.
2. Rank one cannot occur for a nonempty upper-half-plane tuple, so there is no missing degenerate
   analytic case.
3. The integer offsets in `(4)` are not covered literally by Kato's stated rational-ray
   hypothesis. Formula `(6)` is the load-bearing bridge that removes them.
4. The theorem supplies relation-side DA faces. It supplies no Euler packets, Gamma--prime Gram
   block, positive innovation identity, cofinal refinement map, or summable transition defect.
   It therefore cannot discharge the semilocal polarization theorem required by
   `docs/reports/rh-proof-shape-1707.md`.

## Parent-theory and novelty verdict

Kato proves DA for a period vector in `omega*Q^I` and proves the common-ray residue factorization.
The all-coordinate multiplication formula is a standard generalized q-Pochhammer residue identity;
it is also printed as formula `(B.2)` in Yang Lei and Sam van Leuven, *Modularity in d > 2 free
conformal field theory*, JHEP 11 (2024) 023. Felder--Varchenko provide the order-one multiplication
parent.

The rank-two-with-unit formulation is useful and was missing from this corpus, but its proof is a
direct combination of published identities. It is recorded as a bridge, not as new scientific
knowledge.

Primary links:

- `https://doi.org/10.1619/fesi.64.225`
- `https://doi.org/10.1007/JHEP11(2024)023`
- `https://arxiv.org/abs/math/0212155`

## Unconditional Lean boundary

No Lean theorem is claimed here yet. The corpus already contains the actual arbitrary-order
multiple-Gamma product and hierarchy, plus binary commensurable-nome factorization. The missing
unconditional chain is:

1. common-power extraction for an arbitrary finite period family satisfying `(2)`;
2. arbitrary-finite-family reversed-residue factorization of the actual product;
3. Kato's equal-period algebraic differential equation in the actual meromorphic differential
   field, followed by its rational-ray corollary.

These are proof obligations, not hypotheses to be added to the theorem interface.
