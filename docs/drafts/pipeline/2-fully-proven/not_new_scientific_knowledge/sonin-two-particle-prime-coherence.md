# Two-particle Sonin boundary energy forces prime coherence

- **ID:** `sonin-two-particle-prime-coherence`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / POLARIZED PRIME RIGIDITY
- **Date:** 2026-07-10
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]` -- the
  tensor-square Calkin estimate and its prime-coherence consequence are proved below. The abstract
  tensor amplification is elementary; scientific novelty, if any, lies in the actual Sonin
  realization at the critical Euler weight and the resulting all-prime coherence law. A targeted
  tensor-Toeplitz, crossed-product, and Sonin/prolate priority audit remains necessary.
- **Parents:**
  `finite-sonin-euler-l2-calkin-lower`;
  `all-depth-pair-face-signature-completeness`;
  `euler-support-energy-position-uncertainty`
- **Statement:** On the tensor square of the actual even Sonin carrier, finite pair corners contain
  the full weighted coefficient energy modulo compact operators. Consequently, if the coefficient
  on the prime pair `{p,q}` is a difference `a_p-a_q`, uniformly bounded finite pair sections modulo
  compacts force the entire prime family `(a_p)` to be constant.

## Goal

Test whether the pairwise obstruction structure discovered for general mixed-difference
hypertranscendence has an operator-side analogue strong enough to improve on the one-prime Euler
weight. The one-particle theorem gives only `sum_p |a_p|^2/p`. The pair theorem gives

```text
sum_(p<q) |a_p-a_q|^2/(p q),
```

and the infinite mass `sum_p 1/p=infinity` turns finiteness of this pair energy into exact global
coherence. This is a constraint theorem, not an RH implication: no identification of `a_p` with an
RH polarization defect is assumed or proved.

## Setup

Let `H` be the actual even Sonin Hilbert space at a fixed cutoff. For every real `r>1`, let

```text
L_r=(1-Q)(U_r+U_r^(-1))Q
```

be the Sonin dilation corner, and let

```text
C_r=-r^(-1/2)L_r
```

be the positive Euler normalization. On the Hilbert tensor product `H tensor H`, write

```text
C_(r,s)=C_r tensor C_s.
```

All compact operators below are compact on `H tensor H`.

## Finite pair-energy theorem `[PROVED HERE]`

Let `r_1,...,r_m>1` be distinct. Let `E` be any finite set of ordered pairs `(i,j)` and let
`b_(ij) in C`. Then, for every compact operator `K` on `H tensor H`,

```text
(sum_((i,j) in E) |b_(ij)|^2/(r_i r_j))^(1/2)
  <= ||sum_((i,j) in E) b_(ij) (C_(r_i,r_j))-K||.          (1)
```

Equivalently, for the unnormalized corners,

```text
(sum_((i,j) in E) |d_(ij)|^2)^(1/2)
  <= ||sum_((i,j) in E) d_(ij) (L_(r_i) tensor L_(r_j))-K||. (2)
```

### Proof

Use the common-shell construction from the one-particle Sonin theorem for the finite scale family.
It supplies a unit vector sequence `v_n` and, for every scale index `i`, bounded weakly-null input
vectors `f_(i,n)` such that, as `n->infinity`,

```text
<f_(i,n),f_(k,n)> -> delta_(ik),
<L_(r_j) f_(i,n),v_n> -> delta_(ij).                       (3)
```

The first limit follows because the corrected inputs converge to normalized functions on pairwise
disjoint shells. The second is the scale-matrix limit already used in the one-particle proof.

For an ordered pair `alpha=(i,j)`, put

```text
x_(alpha,n)=f_(i,n) tensor f_(j,n),
w_n=v_n tensor v_n.
```

Equation (3) gives

```text
<x_(alpha,n),x_(beta,n)> -> delta_(alpha,beta),             (4)
```

and

```text
<(L_(r_k) tensor L_(r_l))x_((i,j),n),w_n>
  -> delta_(ki) delta_(lj).                                 (5)
```

Every sequence `x_(alpha,n)` is weakly null. Indeed, its inner product with an elementary tensor is
the product of two one-particle weak matrix coefficients and therefore tends to zero; finite sums
of elementary tensors are dense, and the sequence is bounded.

Choose coefficients `u_alpha` with `sum_alpha |u_alpha|^2=1` and

```text
|sum_alpha d_alpha u_alpha|=(sum_alpha |d_alpha|^2)^(1/2).
```

Put `x_n=sum_alpha u_alpha x_(alpha,n)`. By (4), `||x_n||->1`, and `x_n` is weakly
null. By (5), for

```text
T_d=sum_((k,l) in E) d_(kl)(L_(r_k) tensor L_(r_l)),
```

one has

```text
|<T_d x_n,w_n>| -> (sum_alpha |d_alpha|^2)^(1/2).           (6)
```

Every compact `K` sends `x_n` to zero in norm. Since `||w_n||=1`,

```text
|<(T_d-K)x_n,w_n>| <= ||T_d-K|| ||x_n||.
```

Pass to the limit and use (6) to obtain (2). Substituting
`d_(ij)=b_(ij)/(sqrt(r_i)sqrt(r_j))` proves (1). `QED`

## Prime-coherence theorem `[PROVED HERE]`

Let `a_p in C` be indexed by the primes. For a finite prime set `F`, define

```text
T_F(a)=sum_(p<q; p,q in F) (a_p-a_q)(C_p tensor C_q).       (7)
```

Assume that its finite sections are uniformly bounded modulo compact operators:

```text
sup_(F finite) dist(T_F(a), Compact(H tensor H)) < infinity. (8)
```

Then there is one `a in C` such that

```text
a_p=a
```

for every prime `p`.

### Proof

Let the supremum in (8) be at most `B`. Applying (1) to every finite set gives

```text
sum_(p<q) |a_p-a_q|^2/(p q) <= B^2.                         (9)
```

Fix primes `p` and `r`. The two rows

```text
R_p=sum_(q!=p) |a_p-a_q|^2/q,
R_r=sum_(q!=r) |a_r-a_q|^2/q
```

are finite by (9). For every other prime `q`,

```text
|a_p-a_r|^2 <= 2|a_p-a_q|^2+2|a_r-a_q|^2.
```

Multiply by `1/q` and sum over `q` different from `p,r`. If `a_p!=a_r`, the left side is infinite
because the reciprocal-prime sum diverges, while the right side is at most `2R_p+2R_r<infinity`.
This contradiction gives `a_p=a_r`. Since `p,r` were arbitrary, the family is constant. `QED`

The same infinite-mass argument holds for potentials in any Hilbert space once an appropriate
Hilbert-valued pair representation is supplied.

## Why this is stronger than the one-particle theorem

The one-particle Euler estimate says that bounded finite sections imply

```text
sum_p |a_p|^2/p < infinity.
```

This is the `v=1/2` Euler Hilbert weight and by itself gives no new control inside the critical
strip. The two-particle theorem does not improve that weight for arbitrary pair coefficients.
Instead, it exploits the coboundary form `a_p-a_q`: finite critical pair energy against the infinite
measure `sum_p delta_p/p` forces exact equality of all local potentials. Pairing, rather than decay,
closes the half-weight gap.

## Bidirectional research consequence

### From RH/Sonin research to general hypertranscendence

The theorem supplies a natural normed polarization for pair-indexed obstruction data. The finite
mixed-difference classification says that all DA/HT information is carried by compatible pair-face
divisors. A Hilbert realization of their lift discrepancies as potentials `a_p-a_q` would therefore
turn bounded two-particle boundary energy into a global coherence theorem for an infinite family of
hypertranscendental constraints. This would be a new infinite-rank extension of the finite
pair-face normal form.

### From hypertranscendence research toward RH

The pair-face theorem identifies pair data with triple compatibility as the exact finite
information boundary. The present theorem shows that pair differences are also exactly where the
critical prime weight can become rigid. A viable RH bridge would have to construct local
functional-equation polarization potentials `a_p` such that:

1. their differences are functorial images of prime-specialized pair-face charges;
2. the resulting two-particle Sonin operator satisfies the uniform Calkin bound or a stronger
   positive-form estimate;
3. the archimedean normalization fixes the surviving constant potential to zero; and
4. vanishing of all local potentials forces `kappa_-(m_xi)=0`.

None of these four realization statements is proved here. The theorem proves that, if they are
obtained, the infinite-prime coherence step is no longer missing.

## Non-results and falsifiers

- This does not prove RH or an RH equivalent.
- No canonical map from orbit-residue divisors to the scalars `a_p` is known.
- Pair-face compatibility is an equalizer condition after pushforward, not automatically a scalar
  gradient representation `D_(pq)=a_p-a_q`.
- The orbit quotient for the prime periods is incompatible with the strongly continuous Mellin
  dilation representation if one insists that structural periods act trivially. A successful map
  must retain the period action, for example through a crossed-product or groupoid lift.
- Calkin norm control is not positivity and does not by itself compute the negative index of the
  `xi` Herglotz/de Branges kernel.
- If a proposed construction factors only through the one-prime positive Euler sum, the formalized
  reciprocal-prime obstruction rules it out.

## Novelty and significance gate

- **NOVEL:** `[UNVERIFIED]` Tensor amplification of a regular-representation lower bound is standard
  in spirit. No priority claim is made until the actual-Sonin tensor-square estimate and the
  reciprocal-prime coherence consequence are checked against Toeplitz tensor products,
  semigroup/crossed-product boundary representations, and prolate/Sonin operator theory.
- **SIGNIFICANT:** The theorem gives a non-circular mechanism by which genuinely pairwise data can
  force exact all-prime coherence at the critical Euler weight. It identifies a precise place where
  the pair-face structure of general hypertranscendence can interact with the RH polarization
  problem without pretending that hypertranscendence itself implies RH.

### Partial priority audit

Targeted exact, stronger-parent, and mechanism searches located:

- Connes--Moscovici, *Prolate spheroidal operator and Zeta*, for the Sonin/prolate carrier and its
  RH motivation, but not tensor-square Calkin coefficient recovery or prime-pair coherence;
- Larsen--Li, *Dilations of semigroup crossed products as crossed products of dilations*, and the
  Davidson--Fuller--Kakariadis semicrossed-product theory, for the general crossed-product parent of
  dilation actions, but not the fixed-Sonin common-shell estimate or reciprocal-prime consequence;
- general Toeplitz essential-norm and product-system literature, but no located theorem with the
  displayed `1/(pq)` pair energy on a Sonin carrier.

No exact statement was found in this pass. This is evidence for continued audit, not a priority
certificate.

## Gates

- [x] 0 -> 1: exact tensor-square statement, proof mechanism, and falsifiers isolated
- [x] 1 -> 2: complete paper proof including compact perturbations and the all-prime consequence
- [ ] 2 -> 3: formalize the Hilbert tensor-product estimate and prime-coherence endpoint in Lean
- [ ] 3 -> 4: independent priority audit and construction of a genuine polarization-potential map

## Log

- 2026-07-10 -- Tensorized the common-shell matrix coefficient, proved the weighted pair Calkin
  lower bound, and used reciprocal-prime infinite mass to force exact coherence of prime
  potentials.
