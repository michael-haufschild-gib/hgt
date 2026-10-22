# The CCM characteristic Evans boundary state has infinite rank

- **ID:** `ccm-characteristic-evans-boundary-infinite-rank-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Kronecker's finite-rank Hankel theorem, the meromorphic digamma pole lattice, and
  `ccm-characteristic-crossing-interior-mode-reduction-law.md`

## Statement

Fix an aperture `a>0`. Let `W_a` be the corrected polar--Euler--Gamma symbol and factor its finite
real characteristic set as

```text
W_a=b_a c_a,
b_a(xi)=p_a(xi)/(1+xi^2)^L,                               (1)
```

where `p_a` is the real characteristic polynomial and `c_a` is real-zero-free. Let `k_a` be the
distribution kernel of `c_a(D)`. Define the right exterior trace map

```text
E_(a,+):u |->1_(a,infinity)c_a(D)u,
supp u subset [-a,a].                                     (2)
```

Then `E_(a,+)` has infinite rank. The same holds for the left exterior trace. Consequently the
source-defined characteristic Evans relation cannot be replaced by the raw finite interior
characteristic packet alone.

## 1. Infinite meromorphic pole lattice

The analytic continuation of the Gamma symbol is

```text
m_C(z)
 =(1/2)(psi(1/4+i z/2)+psi(1/4-i z/2))-log pi.           (3)
```

It has simple poles at

```text
z=plus_or_minus i(2n+1/2),       n=0,1,2,... .           (4)
```

The finite prime cosine sum and the aperture polar multiplier are entire. The factor `(1)` is
rational and removes only finitely many real zeros. Therefore `c_a` retains the infinite pole
lattice `(4)` and is not rational.

## 2. Exterior trace is a Hankel kernel

For `x>a` and `y in (-a,a)`, one has `x-y>0` and

```text
(E_(a,+)u)(x)=integral_(-a)^a k_a(x-y)u(y)dy.             (5)
```

After the changes of variables `s=x-a>0` and `t=a-y in (0,2a)`, equation `(5)` has kernel

```text
k_a(s+t).                                                 (6)
```

Thus every bounded truncation of the exterior map is a Hankel integral operator.

## 3. Infinite-rank proof

Assume that `E_(a,+)` has finite rank `N`. Restrict its output to any interval `(a,a+epsilon)`.
The Hankel operator with analytic kernel `(6)` still has rank at most `N`. The local form of
Kronecker's finite-rank Hankel theorem forces

```text
k_a(t)=sum_(j=1)^J P_j(t)exp(lambda_j t),
J<=N,                                                     (7)
```

on a nonempty positive interval, with polynomials `P_j`. The kernel is real analytic for `t>0`, so
analytic continuation extends `(7)` throughout the positive half-line. Its Laplace transform is
rational, with only finitely many poles and finite Jordan orders.

That Laplace transform is the appropriate half-plane branch of `c_a`. This contradicts the
infinite pole lattice `(4)`. Hence `E_(a,+)` has infinite rank. Reflection gives the left-hand
statement. `QED`

## Positive CCM consequence

The interior reduction

```text
v=c_a(D)u,
p_a(D)v=0 on (-a,a)                                      (8)
```

is finite-dimensional, but the complete boundary state is not. Every successful CCM screw proof
must therefore carry

```text
finite real characteristic packet
  + infinite Gamma exterior-trace state
  + two-sided support matching
  + mean-zero and affine anchors.                         (9)
```

The native Evans object is an operator/Fredholm relation on an infinite-dimensional boundary
space, possibly with a finite characteristic block attached. A finite effective determinant is
legitimate only after an exact Wiener--Hopf/Fredholm Schur-complement elimination whose entries
retain the resolvent of that infinite block. A raw characteristic determinant whose entries use
only `p_a`, or any fixed finite boundary jet, necessarily discards source data.

This remains true in the prime-free small-aperture regime of
`ccm-prime-free-aperture-characteristic-pair-law.md`. There the ambient symbol has a real
characteristic pair and the screw operator is known to be injective; the injectivity is paid for by
the infinite Gamma boundary state, not by absence of interior modes.

`[PROVED SUBSEQUENT REDUCTION]` After the infinite state is reconstructed exactly by the logarithmic
Dirichlet inverse, the rational factor `p_a/(1+xi^2)^(d_a/2)` transmits only a `d_a`-dimensional
exponential-polynomial residual to the interior. Hence an exact finite Gram determinant does exist,
but its entries retain the full infinite reconstruction. This is proved in
`ccm-rational-residual-finite-evans-matrix-law.md` and does not contradict the infinite-rank theorem.

## Classification and Lean decision

Kronecker's theorem and the digamma pole lattice are classical. Their application here is a route
bridge, not new scientific knowledge. The formal tree lacks analytic half-line Hankel kernels,
Kronecker's theorem, and the meromorphic full CCM symbol. A finite-dimensional formal shadow would
contradict the theorem's content, so no Lean wrapper is added.

## Gates

- [x] infinite digamma pole lattice retained after characteristic factorization
- [x] exterior trace identified as a Hankel kernel
- [x] finite exterior rank contradicted by Kronecker's theorem
- [x] raw characteristic-only finite determinant shortcut retired
- [ ] construct the infinite-dimensional Fredholm Evans operator
- [x] construct its exact finite effective residual while retaining the infinite boundary resolvent
- [ ] prove its kernel is zero through every aperture
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "no Lean wrapper is added" decision recorded above, which is stale.
The worry there was that a *finite-dimensional* shadow would contradict the theorem; the module
below states the theorem in its genuine direction — no finite-dimensional space contains the Hankel
columns — so nothing is weakened.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMEvansBoundaryInfiniteRank.lean`
(10 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired
into `formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `exterior_displacement_split` — **equations (5) → (6)**: `x - y = (x-a) + (a-y)`, the exact change
  of variables that turns the exterior trace into a Hankel kernel.
- `hankelColumn`, `hankelColumn_eq_realTranslate` — **equation (6)**: the columns `t ↦ k(s+t)` of
  the Hankel kernel are exactly the translates of `k`.
- `mem_expPolySpace_of_hankelColumns` — **section 3, Kronecker step**: if every Hankel column lies
  in one finite-dimensional space then the translation span of `k` is finite-dimensional, so by the
  Anselone–Korevaar equivalence (`HTGeometry.mem_expPolySpace_iff_finiteDimensional_translationSpan`,
  the continuous form of Kronecker's finite-rank Hankel theorem, already in the corpus) `k` is an
  exponential polynomial.
- `exists_finite_frequencies` — **equation (7)**: such a kernel is a finite sum of blocks
  `P_j(t) e^{λ_j t}`, i.e. it has only finitely many frequencies.
- `exists_entire_extension_of_hankelColumns` — the regularity step: a finite-rank Hankel kernel
  extends to an **entire** function, so its continuation has no singularity at all.
- `not_hankelColumns_finiteDimensional` — **the infinite-rank theorem**: contrapositively, a
  continuous kernel with no entire extension admits *no* finite-dimensional space containing all of
  its Hankel columns.  This is the card's conclusion for `E_{a,+}`.
- `digammaArgument_eq_neg_natCast_iff`, `digammaArgumentNeg_eq_neg_natCast_iff` — **equation (4)**:
  the two digamma arguments `1/4 ± i z/2` hit the nonpositive integer `-n` exactly at
  `z = ± i(2n + 1/2)`.
- `gammaPoleLattice`, `gammaPoleLattice_infinite` — the pole lattice is infinite.
- `not_subset_rootSet_of_gammaPoleLattice` — **section 1, conclusion**: the lattice is not contained
  in the zero set of any nonzero polynomial, so a rational factorization cannot absorb it and `c_a`
  is not rational.

Reused, not rebuilt: `HTGeometry.realTranslate`, `translationSpan`,
`mem_expPolySpace_iff_finiteDimensional_translationSpan`,
`exists_expMonomialSpace_of_mem_expPolySpace` (`AnseloneKorevaarTranslationRank`);
`expPolySpace`, `exists_entire_extension`, `analyticOnNhd_of_mem_expPolySpaceC`
(`RealExponentialPolynomial`); `expMonomialSpace_le_blockSpan` (`ExponentialPolynomialModes`, built
for `ccm-characteristic-crossing-interior-mode-reduction-law`).

Deliberately outside the Lean statement (cited parents, not results of this card):

- The distribution kernel `k_a` of `c_a(D)` and the integral form `(5)` of the exterior trace.
- The meromorphic continuation `(3)` of the Gamma symbol and the identification of its poles with
  the poles of `Γ` — only the *lattice* `(4)` is formalized.
- The identification of the Laplace transform of the kernel with the half-plane branch of `c_a`.
