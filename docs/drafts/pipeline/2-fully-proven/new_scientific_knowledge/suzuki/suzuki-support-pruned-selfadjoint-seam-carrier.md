# Support-pruned prime seams have an exact self-adjoint Hilbert carrier

- **ID:** `suzuki-support-pruned-selfadjoint-seam-carrier`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-SPECIFIC OPERATOR CONNECTOR
- **Scientific status:** `[PROVED HERE] [SOURCE-SPECIFIC IDENTIFICATION]`
  `[ABSTRACT COMPRESSION STANDARD] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Input:** `suzuki-two-root-valuation-wiener-lift.md`,
  `suzuki-completed-zero-mode-corona-seam-law.md`

## 1. Exact carrier

Fix an aperture \(a>0\).  Let \(P_a\) be the finite set of primes occurring among Suzuki's
visible prime powers \(p^j\leq e^{2a}\), and put

```text
Gamma_a = Z^(P_a),
lambda(nu) = sum_p nu_p log p.
```

Let `Root={left,right}` and define the oriented seam vertices

```text
V_a = Root x Gamma_a,
x(left,nu)  = -a+lambda(nu),
x(right,nu) =  a-lambda(nu),
S_a = {(root,nu) : |x(root,nu)|<a}.                    (1)
```

The two root labels are **oriented germ labels**, not a claim that evaluation in physical space is
injective.  At an opposite-end resonance two vertices can have the same physical coordinate, but
their one-sided punctured germs have opposite orientations and remain separately recoverable.  This
is exactly the oriented collision law already proved in
`suzuki-completed-zero-mode-corona-seam-law.md`.

Set

```text
H_a = ell^2(V_a),      P_a^S c = 1_(S_a)c.             (2)
```

For \(\delta\in\Gamma_a\), let

```text
(U_delta c)(root,nu)=c(root,nu-delta).                  (3)
```

Then \(U_\delta\) is unitary and \(U_\delta^*=U_{-\delta}\).

For every visible prime power \(p^j\), put

```text
delta_(p,j)=j e_p,
w_(p,j)=(log p)/p^(j/2)>0.                              (4)
```

Suzuki's exact finite-aperture prime symbol

```text
- sum_(p^j<=e^(2a)) w_(p,j)
    [exp(+i xi j log p)+exp(-i xi j log p)]             (5)
```

therefore has the coefficient-space realization

```text
A_a^prime
 =-sum_(p^j<=e^(2a)) w_(p,j)
     (U_(delta_(p,j))+U_(delta_(p,j))^*),               (6)
T_a=P_a^S A_a^prime P_a^S.                              (7)
```

The sign in `(6)` is already Suzuki's negative prime sign.  In formulas written in normalized
Gamma form as `scalar Gamma operator - T_a^Gamma`, the positive adjacency is

```text
T_a^Gamma=-T_a.                                         (7a)
```

Both operators are bounded and self-adjoint.  Confusing `T_a` with `T_a^Gamma` reverses the
literal prime term.

### Theorem

`[PROVED]` The operators `(6)` and `(7)` are bounded and self-adjoint.  Moreover

```text
||A_a^prime||
 <=2 sum_(p^j<=e^(2a)) (log p)/p^(j/2),                 (8)
```

and, for \(q=(r,\nu)\),

```text
(T_a c)(q)
=1_(S_a)(q)
  [-sum_(p^j<=e^(2a)) w_(p,j)
    {1_(S_a)(r,nu-delta_(p,j))c(r,nu-delta_(p,j))
     +1_(S_a)(r,nu+delta_(p,j))c(r,nu+delta_(p,j))}].   (9)
```

Thus every power \(T_a^k\) sums exactly the length-\(k\) prime words whose **every intermediate
vertex** stays in the aperture.  No path is restored after leaving the interval.

### Proof

Translation of the discrete group \(\Gamma_a\) is a bijection, hence `(3)` permutes the standard
orthonormal basis and is unitary.  Its inverse is translation by \(-\delta\), so
\(U_\delta^*=U_{-\delta}\).  Consequently every
\(U_\delta+U_\delta^*\) is self-adjoint and has norm at most two.  The visible prime-power set is
finite.  Finite real linear combination gives self-adjointness of `(6)`, and the triangle
inequality gives `(8)`.

Coordinate restriction in `(2)` is an orthogonal projection:

```text
(P_a^S)^*=P_a^S=(P_a^S)^2.
```

Therefore

```text
T_a^*=(P_a^S A_a^prime P_a^S)^*
     =P_a^S (A_a^prime)^* P_a^S
     =T_a.
```

Expanding the two translations and the two projections gives `(9)`.  In a product
\((PAP)^k\), the factor \(P\) occurs before and after every occurrence of \(A\); induction on
\(k\) therefore deletes exactly, and only, paths with an inadmissible intermediate vertex.
`QED`

## 2. Endpoint forcing is not homogeneous adjacency

The root vertices \((\mathrm{left},0)\) and \((\mathrm{right},0)\) have physical locations
\(-a\) and \(a\), so neither belongs to the strict interior set \(S_a\).  Hence an endpoint
half-log coefficient enters the interior problem through a boundary injection

```text
B_a(beta_left,beta_right),
```

not as a coordinate of the homogeneous operator \(T_a\).  This separates two mathematically
different questions:

```text
finite prime transport inside aperture  -> bounded self-adjoint T_a;
endpoint completed-domain data          -> forced boundary current B_a beta.  (10)
```

When both signed traces vanish, the root forcing in `(10)` vanishes.  This does **not** yet prove
that the remaining completed-domain state is in
\(L^2(dL;H_a)\), nor that regular forcing has Gamma-strip width greater than \(1/2\).

## 3. Hostile audit

1. **No false spatial injectivity.**  The evaluation
   \((r,\nu)\mapsto x(r,\nu)\) can identify opposite roots.  The theorem uses oriented germ labels,
   whose independence comes from opposite one-sided restrictions, not from spatial separation.
2. **No source-domain smuggling.**  `(2)` constructs the exact Hilbert carrier for a
   square-summable oriented coefficient state.  It does not assert that every vector in Suzuki's
   completed form domain already has such a state.  The subsequent evaluation-rigging theorem
   sharpens this warning: unit-phase scalar evaluation is unbounded on every infinite `ell2`
   seam sector.  A literal realization must land in `ell1 subset ell2` (or an equivalent nuclear
   rigging), not merely in `ell2`.
3. **No positivity claim.**  The minus sign in `(5)` is retained.  Self-adjointness gives skew
   radial transport after Fourier differentiation; it gives no positivity of the restricted Weil
   form.  Gamma-normalized formulas use `T_a^Gamma=-T_a`, not `T_a`.
4. **No unpruned path substitution.**  Formula `(9)` inserts the support projection at every step.
   The unrestricted Laurent convolution and the pruned graph agree only on paths that remain
   admissible throughout.
5. **No RH conclusion.**  This closes an operator-realization ambiguity only.  It cannot decide the
   two-port Hardy kernel or the raw Evans determinant.

## 4. Exact frontier movement

Before this theorem, failure of self-adjointness under dense, support-pruned prime propagation was
listed as a possible escape from the Gamma-current Liouville law.  Formula `(7)` removes that
escape: finite prime transport is an orthogonal compression of a finite real symmetric Laurent
polynomial, even though its spatial orbit is dense.

The remaining RH-bearing seam is now exact:

```text
completed Suzuki zero mode with beta_left=beta_right=0
  -> construct its ell1(S_a)-valued logarithmic tail, hence an H_a-valued L2 tail
  -> reconstruct the scalar mode through bounded ell1 phase evaluation
  -> Gamma-current Liouville kills homogeneous component
  -> prove forced component has strip width sigma>1/2
  -> H1_0 connector.                                    (11)
```

No claim in `(11)` after the first arrow is proved here.  The impossibility of replacing the
first two arrows by a bounded `ell2 -> scalar` evaluation is proved in
`suzuki-support-pruned-evaluation-rigging-fracture.md`.

## 5. Lean decision

The exact unconditional operator content—unitary valuation shifts, symmetric finite prime
adjacency, orthogonal support compression, and self-adjointness—is formalized in

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiSupportPrunedSelfAdjointSeamCarrier.lean
  SuzukiSupportPrunedSeamCarrierBounds.lean
```

The first module carries the carrier, the oriented shift `(3)`, the symmetric step, the finite
prime adjacency `(6)`, the compression `(7)`, the Gamma-normalized sign `(7a)`, self-adjointness of
all three, and the endpoint non-admissibility of section 2:

```text
suzukiSeamLocation, suzukiAdmissibleSeamVertices, suzukiSeamHilbert
suzukiSeamShift, suzukiSeamShift_apply
suzukiSymmetricSeamStep, suzukiSymmetricSeamStep_apply
suzukiSymmetricSeamStep_isSelfAdjoint
suzukiFinitePrimeAdjacency, suzukiFinitePrimeAdjacency_isSelfAdjoint
suzukiSupportPrunedPrimeAdjacency, suzukiSupportPrunedPrimeAdjacency_isSelfAdjoint
suzukiGammaPositivePrimeAdjacency, suzukiGammaPositivePrimeAdjacency_isSelfAdjoint
suzukiSeamRoot_left_not_admissible, suzukiSeamRoot_right_not_admissible
```

The second module closes the two remaining statements of the theorem — the adjoint law
`U_delta^* = U_(-delta)`, the norm bound `(8)`, and the explicit pruned action `(9)`:

```text
suzukiSeamShift_adjoint                        U_delta^* = U_(-delta)
norm_suzukiSeamShift_le                        ‖U_delta‖ ≤ 1
norm_suzukiSymmetricSeamStep_le                ‖U_delta + U_delta^*‖ ≤ 2
norm_suzukiFinitePrimeAdjacency_le             (8): ‖A_a^prime‖ ≤ 2 ∑ |w|
suzukiFinitePrimeAdjacency_apply               coordinatewise action of A_a^prime
suzukiSupportPrunedPrimeAdjacency_apply        (9): the pruned action, with the aperture
                                               indicator applied to every neighbour
norm_lpCoordinateProjection_le                 the aperture compression is a contraction
norm_suzukiSupportPrunedPrimeAdjacency_le      ‖T_a‖ ≤ 2 ∑ |w|
norm_suzukiGammaPositivePrimeAdjacency_le      ‖T_a^Gamma‖ ≤ 2 ∑ |w|
```

Formula `(9)` is the exact source of the "no path is restored after leaving the interval" claim:
each of the two neighbours enters only through its own aperture indicator, and a vertex outside the
aperture is annihilated outright.  Since `T_a = P A P` with `P` idempotent, every power `T_a^k`
inserts `P` before and after each `A`, so only prime words all of whose intermediate vertices stay
admissible survive.

Lean deliberately does not contain a theorem asserting the unproved completed-domain arrow in
`(11)`.
