# Height-adaptive cancelled-source socle--Weyl contradiction to RH

- **ID:** `height-adaptive-cancelled-source-socle-weyl-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONTRADICTION ROUTE] [CONDITIONAL RH CHAIN]`
- **Scientific status:** the local algebra and determinant argument are classical bridges; no new
  scientific-knowledge claim is made without the source descent
- **Inputs:** `height-adaptive-adjacent-divisor-census-collision.md`,
  `CCMSharpPrimeWindowCancellation.lean`, `PrimeDyadicWeyl.lean`,
  `CutoffWeylBoundary.lean`, `WeldWeylMultiplicity.lean`

## Claim

The adjacent cancelled-source collision has a source-module form which is strictly more aggregate
than the existing pointwise multiplicity--Weyl route.  On one bounded admissible domain inside the
shifted right critical half-strip, form the finite zero algebra of the shifted regularized zeta and
let the explicit cancelled sharp source act by multiplication.  Its image has one dimension per
distinct zero, independent of every local multiplicity.  A single internal dyadic Weyl pair on
that image, at one height-adapted depth larger than the zero-count envelope, forces the domain to be
zero-free.  Cofinal exhaustion then proves RH by contradiction.

## Source algebra and the adjacent operator

Write

```text
A(s) = regularizedRiemannZeta(s-1/2),
C(s) = dyadicSharpPrimeCancelledSource(s).
```

Let `Omega` be a bounded admissible domain compactly contained in

```text
1 < Re(s) < 3/2
```

whose boundary contains no zero of `A`.  Use the algebra of germs on a neighborhood of the compact
zero set in `Omega` and define the finite source zero algebra

```text
Q_Omega = O(Omega)/(A),
L_C : Q_Omega -> Q_Omega,     [f] |-> [C f].
```

This construction uses the explicit source function `A`; it does not enumerate or factor its
zeros.  Its semilocal decomposition is used only to prove the following value theorem.

## Socle-rank theorem

`[PROVED ON PAPER]` Suppose `p` is a zero of `A` of order `m>=1`.  The exact cancelled-source
order-loss theorem gives

```text
ord_p(C)=m-1.
```

In a local coordinate `x=s-p`, there are units `u,v` with

```text
A=x^m u,             C=x^(m-1) v.
```

Consequently

```text
Q_p = C{x}/(x^m),
im(L_C|Q_p) = C * [x^(m-1)],
ker(L_C|Q_p) = ([x]),
dim im(L_C|Q_p) = 1,
dim coker(L_C|Q_p) = m-1.
```

The image is the socle of `Q_p`.  Summing the local decompositions gives

```text
dim Q_Omega       = M_Omega = sum_p m_p,
dim coker L_C     = P_Omega = sum_p (m_p-1),
dim im L_C        = D_Omega = number of distinct zeros,
M_Omega = P_Omega + D_Omega.                         (1)
```

Thus the adjacent common-divisor census is the cokernel length of one explicit multiplication
operator, while its difference from the total Xi census is the rank of that operator.  This is a
source-module realization of the finite algebra in the formal adjacent-census capstone.

## Contradiction chain

Let `k` be chosen so that the unconditional zero-count envelope gives

```text
0 <= D_Omega < 2^k.
```

Let `zeta_k` be the primitive `2^k`-th root supplied by the prime dyadic Weyl relation.  Assume the
source construction descends to invertible complex-linear maps on the actual socle

```text
U_k,V_k : im L_C -> im L_C
```

such that

```text
U_k V_k = zeta_k V_k U_k.                              (2)
```

Taking determinants in `(2)` gives

```text
zeta_k ^ D_Omega = 1,
2^k divides D_Omega.
```

Together with the strict bound this forces `D_Omega=0`.  Equivalently, `Q_Omega=0`, so `A` has no
zero in `Omega`.  If RH were false, a shifted right-half Xi zero would lie in some bounded
admissible domain of a cofinal exhaustion; applying the preceding argument to that domain gives
both `D_Omega>0` and `D_Omega=0`, a contradiction.  Therefore the cofinal source--socle Weyl supply
implies RH.

This differs from the pointwise SEM Weyl route.  It asks for one action on the squarefree socle of
the whole bounded source algebra, not an action on every local multiplicity space and not all
dyadic depths.  The required depth may vary with the domain and only has to dominate its
unconditional zero-count envelope.

## Raw-boundary no-go and positive statement

`[PROVED ON PAPER]` The common-divisor length cannot be recovered from the homotopy class of the
raw boundary map `(A,C): boundary(Omega) -> C^2 \ {0}`.  For a sufficiently small generic nonzero
constant `epsilon`, compact boundary separation makes `(A,C+t epsilon)` a boundary homotopy, while
finiteness of the zeros of `A` lets `epsilon` avoid every value `-C(p)` and hence removes all common
zeros of `A` and `C+epsilon`.

**Positive statement:** the stable source object is not the raw pair-valued boundary map.  It is
the finite zero algebra together with the multiplication operator `L_C`, or equivalently its
Fitting/subresultant module.  Any boundary construction must first produce that module or a
derived incidence object retaining the same cokernel length.

## Source attack and exact open core

The global source already supplies, for every prime `p` and depth `k`, the exact relation between
spectral translation and Euler multiplication

```text
T_(p,k) M_p = zeta_k M_p T_(p,k).
```

Euler multiplication is invertible and preserves source multiplication.  Translation does not
preserve the ideal `(A)` and therefore does not automatically act on `Q_Omega` or its socle.  The
open theorem is:

There is now a sharp restriction on what such a descent can mean.  The paper theorem
`prime-modulated-weyl-idealizer-collapse-on-xi-sampling.md`, with algebraic core formalized in
`PrimeWeylSamplingIdealizer.lean`, proves that every finite shift--differential prime operator
preserving the full real-Xi sampling nullspace collapses to a polynomial multiplier; all descended
operators commute.  This does not by itself exclude an action on one finite off-line socle, since
finite sampling support is an explicit boundary case.  It does exclude any cofinal construction
whose finite-prime operators extend compatibly to an idealizer of the full Xi sampling quotient.

**Positive statement:** a surviving cofinal descent must remain an integral boundary-completed
action before passage to the full sampling quotient, or use a genuinely all-prime/nonlocal
incidence operator.  The finite-prime idealizer cannot be the final carrier.

> `[OPEN CORE]` Construct, from the global prime translation--Euler pair and the admissible-domain
> source quotient, a cutoff or derived reduction whose induced operators preserve `im L_C`, are
> invertible there, and satisfy `(2)` at one depth above the domain's zero-count envelope.

The cutoff Weyl identity already says that the projective relation survives exactly when the two
directed boundary-corner products balance.  The source problem is therefore a concrete aggregate
boundary-incidence theorem, followed by invertibility on the socle.  No local multiplicity
divisibility is requested.

## Kill conditions and positive residues

1. **Arbitrary Weyl structure.**  Existence of a Weyl pair on a `D`-dimensional space is already a
   `2^k | D` statement.  The pair must be the explicit descent of the prime source operators.
   **Positive target:** prove the cutoff boundary balance and invertibility before computing `D`.
2. **External packet or tensor factor.**  Tensoring the socle with the standard clock--shift module
   manufactures divisibility.  **Positive target:** both maps act on `im L_C` itself.
3. **Zero enumeration.**  Defining the quotient as a direct sum after listing the zeros is only a
   proof device, not a source construction.  **Positive target:** construct `Q_Omega` as the
   quotient by the explicit function `A` and descend operators functorially.
4. **Full-algebra linearity.**  Endomorphisms linear over the commutative zero algebra commute, so
   they cannot carry a nontrivial Weyl phase.  **Positive target:** the translation generator must
   be semilinear or crossed-product-valued and may permute the squarefree components.
5. **Raw boundary homotopy.**  It forgets common-root length by the perturbation theorem above.
   **Positive target:** retain the Fitting/subresultant module or a derived incidence class.
6. **Full Hurwitz packet.**  A torsion Weyl action on all character components constrains only the
   packet dimension; complementary `L`-function zeros can compensate.  **Positive target:** the
   action must preserve the scalar-zeta socle before taking determinants.
7. **Moving-fiber holonomy alone.**  A projective loop between different fibers has no determinant
   divisibility consequence on one finite space.  **Positive target:** close the loop as actual
   endomorphisms of the fixed aggregate socle.
8. **Cofinal finite-prime sampling idealizer.**  On the full real-Xi sampling quotient every such
   idealizer collapses to commuting polynomial multiplication.  **Positive target:** retain the
   integral cutoff boundary before the full-divisor limit, or construct a closed all-prime/nonlocal
   incidence whose finite reductions act internally on `im L_C`.

## Formalization decision

No new Lean wrapper is added at this stage.  `WeldWeylMultiplicity.lean` already proves the needed
determinant divisibility, and `XiHeightAdaptiveAdjacentCensusCollision.lean` already proves the
height-adapted RH capstone.  The new content is the analytic source-algebra identification and the
source descent; formalizing another hypothesis package before that descent exists would add no
proof strength.

## Gates

- [x] exact cancelled-source local order loss
- [x] zero-algebra socle rank and adjacent cokernel formula on paper
- [x] height-adapted Weyl divisibility contradiction on paper
- [x] raw boundary-pair homotopy no-go and positive replacement
- [ ] source construction of the bounded zero algebra in the formal analytic category
- [ ] internal prime dyadic Weyl descent to the actual aggregate socle
- [ ] cofinal source theorem and unconditional RH
