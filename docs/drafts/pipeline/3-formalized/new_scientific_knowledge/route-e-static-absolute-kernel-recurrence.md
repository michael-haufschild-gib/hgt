# Route E static absolute cross-prime kernel recurrence

- **ID:** `ROUTE-E-STATIC-ABSOLUTE-KERNEL-RECURRENCE-001`
- **Stage:** 3-formalized
- **Type:** `[EXHAUSTIVE PRODUCER-CLASS NO-GO]` / `[POSITIVE ROUTE CONSTRAINT]`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL AUDIT OMITTED BY INSTRUCTION]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no

## Purpose

The static diagonal dichotomy leaves an apparent off-diagonal escape.  This theorem closes every
fixed cross-prime kernel whose matrix entries are absolutely summable.  Positivity, Hermitian
symmetry, finite rank, and diagonal structure are not assumed.  Simultaneous prime-phase recurrence
kills a finite matrix head, while absolute summability kills its complete infinite tail.

This still does not close Route E.  A surviving cross-prime producer must move with physical
aperture/frequency or possess a singular non-absolutely-summable principal part with a source-given
renormalization.

## Exact theorem

Let \(K=(K_{pq})_{p,q\in\mathbb P}\) be any complex kernel satisfying

\[
 \sum_{p,q}|K_{pq}|<\infty.                              \tag{1}
\]

Put \(v_p(t)=1+e^{it\log p}\) and define the absolutely convergent cross-prime form

\[
 \mathcal Q_K(t)=\sum_{p,q}K_{pq}v_p(t)\overline{v_q(t)}. \tag{2}
\]

Then for every \(\delta>0\) and \(T\in\mathbb R\), there exists \(t>T\) such that

\[
 \boxed{|\mathcal Q_K(t)|<\delta.}                       \tag{3}
\]

Consequently no fixed absolutely summable cross-prime kernel can have a positive uniform lower
bound in modulus.  This includes every nonnegative diagonal summable frame, every finite-rank
kernel with absolutely summable entries, and every positive/Hermitian kernel satisfying `(1)`.

## Proof

Since \(|v_p(t)|\le2\), each summand in `(2)` has norm at most \(4|K_{pq}|\); `(1)` gives absolute
convergence for every \(t\).

Fix \(\delta>0\).  Choose a finite pair set \(A\subset\mathbb P^2\) such that

\[
 \sum_{(p,q)\notin A}4|K_{pq}|<\delta/2.                 \tag{4}
\]

Let \(P\) contain every prime occurring as either coordinate of a pair in \(A\), and set
\(H=\sum_{(p,q)\in A}|K_{pq}|\).  Choose \(\varepsilon>0\) with
\(H\varepsilon^2<\delta/2\).  Rational independence of \(\{\log p:p\in P\}\), followed by
cofinal Kronecker recurrence to the torus point with every coordinate \(-1\), supplies \(t>T\)
such that

\[
 |v_p(t)|<\varepsilon\qquad(p\in P).                    \tag{5}
\]

Every pair in \(A\) has both coordinates in \(P\), so its contribution has norm at most
\(|K_{pq}|\varepsilon^2\).  Hence finite-head norm is below \(H\varepsilon^2<\delta/2\).
The complementary infinite tail is below \(\delta/2\) by `(4)` and the factor-four ceiling.
Triangle inequality proves `(3)`.

## Hostile audit

1. Complete ordered prime-pair `tsum` is controlled; theorem is not finite dimensional.
2. Kernel need not be diagonal, positive, Hermitian, or finite rank.
3. Cancellation inside kernel is not used.  Result follows from absolute tail control and one
   common source recurrence.
4. The theorem does not cover aperture-dependent kernels \(K_x\), frequency-dependent kernels,
   or kernels with non-absolutely-summable principal part defined through a signed/source
   renormalization.
5. It proves no Möbius estimate; `OPEN-SOURCE-001` remains open.

## Positive survivor

Route E cannot be repaired by replacing static diagonal weights with a regular static
off-diagonal matrix.  Any viable quadratic producer must contain at least one load-bearing feature:

- moving support/weights coupled to physical Gibbs boundary;
- a non-absolutely-summable singular cross-prime principal part plus canonical source
  renormalization; or
- a signed nonquadratic statistic that cancels terminal antiscale shells before positive norm.

Combined with parity-coarse determinant law, survivor must still generate
\(D_{\rm anti}\) or within-parity variation at physical-power strength.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/RouteEStaticAbsoluteKernelRecurrence.lean`.

Unconditional declarations:

- `norm_routeEStaticAbsoluteKernelTerm_le_four`;
- `summable_routeEStaticAbsoluteKernelTerm`;
- `exists_gt_norm_tsum_routeEStaticAbsoluteKernelTerm_lt`;
- `not_exists_uniformly_coercive_routeEStaticAbsoluteKernel`.

The recurrence theorem is over complete `Nat.Primes × Nat.Primes` and an actual complex `tsum`.
Targeted audit:
`lake build GaloisForLFunctions.RHTower.RouteEStaticAbsoluteKernelRecurrence` passed `9720/9720`.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.  Module is wired into
`GaloisForLFunctions.RHTower`; it contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
