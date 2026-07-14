# Order-reparameterized charge-gate saturation law

- **ID:** homogeneous-charge-gate-power-saturation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Xi endpoint charge and thermal-orientation gate
- **Statement:** Every strictly increasing reparameterization of the Xi endpoint charge gate is exactly equivalent to the same source-selected squared-height floor; common powers are a special case.

## Goal

Separate genuinely stronger Xi information from algebraic repackaging of the endpoint charge.
The theorem identifies the full order-reparameterized family at once and positively characterizes
what a strictly stronger height theorem must carry: an observable containing information
independent of the single endpoint charge coordinate.

## Theorem

Let $\phi:\mathbb R\to P$ be a strict order embedding into any preorder. Then
$$
  \phi\!\left(\frac{4}{y+1}\right)\le \phi(C)
  \iff
  y\ge\frac{4-C}{C}
$$
for every $C>0$ and $y\ge0$. Thus any two strict order reparameterizations give logically
identical gates.

In particular, powers yield the following homogeneous family. For $C>0$, $y\ge0$, and every
$k\ge1$, define
$$
\mathcal G_k(C,y):
\qquad
\left(\frac{4}{y+1}\right)^k\le C^k.
$$
Then
$$
\mathcal G_k(C,y)
\iff
y\ge \frac{4-C}{C}.
$$
Consequently, for all $k,\ell\ge1$,
$$
\mathcal G_k(C,y)\iff\mathcal G_\ell(C,y).
$$
At $C=\Xi''(0)/\Xi(0)$, every off-line Xi zero satisfies all of these gates, and their common
content is precisely the linear quartet-charge height floor.

## Positive RH obligation

Any argument that improves the present zero-height collar must introduce a carrier not determined
by the single charge coordinate: for example a mixed-height correlation, a logarithmically weighted
source observable with independent scale data, or an exact source--divisor incidence estimate.
Powers, logarithms, exponentials, and all other common strict order reparameterizations cannot
improve the floor.

## Proof

Since $4/(y+1)\ge0$ and $C>0$, strict monotonicity of $x\mapsto x^k$ on the nonnegative reals
gives
$$
\left(\frac{4}{y+1}\right)^k\le C^k
\iff
\frac{4}{y+1}\le C.
$$
Because $C>0$ and $y+1>0$, clearing the positive denominators gives
$$
4\le C(y+1)
\iff
4-C\le Cy
\iff
\frac{4-C}{C}\le y.
$$
The power-invariance statement follows by applying this equivalence twice. For an off-line Xi zero,
the four-copy orbit bound and positivity of the endpoint cross charge give
$$
4\le C_{\mathrm{off}}(y+1)\le C(y+1),
$$
which is the common linear gate and hence every powered gate.

## Formalization

File:
`formal/GaloisForLFunctions/RHTower/XiHomogeneousChargeGateSaturation.lean`

Principal declarations:

- `orderReparameterizedChargeGate_iff_heightFloor`
- `orderReparameterizedChargeGate_invariant`
- `homogeneousChargeGate_iff_heightFloor`
- `homogeneousChargeGate_power_invariant`
- `xiCompletedCurvature_homogeneousChargeGate_iff_heightFloor`
- `xiZeroCopy_homogeneousChargeGate_all_powers`

The module checks independently. The formal lint gate passes, and the principal declarations use
only the standard logical quotient axioms already present in Mathlib.

## Gates

- [x] 0 → 1 in-progress: exact homogeneous family and proof identified
- [x] 1 → 2 fully-proven: unconditional algebraic proof complete
- [x] 2 → 3 formalized: theorem and Xi specialization checked
- [ ] 3 → 4 publication-ready: intentionally retained as a supporting bridge, not a standalone paper
