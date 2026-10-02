# TG mixed-prime reflected collision counterterm

- **ID:** TG-C5-MIXED-COLLISION
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / full source counterterm calculation
- **Route:** TG
- **Parent:** `../3-formalized/tg-reflected-burnol-cubic-collision.md`

## Hard target

Determine the complete mixed-prime principal cubic counterterm before attempting its
identification with Gamma/continuum completion. The desired final theorem remains an arithmetic
source-to-Hardy index identity with a residual nonnegative action and total budget below one.
This finite calculation is not that producer.

## Corpus audit

Mixed-prime search completed with full inventory, no errors, but background index refresh and
mostly source-only compiler metadata. Existing doubled Gram is orthogonal in theta and fixes
the neutral reference. The mixed Euler/Xi Schur-gap theorem shows positive compression has the
wrong domination direction. The existing negative Euler/Wold cubic channel is coefficientwise
and scalar: the direct-subunit-anchor card records intrinsic-clock collapse and raw overshoot.
It cannot be identified with the required mixed inverse-Gram counterterm from its budget alone.

## Source construction

For injective prime-depth labels put
`f_i(r)=A_i r exp(-lambda_i r)` and
`M_j(i,l)=A_i A_l (j+2)!/(lambda_i+lambda_l)^(j+3)`.
Here `M_j` is the literal moment Gram, not a diagonal replacement.
The common-clock reflected Gram is

```
c(k) = [[G,H(k)],[H(k)^*,G]],
G=M_0, H(k)_(i,l)=2 A_i A_l/(lambda_i+lambda_l-2 i k)^3.
```

In the even/odd basis, obtained by the constant Hadamard similarity, it factors as
`c_parity(k)=S(k) J(k) S(k)`, `S(k)=diag(I,kI)`. The entries of J extend rationally to k=0:

```
J(0)=2 [[G,-i M_1],[i M_1,M_2]].
```

This is the Gram of the confluent family `(sqrt(2) f_i,-i sqrt(2) r f_i)`.
Distinct literal decay rates make this family linearly independent. The corpus's
polynomial-exponential uniqueness theorem now supplies the audited proof.
Thus J(0) is invertible without a new analytic premise. Its lower-right inverse block is
`(1/2) K^-1`, `K=M_2-M_1 G^-1 M_1`. All cross-prime coefficients remain present.

## Proposed principal coefficient

Let U and V be the diagonal matrices of squared theta visibility and visibility times contrast.
In the parity basis,

```
p = (1/2)[[I,I],[I,I]],
q = [[I/2+V,U-I/2],[U-I/2,I/2-V]].
```

For arbitrary idempotent p,q and invertible c, cyclicity and the projection-cube identity give

```
Tr(c*C(c^-1 q c,q,p))
 = Tr(c p c^-1 q c (p-q)) + Tr(c (q p q-p q p)).
```

Only one inverse remains. The proposed source limit is therefore

```
lim_(k->0,k!=0) k^2 Tr(c(k)*C(c(k)^-1 q c(k),q,p))
 = -Tr(G K^-1 (U-I/2) G V).
```

For a single cell K=3d/(4lambda^2), recovering TG-C4's
`-2d v(2u-1)lambda^2/3`. For multiple cells this is not the sum of those one-cell coefficients.
The formula above is now verified in `PrimeBurnolMixedCubicPrincipal`, including its equality
with the original reflected source-coordinate cubic. It is only the leading coefficient;
the mixed first-order pole and bounded finite-part statement remain open.

## Gates

- [x] Source and full mixed coefficient conjecture fixed; prior research checked.
- [x] Literal confluent moment Gram and unconditional invertibility (production and axiom audits).
- [x] Exact rational parity factorization, continuous inverse at collision (production and axiom audits).
- [x] Full mixed principal coefficient proved in Lean.
- [ ] Actual Gamma/continuum countercurrent comparison.
- [ ] Residual sub-unit bound and Hardy-index identification.

## Current activity

The corpus search and production audits are complete for the full inverse collision.
`HTGeometry.expPolySum_eq_zero` separates polynomial coefficients at distinct nonzero nodes;
sampling the L2-zero combination at positive integers avoids importing an extra identity theorem.
The full mixed principal limit now passes its production audit. Next test cofinal operator
survival and actual arithmetic counterterm matching.

### Full cubic coefficient audit

The production check verifies continuity of the actual parity Gram, eventual punctured
invertibility, actual theta idempotence, the full block limit and the single-inverse cubic
passage. The finite theta values come from the corpus's `sech/tanh` polarization and its
proved Pythagorean identity. Exact conjugation invariance identifies the parity calculation
directly with the original reflected source coordinates.

Fresh corpus search returned complete inventory with compiler freshness mostly pending;
its broad semantic hits were mostly irrelevant. The focused lexical PrimeBurnol search
recovered the exact audited inverse and single-inverse cubic results. No prior completed
mixed theta cubic limit was found in those hits.

### Desingularization convention

For the implementation, absorb the odd-sector phase into the scaling matrix instead:
`T(k)=diag(I,i*k*I)`, `c_parity(k)=T(k) J(k) T(k)^*`.
Then `J(0)=2[[G,M_1],[M_1,M_2]]` is the unphased literal moment Gram.
This is equivalent to the phased convention above; its lower-right inverse block and the
proposed leading trace coefficient are unchanged. Entrywise rational formulas make J continuous
at zero without assuming an exchange of a derivative and an improper integral.

The combined scratch audit passed with no warnings. It proves literal radial jets in L2,
polynomial-exponential independence, the exact factorial moment matrix, rational source
factorization, continuous desingularized inverse, and the reduction to one inverse in the
weighted cubic. It also proves

```
lim_(k->0,k!=0) k^2 c_parity(k)^-1 = [[0,0],[0,(1/2)K^-1]],
K=M_2-M_1 G^-1 M_1, det K != 0.
```

These are unconditional finite-packet source statements, with injective prime-depth labels
bundled as an embedding. No diagonal replacement or assumed inverse is used. Separate production
leaf audits passed for `PrimeBurnolConfluentMomentGram` and
`PrimeBurnolMixedReflectedCollision`, with no warnings. All 21 public theorem axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`. The subsequent cubic principal coefficient
is now also production-checked. Finite invertibility alone does not give uniform control when
the prime-depth packet grows; the dedicated TG-C6 card records the new cofinal test.

The confluent corpus search returned useful polynomial-exponential uniqueness results despite
a semantic deadline (partial result, complete inventory). The earlier mixed-collision search
reported complete results. Both searches were checked against literal source definitions.
