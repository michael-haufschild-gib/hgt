# Route E: common divisors of conditioned slot receivers

- **ID:** E-CONDITIONED-SLOT-DIVISORS-001
- **Stage:** 3-formalized
- **Target:** test source arithmetic that survives arbitrary product-window conditioning.
- **Status:** exact divisor law, literal-history transfer, and stronger source-derived bounded-activation support obstruction are closed in Lean and pass the final targeted build.
- **Parent:** [boundary-mass closure](../5-failed/route-e-negligible-discard-integer-cells.md).

## Source and exact support law

Keep literal singleton histories with positive integer inactive factors
`a_c` and active factors `b_c`. A component is active in exactly one slot.
Let `A=prod_c a_c`, and let `q>=2` distinct slot receivers lie in an
interval of width `W`. The selected slots may be only part of the history.
Theorem:

```
A^(q-2) <= W^q.
```

This does not assume independence, a counting law, a complete cell, or
coprimality. Distinctness concerns physical integer receiver values, not
merely different history labels.

## Proof

For each unordered pair of selected slots `r,s`, form `C_rs` from the
inactive factors of all components active in neither slot. This integer
divides both receivers, hence their nonzero difference. Therefore
`1<=C_rs<=W`.

Every component active at a selected slot contributes its inactive factor
to exactly `choose(q-1,2)` of these pair products. A component active
outside the selected slots contributes to all `choose(q,2)` pairs. Since
all factors are at least one,

```
A^choose(q-1,2) <= prod_(r<s) C_rs <= W^choose(q,2).
```

The Lean proof uses ordered pairs, giving exponents `(q-1)*(q-2)` and
`q*(q-1)`, and cancels the positive power `q-1` to obtain the bound. No distinct-prime or unique-factorization
premise is used: the divisibility comes directly from the literal product formula.

## Consequence to test against the source

For five distinct receivers, the law becomes `A^3<=W^5`. At the actual
window `W=2*sqrt(X)*exp(log(X)/log(log(X)))`, a schedule with
`log(A)/log(X)->1` would violate this inequality eventually. Each admitted
history then has at most four distinct receiver values. This does not
bound the union of receiver values across different histories. Larger distinct support forces a
smaller inactive baseline and therefore a substantial total activation
gain. The baseline condition is not automatic; it must be derived from
the proposed factor data before excluding a source construction.

## Unpaid endpoint

This tests unsigned receiver support and possible load collapse. It gives
no Möbius covariance bound. Independent correlated incidence remains open
unless its actual baseline and receiver multiplicities meet this test.
The ordered-pair divisor product identity, the bound `A^(q-2)<=W^q`
for `q>=2`, its literal selected-history transfer, and the growing-window
five-receiver obstruction now pass `lake env lean /tmp/route_e_slot_divisors.lean`.
The strengthened scratch also passes without diagnostics. The finished
`formal/GaloisForLFunctions/RHTower/RouteEConditionedSlotDivisors.lean`
passes `lake build GaloisForLFunctions.RHTower.RouteEConditionedSlotDivisors`
and is wired into `RHTower.lean`. No umbrella build was run. Do not infer
injectivity of physical receivers from history labels.

## Stronger source-derived baseline theorem

The stronger theorem derives the baseline from source factor sizes.
Suppose a fixed natural `K` satisfies `b_c<=a_c^K` for every
component, and one singleton history has `M>=10*(K+1)` slots, all in
`[L,L+W]` with `L>=0`. The exact histogram product identity gives

```
prod_r n_r = A^(M-1)*B,    B=prod_c b_c <= A^K,
L^M <= A^(M-1+K).
```

Raise the last inequality to the tenth power and use
`10*(M-1+K)<=11*M`. Since `A>=1` and `M>0`, cancellation of the `M`th
power gives `L^10<=A^11`. Five distinct receivers would also give
`A^3<=W^5`, hence `L^30<=A^33<=W^55`.

At the actual growing window, `W^55<L^30` eventually because
`log(W)/log(X)->1/2` and `log(L)/log(X)->1`. Thus each history in this class has at most
four distinct physical receivers regardless of conditioning, with no
assumed baseline limit and no independence assumption. The factor power
bound must be fixed along the source schedule; unrestricted growing
activation powers are not excluded. This full source-derived statement is
closed as `eventually_singleton_bounded_activation_no_five`; it has no
assumed logarithmic baseline limit. Its finite positive survivor is
`singleton_history_baseline_tenth_power`, derived from exact source
product conservation.

For example, `a_c>=2` and `b_c<=2*a_c` imply `b_c<=a_c^2`, because
`a_c^2-2*a_c=a_c*(a_c-2)>=0`. Thus the proved theorem applies to this
near-unit integer class with `K=2` and at least thirty slots. This is a
direct specialization of the general bound, not a separately built lemma.
It restricts distinct values within each history; it does not bound the
union across histories or forbid many slots from sharing a value.

## Discovery audit

Deep divisor-product and conditioned-exchange searches were partial and
returned no checked ingredient sets. Source inspection recovered exact
histogram product conservation, singleton slot counts, and off-diagonal
pair cardinality. Those source facts drive the new argument.

Broad September searches found [Coulomb partition-function estimates](https://arxiv.org/html/2609.00867v1).
The displayed estimate is for `E exp(-beta*U)` under an independent
reference law with exactly centered marginals. It controls the negative
energy tail. Neither that law nor its centering is established for the
literal Möbius prefixes, and the required covariance bound concerns the
upper side. No partition-function bound is transferred here.

The [Fraenkel conjecture preprint](https://arxiv.org/html/2609.01570v1)
uses minimum-gcd divisor concentration after Fourier cancellation of an
exact periodic partition. Its claimed closure also uses three finite
computational exclusions, which were not run or imported. No corresponding
periodic partition identity is established for the actual Route E source.

## Remaining source obligation

A construction requiring five distinct slot values within one history
must escape every fixed activation power bound, or use a different
activation histogram. Large support across different histories is not
excluded by this theorem.
Nontrivial factors with inactive value one are outside the displayed power
bound. These survivors still require a source-predeclared arithmetic
relation with unsigned load dispersion, co-degree and expansion estimates,
and the moving-cutoff charges. No claim of signed cancellation or RH follows
from the support theorem.

The finite theorem also allows varying activation powers whenever the
pointwise condition `M>=10*(K+1)` holds. Growth of `K` alone does not
evade that finite statement.

The [squarefree majority-sign theorem](route-e-squarefree-conditioned-majority.md)
proves that squarefreeness supplies a common repeated receiver across the literal conditioned cell.
For fixed activation powers it forces all but at most three slots per history to share that receiver
and gives an invariant-weight fixed-anchor Möbius bias of size `1-6/M`. This is an obstruction:
bounded support produces sign alignment rather than cancellation.

After the final leaf, `scripts/formal_tools.py index` completed and
`scripts/formal_tools.py lint --check-generated` passed with existing
large-file warnings. No own Lean process remains running.
