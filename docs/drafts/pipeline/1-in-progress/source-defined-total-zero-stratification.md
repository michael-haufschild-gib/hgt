# Source-defined total stratification of the Xi divisor

- **ID:** `source-defined-total-zero-stratification`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / COMPLETE ZERO-GROUP PROGRAM
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`

## Exact completion claim

Construct a countable source-defined label type `I`, predicates `G_i(rho)` on Xi divisor copies,
and source certificates `C_i` such that:

1. **Position-neutrality:** definitions of `I`, `G_i`, and `C_i` use the Euler--Gamma source,
   functional equation, canonical operators, or source limits, but do not test `Re(rho)=1/2`, use a
   critical-line zero count, or label a zero by first knowing it is critical.
2. **Totality:** every Xi divisor copy belongs to at least one group:
   `forall rho : XiZeroCopy, exists i, G_i rho`.
3. **Controlled overlap:** either the groups are disjoint or every overlap is classified by an
   explicit refinement relation; arbitrary singleton/subset encodings are inadmissible.
4. **Non-vacuity/accounting:** each declared group is proved inhabited, or its emptiness is proved
   from source data and recorded as part of the classification.
5. **Independent forcing:** for every `i`, its source certificate proves unconditionally
   `G_i rho -> Re(rho)=1/2` by the mechanism assigned to that stratum.
6. **Formal closure:** the definitions, totality/overlap theorem, non-vacuity accounting, and every
   per-group forcing theorem are formalized in Lean without RH-equivalent assumptions.

Only this complete package closes the zero-group goal. A single subgroup theorem, a target-defined
partition, or a family whose totality assumes RH does not.

## Current frontier

- Horizontal multiplicity one is a non-vacuous divisor-defined group of positive lower density,
  but its density is a routine corollary of known critical/simple-critical proportions and its
  membership requires the full zero divisor. It is bridge/support material, not a source stratum.
- The endpoint-curvature band gives an unconditional source-produced placement theorem, but no
  noncomputational theorem currently proves the band contains a zero.
- Multiplicity ladders, orbit parity, charge visibility, window censuses, Hedenmalm multiplicity
  chains, and completed-flux graded reality classify target data or give RH-equivalent consumers;
  no audited family currently supplies totality plus unconditional per-stratum source forcing.

The internal and primary-literature audits are now exhaustive over the natural families encountered
in the project. Horizontal support/multiplicity, ordinary multiplicity, reflection orbits, Hardy or
Gram windows, heat-flow genealogy, Speiser geometry, Hedenmalm/de Branges carriers, automorphic
labels, explicit-prime labels, finite self-adjoint approximants, and Euler-region Pick inertia do
not give an already proved total placement cover. The only populated unconditional intrinsic group
is the horizontal-dominance group below; the only source-produced placement mechanism is the
bounded endpoint family.

For a zero `rho` of multiplicity `m(rho)`, let `h(Im rho)` be the total horizontal multiplicity.
Reflection gives the stronger elementary criterion

```text
2 * m(rho) > h(Im rho)  ->  Re(rho)=1/2.
```

Indeed an off-line zero has a distinct reflected partner of the same multiplicity, forcing
`h(Im rho) >= 2*m(rho)`. This strictly contains the singleton-horizontal group, but remains a
routine symmetry-counting bridge and is not a source stratum or a paper result.

## Foundational circularity attack

For any total family satisfying item 2, the conjunction of all item-5 forcing theorems implies RH.
Therefore the complete package is necessarily an RH proof. The grouping representation is useful
only if the labels expose genuinely smaller source theorems whose proofs do not share one hidden
RH-equivalent premise. Merely defining `G_0` to be the critical zeros, using singleton groups, or
setting the label equal to an RH certificate is circular and inadmissible.

## Rejected target-side obstruction stratification `[BRIDGE]`

Fix the canonical absolute-Euler squared base `y=1`, corresponding to `s=3/2`. For an ambient
open-strip point `rho=1/2+delta+i*gamma`, define

```text
A(rho)  = 1 + gamma^2 - delta^2,
B(rho)  = 2*delta*gamma,
mu(rho) = (A(rho)-i*B(rho))^(-1)
        = (1-(rho-1/2)^2)^(-1).
```

Every Xi zero has `gamma != 0`, and the open strip plus the source height gap gives `A(rho)>0`.
Hence `mu(rho)` lies in the open right half-plane. Define ambient predicates

```text
G_infinity(rho) :<-> forall n>=1, 0 < Re(mu(rho)^n),
G_n(rho)        :<-> (forall 1<=k<n, 0 < Re(mu(rho)^k))
                     and Re(mu(rho)^n) <= 0.
```

These predicates are defined on ambient strip points and are reflection-covariant. They give a
canonical disjoint exhaustive **obstruction decomposition** of every Xi zero:

1. If `delta=0`, then `mu(rho)>0`, so `G_infinity(rho)` holds.
2. If `delta!=0`, then `B(rho)!=0`. Write `mu=r*exp(i*theta)` with
   `0<|theta|<pi/2`. For
   `n=ceil(pi/(2*|theta|))`, one has `pi/2<=n*|theta|<pi`; hence
   `Re(mu^n)<=0`. Well-ordering gives a unique first such `n`, so exactly one `G_n` holds.
3. Conversely `G_infinity(rho)` forces `theta=0`, hence `B(rho)=0`; because `gamma!=0`, this gives
   `delta=0` and therefore `Re(rho)=1/2`.

Thus the line condition and its off-line complement admit an exact first-bad-order decomposition.
This is useful for locating the current source frontier, but it does **not** identify the groups
required by the completion claim. Membership is computed from the target zero coordinate, and on
Xi zeros `G_infinity` is semantically equivalent to `Re(rho)=1/2`. The ambient reformulation does
not turn it into an independent Euler--Gamma source label.

The existing source theory proves the finite prefix:

```text
G_n is empty for 1 <= n <= 14   [reciprocal-square sector],
G_n is empty for 15 <= n <= 19  [five order-specific compact-corner source exclusions].
```

Equivalently, every hypothetical off-line Xi zero belongs to exactly one still-open group `G_n`
with `n>=20`. The order-`15` through order-`19` conclusions are already Lean-formalized. The
order-`1` through order-`14` shifted conclusion has a complete paper proof but still needs one
batched Lean formalization.

The finite prefix is also not evidence for different populations forced by different reasons.
`G_1,...,G_19` are empty; powers one through fourteen share one sector estimate, and powers fifteen
through nineteen are repeated applications of the same fourth-trace source budget. The packaging
therefore fails the dual novelty--significance gate as a main result. It remains a route diagnostic:
any actual off-line zero must enter the target-side tail at a unique order at least twenty.

The strongest exact positive residue is better stated without the artificial group labels. For
every Xi divisor copy `rho`, every real squared base `y>1/4`, and

```text
mu_y(rho) = (y-(rho-1/2)^2)^(-1),
```

the paper sector theorem and the five formal corner exclusions together give

```text
0 < Re(mu_y(rho)^k)    for 1 <= k <= 19.
```

Equivalently `|arg(mu_y(rho))|<pi/38`. Letting `y` decrease to `1/4` gives the unconditional
closed boundary-sector constraint

```text
2*|delta*gamma| / (gamma^2-delta^2+1/4) <= tan(pi/38).
```

This all-base sector bound is a real strengthening of the corpus statement and is the form to
audit for external novelty. That audit is now negative. The atom is an individual summand of
Voros's generalized secondary zeta function, and Platt--Trudgian's unconditional verification of
RH through height `3*10^12`, combined with `|delta|<1/2`, gives the much stronger global estimate

```text
|arg(rho*(1-rho))| < 1/(3*10^12).
```

Increasing `y` only improves that sector. Therefore `pi/38` is not new zero-location knowledge and
is not a standalone paper result. The computation-free source-trace proof method remains a
possibly reusable residue. The statement also shows why the first-bad label is non-intrinsic: its
index depends on `y`, is nondecreasing with `y`, and tends to infinity as `y` tends to infinity for
every fixed off-line point.

## Open cores

1. `[OPEN CORE]` Construct a genuinely source-defined total label whose membership is selected
   without first reading the target zero coordinate, and whose populated strata are forced by
   independently stated source mechanisms.
2. `[DIAGNOSTIC CORE]` Prove source-side emptiness of target obstruction classes `G_n` for every
   `n>=20`, if this decomposition remains useful to a genuine source label.
3. `[OPEN CORE]` Replace the finite fourth-trace corner budget in the cofinal tail. For first-bad
   order `n`, the worst admissible height grows linearly in `n`, so the minimum contribution to any
   fixed reciprocal-trace budget tends to zero. Consequently no fixed finite collection of
   endpoint budgets can close all groups.
4. `[OPEN CORE]` Construct a moving-order or height-excisive source certificate: a completed
   Chebyshev window, a trace-class window index, or another all-place localization whose strength
   does not decay on the `G_n` corner as `n->infinity`.
5. `[LEAN HOLD]` Do not formalize the target-side partition merely because it is easy. Formalize it
   only if a genuine source classifier reuses it. Do not build the infinite source interface until
   its paper theorem exists.

## Gates

- [x] exact meaning of `all groups found and proven` fixed
- [x] singleton horizontal bridge demoted after significance failure
- [x] exhaustive internal and external group-family audit
- [x] target-side first-bad-order obstruction decomposition constructed and proved total/disjoint
- [x] first nineteen target obstruction strata source-proved empty
- [x] first-bad decomposition rejected as the final group family after source and dual-gate audit
- [ ] genuinely source-defined total label constructed
- [ ] every per-group source forcing theorem proved on paper
- [ ] all groups and totality formalized unconditionally in Lean
- [ ] dual novelty/significance gate passed for the complete package

## Log

- 2026-07-17 — Created after correcting the premature completion of the singleton-horizontal
  subgroup run. The goal is complete only with an exhaustive source-defined cover and unconditional
  proofs for every group.
- 2026-07-17 — Completed the literature/corpus group audit and selected the canonical
  first-bad-reciprocal-power stratification. The line group plus the `G_n` obstruction groups are
  disjoint and exhaustive. Existing source theorems empty `G_1,...,G_19`; the complete open core is
  the cofinal tail `G_n`, `n>=20`.
- 2026-07-17 — Rejected that stratification as the final answer after the mandatory source and
  novelty--significance audit. It reads the target zero coordinate, encodes the line condition in
  `G_infinity`, and supplies empty obstruction chambers rather than populated groups forced for
  different reasons. Retained it only as a precise diagnostic of the moving-order tail.
