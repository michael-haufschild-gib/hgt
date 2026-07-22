# Möbius–Laplace prime-divisibility anti-TP2 law

- **ID:** `mobius-laplace-prime-divisibility-anti-tp2`
- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** THEOREM (Lean)
- **Source:** Möbius–Laplace critical renewal law; failure of ambient renewal coercivity
- **Statement:** Every distinct-prime divisibility table of the Möbius–Laplace renewal mass has a strictly negative determinant at every positive scale.
- **Scientific status:** `[FORMALIZED] [NEW TO CORPUS] [CLASSICAL EXPONENTIAL-KERNEL CONSEQUENCE] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Goal

Extract a source-specific sign law from the exact renewal identity

```text
sum_(k>=1) Phi(kx)=exp(-x),
Phi(x)=sum_(n>=1) mu(n)exp(-nx),
```

without assuming decay, continuation, RH, zero information, or positivity of the individual
values `Phi(kx)`.  The theorem identifies strict two-prime negative dependence before any norm or
absolute value is taken.  It is not the missing half-decay estimate.

## Gates

- [x] 0 → 1 in-progress: exact source object and hostile attack fixed
- [x] 1 → 2 fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean theorems, module build, axiom audit, and formal lint
- [x] Parent-theory gate: classical strict total positivity of `K(u,v)=exp(uv)` contains the
  determinant sign after reversing one variable order
- [ ] 3 → 4 publication-ready: not eligible as a new-science claim; reusable connector only

## Exact theorem

Fix `x>0`, a positive integer dilation `a`, and distinct primes `p,q`.  Write

```text
L(b)=sum_(k>=1) Phi(abkx)=exp(-abx).
```

Partition the dilation index `k` by divisibility by `p` and `q`.  With row `0/1` denoting
`p∤k/p|k` and column `0/1` denoting `q∤k/q|k`, the four signed cylinder masses are

```text
A00=L(1)-L(p)-L(q)+L(pq),
A01=L(q)-L(pq),
A10=L(p)-L(pq),
A11=L(pq).                                             (PD1)
```

Every row and column marginal is positive:

```text
A00+A01=L(1)-L(p)>0,   A10+A11=L(p)>0,
A00+A10=L(1)-L(q)>0,   A01+A11=L(q)>0.                 (PD2)
```

Nevertheless the complete two-prime determinant is strictly negative:

```text
det A
 =A00 A11-A01 A10
 =L(1)L(pq)-L(p)L(q)
 =exp(-a(1+pq)x)-exp(-a(p+q)x)
 <0.                                                   (PD3)
```

Equivalently, after normalization by the positive total mass `L(1)`, the two prime-divisibility
indicators have strict negative covariance wherever that signed normalization is used.  The claim
is the determinant identity and sign, not a claim that all four cells form a probability measure.

## Paper proof

Absolute summability of `k ↦ Phi(kx)` is already proved in the parent renewal theorem.  The
subseries over `p|k` is obtained by `k=p ell`, so its mass is `L(p)`; similarly the `q` and joint
subseries have masses `L(q)` and `L(pq)`.  Distinct primality gives
`p|k and q|k iff pq|k`.  Finite inclusion–exclusion yields `(PD1)`.  The marginal identities
`(PD2)` follow by cancellation, and strict positivity follows because `b ↦ exp(-abx)` is strictly
decreasing for `a,x>0`.

Expanding the determinant in `(PD1)` cancels every quadratic term except

```text
L(1)L(pq)-L(p)L(q).
```

Substitute `L(b)=exp(-abx)` and combine exponentials.  Since

```text
1+pq-(p+q)=(p-1)(q-1)>0,
```

one has `a(1+pq)x>a(p+q)x`.  Strict decrease of the real exponential proves `(PD3)`.
`[PROVED HERE]`

## Hostile audit

1. **Does anti-TP2 imply half-decay?** No.  Cylinder sums are linear marginals and do not bound
   the atom `Phi(x)`; signed arrays with the same marginals can have arbitrarily large atoms.
2. **Hidden RH input?** No.  Only absolute renewal, reindexing, inclusion–exclusion, and strict
   exponential monotonicity occur.
3. **Probability language smuggling positivity?** No.  `A00` can be negative at fine scale.  Only
   row/column marginals and determinant sign are asserted.
4. **Generic Gram positivity?** No.  The determinant is strictly negative.  The sign comes from
   arithmetic dilation geometry `lcm(p,q)=pq`, not a positive-semidefinite form.
5. **Independent source?** Yes.  Prime divisibility and the Möbius Lambert identity are fixed
   before evaluating any zero or decay statement.
6. **Can one prime suffice?** No.  One-prime shells are positive differences of exponentials;
   strict interaction first appears in the two-prime determinant.

## Scientific classification and literature audit

`[CORPUS]` The exact critical renewal law and its Mellin-symbol obstruction were already present.
No prime-divisibility cylinder table, determinant, TP2/anti-TP2 classification, or negative
covariance law for this renewal mass was found in the corpus.

Liflandsky's 2026 paper gives the discrete Möbius–Laplace transform, explicit formula, and RH
criterion, but does not state this dilation-divisibility table:
<https://arxiv.org/abs/2607.09797>.

The determinant itself collides with classical total-positivity theory.  The kernel
`K(u,v)=exp(uv)` is a standard strictly totally positive kernel; see, for example, Johnson and
Richards, who explicitly call it the fundamental classical example while extending it to
hyperdeterminants: <https://arxiv.org/abs/2412.03000>.  Replacing `v` by `-v`, or equivalently
reversing its order, gives the strict sign-regular determinant of `exp(-uv)` used in `(PD3)`.
The Boolean row/column difference operations expose that same `2x2` minor.

Therefore the source-specific Möbius-renewal interpretation is new to this corpus, but the
mathematical sign mechanism is a classical exponential-kernel consequence.  Final status:
`[NEW TO CORPUS] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  No external novelty or priority claim remains.

## No-go closure

- **Exact killing theorem/mechanism:** Proposed novelty is absorbed by classical strict total
  positivity of `exp(uv)` and sign-regularity of `exp(-uv)`.  Proposed analytic leverage also
  fails: cylinder marginals do not control the atom `Phi(x)`.
- **Strongest positive survivor:** Exact source theorem `(PD1)`--`(PD3)`: Möbius--Laplace renewal
  turns the classical exponential minor into a strict two-prime anti-TP2 divisibility law, with
  all one-prime marginals positive.  Lean formalization is dependency-closed and audited.
- **New insight:** Any viable renewal proof must preserve signed cross-prime interaction before
  absolute values; product-independence, positive association, and prime-diagonal energy cannot
  produce half-decay.
- **Status:** Paper-proved, Lean-proved, module build/axioms/lint green; classified as reusable
  connector, not external new science.

## Frontier consequence

The renewal solution has a rigid source-specific signed interaction unavailable to ambient
coercivity: all one-prime divisibility marginals are positive while every two-prime determinant is
strictly negative.  Any viable half-decay argument using renewal cylinders must preserve this
anti-TP2 interaction before taking absolute values.  The theorem rules out product-independence,
positive-association, and prime-diagonal norm models as source mechanisms.  Open core remains an
analytic inequality converting the full compatible family of signed prime-cylinder laws into
pointwise control of the distinguished causal solution.

## Lean formalization

Module:

```text
formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean
```

Principal declarations:

```text
mobiusLaplaceRenewalMass
ofReal_mobiusLaplaceRenewalMass_eq_tsum
mobiusLaplacePrimeDivisibilityCell00
mobiusLaplacePrimeDivisibilityCell01
mobiusLaplacePrimeDivisibilityCell10
mobiusLaplacePrimeDivisibilityCell11
mobiusLaplacePrimeDivisibility_marginals_pos
mobiusLaplacePrimeDivisibilityDet_eq_massCross
mobiusLaplacePrimeDivisibilityDet_eq_exp_sub_exp
mobiusLaplacePrimeDivisibilityDet_neg
```

The source file passes:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean
```

Verification:

```text
lake build GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
  -> Build completed successfully

#print axioms ofReal_mobiusLaplaceRenewalMass_eq_tsum
#print axioms mobiusLaplacePrimeDivisibility_marginals_pos
#print axioms mobiusLaplacePrimeDivisibilityDet_eq_exp_sub_exp
#print axioms mobiusLaplacePrimeDivisibilityDet_neg
  -> [propext, Classical.choice, Quot.sound]

scripts/formal_tools.py lint
  -> formal lint passed
```

## Log

- 2026-07-21 — Derived exact two-prime table and strict determinant sign from the renewal law.
- 2026-07-21 — Hostile audit rejected any direct half-decay inference; retained anti-TP2 as the
  strongest non-trivial positive survivor.
- 2026-07-21 — Targeted corpus and literature searches found no exact source-specific statement.
- 2026-07-21 — Formalized renewal-mass bridge, exact four-cell table, positive marginals,
  determinant collapse, exponential normal form, and strict anti-TP2 theorem; targeted Lean source
  check passed with no diagnostics.
- 2026-07-21 — Final module build, axiom audit, and repository formal lint passed.
- 2026-07-21 — Hostile parent-theory audit found classical strict total positivity of `exp(uv)`;
  downgraded from novelty-unverified to `NOT NEW SCIENTIFIC KNOWLEDGE` while retaining the exact
  formal source-specific survivor.
