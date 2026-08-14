# Horizontal--vertical packet renewal budget and cofinal properness law

- **ID:** ULF-CRG-4
- **Stage:** 3-formalized
- **Type:** THEOREM / FUSION CONSERVATION LAW / NO-LOOPHOLE CLASSIFICATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [ARBITRARY PACKET RENEWAL]`
  `[LEAN NOT YET WRITTEN] [NOT RH]`
- **Programme:** `cofinal-renewal-geometry`
- **Parents:**
  - `disjoint-aperture-global-renewal-moment-properness-and-cubic-threshold-law.md`
  - `../packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`

## 1. Closed loophole

Common-recovery information isometry was previously proved for the two split laws

```text
mu tensor K,       nu tensor K.
```

That does not by itself exclude a joint intervention that changes observer and latent history
together.  This theorem allows an arbitrary renewed packet law `Q` on the full product.  It proves
that latent-history information cannot replenish an evacuated observer aperture.  Vertical action
is an additional nonnegative budget term; it never acts as negative horizontal cost.

## 2. Setup

Let `X` be an observer/source space, `H` a latent-history space, `mu` a probability law on `X`, and
`K:X -> Prob(H)` a Markov recovery kernel.  The baseline formed packet is

```text
P(dx,dh)=mu(dx)K(x,dh).                                (HVP.1)
```

Let `Q` be any probability law on `X x H` with

```text
Q << P,       D(Q||P)<infinity.                        (HVP.2)
```

Write

```text
nu=pi_*Q
```

for its observer marginal.  Let `(A_n)_(n>=1)` be pairwise-disjoint measurable apertures in `X`
and let `N:X->[0,infinity)` be any measurable formation gauge, usually constant `phi(n)` on
`A_n`.  Assume

```text
Z_mu(lambda)=integral exp(lambda N)dmu<infinity        (HVP.3)
```

for some `lambda>0`.

## 3. Arbitrary-packet horizontal properness

### Theorem 3.1 — marginal action cannot exceed packet action

```text
D(nu||mu) <= D(Q||P).                                  (HVP.4)
```

### Proof

Projection `pi:X x H->X` sends `P` to `mu` because `K` is Markov, and sends `Q` to `nu`.  Relative-
entropy data processing under `pi` proves `(HVP.4)`.

### Theorem 3.2 — packet entropy controls horizontal formation gauge

```text
lambda integral N(x)dQ(x,h)
 <= D(Q||P)+log Z_mu(lambda).                          (HVP.5)
```

Equivalently,

```text
lambda integral N dnu
 <= D(Q||P)+log Z_mu(lambda).                          (HVP.6)
```

### Proof

The gauge depends only on the recovered coordinate, so

```text
integral N(x)dQ(x,h)=integral N dnu.
```

Apply the entropy--exponential-moment inequality to `(nu,mu)` and use `(HVP.4)`.  Alternatively,
apply it directly to `(Q,P)` and observe from the Markov property that

```text
integral exp(lambda N(x))dP(x,h)=Z_mu(lambda).
```

The second proof shows that no disintegration theorem is needed.

### Corollary 3.3 — arbitrary latent intervention cannot cross the work wall

Suppose `mu(A_n)<=C exp(-beta n^gamma)`, the renewed aperture masses are

```text
alpha_n=Q(A_n x H),
```

and positive work satisfies

```text
W_n<=K n^d,       alpha_n W_n>=c>0.                   (HVP.7)
```

Then finite packet action forces

```text
d>gamma+1.                                            (HVP.8)
```

In particular ordinary exponential evacuation excludes constant, linear, and quadratic persistent
current even when `Q` is an arbitrary correlated observer--history law.

### Proof

Use `(HVP.5)` with `N(x)=n^gamma` on `A_n`.  Then

```text
sum_n n^gamma alpha_n<infinity.
```

Equation `(HVP.7)` gives `n^gamma alpha_n>=(c/K)n^(gamma-d)`.  The p-series converges only when
`d>gamma+1`.

## 4. Exact horizontal--vertical conservation law

For this section assume `X` and `H` are standard Borel spaces, so `Q` has a regular conditional
law `L(x,dh)` over its marginal `nu`:

```text
Q(dx,dh)=nu(dx)L(x,dh).                                (HVP.9)
```

### Theorem 4.1 — packet action splits into horizontal and vertical budgets

```text
D(Q||mu tensor K)
 = D(nu||mu)+integral D(L_x||K_x)dnu(x).               (HVP.10)
```

Define

```text
V_K(Q)=integral D(L_x||K_x)dnu(x)>=0.                  (HVP.11)
```

Then the sharpened cofinal conservation law is

```text
lambda integral N dnu + V_K(Q)
 <= D(Q||P)+log Z_mu(lambda).                          (HVP.12)
```

### Proof

Equation `(HVP.10)` is the relative-entropy chain rule for a joint law and the reference
disintegration `(HVP.1)`.  The observer entropy inequality gives

```text
lambda integral N dnu<=D(nu||mu)+log Z_mu(lambda).
```

Substitute `D(nu||mu)=D(Q||P)-V_K(Q)` from `(HVP.10)` and rearrange.

### Interpretation

The two terms on the left of `(HVP.12)` are not analogies:

1. `lambda integral N dnu` is horizontal formation/renewal cost;
2. `V_K(Q)` is vertical deviation from certified recovery history.

They draw from one exact packet information budget.  Increasing vertical history complexity cannot
pay horizontal aperture loss.  It tightens the available horizontal bound by precisely `V_K(Q)`.

## 5. Equality and minimum-action classification

### Theorem 5.1 — common recovery is the unique zero-vertical intervention

```text
V_K(Q)=0
```

if and only if

```text
L_x=K_x       for nu-almost every x.                  (HVP.13)
```

Equivalently, among all packet laws with fixed observer marginal `nu`, the split formation

```text
Q_min=nu tensor K                                      (HVP.14)
```

uniquely minimizes `D(Q||P)`, with minimum value `D(nu||mu)`.

### Proof

Relative entropy is nonnegative and vanishes exactly when its two probability laws agree.  Apply
this pointwise in `(HVP.11)`.  Equation `(HVP.10)` then gives the minimization statement.

Thus the earlier common-recovery isometry is not merely one convenient lift.  It is the unique
least-action packet lift of every observer renewal.

## 6. Functional-equation action

Let `R:X->X` be a measurable involution preserving `mu` and `N`.  Its canonical packet lift applies
`R` to the observer and regenerates history from `K`.  On split packets it preserves the complete
action exactly, as previously proved.

For an arbitrary packet renewal `Q`, functional-equation transport can rearrange the vertical term
only if an action on conditional kernels is specified.  Regardless of that choice, `(HVP.5)` remains
valid after transport whenever the reference packet and gauge are invariant.  Therefore functional-
equation holonomy cannot create a negative vertical budget that evades cofinal properness.

## 7. Four-organ fusion and prediction

The exact law `(HVP.12)` fuses four structurally distinct organs:

| organ | typed quantity |
|---|---|
| source/admission | `mu`, apertures `A_n`, gauge `N` |
| packet formation | reference disintegration `mu tensor K` |
| latent history/recurrence | conditional renewal `L_x` and vertical action `V_K(Q)` |
| information properness | total packet KL and its compact horizontal sublevels |

It predicts a theorem in every proposed hidden-history or recurrence completion:

> If the completion is reached by a Markov recovery packet and the renewed joint law has finite KL
> relative to that packet, then latent winding, holonomy, recurrence, or edge-mode information
> cannot replenish an exponentially evacuated source aperture.  Its conditional KL is a positive
> competitor for the same action budget.

A purported recurrence-based rescue must therefore exhibit at least one precise failure of the
hypotheses: singular path law, infinite action, non-Markov/source-dependent recovery, a gauge not
read from the recovered observer, or a non-probability source operation.

This is route-independent leverage.  It does not identify which failure the arithmetic source
chooses.

## 8. Hostile loops

1. **A correlated packet renewal may be cheaper than split renewal.** False by `(HVP.10)`.
2. **Latent history can subsidize horizontal admission.** False; vertical KL enters with positive
   sign in `(HVP.12)`.
3. **Disintegration is needed for the properness theorem.** False; data processing proves
   `(HVP.5)` on arbitrary measurable spaces.  Standard Borel hypotheses are needed only for the
   exact vertical decomposition.
4. **Common recovery is information-neutral for arbitrary joint laws.** False as stated.  It is
   the zero-vertical, least-action representative.  Arbitrary joint laws pay extra vertical KL.
5. **The theorem proves recurrence is useless.** False.  Recurrence can carry independent physical
   information, but not replenish this horizontal probability mass at finite KL under the stated
   packet doctrine.
6. **The theorem proves RH.** False.  A literal source comparison still must place one persistent
   off-center current into the horizontal apertures and prove finite total packet action.

## 9. Literature boundary

Relative-entropy chain rules, disintegration, sufficient recovery, and Schrödinger bridge action
are established mathematics.  Current bridge theory studies conditional and marginal entropy
rates separately; see Trentini--Stancevic--Bronstein--Tong--Ambrogioni,
[arXiv:2605.16126](https://arxiv.org/abs/2605.16126), and Del Moral,
[arXiv:2504.18822](https://arxiv.org/abs/2504.18822).  These are close conceptual parents for the
horizontal--vertical split, not evidence for an HGT-specific theorem.

New-to-corpus content is the exact fusion of arbitrary packet renewal, cofinal formation gauge,
source work threshold, and common-recovery least-action classification.  No external source was
found for this arithmetic/properness package.  External novelty remains unverified.

## 10. Lean boundary

No Lean was written or built.  Existing formal parents provide common-kernel KL equality, KL data
processing under measurable maps, and the split functional-equation action.  Future formalization
needs a general entropy--exponential-moment inequality and a discrete/standard-Borel version of the
joint KL chain rule.  The standard-Borel disintegration theorem should not be hidden as an axiom;
if unavailable, formalize `(HVP.5)` first and keep `(HVP.10)` paper-level.

## Log

- 2026-08-13 — identified arbitrary correlated packet renewal as a loophole in split-formation
  properness.
- 2026-08-13 — closed it by data processing and proved exact horizontal--vertical budget law under
  standard-Borel disintegration.
- 2026-08-14 — Full unconditional Lean closure of HVP.4--HVP.14, including arbitrary-packet data processing, canonical conditional-kernel KL chain rule, exact vertical budget, work wall, and unique least-action classification; targeted build, umbrella elaboration, scoped forbidden-token scan, and standard-only axiom audit pass.
