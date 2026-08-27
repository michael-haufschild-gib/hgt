# Positive-contact tropicalization, observation monotonicity, and ramification law

- **ID:** ULF-PCFG-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Statement:** Order at a marked analytic event is a tropical valuation on nonnegative response
  germs, can only increase under information-losing observation, is preserved by exact recovery,
  doubles under positive Gram formation, and multiplies under ramification; reflection-compatible
  ramification preserves half-order parity.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN-PROVED]`

## Goal

Extract one coordinate-free law shared by contact geometry, positive response, Fisher information,
Gram formation, observer contraction, and ramified source changes. The theorem is not an RH
selector. It supplies a discriminator that prevents those operations from being treated as
independent sources of information.

## Gates

- [x] 0 -> 1 in-progress: exact germ category, operations, and counterexamples identified
- [x] 1 -> 2 fully-proven: complete proof below; no open dependency
- [x] 2 -> 3 formalized: exact package in `PositiveContactTropicalization.lean`
- [ ] 3 -> 4 publication-ready

## 1. Positive analytic contact

Let `A_+` be the set of nonzero real-analytic germs `f` at zero such that

```text
f(0)=0,   f(t)>=0
```

on some real neighborhood of zero. Write `nu(f)` for the least integer `m` whose Taylor
coefficient at degree `m` is nonzero, and `lc(f)` for that coefficient.

Every `f in A_+` has a unique leading normal form

```text
f(t)=lc(f)t^nu(f)+o(|t|^nu(f)).                         (PC.1)
```

### Theorem 1.1 -- positive tropical semiring

For `f,g in A_+`,

```text
nu(f+g)=min(nu(f),nu(g)),
nu(fg)=nu(f)+nu(g).                                    (PC.2)
```

Moreover `nu(f)` is even and `lc(f)>0`.

### Proof

If the first nonzero Taylor degree of `f` were odd, its leading monomial would change sign across
zero. If its leading coefficient were negative, `f` would be negative on both sufficiently small
sides. Thus the order is even and the leading coefficient is positive. Products multiply leading
monomials. In a sum, the term with smaller order survives; at equal order the new leading
coefficient is the sum of two positive coefficients and cannot cancel. This proves `(PC.2)`. QED.

Thus positive addition is tropical minimum and multiplication is tropical addition. The
noncancellation is load-bearing: signed analytic germs do not satisfy the first identity.

## 2. Observation is contact-monotone

### Theorem 2.1 -- analytic data-processing contact law

Let `f,g in A_+` and suppose

```text
0 <= g(t) <= f(t)                                      (PC.3)
```

near zero. Then

```text
nu(g)>=nu(f).                                          (PC.4)
```

If the two orders agree, then

```text
lc(g)<=lc(f).                                          (PC.5)
```

### Proof

Put `m=nu(f)` and `n=nu(g)`. If `n<m`, divide `(PC.3)` by `|t|^m` along positive `t`. The quotient
`g(t)/t^m` is asymptotic to `lc(g)t^(n-m)` and tends to positive infinity, whereas `f(t)/t^m`
tends to `lc(f)`. Contradiction. Hence `n>=m`. If `n=m`, division by `t^m` and passage to the limit
gives `(PC.5)`. QED.

### Corollary 2.2 -- divergence and Fisher response

Let `D_src(t)` and `D_obs(t)` be nonzero analytic nonnegative divergence germs based at the same
law. If a Markov observation satisfies data processing,

```text
D_obs(t)<=D_src(t),
```

then its contact order cannot decrease. If the observation has a common recovery making the
divergences equal, both contact order and leading coefficient are preserved. The same conclusion
holds for the first nonzero analytic Fisher/Hellinger response obtained from those divergence
germs.

This is an application of Theorem 2.1, not a new form of the data-processing inequality.

## 3. Positive Gram formation doubles hidden contact

Let `V` be a finite-dimensional real inner-product space and let `v` be a nonzero analytic
`V`-valued germ with `v(0)=0`. Define `nu(v)` as the smallest Taylor degree having a nonzero vector
coefficient.

### Theorem 3.1 -- Gram doubling

```text
nu(||v||^2)=2 nu(v),
lc(||v||^2)=||lc(v)||^2>0.                             (PC.6)
```

For finitely many analytic vectors `v_j`,

```text
nu(sum_j ||v_j||^2)=2 min_j nu(v_j).                  (PC.7)
```

### Proof

Write `v(t)=t^k(a+O(t))` with `a!=0`. Then

```text
||v(t)||^2=t^(2k)(||a||^2+O(t)),
```

which proves `(PC.6)`. Equation `(PC.7)` follows from Theorem 1.1 because every summand is
nonnegative and at least one minimal leading squared norm is positive. QED.

The positive observer therefore retains twice the smallest hidden contact but forgets which vector
or representation channel attained it.

## 4. Ramification and reflection

Let `phi` be a nonzero real-analytic germ with `phi(0)=0` and order `r`.

### Theorem 4.1 -- contact ramification

For every nonzero analytic germ `f` with `f(0)=0`,

```text
nu(f o phi)=r nu(f).                                  (PC.8)
```

If `phi` is reflection-compatible,

```text
phi(-t)=-phi(t),                                       (PC.9)
```

then `r` is odd. Consequently, if `nu(f)=2k`, the parity of the half-order `k` is unchanged by
every reflection-compatible ramification:

```text
r k = k (mod 2).                                      (PC.10)
```

### Proof

Write `f(s)=a s^m+O(s^(m+1))` and `phi(t)=b t^r+O(t^(r+1))`, with `a,b` nonzero. Substitution gives

```text
f(phi(t))=a b^m t^(rm)+O(t^(rm+1)),
```

proving `(PC.8)`. An odd analytic germ contains only odd Taylor powers, so its first nonzero degree
`r` is odd. Equation `(PC.10)` follows. QED.

An even power substitution can change half-order parity, but it is not reflection-compatible: it
identifies the two source sides and therefore changes the marked symmetry problem rather than
repairing it.

## 5. Exact conservation identities

For independent positive response germs `f_1,...,f_N`, formation by product laws adds their
divergences and hence

```text
nu(f_1+...+f_N)=min_i nu(f_i).                         (PC.11)
```

Repeating one identical formation `N` times leaves its order fixed and multiplies its leading
coefficient by `N`. Exact common recovery leaves both quantities unchanged. Thus formation count,
observer loss, and ramification have distinct signatures:

| mechanism | contact order | leading coefficient |
|---|---:|---:|
| independent positive sum | minimum | sum on minimal face |
| `N` identical copies | unchanged | multiplied by `N` |
| lossy observation | can increase | decreases on an equal-order face |
| exact recovery | unchanged | unchanged |
| positive Gram square | doubles hidden order | squares hidden norm |
| order-`r` ramification | multiplied by `r` | rescaled by leading ramification coefficient |

This table gives experimentally distinct laws rather than several names for one obstruction.

## 6. Corpus specialization

- `RingOrdRamification.lean` proves the local DVR version of `(PC.8)`.
- `StokesFormalContactInvariance.lean` proves invariance under tangent formal reparameterization.
- `ConstraintFrameRelativity/ValuatedPluckerGram.lean` proves Gram/minor depth doubling and positive
  leading-square retention.
- `ConstitutiveFunctionalEquationPacketLift.lean` proves exact KL preservation through common
  recovery, supplying the equality case of Corollary 2.2.
- The Wold response card has exact contact order two, so its hidden polarized contact is one.

The new contribution here is the single contact ledger connecting those theorem surfaces and
separating their signatures. Generic ingredients are established mathematics.

## 7. External parent theories and hostile verdict

- Ay--Jost--Le--Schwachhoefer prove Fisher monotonicity and invariance under sufficient statistics:
  https://arxiv.org/abs/1207.6736
- Herbig--Pflaum describe invariant functions through Hilbert maps for compact-group actions:
  https://arxiv.org/abs/1802.00143
- Cimpric--Kuhlmann--Scheiderer and Gatermann--Parrilo treat equivariant sums of squares and their
  representation blocks:
  https://arxiv.org/abs/0808.0034
  https://arxiv.org/abs/math/0211450
- Tropical valuation and ramification laws are classical.

**Verdict:** `[BRIDGE]`, not a priority claim. The route-independent leverage is exact: positive
formation cannot cancel first contact; observation cannot create a lower-order signal; exact
recovery cannot alter contact; and legitimate reflection reparameterization cannot change
half-order parity.

## 8. Scope

- Analyticity and finite order are essential. Flat smooth germs need not have a finite contact.
- Positivity is essential for tropical addition without cancellation.
- Contact does not determine global properness, phase, orientation, or coefficient history.
- Equal contact does not imply statistical sufficiency.
- This theorem constructs no Xi landing and proves no RH statement.

## Lean status

Formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/PositiveContactTropicalization.lean`. The module proves:

- extraction and uniqueness of exact analytic contact order and leading coefficient;
- even order and positive leading coefficient for nonnegative zero germs;
- exact tropical sum/product laws, including strict/equal-order leading coefficients;
- observation order monotonicity and equal-order leading-coefficient monotonicity;
- exact recovery, finite positive sums, and identical-copy scaling;
- vector Gram doubling and finite Gram minimum laws;
- exact ramified composition order and leading coefficient;
- odd order for reflection-compatible ramification and half-order parity preservation.

Verification: direct `lake env lean`, targeted module build, and axiom audit of every new public
declaration passed. Axiom output contains only standard Lean foundations (`propext`,
`Classical.choice`, `Quot.sound`). Module is imported by the universal-law-field umbrella.

## Log

- 2026-08-12 -- extracted from contact, positive Gram, Fisher observation, recovery, and
  ramification theorem surfaces; dependency-closed paper proof completed.
- 2026-08-27 -- exact Lean package completed, built, axiom-audited, and wired into
  `GaloisForLFunctions.HTGeometry.UniversalLawField`; promoted to Stage 3.
