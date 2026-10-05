# Reflection-contact parity, minimal oriented rank, and recovery-neutrality law

- **ID:** ULF-PCFG-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A nonzero even positive analytic response of order `2k` has minimal analytic
  reflection-oriented realization rank one when `k` is even and rank two when `k` is odd; exact
  recovery preserves this obstruction, and the order-two Wold response therefore requires a
  two-channel trivial-plus-sign carrier to retain coorientation.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN-PROVED]`

## Goal

Determine whether a positive scalar response can carry the direction exchanged by a functional
equation, and whether the two-sheet formation constructed in ULF-PFM-2 is arbitrary redundancy or
forced minimal representation content.

## Gates

- [x] 0 -> 1 in-progress: scalar conjecture attacked and falsified at odd half-order
- [x] 1 -> 2 fully-proven: sharp rank classification and Wold prediction proved below
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.AnalyticPrimitive`, `GaloisForLFunctions.HTGeometry.ReflectionContactParity`, `GaloisForLFunctions.HTGeometry.ScalarArclengthRegularityWall`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 -> 4 publication-ready

## 1. Oriented response realization rank

Let `I` be a nonzero real-analytic germ at zero satisfying

```text
I(-t)=I(t),   I(t)>=0,   I(0)=0,
nu(I)=2k.                                             (RP.1)
```

An **analytic reflection-oriented realization** of `I` consists of

1. a finite-dimensional real inner-product space `V`;
2. an orthogonal involution `R:V->V`;
3. an analytic curve `Gamma` with `Gamma(0)=0`;
4. the laws

```text
Gamma(-t)=R Gamma(t),
||Gamma'(t)||^2=I(t);                                 (RP.2)
```

5. local coorientation separation:

```text
Gamma(t) != Gamma(-t)
```

for every sufficiently small nonzero `t`.

Define `orrank(I)` as the least possible `dim V`.

## 2. Analytic square-root normal form

### Lemma 2.1

There is a positive even analytic unit `h` near zero such that

```text
I(t)=q(t)^2,   q(t)=t^k h(t),
q(-t)=(-1)^k q(t).                                    (RP.3)
```

Every analytic scalar square root of `I` is locally `q` or `-q`.

### Proof

The first nonzero Taylor degree of a nonnegative analytic germ is even and its coefficient is
positive. Divide `I` by `t^(2k)` to obtain a positive even analytic unit `a` with `a(0)>0`.
Composition with the analytic square-root function near `a(0)` gives the unique positive even
analytic `h=sqrt(a)`. Then `(RP.3)` holds. If `r^2=q^2`, then `(r-q)(r+q)=0` as analytic germs.
The local analytic germ ring is an integral domain, hence `r=q` or `r=-q`. QED.

## 3. Sharp rank classification

### Theorem 3.1 -- reflection-contact rank law

```text
orrank(I) = 1,  if k is even,
orrank(I) = 2,  if k is odd.                           (RP.4)
```

### Proof: even `k`

When `k` is even, `q` is even. Put `V=R`, let the involution be `R=-1`, and define

```text
Gamma(t)=integral_0^t q(s) ds.                         (RP.5)
```

Then `Gamma` is odd, `Gamma'=q`, and `|Gamma'|^2=I`. Since `h>0` and `t^k>=0`, `q` is positive on
both sufficiently small punctured sides. Hence `Gamma` is strictly increasing and separates `t`
from `-t`. Rank zero is impossible for a nonzero response, so the minimum is one.

### Proof: odd `k`, lower bound

Suppose a one-dimensional oriented realization exists. Its orthogonal involution is `+1` or `-1`.
The `+1` action makes `Gamma(-t)=Gamma(t)` and violates separation. Thus the action is `-1`, so
`Gamma` is odd and its derivative is even. But every analytic scalar velocity `v=Gamma'` satisfying
`v^2=I` is `q` or `-q` by Lemma 2.1, and `q` is odd when `k` is odd. Contradiction. Therefore
`orrank(I)>=2`.

### Proof: odd `k`, rank-two realization

Let `V=R^2`, put

```text
v(t)=q(t)(cos t, sin t),
Gamma(t)=integral_0^t v(s) ds,
R=diag(1,-1).                                          (RP.6)
```

Then `||v||^2=q^2=I`. Because `q` is odd, the first component of `v` is odd and the second is even.
Therefore

```text
v(-t)=-R v(t),
Gamma(-t)=R Gamma(t).                                  (RP.7)
```

For sufficiently small positive `t`, both `q(t)` and `sin t` are positive, hence

```text
Gamma_2(t)=integral_0^t q(s) sin(s) ds > 0.
```

This component is odd, so `Gamma_2(-t)=-Gamma_2(t)` and the two source sides are separated. Thus
rank two exists, proving `(RP.4)`. QED.

### Corollary 3.2 -- forced representation and orientation latency

When `k` is odd, every minimal rank-two realization has one trivial and one sign representation
channel. After an orthogonal change of basis its involution is `diag(1,-1)`. If the corresponding
velocity components are `v_+` and `v_-`, then

```text
nu(v_+)=k,
nu(v_-)>k,
nu(v_-) is even.                                       (RP.7a)
```

In particular the leading positive response lies in the reflection-trivial position channel, while
the reflection-separating sign channel is necessarily subleading.

### Proof

The involution cannot be `+I`, because that folds the curve. If it were `-I`, the whole curve would
be odd and its velocity even. Every nonzero component would then have even order, so the norm
square would have order divisible by four, contradicting `nu(I)=2k=2 mod 4`. Thus both eigenspaces
are nonzero and, in dimension two, each has dimension one.

Equivariance makes the `+` position coordinate even and its velocity odd; it makes the `-` position
coordinate odd and its velocity even. Since the minimum velocity order is `k`, the even-order
component cannot attain the odd value `k`. The odd component must attain it, while the even
component is nonzero by separation and has a strictly larger even order. QED.

## 4. Scalar arclength regularity wall

The intrinsic signed arclength of the positive response is

```text
A(t)=sign(t) integral_0^|t| sqrt(I(s)) ds.             (RP.8)
```

### Corollary 4.1

- If `k` is even, `A` is analytic and is the rank-one realization `(RP.5)`.
- If `k` is odd, `A` is `C^k` but not `C^(k+1)` at zero.

### Proof

For even `k`, `sqrt(I)=q` and the signed integral is the analytic odd primitive. For odd `k`,

```text
sqrt(I(t))=|t|^k h(t),
A(t)=h(0)/(k+1) sign(t)|t|^(k+1)+higher order.          (RP.9)
```

Here `k+1` is even. The leading function `sign(t)|t|^(k+1)` has matching derivatives through order
`k` and opposite nonzero one-sided derivatives at order `k+1`. Higher-order terms cannot cancel
that jump. QED.

Thus positivity, scalar analyticity, and reflection separation form an exact trilemma at odd
half-order. Rank two resolves it without abandoning positivity or analyticity.

## 5. Statistical fold and common-recovery no-go

For any scalar analytic primitive `Theta` with `Theta'=q` and `|Theta|<pi/2`, define the local
Bernoulli family

```text
p(t)=(1+sin Theta(t))/2.                               (RP.10)
```

Its Fisher information is exactly

```text
(p'(t))^2 / (p(t)(1-p(t))) = (Theta'(t))^2 = I(t).     (RP.11)
```

When `k` is odd, `q` is odd and `Theta` is even, so

```text
p(t)=p(-t).                                            (RP.12)
```

The scalar statistical model has the correct positive response but folds the two reflection sides.

If `K` is any parameter-independent common recovery kernel, split formation gives

```text
E_K(p(t))=E_K(p(-t))                                   (RP.13)
```

whenever `(RP.12)` holds. Exact KL preservation through `K` therefore cannot create the missing
sign channel. Conversely, if an observer and its common recovery preserve the full divergence
germ, they preserve `I`, its half-order `k`, and the rank obstruction `(RP.4)`.

This is the precise sense in which information-neutral recovery is neutral: it transports an
existing oriented polarization isometrically but cannot manufacture one from a folded scalar law.

## 6. Wold and packet-formation prediction

The literal Wold response is

```text
I_W(u)=cosh(u)-sinh(u)/u
      =u^2/3+u^4/30+... .                              (RP.14)
```

Hence `nu(I_W)=2`, so `k=1` is odd. Theorem 3.1 gives

```text
orrank(I_W)=2.                                         (RP.15)
```

The two-sheet functional-equation packet carries the permutation representation of `Z/2`. In the
basis

```text
e_+=(1,1),   e_-=(1,-1),
```

sheet swap acts as `diag(1,-1)`. It is exactly the representation type forced by Corollary 3.2.
Therefore:

> Any analytic positive realization of the Wold response that retains functional-equation
> coorientation needs at least two real channels. Any coupling of that response to the existing
> functional-equation packet cannot use fewer channels than its two-dimensional sheet
> representation.

This does not assert that the packet theorem by itself realizes the Wold metric. It says that once
the independently constructed Wold response and packet reflection are required to live in one
analytic oriented realization, the packet's real representation dimension is minimal. That
conditional coupling statement was not present in the packet-formation theorem.

## 7. Reflection-compatible coordinate invariance

By ULF-PCFG-1, an odd analytic reparameterization has odd order `r` and sends half-order `k` to
`rk`. Hence the parity in `(RP.4)` is invariant under every reflection-compatible analytic
ramification. An even ramification can flip the parity only by ceasing to intertwine reflection and
folding source sides in its own parameter map.

Thus the rank obstruction is not a coordinate artifact.

## 8. Hostile correctness and significance review

### Attacks that fail

1. **A scalar analytic square root always orients the source.** False for odd `k`: its primitive is
   even.
2. **Odd half-order forces nonanalyticity in every realization.** False: `(RP.6)` is analytic in
   rank two.
3. **Any two-channel lift works.** False: the involution and parity of the velocity components are
   load-bearing.
4. **Common recovery can restore the sign.** False by `(RP.13)`.
5. **Ramification removes the obstruction.** False for every reflection-compatible ramification.

### External parents

Equivariant singularity theory, invariant sum-of-squares theory, Hellinger/Fisher immersion, and
representation-block decompositions are established. Relevant parents include:

- https://arxiv.org/abs/0808.0034
- https://arxiv.org/abs/math/0211450
- https://arxiv.org/abs/1802.00143
- https://arxiv.org/abs/1207.6736
- https://arxiv.org/abs/2604.12725

The rank calculation is elementary once the invariant is defined. No priority claim is made.
Its significance is corpus-level and structural: it predicts a forced minimal packet dimension
from an independently constructed response contact.

## 9. Scope

- This is a local real-analytic theorem, not a global immersion classification.
- The rank-two construction proves existence, not source canonicity or uniqueness.
- The positive scalar response does not determine which oriented rank-two lift nature chooses.
- The theorem gives no global work bound, Xi comparison, or RH selection.
- Hypertranscendence is not identified with contact order or rank.

## Lean status

Fully formalized, unconditionally: see the Lean certificate below.


## Lean certificate

Modules `GaloisForLFunctions.HTGeometry.AnalyticPrimitive` (reusable: the primitive of a real-analytic germ
is real analytic, with its termwise power series; parity and positivity of primitives),
`GaloisForLFunctions.HTGeometry.ReflectionContactParity` (responses, oriented realizations, square-root
normal form, rank law, forced channel structure, Wold response, sheet swap, ramification invariance) and
`GaloisForLFunctions.HTGeometry.ScalarArclengthRegularityWall` (the `|t|`-power wall, signed arclength,
Bernoulli fold, divergence-Hessian recovery law).  Corpus inputs: `AnalyticContact`, `PositiveAnalyticContact`,
`PositiveAnalyticContact.exists_of_analytic_eventually_nonnegative`, `positiveAnalyticContact_normSq`,
`PositiveAnalyticContact.analyticOrderAt_add_eq_min`, `analyticOrderAt_comp_eq_mul`, `analyticAt_inner`,
`halfOrder_parity_iff_of_antireflection` (ULF-PCFG-1), `abs_le_abs_of_mem_uIcc_zero`,
`RHTower.sourceHorizontalWoldPrimeClockResponse` with its evenness, quadratic lower bound and closed form;
mathlib `FormalMultilinearSeries.ofScalars`, `intervalIntegral.hasSum_intervalIntegral_of_summable_norm`,
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`, `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`.

| Claim | Lean declaration |
|-|-|
| (RP.1) nonzero even positive analytic response of order `2k` | `EvenPositiveResponse`, `EvenPositiveResponse.k_pos`, `EvenPositiveResponse.not_eventually_zero` |
| (RP.2) analytic reflection-oriented realization; `orrank(I)` = least dimension | `OrientedRealization`, `orientedRank`, `OrientedRealization.map`, `OrientedRealization.toEuclidean`, `OrientedRealization.orientedRank_le` |
| Lemma 2.1, (RP.3) `I = q²`, `q = tᵏ h`, `h` positive even analytic unit, `q(-t) = (-1)ᵏ q(t)` | `EvenPositiveResponse.exists_unit`, `EvenPositiveResponse.exists_sqrt`, `EvenPositiveResponse.exists_sqrt'` |
| Lemma 2.1 every analytic square root is `q` or `-q` | `eventuallyEq_or_eventuallyEq_neg_of_sq_eq` |
| Theorem 3.1, (RP.4) `orrank(I) = 1` (k even), `2` (k odd) | `EvenPositiveResponse.orientedRank_eq` |
| Theorem 3.1 rank zero impossible; involution `+1` folds | `OrientedRealization.finrank_pos`, `OrientedRealization.not_subsingleton`, `OrientedRealization.refl_ne_id` |
| Theorem 3.1 even `k`: `Γ = ∫₀ᵗ q`, `R = -1`, strictly monotone separation (RP.5) | `EvenPositiveResponse.exists_lineRealization`, `EvenPositiveResponse.exists_lineRealization_of_sqrt`, `eventually_ne_neg_of_pos_of_odd` |
| Theorem 3.1 odd `k` lower bound: no line realization (`R = ±1`; `R = -1` makes `Γ'` even) | `OrientedRealization.two_le_finrank`, `OrientedRealization.refl_ne_neg_of_odd`, `OrientedRealization.velocity_contact`, `OrientedRealization.deriv_neg`, `AnalyticContact.order_even_of_even` |
| Theorem 3.1 odd `k` rank-two realization `v = q(cos t, sin t)`, `R = diag(1,-1)`, `Γ₂ > 0` (RP.6)–(RP.7) | `EvenPositiveResponse.exists_planeRealization`, `norm_smul_add_smul_sq`, `inner_smul_add_smul_right` |
| Corollary 3.2 forced representation: `R ≠ ±1`, orthonormal eigenbasis, `R = diag(1,-1)` | `OrientedRealization.exists_eigenbasis`, `eq_inner_smul_add_inner_smul`, `OrientedRealization.inner_refl` |
| Corollary 3.2, (RP.7a) `ν(v₊) = k`, `ν(v₋) > k` even | `OrientedRealization.channel_orders`, `AnalyticContact.order_odd_of_odd`, `exists_analyticContact` |
| (RP.8) signed arclength `A(t) = sign(t) ∫₀^{∣t∣} √I` | `signedArclength`, `signedArclength_eventuallyEq` |
| Corollary 4.1 even `k`: `A` analytic and is the rank-one realization | `EvenPositiveResponse.signedArclength_of_even`, `OrientedRealization.congrCurve` |
| Corollary 4.1 odd `k`, (RP.9): `A` is `Cᵏ` not `C^{k+1}` at `0` | `EvenPositiveResponse.signedArclength_of_odd`, `contDiff_pow_mul_abs`, `not_contDiffAt_pow_mul_abs`, `hasDerivAt_pow_succ_mul_abs`, `hasDerivAt_mul_abs` |
| (RP.10)–(RP.11) Bernoulli family `p = (1 + sin Θ)/2`, Fisher information `p'²/(p(1-p)) = Θ'² = I` | `bernoulliFamily`, `hasDerivAt_bernoulliFamily`, `bernoulliFamily_fisher`, `EvenPositiveResponse.bernoulli_fisher_eq` |
| (RP.12) odd `k`: every scalar analytic primitive `Θ` with `Θ'² = I` is even, `p(t) = p(-t)` | `EvenPositiveResponse.even_of_sq_deriv`, `eventually_eq_add_primitive_deriv` |
| (RP.13) any parameter-independent recovery folds the two sides | `EvenPositiveResponse.bernoulli_fold` |
| §5 converse: divergence-germ preservation preserves `I`, half-order and `orrank` (Fisher = KL Hessian) | `binaryKL`, `hasDerivAt_deriv_binaryKL`, `fisher_eq_of_binaryKL_eventuallyEq`, `recovery_preserves_response`, `orientedRank_congr`, `OrientedRealization.ofEventuallyEq` |
| (RP.14) `I_W(u) = cosh u - sinh u / u`, `ν(I_W) = 2` | `woldResponse`, `woldResponse_eq_cosh_sub_dslope`, `analyticAt_woldResponse`, `woldResponse_evenPositive` |
| (RP.15) `orrank(I_W) = 2` | `orientedRank_woldResponse` |
| §6 sheet swap acts as `diag(1,-1)` in `e± = (1,±1)/√2`; the packet realizes the Wold response | `sheetSwap`, `sheetPlus`, `sheetMinus`, `sheetSwap_sheetPlus`, `sheetSwap_sheetMinus`, `sheetSwap_sheetSwap`, `sheet_orthonormal`, `EvenPositiveResponse.exists_sheetRealization`, `exists_woldSheetRealization` |
| §7 odd ramification of order `r`: half-order `k ↦ rk`, parity and `orrank` invariant | `EvenPositiveResponse.comp_odd`, `EvenPositiveResponse.orientedRank_comp_odd` |
| §8 attacks 1–5 | `EvenPositiveResponse.even_of_sq_deriv`, `EvenPositiveResponse.exists_planeRealization`, `OrientedRealization.refl_ne_neg_of_odd`, `OrientedRealization.refl_ne_id`, `EvenPositiveResponse.bernoulli_fold`, `EvenPositiveResponse.orientedRank_comp_odd` |
| analytic primitives (used throughout) | `primitiveAtZero`, `hasFPowerSeriesOnBall_primitiveAtZero`, `analyticAt_primitiveAtZero`, `eventually_hasDerivAt_primitiveAtZero`, `primitiveAtZero_neg_of_even`, `primitiveAtZero_neg_of_odd`, `eventually_primitiveAtZero_pos` |

Realizations are defined in an arbitrary real inner-product space; `orrank` is computed on
`EuclideanSpace ℝ (Fin n)`, and every finite-dimensional realization transports there.  The lower bounds hold
in every finite-dimensional space.  §9 (scope) carries no Lean obligation.

## Log

- 2026-08-12 -- scalar orientation conjecture falsified at odd half-order.
- 2026-08-12 -- rank-two survivor constructed; sharp parity classification and Wold minimal-double
  prediction proved on paper.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
