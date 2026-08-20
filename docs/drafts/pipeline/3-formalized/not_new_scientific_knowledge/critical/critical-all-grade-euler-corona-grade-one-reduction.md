# The critical all-grade Euler-ray corona is its grade-one face

- **ID:** `critical-all-grade-euler-corona-grade-one-reduction`
- **Stage:** 3-formalized / not-new
- **Type:** theorem (Lean), `[BRIDGE]`
- **Statement:** In the critical Marcinkiewicz topology on all prime-power coefficients, every
  grade `m>=2` of a bounded degree-one Euler ray is a vanishing tail.  The quotient class of the
  complete nonlinear ray is therefore exactly the class of its grade-one coordinate.  The actual
  unit Euler source survives with norm one, while every right-half shift ray is approximable by
  finite Euler rays even after all prime-power grades are retained.

## All-grade critical space

Let a prime-power coefficient array be a field

```text
c=(c_(p,m))_(p prime, m>=1).
```

Define

```text
||c||_pp = sup_(X>=2) 1/log X *
             sum_(p^m<=X) |c_(p,m)|/p^m.                 (1)
```

Write `M_pp` for the resulting Banach space and `M_pp,0` for the closure of finite-support arrays.
The grade-one embedding of a prime field `b` is

```text
iota(b)_(p,1) = (log p)b_p,
iota(b)_(p,m) = 0,                  m>=2.                 (2)
```

Then

```text
||iota(b)||_pp
  = sup_(X>=2) 1/log X * sum_(p<=X) (log p)/p |b_p|
  = ||b||_M.                                             (3)
```

Thus `iota : M_log -> M_pp` is an isometry.  Conversely, grade-one projection

```text
pi_1(c)_p = c_(p,1)/(log p)                              (4)
```

is contractive and sends `M_pp,0` into `M_0`.  Hence (2)--(4) induce an isometric embedding

```text
Q_log=M_log/M_0  ->  Q_pp=M_pp/M_pp,0.                   (5)
```

## Nonlinear Euler rays

For a bounded degree-one parameter field `a`, `|a_p|<=1`, put

```text
Phi(a)_(p,m)=(log p)a_p^m.                               (6)
```

This is the complete prime-power coefficient ray of the associated degree-one Euler source.  Its
higher-grade part is

```text
H(a)=Phi(a)-iota(a).
```

It is absolutely summable at the critical Dirichlet weight:

```text
sum_p sum_(m>=2) |H(a)_(p,m)|/p^m
  <= sum_p (log p) sum_(m>=2) p^(-m)
  =  sum_p (log p)/(p(p-1))
  <  infinity.                                           (7)
```

Every weighted absolutely summable array belongs to `M_pp,0`, because deleting a sufficiently
large finite set makes its `M_pp` norm at most its weighted `l^1` tail divided by `log 2`.
Therefore

```text
H(a) in M_pp,0,
[Phi(a)]_[Q_pp] = [iota(a)]_[Q_pp].                       (8)
```

Equation (8) is the grade-one reduction theorem.  Although `Phi` is nonlinear and satisfies every
quadratic Euler ray equation, its critical corona map is exactly the linear grade-one quotient map.

## Exact unit and shift classification

For the actual zeta parameter `a_p=1`, Mertens' theorem gives

```text
||[Phi(one)]||_[Q_pp]
  = ||[one]||_[Q_log]
  = 1.                                                    (9)
```

The upper bound follows from (8) and the grade-one truncations.  The lower bound follows by applying
the contractive quotient projection induced by `pi_1`.

Now let `z` lie in the open right strip and put

```text
epsilon=Re z-1/2>0,
tau_z(p)=p^(1/2-z).
```

The complete nonlinear shift ray is absolutely summable:

```text
sum_p sum_(m>=1) |Phi(tau_z)_(p,m)|/p^m
  = sum_p (log p) sum_(m>=1) p^(-m(1+epsilon))
  < infinity.                                            (10)
```

Consequently

```text
Phi(tau_z) in M_pp,0,
[Phi(tau_z)]_[Q_pp]=0.                                   (11)
```

If `tau_z^(Y)` is truncated to primes `p<=Y`, then `Phi(tau_z^(Y))` is a finite Euler ray and

```text
||Phi(tau_z)-Phi(tau_z^(Y))||_pp -> 0.                   (12)
```

This convergence retains every prime-power grade and every quadratic ray equation.

## Tangent version at the actual source

The derivative of (6) at `a=one` is

```text
DPhi_one(b)_(p,m)=m(log p)b_p.                           (13)
```

For the critical summable tangent space

```text
T_1={b : sum_p |b_p|(log p)/p<infinity},
```

the full tangent ray is again absolutely summable:

```text
sum_p sum_(m>=1) |DPhi_one(b)_(p,m)|/p^m
  = sum_p |b_p|(log p) * p^(-1)/(1-p^(-1))^2
  <= 4 ||b||_1.                                          (14)
```

Thus adding all tangent grades does not strengthen the critical summable topology used in the
weighted joint-decoupling theorem.  In fact the reduction extends to all of `M_log`.  Put

```text
alpha_p=|b_p|(log p)/p,
K=||b||_M.
```

The higher-grade part satisfies

```text
sum_p sum_(m>=2) |DPhi_one(b)_(p,m)|/p^m
  <= C sum_p alpha_p/p.                                  (14a)
```

On the dyadic block `2^k<p<=2^(k+1)`, the defining Marcinkiewicz bound gives

```text
sum_(2^k<p<=2^(k+1)) alpha_p/p
  <= 2^(-k) sum_(p<=2^(k+1)) alpha_p
  <= K(k+1)(log 2)2^(-k).                                (14b)
```

Summing in `k` proves that the grades `m>=2` are weighted `l^1`, continuously in `||b||_M`.
Therefore

```text
[DPhi_one(b)]_[Q_pp]=[iota(b)]_[Q_pp]       for b in M_log.
```

If `b in M_0`, finite-support prime fields converge to `b` in `M_log`, and their complete tangent
rays converge to `DPhi_one(b)` in `M_pp`.  Thus the all-grade tangent over `M_0` is exactly the
vanishing-tail tangent used in the strengthened weighted joint-decoupling theorem.

## Source--divisor consequence

The result gives the exact positive classification of what all-order Euler ray algebra retains at
the first non-summable boundary:

```text
complete bounded Euler ray modulo vanishing tails
  = grade-one prime field modulo vanishing tails.         (15)
```

In particular, an off-line residue character `tau_z` remains a finite-ray limit in the full
nonlinear source image.  Its nonzero prime-zeta residue, if `z` is a zeta zero, lives in the
vanishing-tail graph described by `prime-shift-residue-closability-criterion.md`; it is not promoted
to the nonzero corona by higher prime-power grades.

Therefore the missing RH compatibility cannot be obtained from:

1. the quadratic Euler ray equations alone;
2. the complete bounded prime-power coefficient corona alone; or
3. closability of a residue reader on the vanishing-tail layer.

It must couple the surviving unit class (9) to global divisor incidence by data not annihilated in
(8).

## Scientific status

This is `[BRIDGE]`, not new scientific knowledge.  The mechanism is the elementary summability of
the grades `m>=2` at the critical Dirichlet weight, together with quotient functoriality.  Its value
is to close the all-grade escape explicitly: the complete nonlinear Euler ray does not repair the
separation between the nonzero source tail and the vanishing off-line residue character.

The theorem introduces no scientifically new mechanism, but it is now formalized: see the Lean
section below.  (The earlier note that no isolated formalization was selected is superseded.)

## Lean formalization — COMPLETE (unconditional)

**`GaloisForLFunctions/RHTower/AllGradePrimePowerCorona.lean`.**  Axiom audit for every capstone:
`propext`, `Classical.choice`, `Quot.sound` only.

The all-grade coefficient array is indexed by pairs `(p, m)` standing for the grade-`m+1`
coefficient at the prime `p`, and `primePowerMass c X = ∑_{p^{m+1} ≤ X} |c_{p,m}| / p^{m+1}` is the
numerator of the seminorm `(1)`; `primePowerQuotient` is the Marcinkiewicz quotient at cutoff `X`.
The grade-one layer `M_log` is the corpus's `WeightedEulerCoefficientSpaces`.

| Theorem | Statement |
|---|---|
| `primePowerIndex`, `primePowerMass`, `primePowerQuotient`, `MemPrimePowerLayer` | the space `M_pp` of `(1)`. |
| **`primePowerMass_gradeOneEmbed`** | **`(2)`–`(3)`: `ι` is an isometry** — the all-grade mass of a grade-one embedded field is exactly its prime-log mass. |
| **`primeLogMass_gradeOneProj_le`** | **`(4)`: grade-one projection is contractive.** |
| `eulerRay`, `eulerRayHigher`, `eulerRay_eq_add` | the complete nonlinear ray `(6)` and its higher-grade part `H(a) = Φ(a) − ι(a)`. |
| **`primePowerMass_eulerRayHigher_le`** | **`(7)`: for a bounded degree-one field the grades `m ≥ 2` carry mass at most `∑_p (log p)/(p(p−1)) ≤ 8`, uniformly in the cutoff.** |
| **`tendsto_primePowerQuotient_eulerRayHigher`** | **`(8)`, the grade-one reduction: the higher-grade quotient tends to zero**, so the complete nonlinear ray and its linear grade-one face have the same critical corona class. |
| **`tendsto_primePowerQuotient_eulerRay_unit`** | **`(9)`: the actual unit Euler source survives with quotient exactly one** — Mertens' first theorem through the corpus's `tendsto_mertensPrimeMean_unit`, with the higher grades contributing `O(1/log X)`. |
| `shiftField`, **`primePowerMass_eulerRay_shift_le`, `tendsto_primePowerQuotient_eulerRay_shift`** | **`(10)`–`(11)`: the off-line shift ray has zero corona class** even with every prime-power grade retained — the mass is uniformly bounded by `2·primeLogRpowTailConstant ε` and the quotient vanishes. |
| `eulerTangent`, **`primePowerMass_eulerTangent_le`** | **`(13)`–`(14)`: the complete tangent ray has mass at most `4` times the grade-one mass**, so adding all tangent grades does not strengthen the critical summable topology. |
| `eulerTangentHigher`, **`primePowerMass_eulerTangentHigher_le`** | **`(14a)`–`(14b)`: the extension to all of `M_log`** — for a field in the logarithmic Marcinkiewicz layer with constant `K`, the tangent grades `m ≥ 2` carry mass at most `24 K log 2`, uniformly in the cutoff, continuously in `K`. |
| `sum_primesBelow_primeLog_div_le` | the dyadic-block step of `(14a)`: `∑_p α_p/p ≤ 4 K log 2` from the defining Marcinkiewicz bound. |
| `sum_range_pow_le`, `sum_range_add_one_mul_pow_le`, `sum_Ico_succ_mul_pow_le`, `primePowerMass_le_prod` | the reusable finite geometric and grouping bounds the estimates run on. |

Every statement is a finite-cutoff inequality or a limit of such; no hypothesis on `ζ`, on the
zeros, or on any unproved analytic input enters any proof.  Complex parameter fields are covered
because the seminorm sees only absolute values: the mass of a complex ray equals the mass of the
real ray of its moduli, which is what the shift-ray statement is instantiated at.

## Log
- 2026-08-20 — **formalized**: unconditional Lean proofs of the all-grade prime-power Marcinkiewicz
  layer, the grade-one isometry and contraction, the grade-one reduction of the complete nonlinear
  Euler ray, the exact Mertens unit class, the vanishing off-line shift ray, and both tangent bounds
  (critical-summable and Marcinkiewicz).  Axiom audit clean.  Stage → 3-formalized.
