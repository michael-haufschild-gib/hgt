# The telescoping m-free tower

- **ID:** `mfree-telescoping-tower`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The rungs of the `m`-free ladder compose: power dilations form a
  multiplicative semigroup, the dilated `m`-free indicators telescope under Dirichlet
  convolution to the `m^K`-free indicator, the L-series rungs multiply out to
  `zeta(s)/zeta(m^K s)`, and each rung carries one `zeta(m^k z)^(-1)` carrier limit on
  its nested half-plane `re z > 1/m^k`.

## Exact relations

For `a, b, m >= 1`:

```text
mPart a (mPart b f) = mPart (a*b) f          (mPart 1 f = f)                     (1)
prod_{k<K} mPart (m^k) [·, m-free] = [·, m^K-free]     (Dirichlet convolution)   (2)
prod_{k<K} L([·, m-free], m^k s) = zeta(s)/zeta(m^K s)          on re s > 1      (3)
dpoly2 (mPartMoebiusCoeff (m^k)) (Icc 1 N) z -> zeta(m^k z)^(-1)
                                                on re z > 1/m^k, per rung k      (4)
```

## Proof

`(1)` off `(a·b)`-th powers both sides vanish (an `a`-th power whose root is not a `b`-th
power cannot be an `(a·b)`-th power); at `n = j^(a·b) = (j^b)^a` both sides evaluate to
`f j`.  `(2)` by induction it reduces to one telescoping step
`[·, m^K-free] ⍟ mPart (m^K) [·, m-free] = [·, m^(K+1)-free]`, an identity of
multiplicative functions checked at prime powers `p^i`: the divisor sum counts
decompositions `i = j + m^K·t` with `j < m^K` and digit `t < m` — base-`m^K` division
with remainder — which exist uniquely exactly when `i < m^(K+1)`.  `(3)` each factor is
the ladder quotient `zeta(m^k s)/zeta(m^(k+1) s)` (valid since `re(m^k s) > 1`), and the
product telescopes; nonvanishing of the intermediate zeta values is on `re > 1`.
`(4)` is the ladder carrier bridge at the rung `m^k`, whose half-plane
`re z > 1/m^k` nests as `k` grows.

## Parent classification

`[SEARCH]` The identity `zeta(s)/zeta(m^K s)` as a `K`-fold product of consecutive
quotients is trivial classically; the convolution telescope `(2)` is the arithmetic
restatement of base-`m` digit expansion of prime exponents (folklore).  Not new
scientific knowledge; the formalization and the per-rung carrier wiring are new to the
tree.

## Prior-state audit

Absent from mathlib: the power dilation and all four relations (no `mPart`, no `m`-free
indicator, no telescope).  Absent from the tree: `MFreeLadder.lean` provided single
rungs only; no composition law, no convolution telescope, no product form.

## Reuse audit

- `MFreeLadder.lean`: `mPart` and its apply lemmas, `mFreeIndicator` with prime-power
  values, `isMultiplicative_mPart`/`isMultiplicative_mFreeIndicator`,
  `LSeries_mFree_eq_riemannZeta_div`, `tendsto_dpoly2_mPartMoebiusCoeff`,
  `one_lt_natCast_mul_re`, `one_div_natCast_lt_re` (made public in this work);
- mathlib: `eq_iff_eq_on_prime_powers`, `ArithmeticFunction.mul_apply`,
  `Nat.sum_divisorsAntidiagonal`, `Nat.sum_divisors_prime_pow`, `Nat.pow_div`,
  `Nat.div_add_mod`, `Nat.add_mul_mod_self_left`.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/MFreeTower.lean`.

- `mPart_one`, `mPart_mPart`, `mPart_pow_succ`: relation `(1)`;
- `mFreeIndicator_one`, `forall_pow_ne_prime_pow_of_not_dvd`,
  `mPart_mFreeIndicator_apply_prime_pow`, `mFreeIndicator_mul_mPart_mFreeIndicator`,
  `prod_mPart_mFreeIndicator`: relation `(2)`;
- `prod_LSeries_mFreeIndicator_telescope`: relation `(3)`;
- `tendsto_dpoly2_mPartMoebiusCoeff_pow`: relation `(4)`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] composition, arithmetic telescope, L-series telescope, and carrier tower all
      unconditional (half-plane hypotheses only), every `m ≠ 0`, every `K`
- [x] telescope checked against the `K = 0` and `m = 1` degenerate rungs
      (`mFreeIndicator 1 = δ`, `mPart 1 = id`)
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `MFreeTower`; the independent existing failure is
`SummableEulerCalkinInjectivity.lean`.  All ten public theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Opens

The telescope `(2)` presents `[·, m^K-free]` as a `K`-fold convolution of dilations of
one atom — a factorization system on indicators.  Two forward objects: (i) the inverse
telescope — convolving `(2)` against dilated Möbius factors to expand `mPart (m^K) mu`
as `prod_{k<K} mPart (m^k) (dilated mu-atom)`, giving a product presentation of the
`zeta(m^K z)^(-1)` carrier coefficients themselves; (ii) the mixed-radix version — for a
sequence `m_0, m_1, …` of moduli the same digit argument telescopes
`prod_k mPart (m_0⋯m_{k-1}) [·, m_k-free]` to the indicator of exponents below
`m_0⋯m_{K-1}`, a factorial-base ladder whose carrier limits live on half-planes shrinking
as fast as desired — a knob for approaching `re z = 1/2` along certified carriers.
