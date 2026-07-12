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
[·, E-free] ⍟ mPart E [·, m-free] = [·, E·m-free]      (independent moduli)      (2)
prod_{k<K} mPart (m^k) [·, m-free] = [·, m^K-free]     (Dirichlet convolution)   (3)
prod_{k<K} L([·, m-free], m^k s) = zeta(s)/zeta(m^K s)          on re s > 1      (4)
dpoly2 (mPartMoebiusCoeff (m^k)) (Icc 1 N) z -> zeta(m^k z)^(-1)
                                                on re z > 1/m^k, per rung k      (5)
prod_{k<K} mPart (P_k) [·, m_k-free] = [·, P_K-free],   P_k = m_0⋯m_{k-1}        (6)
prod_{k<K} L([·, m_k-free], P_k s) = zeta(s)/zeta(P_K s)        on re s > 1      (7)
dpoly2 (mPartMoebiusCoeff P_K) (Icc 1 N) z -> zeta(P_K z)^(-1)  on re z > 1/P_K  (8)
```

Relations `(6)`–`(8)` are the mixed-radix tower: the moduli sequence is arbitrary, so the
partial products `P_K` — and with them the nested carrier domains `re z > 1/P_K` — grow
as fast as desired.  The single telescoping step `(2)` (base-`E` division with remainder
at every prime power) drives both the pure-power and the mixed-radix towers.

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
  `mPart_mFreeIndicator_apply_prime_pow`, `mFreeIndicator_mul_mPart_mFreeIndicator`:
  the step `(2)` for independent moduli;
- `prod_mPart_mFreeIndicator`: relation `(3)`;
- `prod_LSeries_mFreeIndicator_telescope`: relation `(4)`;
- `tendsto_dpoly2_mPartMoebiusCoeff_pow`: relation `(5)`;
- `prod_mPart_mFreeIndicator_mixed`: relation `(6)`;
- `prod_LSeries_mFreeIndicator_mixed`: relation `(7)`;
- `tendsto_dpoly2_mixed_radix`: relation `(8)`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] composition, arithmetic telescope, L-series telescope, and carrier tower all
      unconditional (half-plane hypotheses only), every `m ≠ 0`, every `K`
- [x] telescope checked against the `K = 0` and `m = 1` degenerate rungs
      (`mFreeIndicator 1 = δ`, `mPart 1 = id`)
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `MFreeTower`; the independent existing failure is
`SummableEulerCalkinInjectivity.lean`.  All thirteen public theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Opens

The remaining forward object is the inverse telescope: convolving `(2)` against dilated
Möbius factors to expand `mPart (P_K) mu` as a `K`-fold convolution of dilated
Möbius atoms, giving a product presentation of the `zeta(P_K z)^(-1)` carrier
coefficients themselves — the coefficient-level counterpart of `(7)`.  Beyond it, the
mixed-radix freedom in `(6)`–`(8)` invites a diagonal object: choose `m_k` growing so
that `P_K`-rung certificates (via `sqrt-carrier-finite-cutoff-certificate`) hold with a
single uniform gap sequence — a certified carrier family indexed by one parameter whose
domains exhaust `re z > 0`.
