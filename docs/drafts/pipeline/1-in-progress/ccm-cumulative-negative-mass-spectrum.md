# Cumulative negative-mass spectrum of the sharp prime--Gamma carrier

- **ID:** `ccm-cumulative-negative-mass-spectrum`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / exact source-growth reformulation
- **Route:** fixed-window Connes--Weil prime--Gamma tomography

## Claim under verification

For a nonnegative real Dirichlet coefficient `a`, put

```text
A(X)=sum_(1<=n<=X) a(n).
```

At every positive real threshold `sigma`, the following are equivalent:

```text
abscissa_abs(a) <= sigma
iff
for every epsilon>0, A(X)=O_epsilon(X^(sigma+epsilon)).
```

Applied to the negative part `g_(L,N)^-` of the exact sharp prime--Gamma carrier, this should give,
for every fixed positive width `L`, admissible tail `N`, and `alpha>=0`,

```text
every Xi zero has Re rho <= 1/2+alpha
iff
for every epsilon>0,
  sum_(n<=X) g_(L,N)^-(n)=O_epsilon(X^(1+alpha+epsilon)).
```

Consequently RH should be equivalent to the critical cumulative law

```text
sum_(n<=X) g_(L,N)^-(n)=O_epsilon(X^(1+epsilon))
for every epsilon>0.
```

This is a positive carrier theorem: a successful construction must keep the total accumulated
negative prime--Gamma mass below every superlinear scale. Under false RH the cumulative growth
threshold is forced to be `1+delta_*`.

## Proof route

1. Summability at a real exponent `s` bounds `A(X)` by `X^s` times the convergent positive
   Dirichlet sum.
2. Conversely, a bound for `A(X)` at exponent `t<s` gives summability at `s` by a dyadic shell
   decomposition.
3. Quantify between `sigma` and an arbitrary `s>sigma`.
4. Compose with the already established exact abscissa/zero-free-region spectrum of
   `g_(L,N)^-`.

## Gates

- [ ] prove the general nonnegative Dirichlet summatory-growth theorem
- [ ] specialize it to the sharp prime--Gamma negative carrier
- [ ] verify the complete theorem internally without additional assumptions
- [ ] integrate the cumulative formulation into the paper only after verification

