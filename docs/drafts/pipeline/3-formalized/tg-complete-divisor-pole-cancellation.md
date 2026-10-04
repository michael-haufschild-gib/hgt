# TG complete divisor-pole subtraction with adaptive labels

- **ID:** TG-C9.24A
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, native signed arithmetic admission
- **Source:** `CCMPrimeDeficitCompletePole.lean`
- **Statement:** The literal divisor source has one exponential-affine pole and a globally polynomial remainder. Every finite signed packet has the exact two-moment pole below; harmonic neutrality removes it, uniformly for adaptive nonnegative labels and with causal boundary pairs retained.

## Exact theorem

Let `c=1+Real.eulerMascheroniConstant`, `F=ccmPrimeDeficitDilationSource`, `H=ccmPrimeDeficitDivisorSource`, and let `F_force` be the admitted right force whose primitive is F. Set

```
g(t) = F_force(t) - c exp(t)
j(t) = fract(exp(t))
d = integral_(0,infinity) exp(-t) g(t) dt
    - c integral_(0,infinity) exp(-t) j(t) dt
R(t) = H(t) - exp(t)(c t+d).
```

All integrals defining d are proved integrable. There is an unconditional constant `C>0` such that

```
|R(t)| <= C (max(t,0)+1)^2             for every real t.
```

For any finite set S, arbitrary real coefficients v and real shifts u, put

```
m0 = sum_(i in S) v_i exp(-u_i)
m1 = sum_(i in S) v_i u_i exp(-u_i).
```

Then, with every pair included,

```
sum_(i,j in S) v_i v_j H(T-u_i-u_j)
  = exp(T) ((c T+d)m0^2 - 2c m0 m1)
    + sum_(i,j in S) v_i v_j R(T-u_i-u_j).
```

The same C, independent of S, v, u and T, bounds the absolute value of the remainder sum by

```
C (T+1)^2 (sum_(i in S) |v_i|)^2
```

whenever `T>=0` and every `u_i>=0`. No upper bound on u is needed. If `m0=0`, this bounds the complete H-form itself. For integer logarithmic labels, m0 is the signed harmonic moment.

## Dependency-closed paper proof

**1. Actual centered force.** The corpus theorem `abs_ccmPrimeDeficitDilationForce_centered_le` states

`|F_force(t)-c exp(t)+k| <= t/2+2`, where `k=log(2*pi)/2`.

Consequently `|g(t)| <= B(t+1)` for `t>=0`, with `B=2+|k|`. Local integrability follows from the literal force and the continuous exponential. Also `|j(t)|<=1<=t+1`, and j is locally integrable by the exact floor-integral API.

**2. Both weighted tails.** For any locally integrable h with `|h(t)|<=B(t+1)`, use the nonnegative envelope `B exp(-t)(t+1)`. Its primitive is `-B exp(-t)(t+2)` and tends to zero. Its tail integral is `B exp(-T)(T+2)`. The interval-integral criterion proves integrability of `exp(-t)h(t)` on the positive half-line, and norm domination gives the same tail bound. Apply this separately to g and j, keeping their signs in all identities.

**3. Full source quadrature.** `integral_ccmPrimeDeficitDilationForce` and `logarithmicDilationSum_primitive_quadrature` give

```
H(T) = exp(T) integral_0^T exp(-t) F_force(t) dt
       - integral_0^T F_force(T-s) j(s) ds.
```

Insert `F_force(t)=c exp(t)+g(t)`, then split each weighted integral at T. This yields the exact remainder identity

```
R(T) = -exp(T) integral_(T,infinity) exp(-t) g(t) dt
       + c exp(T) integral_(T,infinity) exp(-t) j(t) dt
       - integral_0^T g(T-s) j(s) ds.
```

The first two terms together are bounded by `(B+|c|)(T+2)`. The complete last term is bounded by `B(T^2/2+T)`, integrating the pointwise envelope `B(T-s+1)`. Hence one fixed positive C bounds R by `C(T+1)^2` for nonnegative T.

**4. Causal boundary.** The corpus proves `H(t)=0` for `t<=0`. Thus `R(t)=-exp(t)(ct+d)` there. Since `exp(t)<=1` and `exp(t)|t|<=1`, its absolute value is at most `|c|+|d|`. Enlarge C once to obtain the global envelope. This retains negative shifted-time terms rather than applying a positive-time estimate outside its domain.

**5. Complete finite form.** Expand each exponential as `exp(T)exp(-u_i)exp(-u_j)`, keeping both linear shift terms. Finite distributivity gives `(c T+d)m0^2-2c m0 m1` exactly. For `u_i,u_j>=0` and `T>=0`, `max(T-u_i-u_j,0)<=T`; apply the global remainder envelope and the finite triangle inequality. Harmonic neutrality makes the complete pole zero.

## Mathematical contribution and limit

C9.23 identified only the leading fixed-packet `T exp(T)` coefficient. This theorem subtracts the entire exponential pole, proves a global remainder envelope, and allows coefficients and labels to depend on T. It uses no interchange of fixed and moving limits.

The coefficient-mass square is retained. At the actual moving arithmetic cutoff it can still cost the full exponential scale. Therefore no native `soninPrimePolarGridEnergy` estimate, RH implication discharge, joint Hardy cubic compatibility or strict contraction has been proved here. The next attack is the actual signed quadratic remainder after a harmonic-neutral extension of the literal Möbius head.

## Lean certificate

Five public theorems and two definitions in `formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitCompletePole.lean`:

- `ccmPrimeDeficitDivisorPoleRemainder_polynomial_bound`
- `ccmPrimeDeficitDivisorPoleRemainder_global_bound`
- `ccmPrimeDeficitDivisorSource_finite_pair_eq_complete_pole`
- `ccmPrimeDeficitDivisorSource_finite_pair_remainder_bound`
- `ccmPrimeDeficitDivisorSource_harmonic_neutral_bound`

Final foreground `lake --old env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitCompletePole.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMPrimeDeficitCompletePole.olean`: exit 0, no diagnostics. RHTower import wired; index exit 0; all seven API entries verified. Separate /tmp axiom audit: exit 0; all five theorems depend only on propext, Classical.choice and Quot.sound. Authoritative `scripts/formal_tools.py lint`: exit 1, thirteen unrelated unreachable modules, no finding for this leaf. Logs: `/tmp/tg-c924-complete-pole-{final,axioms,index,lint}.log`; audit source `/tmp/tg-c924-complete-pole-axioms.lean`.

## Log

- 2026-10-04: Corpus searches and exhaustive source search checked. Paper proof completed; five public theorems pass final leaf elaboration without heartbeat changes, numerical experiments, axioms or proof holes.
