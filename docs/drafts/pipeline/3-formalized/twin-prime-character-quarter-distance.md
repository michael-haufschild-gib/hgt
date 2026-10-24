# Character distance from the finite 3–4–1 inequality

- **ID:** twin-prime-character-quarter-distance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [character-uniform nonpretentiousness](../1-in-progress/twin-prime-character-uniform-nonpretentiousness.md).
- **Statement:** The actual Liouville distance has a quarter logarithmic loss in both frequency and modulus, uniformly over all complex Dirichlet characters.

## Exact statement

Write `u_chi,t(n)=chi(n) exp(i t log n)` and

```text
D(N,chi,t) = sum_(p<=N prime) (1+Re u_chi,t(p))/p.
```

There is an absolute, explicitly defined constant `C` such that,
for every integer `N>=3`, positive modulus `q`, character `chi`
modulo `q`, and real `|t|>=9`,

```text
D(N,chi,t) >= (log log N - log log |t| - log q)/4 - C.       (1)
```

Consequently, on the arithmetic parameter domain
`q <= (log N)^(1/125)` and `log |t| <= (log N)^(4/5)`,

```text
D(N,chi,t) >= (6/125) log log N - C.                       (2)
```

These statements assume no cancellation, nonpretentiousness,
zero-free region, or character-dependent bound. All analytic
inputs below are existing unconditional theorems.

## Attack and status

Verdict **BRIDGE**. The parent mechanism is the classical
3–4–1 trigonometric inequality, already used for the plain row
in `RHTower/Sieve/PrimeCosineSumSharp.lean`. This is an explicit
character-uniform assembly, not a new scientific theorem.
The source target remains the stronger full-frequency bound
in [Matomäki–Radziwiłł–Tao, (1.12)](https://arxiv.org/pdf/1503.05121v3).

Direct finite-prime positivity is better than first taking the
character L-function product: it avoids a modulus-dependent
principal pole bound. Thus only the squared character pays
`log K(q)`, with coefficient `1/4`, rather than `1`.

## Complete paper proof [PROVED HERE]

Let

```text
S2 = sum_p p^(-2),
T = 2(log 2 + 2(2*mertensFirstConst + 1/2))/log 2,
E = S2 + T + 1 + log 4,
K(q) = (2+6q)e + 17*2^(omega(q)),
B = 8e+17,
C = (mertensSecondLowerConst + E + log 2 + log B)/4.
```

Every constant is independent of `N,q,chi,t`.

### Uniform comparison with the actual L-function

For any character `psi`, real `v`, and `sigma=1+1/log N`,

```text
|sum_(p<=N) Re u_psi,v(p)/p
  - log |L(sigma-i v,psi)|| <= E.                         (3)
```

Indeed `|psi(n)|<=1`. The complex prime series at `sigma-i v`
is absolutely convergent, dominated termwise by `p^(-sigma)`.
Its distance from the Euler logarithm is at most `S2`, by
`TransHorizonIncidenceMechanics.norm_tsum_char_sub_eulerLog_le`.
`RHTower.exp_eulerLog` identifies the real part of that logarithm
with `log |L|`, without a choice of logarithm branch.

The omitted tail has modulus at most `T`, by
`RHTower.Sieve.tsum_primeTailTerm_le`. The finite abscissa shift
has absolute value at most

```text
(sigma-1)(log N+log 4) <= 1+log 4,
```

by `abs_sum_weight_shift_le` and `log N>=1` for `N>=3`.
The identity `p^(-sigma+i v)=p^(-sigma) exp(i v log p)`
gives the same actual character weights in all three steps.
The triangle inequality proves (3).

### Finite positivity before analytic estimation

For every complex `z` in the closed unit disk,

```text
3+4 Re z+Re(z^2) = 2(1+Re z)^2+1-|z|^2 >=0.
```

Apply this to `z=u_chi,t(p)` and divide by the positive prime
`p`. Since `u_chi,t(p)^2=u_(chi^2),2t(p)`, summation gives

```text
sum_(p<=N) 1/p - sum_(p<=N) Re u_(chi^2),2t(p)/p
  <= 4 D(N,chi,t).                                      (4)
```

Primes dividing `q` cause no exception: their character value
is zero and the disk inequality remains valid.

Since `1<sigma<=2` and `|-2t|>=18`, the already proved
`RHTower.norm_LFunction_le_log` gives

```text
|L(sigma-2it,chi^2)| <= K(q) log(2|t|).
```

Its norm is positive by `exp_eulerLog`. Taking logarithms,
using (3), and `log(2|t|)<=2 log|t|` for `|t|>=9` gives

```text
sum_(p<=N) Re u_(chi^2),2t(p)/p
 <= log K(q)+log log|t|+log 2+E.                         (5)
```

The distinct prime-divisor product divides `q` and every factor
is at least two. Thus `2^omega(q)<=q`, already certified by
`RHTower.Sieve.two_pow_card_primeFactors_le`. Since `q>=1`,
`K(q)<=Bq`, hence `log K(q)<=log B+log q`.
Finally `le_mertensS` gives
`sum_(p<=N)1/p >= log log N-mertensSecondLowerConst`.
Insert these bounds into (4) to prove (1).

Taking logarithms of the two parameter-domain inequalities in
(2), using positivity of `log N` and `log|t|`, yields
`log q <= (1/125)log log N` and
`log log|t| <= (4/5)log log N`. The remaining coefficient is
`(1-1/125-4/5)/4=6/125`, proving (2).

At every prime `lambda(p)=-1`. Therefore
`1-Re(lambda(p)*conj(u_chi,t(p)))=1+Re(u_chi,t(p))`.
This identifies `D` exactly with the actual Liouville
pretentious distance squared, including primes dividing `q`.

## Limits and next open core

(2) pays the `exp(-M/20)` term with logarithmic exponent
`3/1250`, which is stronger than `1/700`, in its stated
frequency domain. It does not exceed the source's
`(1/8)log log N` near-resonance threshold. No conclusion is
claimed for the missing bounded-height or high-frequency
domains. The full character-uniform distance target and
Twin Prime infinitude remain unproved.

## Lean gate

- [x] Exact statement, complete proof, and existing inputs inspected.
- [x] Implement actual finite distance and unconditional comparison.
- [x] Formalize (1), (2), and the actual Liouville identity.
- [x] Foreground leaf compilation and transitive axiom audit.
- [x] Import completed leaf in `twin-prime/Main.lean`.

## Lean certificate

Module: `formal/GaloisForLFunctions/twin-prime/CharacterPrimeDistance.lean`.
Namespace: `TwinPrime.CharacterDistance`.

- `norm_phase_le_one`, `phase_sq`: actual character phase and squaring.
- `harmonic_sub_square_le_four_distance`: finite 3–4–1 positivity.
- `primeSum_log_comparison`: two-sided absolute error in (3).
- `character_constant_le`: `K(q)<=(8e+17)q`.
- `distance_eq_liouville`: exact identity with the corpus's
  pretentious squared distance of the actual Liouville function.
- `quarter_distance`: inequality (1), with every cutoff `N=n+3`.
- `middle_frequency_distance`: inequality (2), on the displayed
  growing-modulus and frequency domain.
- `middle_frequency_decay`: the actual penalty is at most
  `exp(C/20)*(log N)^(-3/1250)`.

The final foreground leaf command was
`lake --old env lean GaloisForLFunctions/twin-prime/CharacterPrimeDistance.lean`,
run from `formal/`. It passed without warnings. All nine capstone
transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. No umbrella was compiled and no olean was rebuilt.
The bounds have no analytic premise; the subtypes specify only
positive modulus and numerical parameter ranges.

## Research audit

No new scientific theorem beyond the established parent mechanism
is claimed. This batch advances the checked character assembly,
not the arithmetic frontier or the twin-prime conclusion. The
[high-frequency receiver continuation](../1-in-progress/twin-prime-character-route-t-receiver.md)
records the exact next unresolved transport and the limitation of
the existing `9/10` region. The main goal remains active.
