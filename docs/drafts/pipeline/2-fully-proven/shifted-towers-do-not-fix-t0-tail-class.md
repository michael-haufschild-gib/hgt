# Shifted Towers Do Not Fix The T0 Tail Class

- **ID:** shifted-towers-do-not-fix-t0-tail-class
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/consolidated/gpt/proof-route.md, `T_0` infinite / shifted finite towers
- **Statement:** Finiteness of every positive shifted moment is compatible with many incompatible divergence rates for the unshifted mass `T_0`. Therefore the shifted proof route does not supply a canonical `T_0` regularization rate.

## Goal

Block a Tauberian false repair of the invalid unshifted `T_0` tower. Once the route shifts away from `T_0`, the finiteness of the shifted tower alone does not identify whether the missing `T_0` divergence is logarithmic, linear, stretched-exponential in a cutoff, or another admissible near-zero tail class.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let `(a_n)_{n>=1}` be positive and define a reciprocal measure

```text
mu = sum_{n>=1} a_n delta_{exp(-n)}.
```

Then

```text
T_0 = sum_n a_n,
T_k = sum_n a_n exp(-kn),  k>=1.
```

If

```text
sum_n a_n = infinity
```

but

```text
sum_n a_n exp(-kn) < infinity  for every k>=1,
```

then `T_0` is infinite while every shifted positive moment is finite.

The condition allows many incompatible `T_0` divergence classes. For example:

```text
a_n = 1/n          gives T_0(N) ~ log N,
a_n = 1            gives T_0(N) = N,
a_n = exp(sqrt n)  gives stretched-exponential T_0(N),
```

and in all three cases `sum_n a_n exp(-kn)<infinity` for every `k>=1`.

By contrast, the control case

```text
a_n = exp(n)
```

already makes `T_1=sum_n exp(n) exp(-n)=sum_n 1` diverge, so it is outside the shifted finite tower regime.

Thus the shifted finite tower condition separates admissible from too-large near-zero mass, but it does not choose one admissible `T_0` divergence rate. Any proof route that reinstates `T_0` by a cutoff, finite part, or Tauberian normalization must import an additional source theorem specifying the near-zero tail class.

## Computation

Numerical and visual check:

- `computations/2026-06-21-penrose-proof-r12-t0-tail-classes.py`
- `computations/2026-06-21-penrose-proof-r12-t0-tail-classes.txt`
- `computations/2026-06-21-penrose-proof-r12-t0-tail-classes.svg`

## Log

- 2026-06-21 -- created in 2-fully-proven from the Tauberian/heavy-tail NODE, method 5 make visual.
