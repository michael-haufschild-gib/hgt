# Route E Deninger vacuum Meyer-tail / hard-collar decomposition

- **ID:** `ROUTE-E-DENINGER-VACUUM-MEYER-TAIL-HARD-COLLAR-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT POSITIVE NO-GO SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-deninger-vacuum-finite-dilation-fracture.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Statement:** One fixed smooth cutoff splits the vacuum into a strict Deninger Meyer tail and a
  compact collar; after Möbius dilation, the collar is exactly a finite sum through scale `2/x`.

## Goal and non-theatre standard

Finite vacuum-dilation masks cannot enter the strict Deninger source. A completed no-go needs its
strongest positive replacement: isolate exactly which part of the vacuum is strict and which part
retains the arithmetic obstruction. Merely naming a “compact error” is insufficient. The support
cutoff, all derivative bounds, Möbius summability, and finite aperture must be literal theorems.

## Exact construction

Let `κ(t)` be smooth, zero for `t ≤ 0`, and one for `log 2 ≤ t`. Define

```text
V(x) = exp(-x)
H(x) = κ(log x) V(x)
C(x) = (1 - κ(log x)) V(x).
```

Then, pointwise,

```text
V(x) = H(x) + C(x).
```

The logarithmic tail `t ↦ H(exp t)` vanishes on the full left half-line `t ≤ 0`. Every derivative
on the right is a polynomial in `exp t` times `exp(-exp t)`, hence decays faster than every
exponential. Therefore it satisfies the two-sided all-order strong-log condition and canonically
defines an element of `DeningerExpSchwartz`.

The collar vanishes for `x ≥ 2`. For every `x>0`, define

```text
T_x(n) = μ(n) H(n x),
C_x(n) = μ(n) C(n x),
B(x)   = floor(2/x) + 1.
```

Then `C_x(n)=0` for every `n ∉ range(B(x))`, both series are summable, and

```text
sum_n μ(n) exp(-n x)
  = sum_n T_x(n) + sum_{n in range(B(x))} C_x(n).
```

This is exact at the cutoff boundary: the possible equality term `n x = 2` already vanishes.

## Reusable infrastructure

The proof also closes a missing generic bridge. If `g : R -> C` has all-order, all-weight decay at
both logarithmic ends (`DeningerMeyerStrongLogDecay g`), then the weighted derivatives have global
two-sided bounds and `g` canonically lands in `DeningerExpSchwartz`. This replaces repeated manual
Schwartz-seminorm constructions for future Deninger source vectors.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.RouteEDeningerVacuumCollarDecomposition
```

Principal declarations:

```text
DeningerMeyerStrongLogDecay.expSchwartzBounds
deningerExpSchwartzOfStrongLogDecay
routeEVacuumMeyerLogTail_strongLogDecay
routeEVacuumMeyerDeningerSource
routeEVacuumKernel_eq_tail_add_collar
routeEVacuumMeyerTail_exp
routeEVacuumCollarTerm_eq_zero_of_not_mem
summable_routeEVacuumMeyerTailTerm
tsum_routeEVacuumCollarTerm_eq_finite
routeE_mobiusVacuum_easyTail_hardCollar_decomposition
```

Module is imported by `GaloisForLFunctions.RHTower`. No axiom, `sorry`, `admit`, `opaque`,
`unsafe`, numerical computation, RH premise, or unproved arithmetic estimate is introduced.

## Exact remaining boundary

The theorem certifies tail **kernel** as strict and proves fixed-`x` absolute summability of its
Möbius series. It does not assert that the entire Möbius tail sum is itself a strict-source vector.
More importantly, finite collar is exactly smoothed Mertens mass up to `2/x`; no cancellation bound
for it follows from source topology. Required estimate remains `OPEN-SOURCE-001`.

## Novelty status

Per current research directive, no external literature search was performed. Result is new to
internal Route E corpus at this exact all-order/finite-support level and is classified
conservatively as `[BRIDGE] [NOVELTY UNVERIFIED]`.

## Log

- 2026-08-12 — exact all-order Meyer-tail source, reusable strong-log landing, finite collar
  aperture, and Möbius decomposition proved in Lean; umbrella import added.
