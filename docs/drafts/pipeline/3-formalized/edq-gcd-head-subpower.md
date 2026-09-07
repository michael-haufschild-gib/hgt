# EDQ all-gcd heads: unconditional total remainder bound

Stage: 3-formalized. Arithmetic estimate; RH remains open.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Closed statements

For positive r and cutoff N, let

```
B_r(N,k) = sum_(1<=d,e<=N, gcd(d,e)=r) mu(d)mu(e)*(k mod d)/d*(k mod e)/e,
K_r(N)   = sum_(1<=d,e<=N, gcd(d,e)=r) mu(d)mu(e)/(d*e),
H_r(N)   = sum_(1<=k<=N) B_r(N,k)/[k(k+1)],
A_N      = sum_(1<=k<=N) k/(k+1).
```

For every epsilon>0, there is C_epsilon>0 such that, for every natural N,

`sum_(r=1..N) |H_r(N)-A_N*K_r(N)| <= C_epsilon*N^epsilon`.

The bound controls the sum of absolute remainders across all gcd groups,
not only one fixed group or their signed sum. It includes N=0. No RH,
harmonic-decay, sign, or numerical premise is used.

Lean also proves the resulting comparison

`|sum_r |H_r(N)| - A_N*sum_r |K_r(N)|| <= C_epsilon*N^epsilon`.

The definitions use coprime cofactor pairs d=r*a, e=r*b. The theorem
`gcd_pairs_eq_image` identifies this parametrization with exactly the original
positive gcd-r pairs. Multiplication by positive r is injective. The two
`*_eq_actual` theorems retain the original Möbius coefficients and original
moduli in the residue and harmonic forms.

## Arithmetic proof

Set Q=floor(N/r), t=floor(k/r), and v=k/r as a real number. The Möbius product
is mu(r)^2*mu(a)*mu(b), with the exact masks gcd(a,r)=gcd(b,r)=1. A failed
mask makes the corresponding original Möbius coefficient zero. The complete
inner floor column is the prime-supported count S_(r*a)(t), by the preceding
[complete-column theorem](edq-coprime-column-cancellation.md).

Writing

```
L = sum_(a<=Q, gcd(a,r)=1) mu(a)*S_(r*a)(t)/a,
F = sum_(a<=Q, gcd(a,r)=1) mu(a)*floor(t/a)*S_(r*a)(t),
```

finite polarization gives exactly

`B_r(N,k)-k^2*K_r(N)=mu(r)^2*(-2*v*L+F)`.

The actual v is retained, including its fractional offset v-t. For t=0 the
remainder is zero. Otherwise r*a<=N and t<=N give
`S_(r*a)(t)<=C_delta*N^(2delta)`. Therefore

```
|L| <= C_delta*N^(2delta)*(1+log N),
|F| <= v*C_delta*N^(2delta)*(1+log N).
```

After multiplication by 1/[k(k+1)], the absolute remainder is at most

`3*C_delta*N^(2delta)*(1+log N)/(r*k)`.

Summing r and k costs two further harmonic factors. Taking delta=epsilon/5
and bounding each logarithmic factor by a delta-power yields the theorem.
The variation comparison follows from the reverse triangle inequality.

## Consequence for the open bound

The [finite head-budget diagnostic](../2-fully-proven/computations/edq-gcd-head-tail-budget-2026-09-07/REPORT.md)
found failures of a fixed constant budget after splitting the polynomial
from the corrected head. Those finite failures do not distinguish the two
strategies at the level of cutoff exponents: the complete aggregate
correction is now proved subpower. The initial arithmetic coefficient
variation remains unpaid, as does the full later tail.

This theorem closes the all-gcd extension of the
[coprime initial remainder](edq-coprime-head-subpower.md). It does not bound
the retained harmonic coefficients, the complete EDQ energy, or the cofinal
current required for RH. No route is retired.

## Lean verification

Module: `GaloisForLFunctions.RHTower.EulerDeletionGcdHeadSubpower`.
Namespace: `RHTower.DeletionGcdHead`.
Three public definitions and five public theorems.

The complete scratch passed `LEAN_NUM_THREADS=1 lake env lean` without
diagnostics. Final `lake build --old` of this leaf passed; its own compilation
took 10 seconds. Six missing dependency artifacts required targeted recovery
and dependency builds; no full or umbrella build ran. Cached dependency logs
included older warnings; the new leaf produced none. Foreground checks and
the targeted build used one Lean process for this agent at a time.

Only the eight new public declarations were audited in a separate temporary
file. Each depends on exactly `propext`, `Classical.choice`, and `Quot.sound`;
none uses a computational certificate or added axiom. The umbrella import is
wired and indexes were refreshed once. No numerical experiment ran for this
proof. Repository formal lint passed. All owned temporary scratch files were
removed after the checks; no owned Lean process remains.
