# Bounded-support Weil tests cannot annihilate the critical-line tail

- **ID:** bounded-support-weil-critical-tail-uniqueness
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / formalized analytic core
- **Source:** Burnol small-support Weil positivity; Platt--Trudgian divisor residualization; positive proportion of simple critical zeros
- **Statement:** `[PROVED HERE]` The Mellin transform of a nonzero smooth compactly supported test cannot vanish at all but finitely many simple critical-line zeros of the Riemann zeta function. Consequently no bounded-support Weil test can annihilate the unknown infinite fixed-orbit tail while retaining a free-orbit detector.

## Goal

Test the first genuinely infinite-Euler, no-jet route.  Burnol proved unconditional Weil positivity
for all smooth tests supported in a fixed nontrivial multiplicative neighborhood of `1`.  After a
finite certified critical-line divisor is annihilated, this gives an unconditional positive residual
form.  The question is whether the same bounded-support class can also annihilate the unknown
critical-line tail and isolate a first free orbit.

## Gates

- [x] 0 → 1 in-progress: Burnol-positive class, finite certified annihilator, and tail-isolation question stated.
- [x] 1 → 2 fully-proven: exponential-type zero count and critical-zero-density contradiction proved.
- [ ] 2 → 3 formalized: the exponential-type zero-count engine is formalized as `RHTower.exponentialType_zeroCount_le` and `RHTower.exponentialType_zeroCount_linear`; the Paley--Wiener and external critical-zero-density imports remain paper-level.
- [ ] 3 → 4 publication-ready: not applicable without a novelty upgrade; current classification is `[BRIDGE]`.

## Setup

For `g in C_c^infinity(0,infinity)`, write

```text
G(s) = integral_0^infinity g(u) u^(s-1) du.
```

After `u=exp(x)`, set

```text
phi(x) = exp(x/2) g(exp x),
F(z)   = G(1/2+i z) = integral_R phi(x) exp(i z x) dx.
```

The function `phi` is smooth and compactly supported.  Hence `F` is entire and, if
`supp(phi) subset [-A,A]`, satisfies

```text
|F(z)| <= ||phi||_1 exp(A |z|).
```

Thus `F` has finite exponential type.

## Theorem 1: linear zero density for finite exponential type

`[PROVED HERE + LEAN]` Let `F` be a nonzero entire function with

```text
|F(z)| <= C exp(A |z|),    A >= 0, C >= 1.
```

Choose `c` with `F(c) != 0`.  Jensen's inequality on the concentric discs of radii `r` and `2r`
gives, for `r>=1`,

```text
N_F(c,r)
 <= [log C + A(|c|+2r) - log|F(c)|] / log 2
 <= K(1+r).
```

Here `N_F(c,r)` counts zeros with multiplicity in the closed disc.  The exact inequalities are
formalized in `ExponentialTypeZeroDensity.lean`; the full project build and formal lint pass.

## Theorem 2: the critical-line tail is a uniqueness set

`[PROVED HERE, external density input]` Pratt--Robles--Zaharescu--Zeindler prove unconditionally
that a positive proportion of all nontrivial zeta zeros are simple and on the critical line; their
bound is `kappa_* >= 0.407511`.  Together with the Riemann--von Mangoldt asymptotic, the number
`N_simple,0(T)` of distinct simple critical-line ordinates up to `T` therefore satisfies

```text
N_simple,0(T) >= c T log T
```

for some `c>0` and all sufficiently large `T`.

Suppose `G(1/2+i gamma)=0` at all but finitely many simple critical-line zeros.  Then `F` has at
least `c T log T + O(1)` distinct zeros in a disc of radius `T+O(1)`.  Theorem 1 gives only `O(T)`
zeros unless `F` is identically zero.  Hence `F=0`.  Fourier injectivity gives `phi=0`, and therefore
`g=0`.

The same proof applies if finitely many initial critical-line zeros are omitted.  In particular, the
entire unknown fixed-orbit tail remains a uniqueness set after deleting the Platt--Trudgian prefix.

## Finite-prefix residual positivity

`[BRIDGE]` Burnol proved that there is `c_B>1` such that the Weil zero form

```text
Z(g * g_tau) = sum_rho G(rho) G(1-rho)
```

is nonnegative whenever `g` is smooth and supported in `[1/c_B,c_B]`.  Let `D_0` be any finite
certified critical-line divisor and restrict to tests with `G(rho)=0` for `rho in D_0`.  Every term
from `D_0` vanishes, so Burnol's theorem gives the exact residual inequality

```text
sum_(rho notin D_0) G(rho) G(1-rho) >= 0.
```

This annihilator is nontrivial.  In logarithmic coordinates, if the positive ordinates in `D_0` are
`gamma_1,...,gamma_N`, apply the constant-coefficient operator

```text
P(D) = product_j (D^2 + gamma_j^2)
```

to a nonzero bump supported strictly inside the same interval.  Its Fourier transform is multiplied
by `product_j (gamma_j^2-z^2)`, so it vanishes at every `+/- gamma_j`; differentiation does not enlarge
support.  A nonzero compactly supported function cannot lie in the kernel of a nonzero
constant-coefficient differential operator, so the resulting annihilator is nonzero.

Theorem 2 shows exactly where this positive result stops: no nonzero member can also annihilate the
infinite fixed-orbit tail.

## Consequence for verified-height amplification

`[PROVED NO-GO]` A bounded multiplicative-support Weil class cannot isolate a first free orbit by
removing every fixed-orbit contribution.  The finite Platt--Trudgian divisor can be killed without
leaving Burnol's positive class, but the unknown infinite critical-line tail cannot: it is already a
uniqueness set for that class.

This does not say that every bounded-support test is insensitive to every free orbit.  It says the
stronger property needed for an orbit-uniform lower-bound proof--eliminating arbitrary future fixed
orbits so that their positive contributions cannot mask a free orbit--is impossible at bounded
support.

`[OPEN CORE]` A successful infinite-Euler amplifier must therefore do one of the following:

1. use an unbounded-support/all-place test family and prove its positivity without assuming the full
   Weil criterion;
2. replace continuous Weil evaluation by an integer index or local zero count; or
3. prove an explicit upper budget on the unknown fixed-orbit contribution in the proposed extension
   region.

Option 3 is the earlier one-zero count target.  Options 1 and 2 are the only genuinely new no-jet
escapes exposed by this theorem.

## Research classification

`[BRIDGE]` The proof combines classical Paley--Wiener/Jensen theory, Burnol's support-positive Weil
theorem, and a published positive-proportion theorem.  The exact critical-tail uniqueness statement
does not appear in the targeted literature search, but it is mechanically derivable from those parent
results and therefore does not clear the novelty gate.  Its value is the exact elimination of the
bounded-support infinite-Euler route.

## References

- J.-F. Burnol, *Sur les Formules Explicites I: analyse invariante*, C. R. Acad. Sci. Paris 331 (2000), 423--428, arXiv:math/0101068.
- K. Pratt, N. Robles, A. Zaharescu, D. Zeindler, *More than five-twelfths of the zeros of zeta are on the critical line*, Res. Math. Sci. 7 (2020), Article 2, DOI 10.1007/s40687-019-0199-8.

## Log

- 2026-07-10 -- Paper theorem completed; Jensen zero-density core formalized in Lean.  Classified as formalized analytic infrastructure plus a paper-level not-new route obstruction.

## Lean status update (2026-08-25)

`formal/GaloisForLFunctions/RHTower/XiSimpleCriticalExponentialTypeBound.lean` closes the
finite-prefix Paley--Wiener/Jensen bridge on the actual Xi divisor:

* `xiSimpleCriticalZeroFinset` and `xiSimpleCriticalOrdinateFinset` identify the actual simple
  critical zeros in `(0,T]` with an injective finite set of positive ordinates, whose cardinality is
  exactly `xiSimpleCriticalZeroCount T`;
* `exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros` proves that if a
  nonzero entire finite-exponential-type function vanishes at all of those ordinates apart from a
  fixed finite set `E`, then
  `xiSimpleCriticalZeroCount T <= K(1+T)+#E` for every `T>=1`;
* `exists_xiSimpleCriticalZeroCount_linear_of_cofinite_suzukiFourier_zeros` specializes the result
  to the literal Fourier transform of arbitrary compactly supported `L²` data using the existing
  Paley--Wiener growth theorem; `suzukiCutoff_eq_zero_of_compactFourier_eq_zero` closes the final
  Fourier-injectivity step.

`formal/GaloisForLFunctions/RHTower/WeilCriticalMellinLogBridge.lean` now closes the literal
test-function notation bridge for every continuous multiplicative test `g` supported in
`[exp(-a),exp(a)]`: it constructs `phi(x)=exp(x/2)g(exp x)`, proves its support lies in
`[-a,a]`, packages it as the actual global `L²` vector consumed by Suzuki's compact Fourier
carrier, and proves exactly

```text
mellin g (1/2+i t) = suzukiCompactL2Fourier a phi_L2 t.
```

Both leaves pass direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. They are wired
into `RHTower.lean`; no umbrella build was run.

Remaining for 2 -> 3 is now exactly the unconditional superlinear provider
`xiSimpleCriticalZeroCount T >= c*T*log T` for all sufficiently large `T`. It is the same PRZZ
simple-critical density input already tracked by the Levinson programme; no hypothesis wrapper has
been added.

## Lean status update (2026-08-30) — consumer side CLOSED, gate pinned to one statement

**Staleness audit.**  Every Lean declaration this card claims was re-verified against the tree:
`exponentialType_zeroCount_le`, `exponentialType_zeroCount_linear`, `xiSimpleCriticalZeroCount`,
`exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros`,
`exists_xiSimpleCriticalZeroCount_linear_of_cofinite_suzukiFourier_zeros`,
`suzukiCutoff_eq_zero_of_compactFourier_eq_zero` — all present, none stale.

**New: the consumer step.**  `formal/GaloisForLFunctions/RHTower/XiSimpleCriticalSuperlinearConsumer.lean`
(axiom-clean, wired into `RHTower.lean`, exact leaf build with no warnings) closes the last
*structural* step of this card:

* `not_linear_bound_of_superlinear` — a linear upper bound `F T ≤ K(1+T)+m` and a superlinear lower
  bound `c·T·log T ≤ F T` are incompatible;
* **`suzukiCompactL2Fourier_eq_zero_of_superlinear_simpleCritical`** — given
  `∀ᶠ T, c·T·log T ≤ N₀,s(T)` with `c > 0`, any compactly supported `L²` datum whose Fourier
  transform vanishes at all but finitely many simple critical ordinates has *identically vanishing*
  Fourier transform;
* **`suzukiCutoff_eq_zero_of_superlinear_simpleCritical`** — hence the compactly supported source
  itself vanishes.  This is the card's Theorem 2 in Lean, with its analytic input isolated as the
  single explicit premise.

**The gate is now exactly one unconditional statement:**

```text
∃ c > 0, ∀ᶠ T in atTop,  c · T · log T  ≤  (xiSimpleCriticalZeroCount T : ℝ).
```

Nothing else on this card is open.  That statement is a positive proportion of *simple* critical
zeros (Levinson's method plus Heath-Brown's simple-zero refinement); it is not obtainable from
Riemann–von Mangoldt alone, because bounded multiplicities only give `≫ T` distinct ordinates, and
the exponential-type bound already supplies `O(T)`.

**Owner of the gate:** `docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`.
Progress there on 2026-08-29/30: the *whole arithmetic layer* of the mollified second moment is now
closed — both Selberg families

```text
∑_{m,n≤N} c(m,n)·log(N/m)^i log(N/n)^j                ~ (ij/(i+j−1))·(log N)^{i+j−1}
∑_{m,n≤N} c(m,n)·log(N/m)^i log(N/n)^j·log(m,n)        ~ (ij/((i+j−1)(i+j)))·(log N)^{i+j}
```

are unconditional Lean theorems (`tendsto_selbergOriginalLogMonomial_div_log_pow`,
`tendsto_selbergOriginalGcdLogMonomial_div_log_pow`), and the pair was verified to reproduce Young's
constant `c(P,Q,R,θ)` exactly.  The remaining gate there is the analytic twisted second moment.

## Lean status update (2026-08-30, later) — the gate is now shared with card 2, and stated in density form

**New: the census is the Riemann–von Mangoldt counting function.**
`formal/GaloisForLFunctions/RHTower/XiCensusVonMangoldtBridge.lean` (axiom-clean, wired, exact leaf
build, `lake env lean` warning-free):

* `stripFinsetPos_eq_image` — the census index set is exactly the `ξ`-divisor support with positive
  ordinate (every `ξ`-zero lies in the open strip, and the divisor support is the zero set);
* **`xiPosZeroCount_eq_xiZeroCount`** — `N(T)` as used by this folder's charging law *is* the
  corpus's counting function `xiZeroCount T`, as integers;
* **`eventually_inv_four_pi_mul_le_xiPosZeroCount`** — hence, unconditionally,

  ```text
  ∀ᶠ T,  (1/4π)·T log T ≤ N(T),
  ```

  from `exists_xiZeroCount_close` (the corpus's unconditional Riemann–von Mangoldt asymptotic);
* **`exists_superlinear_of_le_liminf_xiSimpleCriticalRatio`** —

  ```text
  0 < c,   c ≤ liminf N₀,s(T)/N(T)   ⟹   ∃ c' > 0, ∀ᶠ T,  c'·T log T ≤ N₀,s(T),
  ```

  with the explicit constant `c' = c/(8π)`.

**Consequence — this card's theorem now holds in density form.**
`formal/GaloisForLFunctions/RHTower/XiCardGateUnification.lean` (axiom-clean, wired, clean):

* **`suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio`** — for *any* `c > 0` with
  `c ≤ liminf xiSimpleCriticalRatio atTop`, a compactly supported `L²` source whose Fourier
  transform vanishes at all but finitely many simple critical ordinates is itself zero;
* `suzukiCutoff_eq_zero_of_prattRoblesZaharescuZeindler` — the PRZZ constant `0.407511457`
  discharges it;
* `suzukiCutoff_eq_zero_of_levinson` — so does Levinson's own `0.3474`.

**What this changes.**  This card and `horizontal-singleton-zero-fibers.md` no longer have two
different gates.  Card 2 needs `κ_s ≤ liminf xiSimpleCriticalRatio` for a specific decimal; this
card needs the *same* liminf bounded below by *any* positive number.  The superlinear-count
formulation is now derived, not assumed, and the weakest sufficient input for this card is

```text
∃ c > 0,  c ≤ liminf xiSimpleCriticalRatio atTop
```

— i.e. any positive proportion of simple critical zeros.  Levinson's method with Heath-Brown's
simple-zero refinement supplies it; the programme card
`docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md` owns it, and its
analytic gate (the twisted second moment) had its **main term closed in Lean on 2026-08-30**
(bricks 5ap–5ay), by two independent routes that agree.

## Lean status update (2026-09-01) — the shared gate's consumer half is Lean-closed

This card's gate is `∃ c > 0, c ≤ liminf xiSimpleCriticalRatio atTop`, which the folder shares with
`horizontal-singleton-zero-fibers.md`.  Levinson's method supplies it (an odd fibre of multiplicity
≥ 3 costs three zeros, so `N₀,s ≥ O − N/3`, and `liminf O/N > 1/3` therefore gives a positive
proportion of *simple* critical zeros).

Today the whole consumer half of Levinson's method became unconditional Lean — eighteen new
axiom-clean modules, capstone `RHTower.exists_le_xiOddFiberCount_of_mollified_meanSquare`.  Full
detail is on `docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`
(bricks 7a–7e).  What remains for this card is exactly the mollified mean square of
`(ζ + λζ′)·Ψ` on the Levinson abscissa, plus the density passage.  Card stays at stage 2.

### Gate reduction completed (2026-09-01, later)

`RHTower.le_liminf_xiSimpleCriticalRatio_of_gate` now derives this card's *exact* gate

```text
∃ c > 0,  c ≤ liminf xiSimpleCriticalRatio atTop
```

from `LevinsonMeanSquareGate R c` alone (Levinson's mollified mean square), unconditionally and
axiom-clean; `suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio` then closes the card's
Theorem 2.  The only open statement left for this card is therefore the mollified mean square
itself.

## Lean status update (2026-09-02) — sign repaired; physical-scale gate remains open

An exact corpus search found no unconditional provider for

```text
∃ c > 0, c ≤ liminf xiSimpleCriticalRatio atTop.
```

The apparent shortcut through the finite-polynomial mean square does not discharge it.  In
`LevinsonFiniteCoefficientMeanSquareLimit.lean` the schedule is

```text
height = N^200,  AFE head = N^100,  mollifier = N^49.
```

Thus the mollifier has physical height exponent `49/200`, not `49/100`.  Its exact limit
`19751/14700` cannot be connected to the `49/100` Levinson optimization by relabelling the AFE-head
exponent.  The existing coefficient-energy argument also requires `8 M^2 ≤ L`, which is compatible
with this short mollifier but not with a physical `T^0.49` mollifier against a symmetric
`L ≍ T^(1/2)` AFE head.  A genuine twisted second-moment theorem at the required physical scale is
still missing.

The detector-sign mismatch was repaired independently.  The arithmetic coefficient
`1 - λ log n` uses the classical positive parameter `λ = 1/log T`; the new axiom-clean theorem
`levinsonY_line_re_pos_reciprocal_log` proves the exact archimedean weight is positive throughout
`[20,T]`, and the polar/window/counting chain now exposes that positivity condition without changing
the legacy negative-parameter API.  This is necessary infrastructure, but it does not supply the
missing mean square.  No density hypothesis or axiom was introduced as a substitute, so the card
remains at stage 2.
