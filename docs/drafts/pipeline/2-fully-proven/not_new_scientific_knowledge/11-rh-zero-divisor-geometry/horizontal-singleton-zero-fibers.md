# Horizontal-singleton zero fibers have positive density and satisfy RH pointwise

- **ID:** `horizontal-singleton-zero-fibers`
- **Stage:** 2-fully-proven / not-new-scientific-knowledge
- **Type:** THEOREM / BRIDGE
- **Scientific status:** `[PAPER-PROVED] [LEAN-POINTWISE-PROVED] [BRIDGE] [INSIGNIFICANT AS A STANDALONE PAPER]`
- **Statement:** Let `h(gamma)` be the total analytic multiplicity of all nontrivial zeta zeros
  with imaginary part `gamma`, and let `H_1(T)` count the positive ordinates at most `T` for which
  `h(gamma)=1`. Every such fiber consists of one simple critical-line zero. Moreover
  `H_1(T) >= N_{0,s}(T) - (N(T)-N_0(T))/2`. Consequently at least `0.116158438` of all
  nontrivial-zero copies lie in singleton horizontal fibers in lower density.

## Goal

Produce a non-vacuous intrinsic group of zeta zeros whose members lie on the critical line for a
reason different from their original mollifier or sign-change discovery. Membership is defined in
the full zero divisor by horizontal isolation, without inserting `Re rho=1/2`. The pointwise forcing
mechanism is the fixed-point law for functional-equation reflection, while positive density is a
separate global counting theorem.

## Exact definitions

For `T>0`, let:

- `N(T)` count all nontrivial zeros `rho=beta+i gamma` with `0<gamma<=T`, with multiplicity;
- `N_0(T)` count those copies with `beta=1/2`;
- `N_{0,s}(T)` count simple critical-line zeros;
- `h(gamma)` be the sum of multiplicities over every zero with imaginary part `gamma`;
- `H_1(T)=#{gamma in (0,T] : h(gamma)=1}`.

The endpoint convention is immaterial asymptotically but must be identical in every finite
inequality.

## Paper proof

### Pointwise fiber theorem

`[PAPER-PROVED]` Functional equation and Schwarz symmetry send a zero
`rho=beta+i gamma` of multiplicity `m` to

```text
rho^star = 1-conj(rho) = 1-beta+i gamma
```

with the same multiplicity. Thus reflection acts within each horizontal fiber. If `h(gamma)=1`,
the reflected zero copy must equal the original copy, so `beta=1/2`; total fiber multiplicity one
also makes the zero simple.

### Finite counting inequality

`[PAPER-PROVED]` Start with the `N_{0,s}(T)` simple critical-line ordinates. If one is not
a singleton horizontal fiber, every additional zero at that ordinate is off the line: another copy
at the central point would contradict simplicity. Every off-line copy brings its distinct reflected
copy at the same ordinate with equal multiplicity. Hence each spoiled simple critical ordinate
consumes at least two copies counted by `N(T)-N_0(T)`. Distinct ordinates consume disjoint copies, so

```text
2 (N_{0,s}(T)-H_1(T)) <= N(T)-N_0(T),
H_1(T) >= N_{0,s}(T) - (N(T)-N_0(T))/2.                 (1)
```

Consequently, if

```text
liminf N_0(T)/N(T) >= kappa,
liminf N_{0,s}(T)/N(T) >= kappa_star,
```

then

```text
liminf H_1(T)/N(T) >= kappa_star-(1-kappa)/2.           (2)
```

Pratt--Robles--Zaharescu--Zeindler prove the unconditional bounds

```text
kappa >= 0.417293962,
kappa_star >= 0.407511457.
```

Therefore `(2)` gives the exact advertised decimal lower bound

```text
0.407511457 + 0.417293962/2 - 1/2 = 0.116158438.
```

The liminf passage is valid because for real-valued functions `a,b`,
`liminf(a+b) >= liminf a + liminf b`, and multiplication by the positive scalar `1/2` commutes
with `liminf`. The identical strict or closed height convention is used in all four finite counts.

## Why this is a group theorem rather than an RH restatement

The predicate `h(gamma)=1` does not mention the critical line and can fail under RH-independent
horizontal collisions. Equation `(1)` is not a tautological recount of `N_0`: it removes every
simple critical zero whose ordinate is shared with any hypothetical off-line pair and still leaves
a positive candidate density. The proof of location for a surviving member uses only the
fixed-point structure of functional-equation reflection.

## Primary-source and novelty audit

- Pratt--Robles--Zaharescu--Zeindler, *More than five-twelfths of the zeros of zeta are on the
  critical line*, Research in the Mathematical Sciences 7 (2020), Article 2,
  DOI `10.1007/s40687-019-0199-8`: defines `N`, `N_0`, and `kappa`, identifies `kappa_star` as the
  simple-critical-zero proportion, and proves the two exact constants used above.
- H. M. Bui, *Critical zeros of the Riemann zeta-function*, arXiv:`1410.2433`: explicitly defines
  `kappa_star = liminf N_0^*(T)/N(T)` with `N_0^*` counting simple critical zeros.
- Goldston--Lee--Schettler--Suriajaya, arXiv:`2503.15449v4`, section 7, and
  Goldston--Suriajaya, arXiv:`2511.20059v2`, section 7: define horizontal multiplicity and explicitly
  note that horizontal multiplicity one means one simple critical zero.
- Neither horizontal-multiplicity paper derives the unconditional inequality `(1)` or the
  `0.116158438` lower density. Their density theorems use HMH, PCC, or a narrow-box hypothesis.
  Searches for the exact constant and same-ordinate charging formula found no prior statement.
  This is encouraging but is not a proof of novelty.

## Dual-gate verdict

**Verdict: `BRIDGE / INSIGNIFICANT AS A STANDALONE PAPER`.**

The exact decimal corollary may be absent from the searched literature, but its proof is a routine
two-line combination of the already-published PRZZ proportions with the elementary reflection
pairing already explicit in the horizontal-multiplicity papers. It introduces no new analytic
estimate, no new zero-detecting mechanism, no source-side invariant, and no improvement in the
known proportion of critical or simple-critical zeros. It therefore fails the significance gate
even if priority for the displayed inequality were eventually established.

The result is worth retaining as corpus support and as a normalization check for future horizontal
multiplicity work. It is not new scientific knowledge worth submitting as its own paper. A
paper-worthy successor must prove a new unconditional horizontal-multiplicity estimate from source
data, improve a known zero proportion, or construct a non-vacuous source-defined stratum not
obtained by filtering already-known critical zeros.

## Hostile attacks closed

1. `[CLOSED]` `N_0^*` counts simple critical zeros and its normalization is `N_0^*/N`; this is
   explicit in Bui and is the `kappa_star` quantity used by PRZZ.
2. `[SEARCH CLOSED; NOVELTY STILL UNVERIFIED]` No unconditional singleton-fiber density or exact
   charging inequality was found in the recent horizontal-multiplicity literature or citation
   descendants searched.
3. `[CLOSED]` A spoiled simple central ordinate consumes at least two off-line copies: a second
   central copy contradicts simplicity, while every off-line copy has a distinct equal-order
   reflection. Distinct ordinates give disjoint charges.
4. `[LIMITATION]` Distinguish intrinsic zero-group membership from a source-produced certificate. The
   theorem gives a genuine group and positive density, but deciding membership may still require
   full-divisor information.
5. `[CLOSED]` The corpus comparison found no prior positive-density horizontal-singleton theorem.
   Fixed-window, multiplicity-ladder, susceptibility, and completed-flux objects are consumers or
   conditional source packages; finite passports prove that finite local labels cannot select the
   line.

## Lean target

The exact actual-Xi pointwise theorem is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/HorizontalSingletonZeroFiber.lean`:

- `two_le_xiHorizontalMultiplicity_of_offLine`;
- `xiHorizontalSingletonZero_re_eq_half`;
- `xiHorizontalSingletonZero_order_eq_one`.

The finite global charging inequality `(1)` and the asymptotic numerical corollary are not promoted
to Lean declarations until the project's zero-counting API and the cited analytic proportion
bounds have unconditional formal providers. No hypothesis wrapper or axiom substitutes for them.

## Gates

- [x] 0 -> 1: exact intrinsic group, pointwise mechanism, finite charging inequality, hostile tests,
      and source/target distinction stated
- [x] external primary-source audit of both density inputs and the horizontal-multiplicity parent
- [x] hostile proof audit of `(1)` and liminf passage `(2)`
- [x] 1 -> 2: dependency-closed paper theorem with exact published constants and citations
- [x] exact unconditional Xi pointwise group theorem and simplicity theorem in Lean
- [ ] formalize the finite global counting law and its analytic density inputs before 2 -> 3
- [x] scientific novelty and significance audit: bridge-grade and not standalone-paper worthy

## Log

- 2026-07-17 — Created from the zero-group audit. The first live candidate is the horizontal
  singleton fiber, not a proof-labelled partition: pointwise location comes from symmetry, while
  positive density is charged against the globally available critical/simple-critical proportions.
- 2026-07-17 — Hostile primary-source audit closed the paper theorem with lower density
  `0.116158438`. Pointwise critical-line placement and simplicity were formalized for the actual Xi
  divisor. The card remains in `needs-audit`: the quantitative corollary appears absent from the
  searched literature but the dual novelty/significance gate is not yet closed.
- 2026-07-17 — Corrective dual-gate audit: demoted to `not_new_scientific_knowledge`. The theorem is
  correct and useful, but the quantitative statement is a routine corollary of PRZZ plus elementary
  reflection pairing and is not worth a standalone paper.

## Lean status update (2026-08-19)

`formal/GaloisForLFunctions/RHTower/HorizontalSingletonFiberCharging.lean` now formalizes the
**finite global counting law** and the **density passage**, unconditionally and with no hypothesis
wrapper, on the actual `xi` divisor:

- `xiZeroCount`, `xiCriticalZeroCount`, `xiOffLineZeroCount`, `xiSimpleCriticalZeroCount`,
  `xiSingletonFiberCount` — the four counts `N`, `N₀`, `N − N₀`, `N₀,s`, `H₁` at height `T`,
  built from the existing `stripFinsetLe` Xi-divisor API;
- `criticalFiber_eq_singleton` — an ordinate carries at most one critical-line point;
- `two_le_offLineFiber_sum` — a spoiled simple critical ordinate consumes at least two off-line
  copies (the reflection-charging step);
- `two_mul_xiSimpleCriticalZeroCount_le` — inequality `(1)` in the form
  `2·N₀,s(T) ≤ 2·H₁(T) + (N(T) − N₀(T))`;
- `xiSimpleCriticalZeroCount_sub_le_xiSingletonFiberCount` — the same over `ℝ` in the card's
  displayed form;
- `xiSimpleCriticalRatio_sub_le_xiSingletonFiberRatio` — the normalized law, valid also at heights
  with `N(T) = 0`;
- `le_liminf_xiSingletonFiberRatio` — the liminf passage `(2)`;
- `prattRoblesZaharescuZeindler_singleton_density` — the exact `0.116158438` corollary as an
  unconditional implication from the two published proportions.

`#print axioms` on all of these gives only `propext, Classical.choice, Quot.sound`.

Remaining for 2 -> 3: unconditional Lean providers for the two **cited analytic density inputs**
(`κ ≥ 0.417293962` and `κ_* ≥ 0.407511457`, Pratt--Robles--Zaharescu--Zeindler).  These are not
proved by this card; they are the mollified-moment lane whose substrate is being built on
`hardy-critical-line-moment-anchor`.

## Lean status update (2026-08-20)

**Name-collision repair.**  `HorizontalSingletonFiberCharging.lean` declared `xiZeroCount` and
`xiCriticalZeroCount` in namespace `RHTower`, colliding with the older `ℤ`-valued box/divisor
definitions in `RHTower/XiZeroCountingFunction.lean`; the `GaloisForLFunctions.RHTower` umbrella
could not elaborate.  The `Finset`-based strict-ordinate counts of this card are now
`xiPosZeroCount`, `xiPosCriticalZeroCount`, with the dependent names
`xiPosCriticalZeroCount_add_xiOffLineZeroCount`, `xiPosCriticalZeroCount_le`,
`card_le_xiPosZeroCount` renamed to match.  All statements are unchanged.

**Remaining gap, scoped.**  The two cited proportions are the *only* obstruction, and they are the
deepest unconditional results in the field: they need Levinson's method (Littlewood's lemma, the
Riemann–von Mangoldt formula, Levinson's `V = Q(−D)ζ` lemma, and a twisted mollified second moment
of `ζ`), and, for the exact displayed decimal, Conrey's `θ = 4/7` mollifier length with the
Deshouillers–Iwaniec spectral input plus the PRZZ two-piece optimization.  A hypothesis wrapper is
not acceptable, so the card stays at stage 2.

That work is now owned by `docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`,
which records the full dependency tree and its state.  Two of its ten bricks are already in the
tree: Littlewood's lemma (`weighted_littlewood_from_rectIntegral`) and the log-mean-to-mean-square
Jensen step (`RHTower/LevinsonLogMeanStep.lean`, `two_mul_integral_log_norm_le`, added today).

Note also that the *non-vacuity* threshold for this card is `κ_* > (1 − κ)/2`, i.e. `κ > 1/3` when
`κ = κ_*`.  So no proportion at or below Levinson's threshold suffices; the card genuinely requires
a `> 1/3` unconditional proportion, and the displayed `0.116158438` requires PRZZ exactly.

## A second, cheaper charging law (2026-08-20) — new mathematics for this card

The card's inequality `(1)` charges the spoiled **simple critical** ordinates against the off-line
census.  It therefore needs *two* proportions, `κ` and `κ_*`, and `κ_*` is the expensive one: it is
Levinson's method plus Heath-Brown's simple-zero refinement.

There is a charging that needs only **one** quantity, and it is the quantity that every sign-change
detector produces natively.

**Fibre parity.**  Off-line copies of a Xi zero come in `s ↦ 1 − s̄` pairs, and that involution's
only fixed points are on the critical line.  Hence for every ordinate `γ`

```text
h(γ) ≡ k(γ)   (mod 2),        k(γ) := the critical-line multiplicity at γ.
```

**Odd-fibre charging.**  Let `O(T)` count the ordinates in `(0, T]` with `h(γ)` odd — equivalently,
by the parity law, the critical-line zeros of odd order.  An odd number other than one is at least
three, so an odd ordinate is either a singleton fibre or carries `h(γ) ≥ 3`.  Distinct ordinates
have disjoint fibres, so

```text
3·O(T) ≤ 2·H₁(T) + N(T),        i.e.   H₁(T) ≥ (3/2)·O(T) − N(T)/2,
```

and in normalized form `H₁/N ≥ (3/2)·(O/N) − 1/2`.  **The bound is non-vacuous exactly when
`liminf O(T)/N(T) > 1/3`.**

**Why this matters for the card's dependency list.**  `O(T)` dominates the number of sign changes
of Hardy's `Z` in `(0, T]`, because a sign change forces a zero of odd order.  Sign changes are
exactly what Selberg's method and Levinson's detector `Re[γ(s)G(s)]` produce; no simple-zero
refinement is involved.  So this route replaces the pair `(κ, κ_*)` by the single proportion
`liminf O/N`, and removes Heath-Brown's theorem from the card's dependency list.

Neither inequality dominates the other pointwise (compare at `(k,j) = (2,0)`, where `(1)` gives `0`
and the odd-fibre law gives `−1`), so the card keeps both; the useful one is whichever matches the
analytic input available.

Lean: `formal/GaloisForLFunctions/RHTower/HorizontalOddFiberCharging.lean` —
`xiOddFiberCount`, `one_le_xiHorizontalMultiplicity_of_mem`, **`three_mul_xiOddFiberCount_le`**,
`xiOddFiberCount_charge_real`, `xiOddFiberRatio`, **`xiOddFiberRatio_charge`**;
`formal/GaloisForLFunctions/RHTower/HorizontalFibreParity.lean` —
`feSchwarz_eq_lineReflect`, **`xiHorizontalMultiplicity_odd_iff`** (the parity law),
`mem_xiOddFiber_iff` (odd fibre = critical zero of odd order).  All axiom-clean.

The sign-change bridge is also closed:
`formal/GaloisForLFunctions/RHTower/HardySignFlipOddOrder.lean` —
`re_xi_linePt_eq`, `re_xi_linePt_scale_pos`, `exists_odd_order_line_zero_of_sign_flip`, and
**`exists_odd_order_line_zero_of_hardyZ_sign_flip`**: `hardyZ τ₁ · hardyZ τ₂ < 0` with `τ₁ < τ₂`
produces `τ' ∈ (τ₁, τ₂)` with `xi(linePt τ') = 0` and `(analyticOrderAt xi (linePt τ')).toNat` odd.
It rests on the corpus's seam-parity theorem `line_sign_flip_iff_odd_total_order` and the on-segment
peeling `xi_line_multi_peel`; the only new step is that an odd *total* forces an odd *summand*.
Axiom-clean.

So the whole combinatorial half of the odd-fibre route is Lean-complete: **any** sign-change count
for `Z` now feeds `H₁ ≥ (3/2)·O − N/2` directly.  What remains is the single analytic proportion
`liminf O(T)/N(T) > 1/3`, which is
`docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`.

## The combinatorial pipeline is closed end to end (2026-08-20)

`formal/GaloisForLFunctions/RHTower/HardySignChainCount.lean` assembles every step into one
statement.  For a strictly increasing chain `g 0 < g 1 < … < g n` inside `(0, T]` across which
Hardy's `Z` alternates in sign,

```text
three_mul_le_two_mul_xiSingletonFiberCount_add_of_sign_chain :
    3·n  ≤  2·H₁(T) + N(T),
xiSingletonFiberCount_ge_of_sign_chain :
    H₁(T)  ≥  (3/2)·n − N(T)/2.
```

The chain of unconditional steps behind it:

1. sign change of `Z` ⟹ critical zero of **odd order** strictly inside the subinterval
   (`exists_odd_order_line_zero_of_hardyZ_sign_flip`, from the corpus's seam-parity theorem);
2. disjoint subintervals ⟹ distinct ordinates (`le_xiOddFiberCount_of_sign_chain`);
3. odd critical order ⟺ odd **fibre** (`xiHorizontalMultiplicity_odd_iff`, the reflection
   involution has the critical line as its exact fixed-point set);
4. odd fibre ⟹ singleton, or fibre multiplicity ≥ 3 (`three_mul_xiOddFiberCount_le`).

All axiom-clean.  **Nothing combinatorial remains.**  The card is now blocked on exactly one
analytic statement: a lower bound of the form `n ≥ (1/3 + δ)·N(T)` for the sign-change count of `Z`
in `(0, T]`.  Levinson's method produces precisely that count — on the critical line his detector
`Re[Γ_ℝ·G]` equals `Ξ` times a nonvanishing factor
(`re_Gammaℝ_mul_levinsonG_eq_half_Y_mul_completed`) — with constant `0.3474… > 1/3`.  That work is
`docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`.

## Status of the one remaining analytic input (2026-08-20, later)

Everything below is Lean-proved and axiom-clean; all of it exists **for this card** and is tracked in
`docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`.

### The window inequality is closed (brick 4)

`RHTower/LevinsonWindowBound.exists_levinson_window_edge_bound` reduces the required sign-change
count to a single zero count.  For real `λ ∈ [−1, 0)` and `20 ≤ T₁ < T₂` at admissible heights:

```text
(n+1)π + π + (T₂−T₁)·6/T₁² + c·log T₁ + c·log T₂
     + 2π·#{zeros of G♯ in [½,4]×[T₁,T₂]}   ≤   θ(T₂) − θ(T₁)
  ⟹  n ≤ xiOddFiberCount T₂  ⟹  H₁(T₂) ≥ (3/2)n − N(T₂)/2.
```

The chain: polar form of `Z` from Levinson's detector; `ψ(T₂)−ψ(T₁) = Δθ + ∫Re(G′/G)`; the entire
detector `G♯ = (s−1)²G`; the rectangle argument principle in argument-variation form; the right edge
`≤ π` (because `Re G > 0` on `Re s = 4`); the horizontal edges `O(log T)` (Backlund + Jensen on the
real trace of `G`); and density of admissible heights.  Modules:
`LevinsonPhaseAdvance`, `LevinsonEntireDetector`, `EntireArgumentVariationRectangle`,
`LevinsonEntirePhaseAdvance`, `LevinsonWindowAdvance`, `PhaseAdvanceIncrementCount`,
`ZetaFarRightDecay`, `LevinsonRightEdge`, `LevinsonStripBound`, `LevinsonRealTrace`,
`LevinsonHorizontalEdge`, `LevinsonAdmissibleHeight`, `LevinsonWindowBound`, plus
`HTGeometry/SegmentPolarForm` and `HTGeometry/SegmentArgumentBound`.

### The mollified second moment (brick 5) — in progress

* **5a closed.**  `HTGeometry/ExponentialWindowIntegral`, `TwistedDirichletMeanValue`,
  `TwistedDiagonal`, `TwistedMeanValueSplit`; `RHTower/Sieve/DistinctReciprocalSum`,
  `TwistedOffDiagonalSum`, `TwistedMeanValueError`, `TwistedDiagonalReindex`.  Capstones:
  `twisted_meanValue_error` (twisted mean value with explicit `U`-free error) and
  `twisted_diagonal_reindex` (for coprime `h,k` the diagonal `nk = mh` is exactly `(kd, hd)`).
* **5b closed.**  The Gaussian smooth approximate functional equation now holds at every `s` with
  `0 < Re s < 2`, `s ≠ 1` — the abscissa `σ₀ = ½ − R/log T` that Levinson's method uses.  Modules:
  `ZetaVerticalLineGrowth`, `GaussianShiftedMoment`, `SmoothAFEZetaGeneralHorizontal`,
  `SmoothAFEZetaGeneralVertical`, `SmoothAFEZetaGeneral`.
* **5c–5e open.**  Assemble `∫|G♯·M|²` at `σ₀` from the general AFE and the twisted mean value;
  evaluate the arithmetic main term; optimize to `κ > 1/3`.

### Why the constants matter for this card

`H₁ ≥ (3/2)·n − N/2` is non-vacuous exactly when `liminf n/N > 1/3`; Levinson's own constant
`0.3474…` already suffices for positivity.  The card's advertised decimal `0.116158438` needs the
PRZZ pair `κ ≥ 0.417293962`, `κ_* ≥ 0.407511457`, i.e. bricks 9–10 (Conrey's `θ = 4/7` mollifier and
the PRZZ optimization) on top of brick 5.

## Lean status update (2026-08-25) — moving displaced cross transfer closed

The phase-faithful direct/reflected cross now reaches the literal moving differentiated smooth AFE
on short dyadic windows. New modules prove the subinterval stationary-oscillation estimate, its
finite Dirichlet-cross expansion, the frozen smooth-AFE specialization, the positive direct-head
energy bound, and the exact moving-equals-frozen-plus-chi-weighted-freezing-error decomposition.
The capstone
`exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_movingReflected_le_frozen_add_dyadic`
bounds the actual moving cross by the unchanged frozen oscillatory integral plus an explicit
square-root error built from unconditional direct and freezing mean squares.

All new declarations pass direct file checks, exact leaf builds, and batched `#print axioms` with
only `propext, Classical.choice, Quot.sound`; all leaves are wired into `RHTower.lean` without an
umbrella build.

This closes moving-coefficient variation and short-window transfer, but not the analytic density
input. Remaining obligations are the sharp coefficient summation in Levinson scaling, the sharp
long-tail estimate for `levinsonCriticalDetectorLongEnergy`, and explicit parameter optimization.
The exact advertised `0.116158438` still requires unconditional Lean providers for the published
PRZZ proportions `κ ≥ 0.417293962` and `κ_* ≥ 0.407511457`. Card therefore remains at stage 2.

## Lean status update (2026-08-25) — exact long-tail frontier exposed

The exact finite-convolution long range is now decomposed coefficientwise into the full
differentiated Barban--Vehov coefficient minus its omitted-head divisor boundary. Both resulting
energies are reindexed on `(L,L*M]`, and the full term has its literal arithmetic quadratic-form
normal form. Independent unconditional caps are available from a divisor-fibre estimate and from
the new finite multiplicative Young inequality; the latter removes the divisor factor but gives
only the coarse bound `longEnergy <= 4*M*headEnergy`.

All new declarations are axiom-clean and wired without an umbrella build. Neither coarse cap is
silently treated as the sharp Levinson asymptotic. Remaining analytic inputs are unchanged: sharp
evaluation of the full and omitted long tails, sharp summation of the displaced mixed-cross
coefficients, and the published parameter optimization. Exact decimal still requires both PRZZ
proportion providers, so card remains at stage 2.
