# Cofinal Floquet lift of the secondary Poisson graph

- **ID:** `deninger-cofinal-floquet-secondary-poisson-graph`
- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION / EXACT RADICAL / FRONTIER CLASSIFICATION
- **Labels:**
  - `DAC_DENINGER_COFINAL_FLOQUET_SECONDARY_POISSON_GRAPH`;
  - `DAC_DENINGER_SECONDARY_GRAPH_POISSON_RANGE_GAP`.
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Inputs:**
  - `DAC_DENINGER_MEYER_SECONDARY_POISSON_REGULATOR`;
  - `DAC_DENINGER_COFINAL_TATE_FLOQUET_TOMOGRAPHY`;
  - `DAC_DENINGER_ALL_PRIME_FLOQUET_COCHAIN_HODGE_ENERGY`.
- **Claim:** the already-formalized two-collar Meyer--Poisson regulator has a canonical full-circle
  half-density lift. Its all-prime square sum is continuous and its radical is exactly the full
  reflected Calderón graph. Literal Poisson boundaries lie in that radical, but the radical is
  strictly typed as a graph relation rather than as the actual Poisson range. This identifies the
  missing Route-L theorem as Poisson-range incidence inside the reflected graph.

## 1. Centered two-collar defect

Work in logarithmic coordinates with
\[
 H_-=\mathscr S_{\exp}(\mathbb R),\qquad
 (Uh)(t)=e^{t/2}h(t).
\tag{1}
\]
Multiplication by any real exponential and reflection preserve $H_-$. For a physical/Fourier
collar pair $(h_+,h_-)\in H_-\oplus H_-$ define
\[
 d_{\mathrm{sec}}(h_+,h_-)(t)
 =Uh_+(t)-Uh_-(-t).
\tag{2}
\]
Thus $d_{\mathrm{sec}}:H_-^2\to H_-$ is continuous.

For $q$ prime, let $L_q=\log q$ and define the full-circle secondary trace
\[
 \mathcal S_q(h_+,h_-)(t)
 =\sum_{j\in\mathbb Z}
   d_{\mathrm{sec}}(h_+,h_-)(t+jL_q).
\tag{3}
\]
It is a smooth $L_q$-periodic function. Its value before orbit summation at $t=\log p$ is
\[
 p^{-1}d_{\mathrm{sec}}(h_+,h_-)(\log p)
 =p^{-1/2}h_+(\log p)-p^{-3/2}h_-(-\log p),
\tag{4}
\]
exactly the scalar two-collar coefficient used by
`DAC_DENINGER_MEYER_SECONDARY_POISSON_REGULATOR` after passing between radial and logarithmic
coordinates. Hence `(3)` is a lift of the existing regulator, not an unrelated reporter.

## 2. Exact all-prime radical

Define
\[
 \mathcal E_{\mathrm{sec}}(h_+,h_-)
 =\sum_q q^{-2}\int_0^{L_q}
   |\mathcal S_q(h_+,h_-)(t)|^2\,dt.
\tag{5}
\]

`[PROVED HERE] [DAC_DENINGER_COFINAL_FLOQUET_SECONDARY_POISSON_GRAPH]`

The series `(5)` is finite and continuous on $H_-^2$, and
\[
 \mathcal E_{\mathrm{sec}}(h_+,h_-)=0
 \quad\Longleftrightarrow\quad
 Uh_+(t)=Uh_-(-t)\quad(t\in\mathbb R).
\tag{6}
\]
Equivalently, its radical is exactly the closed reflected Calderón graph
\[
 \Gamma_{\mathrm{sec}}
 =\{(h_+,h_-):h_+(t)=e^{-t}h_-(-t)\}.
\tag{7}
\]

### Proof

Formula `(5)` is the all-prime periodization energy of the single strong-Schwartz function
$d_{\mathrm{sec}}(h_+,h_-)$. The uniform periodization estimate used for
`DAC_DENINGER_ALL_PRIME_FLOQUET_COCHAIN_HODGE_ENERGY`, together with continuity of `(2)`, proves
finiteness and continuity. If `(5)` vanishes, every prime periodization `(3)` vanishes. Any
infinite prime subfamily is injective on $H_-$ by cofinal periodization tomography, so
$d_{\mathrm{sec}}(h_+,h_-)=0$. This is `(6)` and rearranging `(2)` gives `(7)`. The converse is
immediate.

For the centered contragredient collar flow
\[
 (h_+,h_-)\longmapsto(V_ah_+,V_{-a}h_-),
 \qquad V_a=e^{-a/2}T_a,
\tag{8}
\]
the defect `(2)` translates by $a$. Therefore `(5)` is invariant, as required for a two-sided
weight-one seam.

## 3. Literal Poisson boundaries and exact overkill

Let $f\in H_\cap$, and write in logarithmic coordinates
\[
 h_+(t)=Zf(e^t),\qquad h_-(t)=Z\widehat f(e^t).
\tag{9}
\]
Meyer--Poisson reflection is
\[
 Zf(e^t)=e^{-t}Z\widehat f(e^{-t}).
\tag{10}
\]
Equations `(7)` and `(10)` give
\[
 (Zf,Z\widehat f)\in\ker\mathcal E_{\mathrm{sec}}.
\tag{11}
\]
Thus the full-circle lift admits and annihilates every literal Poisson boundary before any Hilbert
quotient.

`[PROVED HERE] [DAC_DENINGER_SECONDARY_GRAPH_POISSON_RANGE_GAP]`

The information supplied by Poisson reflection alone is exactly `(7)`, not membership in the
smaller range
\[
 \mathcal B_{\mathrm P}
 =\{(Zf,Z\widehat f):f\in H_\cap\}.
\tag{12}
\]
Indeed, for every $h\in H_-$ the pair
\[
 (h,Jh),\qquad (Jh)(t)=e^{-t}h(-t),
\tag{13}
\]
lies in `(7)`. The inclusion `(12)\subset\Gamma_{\mathrm{sec}}$ is strict: Meyer's quotient
$H_-/Z(H_\cap)$ is unconditionally nonzero (one may evaluate at any certified nontrivial zeta
zero), so choose $h\notin Z(H_\cap)$. Then $(h,Jh)$ lies in `(7)` but cannot lie in `(12)`.
Hence any theorem identifying the radical of the secondary Floquet energy with
`(12)` must use an additional source incidence condition proving
\[
 \Gamma_{\mathrm{sec}}\cap\mathcal I_{\Gamma/\mathrm{coP}}
 =\mathcal B_{\mathrm P}
\tag{14}
\]
inside a specified Gamma/co-Poisson chain domain. Neither reflection nor cofinal tomography can
prove `(14)` by itself.

This is the exact positive survivor and exact obstruction exposed by the secondary regulator. The
successor theorem `DAC_DENINGER_MOBIUS_REGULARITY_POISSON_RANGE_CLASSIFICATION` now identifies the
set-theoretic range condition in `(14)`: the canonical Möbius preimage must extend as an
$H_\cap$ function. What remains missing is a Gamma/co-Poisson Green--Stokes realization of that
singular endpoint/Fourier regularity defect, not another reflected trace.

## 4. Conjecture loop

1. **Conjecture: lift the scalar secondary regulator around every prime circle.**
   **Proved by `(2)`--`(5)`.**
2. **Conjecture: cofinal lifting may leave extra invisible periodization modes.**
   **Failed by `(6)`.** Cofinal tomography makes the radical exactly the pointwise reflected graph.
3. **Conjecture: the reflected graph is the Poisson boundary range.**
   **Failed as an inference.** Formula `(13)` shows reflection alone admits every $h\in H_-$;
   Poisson-range membership requires the additional incidence `(14)`, subsequently identified as
   canonical Möbius regularity.
4. **Conjecture: Hilbert completion can supply that incidence.**
   **Failed by `DAC_DENINGER_BOUNDED_FLOQUET_CORRECTION_RESONANCE_NO_GO`.** Every bounded repair
   factors through the resonance-only quotient.

## 5. Hostile audit

- **No rediscovery claim.** Poisson reflection and the scalar two-collar regulator are existing
  corpus results. New content is their full-circle lift, its cofinal exact radical, and the
  resulting range-gap classification.
- **No quotient theatre.** Literal boundaries vanish in `(11)` before completion.
- **No false exactness.** Radical is claimed to be `(7)`, not the smaller range `(12)`.
- **No RH premise or divisor selection.** Proof uses source decay, Poisson reflection, prime
  lengths, and cofinal identity-theorem tomography only.
- **No Lean claim.** Lean corpus was read only during its ongoing refactor.

## Lean status

`formal/GaloisForLFunctions/RHTower/DeningerSecondaryCollarDefect.lean`, together with
`DeningerCollarExchange.lean` and `DeningerMeyerPeriodization.lean`.  Axiom audit for every
declaration: `propext, Classical.choice, Quot.sound`.

### Done

- `(1)` — `deningerRealExpWeight`, `deningerExpMul`: **multiplication by any real exponential
  `e^{ct}` is an operation of `H_-`**, costing `|c|` units of the source exponent.  The proof is the
  Leibniz bound plus `‖D^n e^{ct}‖ = |c|^n e^{ct}`.  `deningerHalfDensityLift` is the case
  `c = 1/2`, i.e. `U`.
- `(2)` — `deningerSecondaryDefect`, the centred two-collar defect, built from `U` and reflection.
- `(4)` — `deningerSecondaryDefect_value`: the scalar two-collar coefficient before orbit
  summation, `x^{-1} d_sec(log x) = x^{-1/2}h₊(log x) - x^{-3/2}h₋(-log x)`.
- **`(6)` ⟺ `(7)`** — `deningerSecondaryDefect_eq_zero_iff`: the radical of the defect is exactly
  the reflected Calderón graph.  This identifies `Γ_sec` as **the graph of the collar exchange `J`**
  of the Möbius--Fourier card: `h₊ = J h₋` is literally `h₊(t) = e^{-t}h₋(-t)`, so the two cards
  share one object.
- `(3)` — the full-circle secondary trace is the corpus's `deningerPeriodizationSum` applied to
  `d_sec`; its absolute convergence at every point is `deningerShiftInt_summable`.

### Also done

- **The period-uniform periodization estimate** —
  `formal/GaloisForLFunctions/RHTower/DeningerPeriodizationFundamentalBound.lean`.  On one
  fundamental interval `0 ≤ t ≤ L` the lattice point `t + jL` is at distance at least `(|j|-1)L`
  from the origin (`deningerLatticeDistance_ge`), so the lattice sum is majorised by the geometric
  series `q_{1,0}(h) r^{|j|-1}` with `r = e^{-L}`, whose total is `q_{1,0}(h)(1 + 2/(1-r))`
  (`deningerLatticeMajorant_tsum`).  For every period at least `log 2` this gives
  **`deningerPeriodizationSum_norm_le_period`: `‖Per_L h(t)‖ ≤ 5 q_{1,0}(h)`, uniformly in the
  period.**  The crude estimate, which only uses `|t| ≤ L`, carries a factor `e^{L} = q` and makes
  the all-prime series diverge; this refinement is what makes `(5)` converge.
- **`(5)` finiteness** — `formal/GaloisForLFunctions/RHTower/DeningerAllPrimeFloquetEnergy.lean`:
  `deningerFloquetTerm` is `q^{-2}∫_0^{log q}‖Per_{log q}h‖²`,
  **`deningerFloquetTerm_le`** bounds it by `25 q_{1,0}(h)²(log q)/q²`, and
  `deningerLogDivSq_summable` (comparison with `∑ n^{-3/2}` through `log n ≤ 2√n`) gives
  **`deningerFloquetTerm_summable`**.  `deningerFloquetEnergy` is the sum, with
  `deningerFloquetEnergy_le` the domination `E(h) ≤ 25 q_{1,0}(h)² ∑_q (log q)/q²`.
- **`(5)` continuity** — `formal/GaloisForLFunctions/RHTower/DeningerFloquetEnergyContinuity.lean`:
  periodization is additive and `|‖u‖²-‖v‖²| ≤ ‖u-v‖(‖u‖+‖v‖)`, so
  **`deningerFloquetEnergy_sub_le`** is the Lipschitz estimate
  `|E(h)-E(k)| ≤ 25 C q_{1,0}(h-k)(q_{1,0}(h)+q_{1,0}(k))`, and
  **`deningerFloquetEnergy_continuous`** follows by squeezing.  On the collar pair space,
  `formal/GaloisForLFunctions/RHTower/DeningerSecondaryFloquetContinuity.lean` proves
  `deningerSecondaryDefectSource_seminorm_le` (`q_{1,0}(d_sec) ≤ q_{2,0}(h₊)+q_{2,0}(h₋)` — the
  half-density weight costs half a unit of exponent, the reflection none) and hence
  **`deningerSecondaryFloquetEnergy_continuous`**: `(5)` is continuous on `H_-²`.
- **The `⟸` half of the radical at the level of `(5)`** —
  `formal/GaloisForLFunctions/RHTower/DeningerAllPrimeFloquetRadical.lean`.  Every term is
  nonnegative, so a vanishing energy kills each term; `continuous_eq_zero_of_intervalIntegral_normSq`
  turns a zero integral of a continuous squared norm into pointwise vanishing on the open
  fundamental interval, and continuity plus periodicity spread that to the line
  (`deningerPeriodizationSum_eq_zero_of_floquetTerm`).  Cofinal prime tomography — now formalized on
  the companion card — then gives **`deningerFloquetEnergy_eq_zero_iff`: `E(h) = 0 ↔ h = 0`**.
- **`(6)` ⟺ `(7)` at the level of the energy, and `(8)`** —
  `formal/GaloisForLFunctions/RHTower/DeningerSecondaryFloquetEnergy.lean`.  The defect is the
  half-density lift of `h₊ - J h₋`, hence a source cochain (`deningerSecondaryDefectSource`), so
  **`deningerSecondaryFloquetEnergy_eq_zero_iff`** reads: the all-prime secondary energy vanishes
  exactly on the reflected Calderón graph `h₊ = J h₋`.  Translation invariance of the energy
  (`deningerFloquetEnergy_shift`, from rotation of the orbit plus invariance of the integral of a
  periodic function over one period) together with `deningerSecondaryDefectSource_flow` gives
  **`deningerSecondaryFloquetEnergy_flow`**, which is `(8)`.

## Gates

- [x] 0 → 1 in-progress: exact source map, topology, and falsifiers specified
- [x] 1 → 2 fully-proven: dependency-closed proof `(1)`--`(14)`
- [x] 2 → 3 formalized: `(1)`--`(8)` proved unconditionally, including the all-prime energy `(5)`
  with its finiteness and continuity, its exact radical, and its flow invariance `(8)`.  Axiom audit
  throughout: `propext, Classical.choice, Quot.sound`.  `(9)`--`(14)` are the classification
  statements about the Poisson range; `(14)` remains explicitly open, as the card states.
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-12 — Formalized the all-prime Floquet energy: the period-uniform periodization bound,
  finiteness, continuity on `H_-²`, the exact radical, and contragredient flow invariance.  Card
  moved to stage 3.
- 2026-08-08 — Lifted the existing secondary two-collar coefficient to full prime circles,
  proved continuous all-prime exact radical, and isolated Poisson-range incidence inside the
  reflected graph. Successor Möbius classification identifies that incidence set-theoretically;
  singular Green--Stokes realization remains open.
