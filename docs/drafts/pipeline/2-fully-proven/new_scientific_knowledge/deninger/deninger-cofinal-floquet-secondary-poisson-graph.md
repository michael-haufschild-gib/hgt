# Cofinal Floquet lift of the secondary Poisson graph

- **ID:** `deninger-cofinal-floquet-secondary-poisson-graph`
- **Stage:** 2-fully-proven
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

### Not yet formalized

- `(5)`: finiteness and continuity of the all-prime energy `∑_q q^{-2}∫_0^{L_q}|S_q|²`.  The
  pointwise convergence of each `S_q` is proved; what is missing is the uniform-in-`q` periodization
  estimate and the `L²` integral over the fundamental interval.
- The `⟸` half of the radical computation at the level of `(5)`: that vanishing of the *energy*
  forces every prime periodization to vanish needs the cofinal tomography injectivity, which is the
  companion card `deninger-cofinal-prime-periodization-tomography-instability`.
- `(8)` invariance of the energy under the contragredient flow (the defect's translation covariance
  is elementary once `(5)` exists).

## Gates

- [x] 0 → 1 in-progress: exact source map, topology, and falsifiers specified
- [x] 1 → 2 fully-proven: dependency-closed proof `(1)`--`(14)`
- [ ] 2 → 3 formalized: `(1)`, `(2)`, `(3)`, `(4)` and the radical computation `(6)`⟺`(7)`
  proved unconditionally; the all-prime energy `(5)`, its flow invariance `(8)`, and the tomography
  input remain (see *Lean status*)
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-08 — Lifted the existing secondary two-collar coefficient to full prime circles,
  proved continuous all-prime exact radical, and isolated Poisson-range incidence inside the
  reflected graph. Successor Möbius classification identifies that incidence set-theoretically;
  singular Green--Stokes realization remains open.
