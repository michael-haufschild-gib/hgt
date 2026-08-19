# Hardy critical-line moment anchor: first unconditional divisor theorem for the corpus

- **ID:** hardy-critical-line-moment-anchor
- **Stage:** 2-fully-proven (paper proof closed 2026-07-18; Lean formalization partial:
  the continuous Hardy-Z substrate is now compiled)
- **Type:** THEOREM (paper) `[PROVED HERE — dependency-closed assembly]`; THEOREM (Lean) pending; `[LITERATURE]` result (Hardy 1914), honestly `not_new_scientific_knowledge`
- **Source:** Hardy 1914; Titchmarsh *Theory of the Riemann Zeta-Function* Ch. 10
  (Thm 10.1: `N_0(T) -> infinity`); Ivić Ch. 11. Corpus substrate:
  `RHTower/SecondMoment.lean` (discrete MV, `abs_cosInt_le`), `RHTower/Mollifier.lean`;
  mathlib `completedRiemannZeta_one_sub`, `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`,
  `Mathlib/NumberTheory/LSeries/ZetaZeros.lean`, `Nonvanishing.lean`.
- **Statement (exact Lean target):** let `N_0(T) :=` number of zeros of `riemannZeta` on
  `{s : ℂ | s.re = 1/2, 0 < s.im ≤ T}`. Then there exist `c > 0`, `T_0` such that
  `∀ T ≥ T_0, N_0(2T) - N_0(T) ≥ 1`, hence `N_0(T) ≥ c * Real.log T` for all large `T`.
  Unconditional; no RH hypothesis anywhere.

## Why this card exists (frontier audit, 2026-07-18)

1. The corpus contains ~72 files of conditional RH gates (all equivalences/implications;
   no unconditional divisor theorem). Every equivalence-web open core is source-side and
   RH-strength (`rh-complete-corpus-dependency-closure.md`; charge-collapse: all faithful
   criteria share `ind_-(J) =` off-line multiplicity, so transports cannot remove charge).
2. Corpus no-gos kill: bounded equivalence transports (charge conservation), finite-rank
   corrections (infinite renormalization rank), scalar Herglotz ratios (cofinal charge
   growth), windowed mollifier detectors (Route B: `V_bd ≥ c₀·loglog N`), sharp carriers
   (Route C: registration gap), verified-height amplification (Route D: reduces to
   enumeration), proportion- blind positivity (extraction log: collapses to dBN).
3. The moment method (Hardy → Selberg → Conrey → Pratt–Robles–Zaharescu–Zeindler) is the
   ONLY known engine producing unconditional constraints on the actual zero divisor. It is
   NOT an equivalence transport: it is an inequality (`|∫Z| < ∫|Z|`), so every corpus
   no-go fails to apply. It has never been attempted in this corpus (searched: no Hardy-Z,
   no zeros-on-line theorem, no moment asymptotics in tree or mathlib).
4. External SOTA (arXiv audit 2024–2026): no new unconditional zero-location engine
   exists; the equivalence criteria published (Arias de Reyna 2024 quasicrystal/tempered
   measure; dynamical contraction criteria) are the same shape as the corpus's web.

## Attack (paper proof = [LITERATURE]; formalization plan exact)

**Refined architecture (2026-07-18, session 2) — supersedes the four-estimate sketch.**
Session-2 derivations eliminated two open cores: (i) the sharp MV theorem is NOT needed —
the second-moment input is split into a lower bound via the AFE diagonal and an upper
bound by Cauchy; (ii) the fourth moment is NOT needed — the crude sup²×second-moment
bound suffices because the mean lemma only needs the crude `O(T^{3/4} log T)` form.
Everything rests on one keystone (symmetric AFE) plus derivative tests.

### Objects and notation

`χ(s) := π^{s−1/2} Γ((1−s)/2)/Γ(s/2)`, so `ζ(s) = χ(s)ζ(1−s)` (mathlib
`completedRiemannZeta_one_sub` in completed form; the χ-factor shape is classical).
On `Re s = 1/2`, `|χ| = 1`; write `χ(1/2+it) = e^{−2iθ(t)}` with θ continuous, real.
`θ'(t) = ½log(t/2π) + O(1/t)`, `θ''(t) = 1/(2t) + O(1/t²)` for `t ≥ 1`
(Stirling for `log Γ` + digamma/trigamma asymptotics; mathlib `Gamma/Digamma.lean`,
`Stirling.lean`). `Z(t) := e^{iθ(t)} ζ(1/2+it) ∈ ℝ` (FE), continuous, and
`Z(t) = 0 ⟺ ζ(1/2+it) = 0`.

### Lemma A (KEYSTONE) — symmetric AFE

For `t ≥ T₀`, `x = y = √(t/2π)`:
```text
ζ(1/2+it) = Σ_{n≤x} n^{−1/2−it} + χ(1/2+it)·Σ_{n≤y} n^{−1/2+it} + E(t),
|E(t)| ≤ C·t^{−1/4} log t.
```
Proof route (classical "reflection principle", Titchmarsh §4.12–4.15): corpus
unconditional E–M AFE (`EMCarrier.zeta_sub_emCarrier_norm_le`) at cutoff `N > x`;
FE converts the tail `Σ_{n>x}` into `χ(s)Σ_{n≤y}n^{s−1}` plus a transition sum
`Σ_{x<n≤N} n^{−1/2}e^{−it log n}` bounded by the van der Corput first-derivative sum
test (`φ(n) = t log n`, `|φ'| ≥ t/N`, Abel summation) — total error `O(t^{−1/4} log t)`.
Sub-lemmas: E–M (corpus ✓), FE (mathlib ✓), Stirling for χ (mathlib ✓),
**van der Corput derivative tests (first and second form) — TO BUILD, elementary,
self-contained, the only new analytic lemma file.**

### Lemma B — convexity sup bound [DROPPED from final chain, session 2]

Not needed: the fourth moment (Lemma F) is proved directly from the AFE, and the
two-term `sup` chain provably cannot close (see session-2 audit trail below).
Retained only as a possible future byproduct (Phragmén–Lindelöf route verified:
mathlib `PhragmenLindelof.lean` + FE + Stirling).

### Lemma C — second moment lower bound `∫_T^{2T}|ζ|² ≥ ½T log T`

From Lemma A (smooth): `ζ = S₁ + χS₂ + E`, `S₁ = Σ_n n^{−1/2−it}V(n/x)`,
`S₂ = Σ_n n^{−1/2+it}W(n/y)`, `|E| ≪ e^{−ct}` so `∫|E|²` negligible. Smooth weights
are real, `|V|,|W| ≤ 1`, `≈ 1` for argument `≤ 1/2`, decaying super-polynomially for
argument `≥ 2`; all sum estimates below are the sharp-cutoff ones with weights only
helping. `∫|ζ|² ≥ ½∫|S₁+χS₂|² − O(∫|E|²)`.
`∫|S₁|²` (and identically `∫|S₂|²`): diagonal `Σ_n n^{−1}V(n/x)²·|{t : x = √(t/2π)}|`
`= T·Σ_{n≤√(T/2π)} n^{−1} + Σ_{√(T/2π)<n≤√(T/π)} n^{−1}(2T−2πn²) = ½T log T − O(T)`;
off-diagonal `≪ Σ_{m≠n}(mn)^{−1/2}/|log(m/n)| ≪ √T·log²T` (crude windowed MV —
corpus `SecondMoment.lean` suffices here because the sum length is `√T`, NOT `T`;
this was the session-2 correction: sharp MV is unneeded at length `√T`).
Cross term `∫S₁χ̄S̄₂ = Σ_{m,n}(mn)^{−1/2}∫e^{i(t log(n/m)−2θ(t))}dt`: second-derivative
test per pair `≤ C√T`, total `≤ C√T·(Σ_{n≤√T}n^{−1/2})² = O(T)`.
Sum: `∫|S₁+χS₂|² = T log T − O(T) ≥ ½T log T` for large `T`. ✓

### Lemma D — second moment upper bound [FOLDED into Lemma F, session 2]

The `O(T log T)` upper bound for `∫|ζ|²` is immediate inside Lemma F's AFE expansion
and is not separately needed by the assembly.

### Lemma E — mean of Z: `∫_T^{2T}Z dt = O(T^{3/4} log T)`

`Z = e^{iθ}ζ = 2Re Σ_n V(n/x)·n^{−1/2}e^{i(θ(t)−t log n)} + O(e^{−ct})` (on the line
`e^{iθ}χS₂ = e^{−iθ}S₂ = conj(e^{iθ}S₁)` when `x = y`, `W = V` real). The smooth
amplitude `V(n/√(t/2π))` has bounded variation `O(1)` on `[T,2T]`, absorbed by the
weighted derivative tests (S3). With `φ_n = θ − t log n`:
`φ_n'(t) = ½log(t/2πn²) + O(1/t)`, `φ_n'' ≍ 1/(2t)`.
- `n ≤ ½√(T/2π)`: `φ' ≥ c > 0` — first-derivative test `≤ C/c`; total `O(T^{1/4})`.
- `½√(T/2π) < n ≤ √(T/π)`: second-derivative test `≤ C√T`; `≍ √T` terms; total
  `O(√T·T^{−1/4}·√T) = O(T^{3/4})`.
- error: `∫|E| = O(T·e^{−cT})`, negligible (smooth route kills the log here).
Total `O(T^{3/4})`. ✓ (No stationary-phase bookkeeping, no `T^{1/4}` lemma.)

### Lemma F — fourth moment `∫_T^{2T}|ζ|⁴ ≪ T log⁴T` (Ingham, elementary form)

From Lemma A (smooth): `|ζ|⁴ ≪ |S₁|⁴ + |S₂|⁴ + |E|⁴`; `∫|E|⁴` negligible.
`S₁² = Σ_{n≤4x²} a_V(n)n^{−1/2−it}` with `a_V(n) = Σ_{d·e=n}V(d/x)V(e/x) ≪ τ(n)`; diagonal
`T·Σ_{n≤x²} τ(n)²/n ≍ T log⁴T` (since `Σ_{n≤X}τ(n)²/n ≍ log⁴X` and `x² = t/2π`);
off-diagonal crude `O(T log⁴T)` — corpus `FourthMoment.lean` /
`FourthMomentDiagonal` machinery (Dirichlet-polynomial fourth moments with divisor
coefficients) is exactly suited; sum length `x² ≍ T` is fine for an upper bound.
Total `∫|ζ|⁴ ≪ T log⁴T`. ✓

### Assembly (the sign change) — final, session-2-corrected

Suppose `Z` has no zero in `[T,2T]`, `T ≥ T₀`. `Z` real continuous ⇒ constant sign ⇒
`|∫Z| = ∫|Z|`. Hölder `∫Z² ≤ (∫|Z|)^{2/3}(∫Z⁴)^{1/3}` gives
```text
∫|Z| ≥ (∫Z²)^{3/2}/(∫Z⁴)^{1/2}
      ≥ (½T log T)^{3/2} / (C T log⁴T)^{1/2}
      = c·T/(log T)^{1/2}        (Lemmas C, F; Z² = |ζ|² on the line)
```
while `|∫Z| = O(T^{3/4})` (Lemma E). Since `T/(log T)^{1/2} ≫ T^{3/4}`,
contradiction. Hence `Z` has a zero in every `[T,2T]`, `T ≥ T₀`; dyadic chaining
`[T,2T],[2T,4T],…` gives `N₀(T) ≥ c·log T`. ∎

**Session-2 audit trail (why this exact architecture):** the two-term chain
`∫|Z| ≥ ∫Z²/sup|Z|` tops out at `T^{3/4−ε}·polylog` and can never beat Lemma E's
`T^{3/4} log T`; the fourth moment is unavoidable at this crudeness level, and the
crude `sup²×second` fourth bound fails by a log — Ingham's `T log⁴T` is the exact
sufficient input. Sharp MV, stationary-phase bookkeeping, log-free RS error, and the
`T^{1/4}` mean lemma are ALL provably unnecessary. Convexity/PL is dropped from the
dependency list. Every input is unconditional and source-pure (Euler product, FE,
E–M, Stirling): no RH, no zero-free region, no density theorem, no computation, no
divisor data fed in.

## Gates

- [x] 0 → 1: well-posed, source-pure, attack mapped, falsifiers known (mean lemma could
  be heavier than sketched; fallback: weaker sign-change window `[T, T+T^{5/6+ε}]` still
  gives `N_0(T) ≥ c·log T` via overlapping windows — check constants in paper-proof phase).
- [ ] 1 → 2: paper proof written out with exact constants, marked `[PROVED HERE]`.
  Session-2 status: architecture CLOSED on paper (Lemmas A–F + assembly, all error
  budgets verified). Remaining for full Gate-4 closure: (i) line-by-line derivation
  of Lemma A (reflection principle: corpus E–M + mathlib FE + derivative tests;
  corpus `SymmetrizedEMCarrier.lean` already carries the χ-symmetrization pattern,
  its error is compact-annulus `O(N^{−σ})` — the t-dependent saddle truncation at
  `x = √(t/2π)` is the new content); (ii) van der Corput first/second-derivative
  tests written out (elementary); (iii) `θ'`,`θ''` asymptotics from mathlib Stirling.
- [ ] 2 → 3: Lean. Ordered build list:
  (a) `VanDerCorput.lean` plus the weighted/second-derivative modules: first/second derivative
  tests **DONE IN THE LIVE CORPUS**;
  (b) `HardyZ.lean`, `HardyZThetaTrace.lean`, and `HardyZSignChange.lean`: `hardyZ` def,
  reality from FE, continuity, zeros ↔ line zeros, exact positive-theta value/sign/zero interfaces,
  the moment-gap-to-actual-zeta-zero Prop consumer, and a finite symmetrized-EM sign certificate
  with explicit pointwise error margins **DONE**. `HardyZPhaseAsymptotic.lean` additionally fixes
  the central orientation, constructs the exact branch-free phase lift, proves
  `zeta(1/2+it)=exp(-i*theta(t))*Z(t)`, and closes the first-order
  `theta'(t)=(1/2)log(t/(2*pi))+o(1)` and
  `theta(t)=(t/2)log(t/(2*pi))-t/2+o(t)` laws **DONE**;
  (c) `SymmetricAFE.lean`: Lemma A (keystone);
  (d) `ZetaSecondMomentLower.lean` / `ZetaFourthMoment.lean`: Lemmas C, F (reuse
  `SecondMoment.lean`, `FourthMomentDiagonal.fourthMoment_bounded` — NOTE its
  `σ > 1/2` hypothesis: the line case needs the limit/perturbation adapter);
  (e) `ZMeanLemma.lean`: Lemma E; (f) `HardyTheorem.lean`: assembly + dyadic
  corollary `N₀(T) ≥ c log T`. Then lint + `#print axioms`.
- [ ] 3 → 4: publication-ready as formalization (novelty: first Lean Hardy theorem;
  honestly `not_new_scientific_knowledge` as mathematics).

## Horizon beyond this card (the lane)

Selberg (positive proportion) → Conrey `2/5` → PRZ 40.88% (external record). The lane's
eventual `[OPEN CORE]` for RH itself: **long mollifiers** — mean values of Dirichlet
polynomials of length `X = T^θ` with `θ` beyond the δ-method barrier (`θ > 1/2`; BCR reach
`1/2+ε` for special coefficients). Farmer: `θ → ∞` gives proportion → 1. Note for the
record: proportion 1 (`N_0(T)/N(T) → 1`) is still strictly weaker than RH (density-blind
to an exceptional set of size `o(T log T)`); even `N_off(T) = o(N(T))` (off-line zeros of
density zero) is OPEN and strictly between density theorems and RH. The moment lane alone
cannot close RH; its role in the corpus is (i) the only unconditional divisor anchor,
(ii) the off-diagonal/shifted-convolution substrate every future one-sided source
estimate needs, (iii) a falsification lab with real external scoreboards.

## Log

- 2026-07-18 — created directly in 1-in-progress after Gate-1 audit of corpus (1636
  RHTower files; ~30 RH chains all source-blocked; charge-collapse no-gos) and external
  arXiv audit (2024–2026: no new unconditional engine). Lane confirmed empty in corpus
  and mathlib.
- 2026-07-18 (session 2) — Gate-3 self-attack rewrote the architecture THREE times:
  (i) sharp MV eliminated (contour trick, then AFE diagonal); (ii) fourth moment
  eliminated then REINSTATED as unavoidable (two-term sup chain loses by `T^ε`, crude
  sup² fourth loses by a log — Ingham `T log⁴T` is the exact sufficient input);
  (iii) mean lemma reduced from `O(T^{1/4+ε})` stationary-phase grade to crude
  `O(T^{3/4} log T)` (first/second-derivative tests only). Final dependency list:
  corpus E–M AFE ✓, corpus crude MV ✓ (length `√T` — the sharp-MV scare was a
  length-`T` artifact), corpus fourth-moment polynomials ✓, mathlib FE/Stirling/
  digamma/residue ✓, **to build: van der Corput tests + symmetric AFE (keystone) +
  Z function + assembly**. Paper proof closes next session; no Lean before that
  (Gate 4). Competitor lanes checked: fable = parity/divisibility cluster,
  gpt = Carleson cancellation — no collision.
- 2026-07-19 — The `HardyZ.lean` substrate is formalized.  A general unitary
  reflection-phase-halving law now covers both `gN` and zeta; the explicit normalized Gamma phase
  gives a globally continuous square root of `zetaChi`, and `hardyZ` has exact zeta-zero, Xi-zero,
  norm-square, continuity, and interval-integrability interfaces.  `HardyZThetaTrace.lean` now
  identifies this same value with the positive theta-cusp cosine trace, including exact sign and
  zeta-zero reflections; `HardyZSignChange.lean` closes a Hardy moment gap into an actual zeta zero
  on the same interval.  The symmetric AFE and moment estimates remain the open analytic core.
- 2026-07-19 — The same substrate now discharges its first-jet interfaces: the normalized Gamma
  phase, zeta line restriction, Hardy Z, continuously oriented finite carriers, and nontrivial
  symmetrized-EM approximants are differentiable.  General phase-halving product-rule and
  even-value-to-odd-derivative laws yield exact derivative reflections and stationary-centre
  corollaries.  This closes regularity bookkeeping for later derivative arguments but does not
  replace the missing height-dependent symmetric AFE.
- 2026-07-19 — Live-corpus reconciliation also discharges the derivative-test item:
  `VanDerCorput.lean`, `VanDerCorputSecond.lean`, and the weighted second-derivative modules already
  provide the required first/second derivative integral bounds.  This is existing corpus support,
  not new work from this card.  The first genuinely missing module in the ordered chain is now the
  height-dependent symmetric AFE.
- 2026-07-19 — The archimedean phase interface is now exact and branch-free:
  `HardyZPhaseAsymptotic.lean` integrates the real normalized-Gamma velocity, proves positivity
  directly at the real central Gamma factors to fix the orientation to one, and identifies the
  resulting exponential phase simultaneously for zeta, `gN`, and symmetrized E--M carriers.  The
  vertical digamma theorem supplies `theta'(t)=(1/2)log(t/(2*pi))+o(1)`, whose general asymptotic
  integration law gives `theta(t)=(t/2)log(t/(2*pi))-t/2+o(t)`, and eventual strict monotonicity.
  The resulting phase is a bijection between terminal rays, so every sufficiently large phase
  level has a unique height.
  A general rotating-frame first-jet law also gives
  `exp(i*theta)z'=A'-i*theta'A` for zeta and every finite reflected carrier; at a zero it identifies
  complex derivative vanishing exactly with real Hardy-amplitude derivative vanishing.
  This closes the value, first-jet, and first-order phase interfaces only; S4's
  quantitative complex digamma and trigamma remainders, S5, and the height-dependent smooth AFE
  remain open.
- 2026-07-25 — The first dependency-closed part of the smooth AFE is now
  formalized in `SmoothAFEGaussianKernel.lean` through
  `SmoothAFEGaussianResidueCrossing.lean`: absolute vertical convergence,
  positive-line contour invariance, removal of the regular part at zero,
  explicit reciprocal limits, and the normalized unit-residue jump. This
  closes the cutoff contour itself, not Lemma A: zeta-series interchange,
  functional-equation reflection, and the uniform Gamma-ratio estimate remain
  open.

## Lemma A derivation route (session-2 FINAL: smooth AFE, never sharpened)

Target (smooth form): for `s = σ+it`, `1/4 ≤ σ ≤ 3/4`, `t ≥ T₀`, `x = y = √(t/2π)`:
```text
ζ(s) = Σ_n n^{−s} V(n/x) + χ(s)·Σ_n n^{s−1} W(n/y) + O(t^{−1/2}),
```
(session-2 verbatim derivation below gives the stronger `O(t^{−1/2})` error).
`V, W` explicit Mellin cutoffs from `G(u) = e^{u²}`: `V(v) = (1/2πi)∫_{(1)}
v^{−w}G(w)w^{−1}dw`, `|V(v)| ≤ C_A v^{−A}` for `v ≥ 1`, `V(v) = 1 + O(v^A)` for
`v ≤ 1`; `W` the dual (`W = V` when `x = y`, `G` even). **The sharp cutoff is never
taken:** session-2 band analysis proved the sharp AFE at the saddle `x = √(t/2π)`
requires Riemann–Siegel-grade band cancellation (`band₁ + χ·band₂ = O(t^{−1/4})`,
each band individually of size `t^{1/4}`) — that is precisely the content to avoid.
Lemmas C/E/F below all run verbatim on smooth weights.

- **Step 1 (smooth AFE, Iwaniec–Kowalski Thm 5.3 method).**
  `A := (1/2πi)∫_{(1)} ζ(s+w) x^w G(w) w^{−1} dw = Σ_n n^{−s} V(n/x)` (absolute
  convergence on `Re w = 1`). Shift to `Re w = −1`: residues `ζ(s)` at `w = 0` and
  `x^{1−s}G(1−s)/(1−s) = O(t^{−1/4})` at `w = 1−s`. On `Re w = −1` apply FE:
  `ζ(s+w) = χ(s+w)ζ(1−s−w)`, `Re(1−s−w) ≥ 3/2` — the dual Dirichlet series
  converges absolutely; expand and use the Stirling ratio
  `χ(s+w)/χ(s) = (t/2π)^{−w}(1 + O(|w|²/t))` (`= y^{−w}x^{w}·x^{-w}`-bookkeeping
  with `xy = t/2π`; the `O(|w|²/t)` remainder costs `O(t^{−1/2})` after `G`'s
  decay). Result: the smooth AFE above, error `O(e^{−ct}) + O(t^{−1/2}) + O(t^{−1/4})`.
- **Step 2 [REMOVED — no sharp-cutoff corollary].**
- **Step 3 (χ on the line).** `[SUBLEMMA S4]` as banked: digamma Weierstrass series
  from mathlib `GammaAux` limit definition; `θ' = ½log(t/2π)+O(1/t)`,
  `θ'' = 1/(2t)+O(1/t²)`; reflection formula verified in mathlib `Gamma/Beta.lean`.

**Sublemma audit (session-2 final):**
- **S3 = {S3a, S3b} only** (integral derivative tests with amplitudes; the SUM test
  is eliminated — no sum test occurs anywhere in the final architecture).
  S3a: `φ' monotone, |φ'| ≥ λ` ⇒ `|∫_a^b A e^{iφ}| ≤ 3(|A(b)| + ∫|A'|)/λ`.
  S3b: `φ'' ≥ μ > 0` ⇒ `|∫_a^b A e^{iφ}| ≤ 8(|A(b)| + ∫|A'|)/√μ`.
  Both by one IBP + monotonicity; elementary; the only new analytic lemma file.
- **S4** (digamma): `ψ(s) = −γ + Σ_{n≥0}(1/(n+1) − 1/(n+s))` from mathlib's
  `GammaAux` limit definition; then `ψ(z) = log z + O(1/|z|)`,
  `ψ'(z) = 1/z + O(1/|z|²)` for `|arg z| < π−δ` by integral comparison
  (termwise: `1/(n+1) − a/(a²+u²)` and `2au/(a²+u²)²` sums vs integrals).
  Gives `θ' = ½ Re ψ(1/4+it/2) − ½log π = ½log(t/2π) + O(1/t)`,
  `θ'' = −½ Im ψ'(1/4+it/2)·... = 1/(2t) + O(1/t²)`. ✓ derivation closed on paper.
- **S5** (Stirling ratio, keystone input): for `w` in a fixed strip, `|τ| ≤ t/2`:
  `χ(s+w)/χ(s) = (t/2π)^{−w}(1 + O((|w|²+1)/t))` — from the
  `π^{s−1/2}Γ((1−s)/2)/Γ(s/2)` form: each `log Γ` ratio is `−(w/2)ψ(·) + O(|w|²/|·|)`
  by S4, the `ψ(1−s)/2)` and `ψ(s/2)` logs telescope to `−w log(t/2π)`, NO spurious
  phase (verified 2026-07-18). ✓ derivation closed on paper.

**Smooth AFE verbatim derivation (session 2, complete).**
`G(w) := e^{w²}`; `V(v) := (1/2πi)∫_{(1)} v^{−w}G(w)w^{−1}dw`:
`V(v) = O(v^{−A})` any `A` for `v ≥ 1` (shift right), `V(v) = 1 + O(v)` for
`v ≤ 1` (shift left, residue 1 at `w = 0`), real on `ℝ₊` (`G` even).
`I := (1/2πi)∫_{(1)} ζ(s+w)x^w G(w)w^{−1}dw = Σ_n n^{−s}V(n/x)` (Fubini absolute).
Shift to `Re w = −1` (strip growth of ζ polynomial from corpus E–M AFE; `e^{−τ²}`
kills horizontals): residues `ζ(s)` at `w = 0`, `x^{1−s}G(1−s)/(1−s)` at `w = 1−s`
(the only crossed poles; `G(1−s) = e^{(1−s)²}` decays `e^{−t²}` ⇒ pole term
`O(x^{1/2}e^{−t²}/t)`, negligible). On `Re w = −1`: FE + absolutely convergent dual
series (`Re(1−s−w) ≥ 5/4`); S5 gives `χ(s+w) = χ(s)(t/2π)^{−w}(1+O(|w|²/t))`;
`(t/2π)^{−w}(xm)^w = (m/y)^w` with `y := t/(2πx)`; the remainder sums to
`O(χ(s)(y/t)Σ_m m^{σ−2}) = O(t^{−1/2})`. Collect:
`ζ(s) = Σ_n n^{−s}V(n/x) + χ(s)Σ_m m^{s−1}W(m/y) + O(t^{−1/2})`, `W = V` (`G` even,
`x = y`). ∎ Gate-4 content of Lemma A is CLOSED (modulo S4a Weierstrass-series
write-out, elementary and mapped).

### S2/S3 subtlety register [SUPERSEDED — smooth route adopted; kept as warning]

The sawtooth/incomplete-gamma route below was abandoned (session 2): its small-end
handling and tail cancellation are the theorem's hidden content and the most
error-prone step to formalize. The smooth contour-shift route (above) eliminates
S1, S2 entirely. Historical notes retained:

1. **Never split the incomplete integral at 0.** `∫_0^X e^{±iv}v^{−s−1}dv` diverges
   (`−s−1 = −3/2−it` at σ=1/2). The contour rotation must keep the
   `Γ(−s) = Γ(1−s)/(−s)` analytic-continuation form and evaluate `∫_x^∞` directly
   against the imaginary-axis contour; the small end is handled by the quarter-arc
   vanishing (`|z^{−s−1}| = |z|^{−3/2}`) plus the Fresnel oscillation, not by a split.
2. **E–M sum↔integral comparison is too lossy for `Σ m^{it}`** (boundary term
   `(t/2)log(b/a)`). The transition sums must use the **second-derivative SUM test**
   `|Σ_{a<m≤b}e^{if(m)}| ≤ C(b−a)√μ + C/√μ`, `μ ≍ t/b²`, giving `O(√t)` for `b ≍ t`,
   then Abel summation for the `m^{-1/2}` weight: transition tail `= O(t^{1/4})`,
   which enters the AFE error only through the Fourier-truncation coefficient
   `O(t^{-1/2})` — total `O(t^{-1/4})` ✓. The dual sum `Σ_{m≤y}m^{s−1}` itself is
   EXACT in the reflection identity, not a truncation.
3. The exact classical template for steps 2–4 is Titchmarsh Thm 4.15.1 (or Ivić
   Thm 4.1): the card's Gate-4 write-out must reproduce its contour bookkeeping
   verbatim-grade, with S1–S4 as the Lean-facing lemma split.


## Log (promotion)

- 2026-07-18 — Gate 4 CLOSED. Full derivation chain written: smooth AFE (contour
  shift, error O(t^{−1/2}), better than needed) with S5 Stirling ratio verified;
  S3 = {S3a, S3b} elementary integral tests; S4 digamma series from GammaAux +
  integral comparisons `ψ = log + O(1/|z|)`, `ψ' = 1/z + O(1/|z|²)`; Lemma C
  cross-term improved (cross-phase derivative `≥ c log T`, never stationary);
  assembly constants verified (`cT/(log T)^{1/2}` vs `O(T^{3/4})`, ratio
  `T^{1/4}/(log T)^{1/2} → ∞`); reality of Z verified from FE; IVT gives the zero;
  dyadic gives `N₀(T) ≥ c log T`. All inputs: corpus E–M AFE / crude MV /
  fourth-moment polynomials; mathlib FE / reflection / GammaAux / residue;
  elementary S3/S4/S5. Moved to 2-fully-proven/not_new_scientific_knowledge
  (known theorem; value = first unconditional divisor theorem in the corpus +
  moment-method substrate). Gate 5 (Lean) begins next session.

## Gate 5 progress log (Lean formalization)

- 2026-07-18 (session 3): `RHTower/VanDerCorput.lean` COMPLETE (S3: firstDerivTest,
  secondDerivTest + helpers; clean, no warnings, in umbrella).
- 2026-07-18 (session 3): `RHTower/DigammaSeries.lean` COMPLETE (truncated
  exponential limits; beta integral `B_n(s) = n!/∏_{k≤n}(s+k)` via the
  `of_tendsto` improper FTC; **Euler limit `Γ(s) = lim n!·n^s/∏_{k≤n}(s+k)`** for
  `0 < Re s` via DCT). In umbrella, indexes regenerated.
- Remaining Gate-5 queue (in dependency order): locally-uniform P_n → Γ on
  compact rectangles (for the logDeriv interchange; dominator split at x=1 with
  x^{c−1}/x^{C−1}); ψ-series `ψ = −γ + Σ(1/(k+1) − 1/(s+k))` via
  TendstoLocallyUniformlyOn.deriv + ratio convergence; ψ/ψ' asymptotics from
  limit forms (the real first-order phase-velocity `o(1)` specialization is now complete);
  the Hardy-Z value, phase, and zero substrate is complete;
  SmoothAFE.lean (keystone: Mellin V from G(u)=e^{u²}, contour shift, S5
  Stirling ratio); moment files C/F (corpus MV reuse); ZMeanLemma (E);
  HardyTheorem assembly.

## Gate 5 progress log (continued)

- 2026-07-18 (session 4): `RHTower/DigammaUniform.lean` COMPLETE (locally-uniform
  Euler convergence: `euler_rect_bound` uniform rectangle estimate +
  `tendstoLocallyUniformlyOn_euler`). In umbrella, module build green.
  Gate-5 step 2 closed. Remaining queue: ψ series via logDeriv interchange
  (TendstoLocallyUniformlyOn.deriv + ratio; logDeriv P_n = log n − Σ_{k=0}^n 1/(s+k));
  ψ/ψ' asymptotics (ψ = log + O(1/|z|), ψ' = 1/z + O(1/|z|²)); the weaker real
  first-order Gamma-phase rate and exact Hardy phase lift are complete;
  SmoothAFE.lean (keystone); moments C/F; ZMeanLemma; HardyTheorem assembly.

- 2026-07-20 — `[BRIDGE] [PAPER-PROVED]` Xi/Hardy/source simplicity interface.  Differentiate
  the exact identity `Xi(t) = -hardyZArchScale(t) / 2 * hardyZ(t)`.  At a Hardy zero, the term
  containing the scale derivative vanishes, so
  `Xi'(t) = -hardyZArchScale(t) / 2 * hardyZ'(t)`.  Since the scale is strictly positive, Xi and
  Hardy Z have the same derivative-vanishing predicate there.  Globally on the real axis the
  existing identity `Xi = thetaCuspCosineRepresentation` gives the stronger all-height law
  `Xi'(t) = -2 ∫₀⁺∞ x * thetaCuspFullSource(x) * sin(t*x) dx`.
  There is also an unconditional complex form: every `XiC` zero lies in the open strip on which
  `thetaCuspFourierLaplace = XiC`, so their derivatives agree at every divisor; differentiating
  under the integral identifies that derivative with
  `∫ thetaCuspFourierLaplaceDerivativeIntegrand(alpha,x) dx`.  Consequently global Xi
  simplicity, the Hedenmalm first-quotient value constraint, and nonvanishing of this explicit
  complex source moment at every centered Xi zero are equivalent without RH.  Under RH this
  specializes to nonvanishing of the real sine moment at every real Xi zero.  This is an exact
  source/value bridge and hypothesis discharge, not new scientific knowledge and not evidence for
  RH.  The smooth height-dependent AFE and moment/sign-change estimates remain the analytic open
  core.
  The bridge extends to every order: the `k`-fold removable quotient at its center is the
  factorially normalized `k`-th Xi jet, and dominated differentiation gives that jet as the
  explicit Fourier--Laplace moment with weight `(-i x)^k`.  Hence a centered Xi divisor has
  multiplicity `k` exactly when the source moments of orders `< k` vanish and the order-`k` moment
  is nonzero.  The order-`k` moment and divided-chain value at the reflected point are
  `(-1)^k` times the original values, so functional-equation reflection preserves the exact
  multiplicity.  Schwarz conjugation conjugates every order-`k` moment, and the combined centered
  reflection gives `(-1)^k` times the conjugate.  This is a dependency-closed
  multiplicity/source classification.  On the real centered axis it agrees exactly with the
  existing positive-half cosine-phase derivative integral, so the same first-nonzero-order law
  reads analytic multiplicity from that real hierarchy.  Under RH, the centered support point is
  canonically the complexification of its real part, discharging both the multiplicity-copy witness
  and the caller-supplied real-coordinate equality from this all-order interface.  The one-sided
  theta boundary anti-reflection defect has the same exact first-nonzero-order classification at
  every logarithmic cut: its terminal jet is the nonvanishing cut exponential times the explicit
  order-`m` theta moment.  Thus boundary covariance preserves, but does not constrain,
  multiplicity.  It is still not an RH proof or a source estimate.

## Gate 5 progress log (2026-08-19) — Lemma F and the assembly step are CLOSED

New module `formal/GaloisForLFunctions/RHTower/HardyFourthMomentSignChange.lean` (wired into
`RHTower.lean`, olean built, `#print axioms` clean).  It installs the card's *final* (session-2)
architecture — the Hölder chain — in place of the two-term sup chain that the card itself proved
cannot close.

- `sq_integral_sq_le_integral_abs_mul_integral_abs_cube` — `(∫f²)² ≤ (∫|f|)(∫|f|³)`, from
  Cauchy–Schwarz with `g = √|f|`, `h = |f|√|f|`;
- `sq_integral_abs_cube_le` — `(∫|f|³)² ≤ (∫f²)(∫f⁴)`, from Cauchy–Schwarz with `g = |f|`,
  `h = f²`;
- **`cube_integral_sq_le`** — the interpolation inequality `(∫f²)³ ≤ (∫|f|)²(∫f⁴)`, i.e. exactly
  `∫|f| ≥ (∫f²)^{3/2}/(∫f⁴)^{1/2}`, over an arbitrary measure;
- **`exists_sign_bracket_of_fourth_moment_gap`** — a continuous `f` on `[α,β]` with
  `S ≤ ∫f²`, `∫f⁴ ≤ F` and `(∫f)²·F < S³` must change sign (no sign change ⟹ `∫|f| = |∫f|` ⟹
  contradiction with the interpolation inequality);
- **`exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap`** — the assembly: the three moment
  estimates produce an actual zero of `ζ` on the critical line inside the window, via the existing
  `exists_riemannZeta_line_zero_of_hardyZ_sign_bracket`;
- `hardyZ_pow_four_eq_norm_pow_four` and
  **`exists_integral_hardyZ_pow_four_dyadic_le_polylog`** — **Lemma F**:
  `∫_N^{2N} Z⁴ ≤ C·N·(1+log N)⁴`, unconditional, obtained from the corpus's already-proved
  `exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog`.

Status of the ordered chain after this session:

| Step | State |
|---|---|
| (a) van der Corput derivative tests (S3) | DONE (`VanDerCorput*.lean`) |
| (b) Hardy `Z`, phase, sign change, first jets | DONE (`HardyZ*.lean`) |
| (c) smooth AFE (Lemma A) | largely built (`SmoothAFEZeta*.lean`, `HardyZSmoothAFEReal.lean`) |
| (d) Lemma F — fourth moment | **DONE** (`exists_integral_hardyZ_pow_four_dyadic_le_polylog`) |
| (d') Lemma C — second-moment lower bound `∫Z² ≥ ½T log T` | OPEN |
| (e) Lemma E — `\|∫Z\| = O(T^{3/4})` | OPEN |
| (f) assembly + dyadic `N₀(T) ≥ c log T` | assembly **DONE**; the dyadic corollary waits on (d'), (e) |

## Gate 5 progress log (2026-08-19b) — Lemma C is CLOSED

New module `formal/GaloisForLFunctions/RHTower/ZetaLineFirstMoment.lean` (wired into
`RHTower.lean`, olean built, `#print axioms` clean) proves the second-moment lower bound
unconditionally, by a **first-moment** route rather than the diagonal computation sketched above.

The mechanism: over a dyadic window the Euler–Maclaurin block
`ζ(s) = Σ_{n≤N} n^{-s} + N^{1-s}/(s-1) − s·emTail_N(s)` (corpus `zeta_eq_emCarrier_sub`) has

* constant term `n = 1` contributing exactly the window length `T`;
* higher Dirichlet terms contributing `O(n^{-1/2}/log n)` each, whose sum splits at `M` into
  `4√M/log 2 + 4√N/log M`;
* the explicit continuation term contributing `3√N/(T log N)`, by the corpus oscillation bound
  `norm_integral_mul_exp_le` applied with amplitude `√N/(s−1)` and frequency `log N`;
* the Euler–Maclaurin remainder contributing `(1+4T)T/√N`.

Taking `M = ⌈T⌉₊` and `N = ⌈65536·T²⌉₊` makes all four errors at most `T/16`, so

```text
‖∫_T^{2T} ζ(1/2+it) dt − T‖ ≤ T/4,     hence   |∫_T^{2T} ζ(1/2+it) dt| ≥ 3T/4,
```

and Cauchy–Schwarz against the constant one gives

```text
∫_T^{2T} |ζ(1/2+it)|² dt ≥ (3T/4)² / T = 9T/16 ≥ T/4.
```

Declarations: `norm_integral_cpow_neg_linePt_le`, `sum_rpow_neg_half_le`,
`norm_sum_integral_osc_le`, `norm_integral_linePt_mul_emTail_le`, `norm_integral_emPole_line_le`,
`norm_integral_riemannZeta_line_sub_le`, `sq_norm_integral_riemannZeta_line_le`,
**`exists_le_integral_norm_riemannZeta_line_sq`**, **`exists_le_integral_hardyZ_sq`**.

This is a *stronger-than-needed-in-shape but weaker-in-size* replacement for the displayed
`½T log T`: the assembly consumes `(∫Z)²·F < S³`, and with `F = O(T log⁴T)` and Lemma E's
`O(T^{3/4})` the value `S = T/4` already closes the chain (`T³/64` versus `T^{3/2}·C T log⁴T`).
No diagonal/off-diagonal mean-value theorem is used anywhere.

| Step | State |
|---|---|
| (a) van der Corput derivative tests (S3) | DONE |
| (b) Hardy `Z`, phase, sign change, first jets | DONE |
| (c) smooth AFE (Lemma A) | exact Gaussian form DONE (`hardyZ_eq_two_tsum_smoothAFE_real`) |
| (d) Lemma F — fourth moment | DONE |
| (d') Lemma C — second-moment lower bound | **DONE** (`exists_le_integral_hardyZ_sq`) |
| (e) Lemma E — `\|∫Z\| = o(T/log²T)` | OPEN — the last analytic step |
| (f) assembly + dyadic `N₀(T) ≥ c log T` | assembly DONE; waits on (e) |
