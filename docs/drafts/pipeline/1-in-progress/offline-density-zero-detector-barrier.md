# Card — Off-line zeros of density zero (`N_off(T) = o(N(T))`): exact frontier, detector resolution barrier (theorem), open core

Lane owner: kimi. Status: ACTIVE (Stage 1; barrier-theorem track formalized this session).
Created 2026-07-18. One claim per card: this card's claim is the **detector resolution
law** (Theorem B1/B2 below); the parent conjecture AAL is the lane's live conjecture.

## The lane's conjecture

**AAL (almost all zeros on the line).** `N_off(T)/N(T) → 0`, where
`N(T) = #{ρ : 0 < γ ≤ T}` and `N_off(T) = #{ρ : 0 < γ ≤ T, β > 1/2}` (multiplicity counted).
Label: `[CONJECTURE]`. Open since Hardy–Bohr–Landau (1914). Implied by RH; strictly weaker
(RH may fail on `o(N)` zeros).

## Gate 1 — frontier

### Internal corpus
- Corpus banks PRZZ as an external input in two proven cards
  (`bounded-support-weil-critical-tail-uniqueness.md`,
  `horizontal-singleton-zero-fibers.md`): *More than five-twelfths* `[LITERATURE]`.
- Formalized blindness precedents `[CORPUS]`: `measuredIndexZero_const`,
  `measuredIndexZero_dust` (MeasuredIndexBlindness.lean — density-zero off-line sets are
  invisible to the measured index); `wCharge_invisible_below_reflection_depth`
  (DeckChargeLadder.lean — charge-blindness); `reflection_parity_barrier`
  (DeciderBarrier.lean); `stripWindow_parity` (WindowLadder.lean — FE pairing of off-line
  zeros mod 2). The present barrier theorem is the *analytic-scale* member of this family.
- Related prior draft lane: `docs/drafts/rh-monodromy-weight-mismatch/` — weakening of RH
  by multiplicity parity ("off-line zeros have even multiplicity"), different axis
  (multiplicity, not counting). Not duplicated here.
- Failed routes read (5-failed): verified-height-amplification (uses PRZZ simple-zeros
  input), equivalence-transport no-gos (charge-collapse family) — none attack AAL.

### External SOTA (audited 2026-07-18 via arXiv API)
- Record proportion: **PRZZ, Res. Math. Sci. 7 (2020), Art. 2: κ > 5/12 ≈ 0.41666**
  `[LITERATURE]` (NOT "40.88%" — that is Conrey 1989; the user's premise was stale).
- No 2020–2026 paper beats 5/12 for ζ. Pratt–Robles 2018 (Res. Number Theory 4:9):
  Feng-mollifier length θ < 6/11 via Kloosterman sums, slight proportion gain.
- Conrey–Farmer–Kwan–Lin–Turnage-Butterbaugh (arXiv:2508.11108, 2025): calculus-of-
  variations optimization of the Levinson linear combination `G`; positive proportion for
  arbitrarily SHORT mollifiers; >2× previous modular-L proportions. Relevance: removes the
  mollifier-length bottleneck at the short end; the binding constraint for κ → 1 is the
  joint (G, M, θ) main-term ratio.
- Density theorems: Selberg `N(σ,T) ≪ T^{1-(σ-1/2)/4} log T` (uniform); Ingham
  `T^{3(1-σ)/(2-σ)} log^5 T`; Huxley `12/5`; Guth–Maynard 2024 (new large values) improve
  exponents at FIXED σ > 1/2 only — all blind in the shrinking strip (K1 below).
- Littlewood 1924: `Σ_{0<γ≤T} (β-1/2) ≪ T log log T` `[LITERATURE]`.
- "Almost all zeros on the line" is open; the only 100% claims found are retracted/erroneous
  (arXiv:2205.00811 "Not worthy of publication"; arXiv:2605.09282 "serious error in Ch. 4").

### Exact residue neither body settles
The strip `0 < (β-1/2)·log T ≤ w(T)` for `w(T) → ∞`, `w(T) = o(log T)` (mesoscopic regime),
and a fortiori the microscopic regime at proportion level. Every known detector is either
coarser (density theorems, prime-side sums, Littlewood budget) or capped below 1
(Levinson–Conrey proportion method at mollifier length θ < ∞).

## Gate 2 — conjecture (what a Fields medalist asks here)

The conjecture is decided exactly at the horizontal scale `1/log T`. Ask: which detector
classes resolve which horizontal scales? The answer is a theorem (below), and it turns the
"vague barrier" into an exact statement: the resolution boundary of ALL smooth
polynomial-scale detectors is Θ(1/log T); AAL lives at and below it.

## Gate 3 — hostile attack: killing mechanisms (each exact)

- **K1 (density route is blind).** Any bound `N(σ,T) ≪ T^{A(σ)(1-σ)} (log T)^B` with A
  bounded near 1/2 has exponent `1 - Θ(δ)` at `σ = 1/2+δ`; the saving over the trivial
  `T·polylog` is `(log T)^{-Θ(δ log T)}`, which is `≍ 1` unless `δ·log T → ∞`. Hence every
  such bound is blind for `δ·log T = O(w)`. This kills Selberg/Ingham/Huxley/Guth–Maynard
  in the strip. (At `δ = 8 log log T/log T`, Selberg gives `N ≪ T`, i.e. `o(N)` — the FAR
  side of the strip IS controlled; the near side is exactly the open core.)
- **K2 (Littlewood budget is exactly tight).** ε-proportion condensation at the Selberg
  scale `δ ≍ log log T/log T` contributes `Θ(ε T log log T)` to `Σ(β-1/2)`, saturating
  Littlewood's `O(T log log T)`. Any improvement `o(T log log T)` still permits
  ε-proportion at scale `o(log log T/log T)`. No budget argument can contradict
  condensation. (Observation: the classical budget is information-theoretically tight for
  this problem — worth stating; not itself a theorem.)
- **K3 (prime-side/smooth detectors at polynomial cutoff are blind).** Theorem B1 below.
- **K4 (repulsion route empty).** No unconditional horizontal repulsion theorem exists at
  any scale; vertical pair correlation needs RH.
- **K5 (de Bruijn–Newman blind at this scale).** Condensation `δ = o(1/log T)` gives H₀
  zero-pairs within `o(1/log T)` of ℝ; collision time-scale `≍ (δ log γ)² → 0`; Rodgers–Tao
  (Λ ≥ 0) and Polymath15 (Λ ≤ 0.22) are insensitive there.

### Relentless interrogation
K1–K3 kill "average/smooth detection of off-line zeros". The why: detector resolution is
coarser than the zeros' allowed distance. Stronger conjecture passing the why —
decompose SC by scale:
- (i) microscopic part: `κ(T) → 1` (proportion method; wall = mollified-moment ratio at
  θ < ∞; the "1/2 barrier");
- (ii) sub-microscopic exclusion: **HR — off-line zeros cannot condense
  sub-microscopically**: no theorem forbids `δ_j·log γ_j → 0` along off-line zeros.
AAL ⟺ SC ⟺ (i) ∨ (ii)-combined control. Both open; no known tool addresses (ii) at all.
This decomposition `[OPEN CORE]` is the exact frontier.

**Equivalence chain E1 (paper, uses [LITERATURE] Selberg input).**
AAL ⟺ `κ(T) := N₀(T)/N(T) → 1` (definitional: `N = N₀ + N_off`).
AAL ⟺ **SC(w₀)**: `#{0<γ≤T : 0 < (β-1/2)log T ≤ w₀(T)} = o(N(T))` for `w₀(T) = 8 log log T`.
Proof: split `N_off` at `δ = w₀/log T`; the far part is `≪ T·(log T)^{1-w₀/4} = o(N)` by
Selberg; the near part is SC. Monotonicity gives the converse. ∎

## Theorem B1 (detector resolution law) [PAPER-PROVED HERE]

**Statement.** Let `Z(T)` be a family of zero-like multisets with weights
`w_j ≥ 0`, `Σ w_j =: W_T`, containing `m_T` off-line atoms at distances `δ_j(T) ≥ 0`.
Then for every polynomial cutoff scale `L_T = A log T` (fixed `A ≥ 1`):
1. (Lipschitz envelope) the per-atom distortion of any smooth/exponential detector at
   scale `L_T` is `exp(δ_j L_T) - 1 ≤ δ_j L_T · exp(δ_j L_T)`.
2. (Sub-microscopic blindness) if `δ_j(T)·log T → 0` uniformly (e.g.
   `δ_j = c/(w(T) log T)`, `w → ∞`), the TOTAL distortion is
   `≤ W_T·(exp(cA/w(T)) - 1) = o(W_T)`: the condensed family is indistinguishable from
   the on-line family for every detector of this class.
3. (Microscopic sharpness) if `δ_j = c/log T` with `c > 0` fixed, the distortion factor is
   exactly `exp(c) - 1 = Θ(1)`: smooth detectors DO resolve the microscopic scale (this is
   precisely why Levinson's method works and where it lives).

**Proof.** (1) `exp y - 1 ≤ y·exp y` for `y ≥ 0`: from `1 - y ≤ exp(-y)`
(`Real.add_one_le_exp`) multiply by `exp y > 0`: `(1-y)exp y ≤ 1`. (2) sum (1) over atoms,
use uniformity `δ_j L_T ≤ cA/w(T) + o(1) → 0`, `exp` continuous at 0. (3)
`(c/log T)·(A log T) = cA` exactly. ∎

**Content.** The resolution boundary of every smooth polynomial-scale detector is exactly
Θ(1/log T). AAL's open core (SC) is the regime `δ·log T ∈ (0, w(T)]` at proportion level:
the proportion method sees the microscopic end but is capped below 1; everything else is
blind. This is the exact, proved form of the "density-blindness" half of the
two-blindnesses barrier, and the analytic-scale sibling of the corpus's formalized
charge-blindness/dust-blindness theorems. Label: obstruction theorem; novelty vs
folklore: the statement as an exact resolution law with the sharp boundary is not in the
literature in this form `[NOVELTY UNVERIFIED]`; corpus-style analogue of
`measuredIndexZero_dust` `[CORPUS]`.

## Lean artifact (this session)

`formal/GaloisForLFunctions/RHTower/DetectorResolutionBarrier.lean`:
`detectorFactor`, `exp_sub_one_le_mul_exp`, `detectorFactor_nonneg`,
`detectorFactor_microscopic` (exact `exp c - 1` at the natural scale),
`detectorFactor_microscopic_pos` (sharpness), `tendsto_detectorFactor_zero`
(sub-microscopic blindness), `totalDistortion_le_mul_exp` (quantitative n-atom bound).
Unconditional; no ζ machinery needed (pure detector calculus).

## Open core (exact, two-ended)

AAL ⟺ SC(w₀). SC decomposes:
- microscopic: `κ(T) → 1` — needs mollified second-moment asymptotics beyond θ = 1/2 at
  proportion-precision (world wall since Conrey 1989; CFKLT-2025 opens the G-optimization
  end);
- sub-microscopic: HR — no known tool.

## Queue
1. Lean artifact build + umbrella + index (this session).
2. Attempt HR-end: does FE + ξ Hadamard + Jensen/Littlewood give ANY sub-microscopic
   repulsion? (Corpus has LittlewoodXi.lean counting tools.)
3. Attempt (i)-end on paper: joint (G, M) optimization main-term analysis à la CFKLT at
   θ = 1/2 — check whether the analytic (non-numeric) part of the proportion formula can be
   pushed past 5/12 structurally.
