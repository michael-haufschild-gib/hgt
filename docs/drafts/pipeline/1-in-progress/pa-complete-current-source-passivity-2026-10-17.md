# PA — complete current source passivity

- **ID:** PA-complete-current-source-passivity-2026-10-17
- **Stage:** 1-in-progress
- **Type:** ROUTE
- **Source:** Read-only current frontier, PA; current local Lean corpus.
- **Statement:** Remove a hard obstruction in the complete prime–archimedean source current while preserving its sign and arithmetic origin.

## Goal

A substantive unconditional source theorem, beyond improved bounds, another RH receiver, or an operator encoding of the same unknown sign. No contribution claimed.

## Plan

1. Inspect the complete current, source continuation, operator domain, and known sign obstructions.
2. Conjecture, attack, and paper-prove a substantive survivor before formalization.
3. Verify exact declarations and axioms; directly compile final source modules, wire any additions, and clean owned scratch.

## Constraints

No web, numerical experiments, novelty audit, old research Markdown, frontier edits, extra axioms, or unproved analytic premises. One owned foreground Lean process at a time; preserve concurrent work. No full or umbrella builds.

## Conjecture ledger

1. Complete-current domain/admission: rejected as rediscovery. Existing bounded self-adjoint multiplication, uniform exponential cutoff convergence, and compact-correction rigidity already discharge formation while retaining the unknown sign.
2. Positive theta/log-concavity or first-atom Ward floors: insufficient; existing Gaussian–Hermite source-mass-calibrated countermodel has negative size-three Hankel determinant despite these properties.
3. Positive raw Stokes completion: already excluded by exact zeroth/first moments; positive supercarriers and physical diagonal transfers retaining a residual floor are already excluded. Two-jet signed correction is already constructed. No credit.
4. **Critical Stokes pole-capacity obstruction — proved.** Gelfond–Schneider separates every critical prime/depth gap. The exact raw residue `I(p,e)=log(p) p^(-(e+1)/2)` is below one; injectivity gives raw singleton mass below `2x` at every positive node. Xi reflection requires at least `2x` at every thermal atom. Existing moment-carrier rigidity therefore rules out *arbitrary passive deletion*, without a residual floor. The stronger positive survivor forces infinitely many strict atom-mass increases in any exact positive completion, excludes finite atom repairs, and combines with the existing supercarrier obstruction to require both added and removed mass. No new analytic-continuation premise or integer-residue theorem was needed. Exact theorem and closure: `../5-failed/pa-critical-stokes-passive-deletion-2026-10-17.md`. No qualifying RH-route contribution claimed.

Three documented deep searches completed with `partial=false`, no errors, and no proof ideas. Index refresh remained incomplete because the background indexer was running; compiler coverage mostly pending/source-only. Exact source reads and `rg` supply the present evidence, not search certification.

## No-go closure

PA remains live. Extract positive survivors before retiring any mechanism; existing theorems receive no new credit.

### Paper proof: arbitrary passive deletion obstruction

Use only existing source definitions and unconditional theorems. Write `r_p=p^(-1/2)`, `c_p` for the critical Gamma contraction, `g_(p,e)=(e+1)W_p`, `x_(p,e)=g_(p,e)^(-2)`, and `w_(p,e)=2b_(p,e)/g_(p,e)`.

1. `r_p^2=1/p` and `c_p^4=(1+r_p)^4/(8(1+r_p^4))`; hence both are nonzero algebraic numbers. The exact inverse-tilt identity gives `W_p=a_p log p`, where `a_p=(1+r_p^2)/(r_p c_p(1-r_p))>0` is algebraic.
2. Equal gaps for different primes would make `log q/log p` algebraic, contrary to the corpus's unconditional Gelfond–Schneider theorem. At one prime, positive `W_p` separates depths. Squaring reciprocals of positive gaps preserves injectivity.
3. The exact edge-current identity gives `b_(p,e)g_(p,e)=I_(p,e)=log(p) r_p^(e+1)`. Since `0<r_p<1`, this is at most `log(p)r_p`. For `t=log(p)/2>0`, `exp(t) >= 1+t+t^2/2 > 2t`; therefore `0<I_(p,e)<1`. Thus `0<w_(p,e)=2I_(p,e)x_(p,e)<2x_(p,e)`.
4. The raw countable measure has singleton mass exactly `w_(p,e)` at each of its injective nodes and zero elsewhere. Consequently its mass at every `x>0` is strictly less than `2x`.
5. The canonical Xi thermal measure has mass at least `2x` at every one of its thermal nodes: a zero copy and its distinct functional-equation reflection have the same reciprocal-square node and each contributes mass `x`. This uses only the functional equation and nonvanishing at the center, not RH. Taking any enumerated node proves the canonical measure is not dominated by the raw Stokes measure.
6. Existing unrestricted moment-carrier rigidity identifies every complete positive prime–archimedean moment witness with that canonical measure. Hence no such witness can be obtained by arbitrary deletion/downweighting of the critical Stokes carrier. Local compact Markov germ equality supplies its moments by the already-proved derivative identity; no analytic continuation or new tail argument is assumed.
7. The enumerated positive thermal nodes tend to zero by summability. Their range cannot be finite: a finite range is closed and would then contain its limit zero, contradicting positivity. Thus the strict raw-mass deficit occurs at infinitely many distinct nodes. Every exact positive moment witness must increase infinitely many singleton masses; a correction changing only finitely many singleton masses is impossible. This is the stronger positive survivor exposed by the proof, with its dependency-closed paper argument recorded before promotion.

Positive survivor to formalize: the exact injective arithmetic pole structure and strict singleton-capacity obstruction, together with the forced amplification alternative at every shared Xi/Stokes node. Combined with the existing supercarrier obstruction, exact positive completion requires a correction with both added and removed mass. No claim that this closes PA or qualifies as the requested RH contribution.

## Verification

New module: `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalPoleCapacity.lean` (388 lines, 25 declarations including one private helper). Initial direct module check passed. All 25 declarations in the exact final source passed a `/tmp` axiom audit, without warnings/errors or heartbeat changes; only `propext`, `Classical.choice`, `Quot.sound`. Source SHA-256: `87ad1d53741960a2ebdeee44b462a9778f680002c2ade1ae2c0d5b1afb2d0cb3`.

Added one umbrella import, corrected the old passive-deletion module's obsolete pending-producer description, and regenerated formal indexes. `scripts/formal_tools.py lint --check-generated` exited 1: 381 existing large-file warnings, two unrelated unwired modules (`RHTower.WeilLineIntegralAnyAbscissa`, `HTGeometry.CayleyDenseResolvent`), and `formal/LEAN_API.md` drift during concurrent source changes. Both unrelated modules are untracked work not authored here. Indexes refreshed again after the lint run; no global lint pass claimed. No full/umbrella build.

Final direct check: `lake --old env lean GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalPoleCapacity.lean` from `formal/`, exit 0 with no diagnostics. Nine owned scratch files removed and absence verified. All owned research, index, lint, and Lean handles exited.

## Log

- 2026-10-17 — Selected previously unworked PA; documented corpus search launched.
- 2026-10-17 — Closed the arbitrary passive-deletion mechanism with its exact positive survivor. PA's high-frequency current sign remains unresolved. Qualifying cross-route progress remains 2/44 (PM, SZ); this no-go is not counted as removal of PA's central proof obstruction.
