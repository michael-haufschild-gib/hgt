# CHMD full-source arithmetic tail selection (2026-10-16)

Persistent unconditional RH goal remains ACTIVE and unbounded. Re-read the goal attachment each new goal turn:
`/Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt`.
Corpus-only research; no web, old research Markdown, novelty audits, numerical experiments, subagents, full builds or heartbeat increases. One owned Lean process at a time.

## Completed contribution
Conjecture tested: literal positive full Doob jump source preserves spatial order, enabling a first-mode shortcut to primitive positivity.
Result: upper-set rate monotonicity fails unconditionally, already at n = 2.
Positive survivor: exact infinite arithmetic tail-selection/recovery law for the COMPLETE original source, including the full archimedean integral and all original Mangoldt atoms.

Let Θ = thetaCuspFullSource = riemannKernelReal, ω = archLevyDensity, a_n = vonMangoldtAtom n.
Literal source rate for x < b:
R(x,b) = [∫_{t>b-x} ω(t)Θ(x+t)dt + Σ_n 1_{b≤x+log n}a_nΘ(x+log n)] / cosh(x/2).
This is defined directly using CHMDDoobGraph.archWeight / massDensity and primeWeight / massDensity. Separate exact cancellation and closed-arch-endpoint identity. For x≥1, full arch integral is integrable and full prime series summable. Backward edges cannot reach b.

For all integer m≥2:
cosh(x/2)R(x,x+log m)/Θ(x+log m) → a_m.
For 0<h<log m-log(m-1):
cosh(x/2)R(x+h,x+log m)/Θ(x+log m) → 0.
If a_m>0, eventually R(x+h,x+log m)<R(x,x+log m).
Unconditional existential witness uses m=2, h=log2/2, 1≤x<y<b.
No semigroup theorem, negative quadratic direction, primitive gap, cosh domination or RH proof is asserted.

## New leaves, namespace RHTower.CHMDTail
1. formal/GaloisForLFunctions/RHTower/CHMDPrimeTailSelection.lean
230 lines, 19 declarations.
SHA256 8599c3afeec8bd27f47ca1a49db40f235ee69859bf2735a23671d15e678f920c
Key results: primeTail_selects_first127, primeTail_advanced_vanishes154, archTail_vanishes214.
Helper defs: envelopeRatio, primeTailTerm, primeTail, archTail.
Proof: existing theta envelope gives uniform normalized prime bound K*m²*|Λn|/n²; existing summability plus Tannery. Arch normalized integrand ≤K*ω on (s,∞), pointwise strict theta ratio→0; filter dominated convergence.

2. formal/GaloisForLFunctions/RHTower/CHMDJumpTailOrderObstruction.lean
238 lines, 21 declarations.
SHA256 08e2e5f7d946287a0c88e86ac1702be83b2eee10fc04032e668c275f0c10bc31
upwardRate literal graph-density definition36.
upwardRate_eq_closed40.
integrable_upward_arch75, summable_upward_primes82.
upwardRate_selects_first158, upwardRate_advanced_vanishes166.
exists_rate_order_reversal223, not_upper_rate_monotone232.
Both leaves wired exactly once into RHTower.lean. Preserve concurrent edits.

## Validation
- Both lake --old build leaf commands exit0.
- Both FINAL PLAIN lake env lean <leaf> audits exit0, empty output.
- Separate /tmp probe checked 34 source/mathlib names with have := @Name, exit0.
- ALL40 declarations #print axioms audited via /tmp, only propext/Classical.choice/Quot.sound.
- Index exit0.
- GLOBAL LINT EXIT1 solely for unrelated concurrent unwired module:
  GaloisForLFunctions.RHTower.PaperThetaCutMeyerCurrent.
  File was untracked, not created/modified by this task; no CHMD lint error. Do not claim global lint passed.
- Scoped whitespace and exact-once imports passed.
- All13 owned scratch files removed; absence verified. All owned processes terminal. NO live owned process.

## Persistence
Paper/positive card:
docs/drafts/pipeline/3-formalized/chmd-full-jump-tail-selection-2026-10-16.md
Failed subroute and strongest positive salvage:
docs/drafts/pipeline/5-failed/chmd-spatial-order-preservation-2026-10-16.md
Main work card appended proof, implementation, hashes, audits, lint exception, cleanup:
docs/drafts/pipeline/1-in-progress/chmd-convolution-defect-elimination-2026-10-15.md

## Lean lessons
Use IntegrableOn in simp-only when converting an Integrable result to IntegrableOn; without explicit unfolding Lean emitted apparent identical-type mismatch.
Include id_eq when simplifying shifted filter compositions.
ArithmeticFunction.vonMangoldt_nonneg has implicit n; use (n:=n), not positional n or (R:=ℝ).
WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi is namespaced.
thetaCuspFullSource_eq_riemannKernelReal needs XiSliceHusimiHeatDictionary import.
Generic name probes need explicit universe zeros.
Redirect leaf-build output: many cached dependency warnings replay (~100k tokens) despite --old. This does not mean umbrella build.
Serena ignores Lean paths; use rg/apply_patch fallback. update_plan unavailable; plan lives in main card.

## Next frontier
Primitive-sector cosh domination remains open. Complete signed graph, exact prime-chain variance decomposition, and arithmetic tail obstruction all retain original source. Do not redo these producers or replace the gap with another RH equivalence. Spatial-order preservation is now ruled out at source-rate level. Continue corpus-driven structural conjectures that survive prime threshold reversals.
