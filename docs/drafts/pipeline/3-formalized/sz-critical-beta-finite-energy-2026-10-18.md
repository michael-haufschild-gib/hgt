# SZ: critical Beta atom and finite-energy first variation

- **ID:** sz-critical-beta-finite-energy-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** literal `suzukiPrimaryBetaKernel`; parent card `sz-critical-source-first-variation-2026-10-18`.
- **Statement:** The literal critical primary Suzuki density has an exact Gamma-ratio mass and a positive-shift first variation on the bounded finite-Levy-energy domain.

## Goal

Supply the primary Gamma-atom and singular-remainder limit needed by the SZ route.
The result uses the actual source kernel and the same Levy weight as BiScale.
The full pole convolution, arithmetic-cusp estimate, complete-source limit, and
Weil positivity remain separate obligations. RH remains open.

## Exact theorem

For `w>0`, define the literal log-coordinate primary density

`B_w(t) = pi^w exp(-t/2) Re(suzukiPrimaryBetaKernel w (exp(-t)))`.

Its mass, for `w<5/2`, is

`M_w = pi^w Gamma(5/4-w/2) / Gamma(5/4+w/2)`.

Let `C` be real and almost-everywhere strongly measurable on the positive ray.
Assume `|C(t)| <= C(0)` almost everywhere and integrability on the positive ray of

`t -> (C(0)-C(t)) * 2 exp(-t/2)/(1-exp(-2t))`.

Then, as `w -> 0+`,

`(integral C(t) B_w(t) dt - C(0))/w`
`-> (log pi - Re(psi(5/4))) C(0)`
`   - integral (C(0)-C(t)) * 2 exp(-5t/2)/(1-exp(-2t)) dt`.

No smoothness, compact-support, innerness, or zeta-zero hypothesis is assumed.

## Paper proof — [PROVED HERE]

1. Substitute `x=exp(-t)` in the existing primary Mellin transform at `s=1/2`.
   The convergence condition is `w<5/2`. Complex powers have positive real bases,
   so the primary density is real and positive on the positive ray. This gives
   both its integrability and the exact mass `M_w`.
2. The Gamma functional equation gives, for `t>0`,
   `B_w(t)/w = [pi^w/Gamma(1+w)] * 2 exp(-(5/2-w)t) (1-exp(-2t))^w /(1-exp(-2t))`.
   For `0<w<=2` this is at most
   `[pi^w/Gamma(1+w)] * 2 exp(-t/2)/(1-exp(-2t))`.
3. The bracketed coefficient tends to one. The density divided by `w` tends
   pointwise to `K(t)=2 exp(-5t/2)/(1-exp(-2t))`. With `D(t)=C(0)-C(t)>=0`, the
   assumed finite Levy energy dominates `D(t) B_w(t)/w` for all sufficiently
   small positive shifts. Dominated convergence gives its integral limit.
4. Gamma differentiation gives `M_0=1` and
   `M'_0=log pi-Re(psi(5/4))`. Boundedness of `C` permits the exact splitting
   `integral C B_w = C(0) M_w - integral D B_w`. Subtract `C(0)`, divide by `w`,
   and combine the two limits.

The atom and remainder are both retained. The shifted density `K` differs from
the full BiScale Levy weight by exactly `2 exp(-t/2)`; the parent proof accounts
for that term together with the source's pole convolution.

## Gates and verification

- [x] Source-pure target and prior corpus search.
- [x] Dependency-closed paper proof, including the stronger measurable finite-energy domain.
- [x] Canonical leaf compilation.
- [x] Axiom audit of all 19 public declarations.
- [x] Umbrella wiring.
- [x] Index refreshed; generated files current at final lint.
- [ ] Repository lint: blocked by three unrelated unreachable BiScale modules.

Canonical source: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalBetaKernel.lean`.
Capstone: `RHTower.tendsto_suzukiCriticalPrimaryPairing_firstVariation`.
Audit script: `/tmp/hgt_sz_beta_axioms.lean`.

Canonical compile: `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalBetaKernel.olean -i .lake/build/lib/lean/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalBetaKernel.ilean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalBetaKernel.lean` — exit 0.
One informational ring tactic suggestion; no compiler error or linter warning.
All 19 public declarations use only `[propext, Classical.choice, Quot.sound]`.
Source SHA256: `09a74d61dd9c1dfa54a20b0ded5995d2cb1356520cd919bc3ba4c45791ff08da`.
Logs: `/tmp/hgt-sz-beta-final.log`, `/tmp/hgt-sz-beta-axioms.log`.
Manifest: `/tmp/hgt-sz-beta-audit-manifest.json`.

`scripts/formal_tools.py index` passed. Final
`scripts/formal_tools.py lint --check-generated` exited 1 solely for unreachable
`FactorialMuntzBoundaryRepair`,
`StationaryResolventMarkovPositivityAndNodalDefectProducer`, and
`TwoLagArithmeticCone` in the BiScale umbrella. No forbidden-declaration,
generated-file, or new-module error remains. Logs:
`/tmp/hgt-sz-final-index.log`, `/tmp/hgt-sz-final-lint.log`.

## Corpus and rotation audit

Direct source search found no prior shift-zero theorem for the literal primary
kernel. Its other references are the defining Mellin module and the arithmetic
module's measurability argument. Retrieved real-Beta asymptotics concern spatial
endpoints at a fixed shift. No external novelty claim is made.

Substantive rotation: RW → TH → MSC → RB → SZ. Next fresh cycle should include a
route candidate. The larger complete-source paper theorem stays on its own card.

## Log

- 2026-10-18 — paper proof, canonical compilation, and complete axiom audit passed.
- 2026-10-18 — umbrella wired and index refreshed; unrelated global lint blockers recorded.
