# FZZ integer-genus replica-tangent interpolation no-go

- **ID:** fzz-integer-genus-replica-tangent
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · FZZ-P analytic continuation of full higher-genus amplitudes/moduli
- **Statement:** Entire continuations agreeing at every integer genus realize every genus-zero derivative; Schwarz-real continuations realize every real derivative.

## Goal

Kill
`integer-genus sine-Liouville amplitudes + entireness/Schwarz reality → canonical genus-zero replica tangent → divisor-mode passivity → RH`.

## Gates

- [x] 0 → 1 in-progress: source-pure, exact chain, attack identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build, axioms/lint audit
- [ ] 3 → 4 publication-ready

## Approach

For entire `F` and target `v`, set
`Fᵥ(g)=F(g)+(v-F′(0)) sin(πg)/π`.
Then `Fᵥ(n)=F(n)` for all `n∈ℕ` and `Fᵥ′(0)=v`. If `F` is Schwarz-real and `v∈ℝ`, its derivative at zero and the deformation coefficient are real, so `Fᵥ` remains Schwarz-real.

## Proof `[PROVED HERE]`

`sin(πn)=0` for every `n∈ℕ`, so `Fᵥ(n)=F(n)`. Since `(sin(πg))'|_{g=0}=π≠0`, differentiation gives `Fᵥ′(0)=F′(0)+(v-F′(0))=v`. Sums and scalar multiples of entire functions are entire. If `F(conj g)=conj F(g)`, differentiation at real `g=0` makes `F′(0)` real; for real `v`, the coefficient is real and `sin(πg)` is Schwarz-real. Thus the Schwarz-real interpolation fibre realizes every real tangent.

Hostile checks: value and normalization at genus zero are preserved; all integer genera are preserved. A strict Carlson-type growth bound may exclude the type-`π` sine direction, and a moduli recursion may fix off-lattice data; neither is supplied by the source paper, so both remain explicit survivor hypotheses rather than counterexamples.

## No-go closure

- **Exact killing theorem/mechanism:** Integer-genus restriction has a sine-null direction whose derivative at zero is nonzero; the tangent map on every entire interpolation fibre is surjective.
- **Strongest positive survivor:** Uniqueness requires a source-derived condition excluding the type-`π` sine direction: strict sampling growth, off-lattice moduli data, or a genus recursion/localization law.
- **New insight:** Bare analytic continuation cannot even determine tangent sign, not merely full continuation.
- **Status:** Lean formalized and umbrella-wired. Mori--Sakai--Shigemori (2026) asks for genus continuation but supplies no growth or uniqueness law.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityIntegerGenusReplicaTangentInterpolationNoGo`
- Capstone: `RHTower.fzzCigarParity_integerGenusReplicaTangentInterpolation_noGo`
- Direct `lake env lean`: PASS
- Targeted build: `9139/9139` PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Lint: new module clean/reachable; global failure only pre-existing unrelated unreachable modules.

## Log

- 2026-09-02 — conjecture frozen after corpus and primary-source audit; hostile testing begun.
- 2026-09-02 — hostile tests passed; `[PROVED HERE]`; moved to 2-fully-proven.
- 2026-09-02 — Lean capstone, targeted build, axioms, reachability passed; moved to 3-formalized.
