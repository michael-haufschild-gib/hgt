# FZZ cubic raw zero-collar cutoff no-go

- **ID:** FZZ-P-CUBIC-RAW-CUTOFF-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · FZZ-P source-fixed full mixed Ward edge
- **Statement:** The physical cubic FZZ raw zero-collar screening integral has no finite collar-removal limit.

## Goal

Retire the raw-source shortcut in the FZZ-P chain:

`raw cubic zero-collar integral -> global neutral Ward -> external-Gamma saturation -> RH`.

## Gates

- [x] 0 → 1 in-progress: literal raw source, exact counterterm, and route chain stated.
- [x] 1 → 2 fully-proven: divergence contradiction below.
- [x] Lean source proof: `RHTower.not_exists_fzzScreeningCubicZero_raw_cutoff_limit` elaborates with `lake env lean`.
- [ ] Final artifact audit: final leaf build and `#print axioms` are deferred because Lake artifact closure is stale and expands beyond permitted audit scope.
- [ ] 3 → 4 publication-ready: route-class obstruction, not an RH proof.

## Proof

The exact collision primitive contributes a correction bounded above by `-36*T`, so its `2π`-multiple tends to `-∞`. The source's exact theorem says raw integral plus this correction tends to the finite local finite part. If the raw integral had a finite limit, subtraction would make the correction converge finitely, contradicting its divergence. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** `not_exists_fzzScreeningCubicZero_raw_cutoff_limit` excludes every proposed finite value for the literal zero-collar integral at the physical cubic charge `(-6,-6)`.
- **Strongest positive survivor:** `fzzScreeningCubicLocalFinitePart` is an exact counterterm-restored finite source object, and the source also provides independently renormalized whole-plane finite-part removal. The theorem does not obstruct either.
- **New insight:** collision renormalization is structural data, not removable scaffolding. Any genuine mixed Ward producer must be a law of the independently renormalized source with both local counterterms retained.
- **Status:** dependency-closed Lean source theorem in `GaloisForLFunctions/RHTower/FZZCigarCubicRawCutoffNoGo.lean`, wired into `RHTower.lean`. It kills only the raw local zero-collar premise; it does not claim a raw whole-plane no-go or rule out the renormalized FZZ-P route.

## Log

- 2026-09-15 — raw cubic zero-collar finite-limit route retired; renormalized mixed-Ward target isolated.
