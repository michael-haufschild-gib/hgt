# Finite Schur quartic quadratic trace-energy defect

- **ID:** GTA-PQ4-QD
- **Stage:** 5-failed
- **Type:** FALSIFIED (producer); THEOREM (Lean) positive survivor
- **Source:** `rh-current-frontier-map.md` · route GTA (`ORIENT`)
- **Statement:** The quadratic defect `HS² − Re tr(M²)` splits exactly into Schur nonnormal energy plus twice transverse spectral energy and quantitatively dominates positive quartic charge, but its vanishing is not necessary for real spectrum.

## Goal
Test whether a root-free quadratic source observable can force the GTA quartic selector.  Close the
route if it conflates nonnormality with transverse orientation, retaining the sharp quantitative
survivor.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: exact module/build and axiom audit green; repository lint blocked by unrelated unwired module
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Schur transport gives

`HS²(M) − Re tr(M²) = (HS²(M) − Σ|λᵢ|²) + 2 Σ(Im λᵢ)²`.

The first summand is nonnegative Schur off-diagonal energy.  Since local quartic charge is at most
`2300 |λ|² (Im λ)²` and every `|λ|² ≤ HS²(M)`, total charge is at most
`1150 HS²(M)` times the transverse quadratic energy, hence at most the same factor times the full
trace-energy defect.  A nilpotent Jordan block has zero quartic charge but positive full defect,
testing necessity sharply.

## Theorem and proof `[PROVED HERE]`
Let `M` be a finite complex matrix and `S` any unitary Schur packet with diagonal entries
`λᵢ = S.T i i`.  Define

`D₂(M) := HS²(M) − Re tr(M²)`,

`N(S) := HS²(M) − Σᵢ |λᵢ|²`, and `T₂(S) := 2 Σᵢ (Im λᵢ)²`.  Then

1. `D₂(M) = N(S) + T₂(S)`;
2. `N(S), T₂(S), D₂(M) ≥ 0`;
3. `Q₄(S) ≤ 1150 HS²(M) T₂(S) ≤ 1150 HS²(M) D₂(M)`;
4. there is a matrix with `Q₄(S)=0` and `D₂(M)=1`.

For (1), Schur similarity and triangular trace powers give
`Re tr(M²) = Σᵢ Re(λᵢ²) = Σᵢ(|λᵢ|² − 2(Im λᵢ)²)`.  Rearrangement proves the split.
Schur orthogonality gives `Σᵢ|λᵢ|² ≤ HS²(M)`, proving (2).  Pointwise quartic control gives
`q₄(λᵢ) ≤ 2300 |λᵢ|²(Im λᵢ)²`; since every `|λᵢ|² ≤ HS²(M)`, summation proves (3).
For (4), take the upper nilpotent Jordan block `[[0,1],[0,0]]`.  Its Schur diagonal is zero,
so `Q₄=0`, while its Hilbert--Schmidt energy is one and its square is zero, so `D₂=1`.

## Conjecturing loop
- `[GTA-PQ4-QD.1]` Full quadratic trace-energy defect decay might be an arithmetic producer for
  quartic decay. Scratch proof confirms sufficiency.
- `[GTA-PQ4-QD.2]` Exact Schur decomposition exposes an additional nonnormal summand.
- `[GTA-PQ4-QD.3]` Nilpotent real-spectrum Jordan block has zero charge and defect one; full defect
  decay is strictly stronger than spectral reality. Positive survivor is the sharp decomposition
  and charge bound.

## No-go closure
- **Exact killing theorem/mechanism:** quadratic defect also measures Schur nonnormality, which can
  remain positive when every eigenvalue is real.
- **Strongest positive survivor:** exact two-term decomposition and dimension-free inequality
  `charge ≤ 1150·HS²·quadraticDefect`.
- **New insight:** a successful quadratic producer must isolate transverse spectral energy from
  nonnormal Schur energy; raw `HS² − Re tr(M²)` cannot do so.
- **Status:** positive survivor dependency-closed and formalized.  Producer retired: vanishing or decay
  of full quadratic defect is not an exact spectral-reality criterion.

## Novelty audit (2026-08-27)
- Corpus searches: `Hilbert Schmidt energy minus real trace square Schur offdiagonal imaginary
  eigenvalues defect theta source`, `quadratic trace energy defect`, and exact theorem-name searches.
  No prior corpus theorem states the combined split or quartic bound.
- Literature searches included exact/formula searches for Schur/Frobenius departure, `Re tr(A²)`,
  imaginary spectral mass, and quartic imaginary-eigenvalue inequalities.
- The summand `HS²(M) − Σ|λᵢ|²` is classical: Henrici's Frobenius departure from normality squared;
  see P. Henrici, *Numerische Mathematik* 4 (1962), 24--40,
  <https://doi.org/10.1007/BF01386294>.  Therefore this component is not novel.
- No exact source was found for the combined decomposition interpreted as transverse spectral energy,
  or for `Q₄ ≤ 1150 HS²·D₂`.  This is absence-of-hit evidence, not priority proof.
- **Verdict:** `UNVERIFIED` novelty for the positive quartic inequality; producer no-go and Henrici
  component are not claimed novel.

## Lean certificate
- Module:
  `GaloisForLFunctions.HTGeometry.FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect`
- Exact direct check: `lake env lean
  GaloisForLFunctions/HTGeometry/FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect.lean` — pass.
- Exact module build: `lake build
  GaloisForLFunctions.HTGeometry.FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect` — pass.
- `#print axioms` for endpoint theorems: `[propext, Classical.choice, Quot.sound]` only.
- Wired into `GaloisForLFunctions.HTGeometry` umbrella.  No full build run.
- Global formal lint remains blocked only by concurrently introduced unwired module
  `GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution`; this card does not import
  or wire that module.

## Log
- 2026-08-27 — frozen after corpus search; `.1 → .2 → .3` scratch loop closed.
- 2026-08-27 — tree module, exact build, axiom audit, positive-survivor paper proof, and literature
  audit completed.  Producer retired with Lean-certified survivor.
