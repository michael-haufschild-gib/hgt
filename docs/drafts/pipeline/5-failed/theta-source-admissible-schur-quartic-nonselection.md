# Theta-source admissible Schur quartic nonselection

- **ID:** `theta-source-admissible-schur-quartic-nonselection`
- **Stage:** 5-failed
- **Type:** NO-GO + POSITIVE SURVIVOR
- **Route:** GTA (`ORIENT` source-selection audit)
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Goal

Decide whether current four-field theta approximation specification can force new Schur quartic
charge to vanish. If not, extract exact positive obstruction and replacement selection law.

## Gates

- [x] 0 → 1 in-progress: source specification, bad-stage corpus theorem, charge, and falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed generic Schur/divisor classification and source no-go
- [x] 2 → 3 formalized: exact Lean theorem, targeted builds, lint, and axiom audit
- [x] 3 → 5 failed: current-spec selector branch retired; positive survivor preserved in Lean

## Parent corpus

- `[LEAN-PROVED]` Every approximation accuracy fibre contains a finite-support, traceless,
  Hilbert--Schmidt-close stage with a nonreal ordinary Fredholm divisor.
- `[LEAN-PROVED]` Finite-packet positive quartic charge is nonnegative and strictly positive exactly
  when its packet contains a nonreal node.
- `[LEAN-PROVED]` Every finite matrix admits Schur triangulation.

## Frozen conjecture

For a finite matrix `M` and any unitary Schur triangularization `Uᴴ M U=T`, define

`Q(T)=Σ_i 100(Im T_ii)²(6(Re T_ii)²+23(Im T_ii)²)`.

Then:

1. `Q(T)=0` iff every zero of `det(1-zM)` is real.
2. If `det(1-zM)=0` for some nonreal `z`, then `Q(T)>0` for every Schur triangularization.
3. At every theta approximation accuracy `k`, there exists an admissible source stage `SK` with a
   nonreal divisor such that every Schur packet of `blockMatrix SK.2 SK.1` has strictly positive
   quartic charge.

Therefore current `ThetaSourceSignedApproximationProperty` cannot imply quartic-charge vanishing.
Any surviving GTA construction must add a selection rule that excludes positive charge inside each
approximation fibre.

## Hostile attacks

- Zero Schur diagonal entries: they generate no finite determinant zero and have zero charge.
- Repeated eigenvalues and arbitrary Schur ordering.
- Non-normal matrices: use triangular determinant product only.
- Nonreal determinant variable is reciprocal to a nonzero Schur diagonal node; check imaginary-part
  inversion in both directions.
- No claim that fixed `Classical.choice` stage is bad; theorem concerns specification fibre.

## Dependency-closed proof

Fix Schur data `U,T` for `M`. Packet faithfulness gives `Q(T)=0` iff every `T_ii` is real.
Schur triangularity gives

`det(1-zM)=Π_i(1-zT_ii)`.

If every `T_ii` is real and the product vanishes, one factor vanishes. That diagonal entry is
nonzero, and taking imaginary parts of `1-zT_ii=0` forces `Im z=0`.

Conversely, suppose every determinant zero is real. For each nonzero `T_ii`, the reciprocal
`z=T_ii⁻¹` zeros the corresponding factor and hence the determinant. Therefore `Im(T_ii⁻¹)=0`.
The identity `Im(w⁻¹)=-Im(w)/normSq(w)` and `normSq(T_ii)≠0` force `Im T_ii=0`.
Zero diagonal entries are already real. This proves the generic iff.

If a nonreal determinant zero exists, generic iff forbids zero charge. Nonnegativity then makes
charge strictly positive, for every Schur packet. Existing source-specific nonselection supplies,
at each accuracy `k`, an admissible `SK` and nonreal `z` with
`det(1-z blockMatrix(SK))=0`. Applying the generic strict theorem to an arbitrary Schur packet of
that block matrix proves positive charge throughout the bad-stage Schur fibre.

## Novelty audit

- Corpus has source-specific spectral nonselection and new packet charge separately, but no theorem
  identifying positive charge as exact obstruction throughout every admissible bad-stage Schur fibre.
- Current exact arXiv searches found no matching positive quartic Schur/divisor classification.
  Priority remains unverified.

## Open core

`[OPEN CORE]` Construct an additional arithmetic selector, not implied by the current four-field
approximation property, that chooses zero-charge stages from the admissible fibres.

## Positive survivor

`[LEAN-PROVED]` For every finite complex matrix and every Schur packet, quartic charge vanishes
exactly when its ordinary Fredholm divisor is real; any nonreal divisor zero forces strictly
positive charge for every Schur packet. At each theta-source accuracy, an admissible stage exists
whose every Schur packet has strictly positive charge. This is the exact selection boundary.

## Log

- 2026-08-27 — opened after corpus refuted derivation of global charge vanishing from current stage specification.
- 2026-08-27 — dependency-closed generic Schur/divisor classification and source-fibre no-go proved;
  generic scratch Lean passed.
- 2026-08-27 — generic classifier formalized in
  `FiniteMatrixSchurPositiveQuarticDivisorCharge`; source-fibre theorem formalized in
  `HedenmalmThetaAdmissibleSchurQuarticNonselection`. Both wired; targeted builds, formal lint,
  and axiom audit passed. Current-spec selector branch retired with positive survivor preserved.
