# Clock scale from projective matrix observations

- **ID:** clock-matrix-scale-projective-recovery
- **Stage:** 3-formalized
- **Type:** PROVED / CORPUS BRIDGE
- **Source:** `ConformalClockSpeciesMixing`, `ProjectiveWignerSmithTomography`.
- **Statement:** Full mixed potential matrices determine scale modulo a common scalar
  defect exactly when the known mass matrix is nonscalar; diagonalization is unnecessary.

## Corpus context and conjecture

`ConformalClockSpeciesMixing` correctly proves that an eigenstate potential contrast
must use the eigenvalue mass gap, rather than a diagonal-entry gap in a different basis.
Its title and broad prose claim that species must first be diagonalized. That stronger
interpretation is not implied by the theorem. For complete matrix data P=sM+dI,
the corpus's projective delay normalization removes d directly.

The proposed bridge works for arbitrary complex mass matrices, including nondiagonalizable
ones. It does not assume positive or selfadjoint masses and does not manufacture a
measurement of the full matrix from scalar data. Independent uncalibrated reporter
gains, species-dependent defects and unknown mass matrices are outside the statement.

Corpus searches: `mass mixing traceless potential matrix scale diagonalization` and
exact text searches in the clock/conformal modules. Returned useful source candidates:
`projectiveDelayNormalize_eq_iff_exists_add_scalar`,
`projectiveDelayPanel_eq_iff_exists_add_scalar`, `matrixTracelessPart_add_scalar`.
Coverage snapshot was older than the live generation; semantic coverage unmeasured.
All cited definitions and proof bodies were inspected. No web search or external read.

## Paper proof [PROVED HERE]

Let M be any complex N-by-N matrix with N>=1. Define
J(Q)=Q-Q(last,last)I, the existing projective delay normalization.
Then J(sM+dI)=sJ(M), directly entrywise. Also J(M)=0 iff M is scalar,
by the corpus's exact scalar-fiber classification.

Hence two projective mixed-potential measurements agree iff
(s1-s2)J(M)=0. Over the complex field this is equivalent to s1=s2 or M scalar.
The scalar defects d1,d2 play no role. Thus scale is identifiable from projective
observations iff M is nonscalar, including defective/nondiagonalizable matrices.
If M=cI, every scale can be absorbed by setting d=v-sc for any prescribed scalar
potential vI. This is the sharp ambiguity boundary.

For the symmetric two-channel source M=[[a,b],[b,d]], P=sM-eI, the complete contrast
((a-d)(P00-P11)+4bP01) equals s((a-d)^2+4b^2). The denominator is the squared
mass gap already proved in the corpus. This is a direct reporter-basis formula;
in particular, equal diagonal entries do not obstruct recovery when b is nonzero.

## Plan

- [x] State exact source, observation and counterexample boundary; audit corpus overlap.
- [x] Complete paper proof.
- [x] Formalize projective matrix classification and two-channel contrast.
- [x] Correct only the overbroad prose, preserving existing source theorem statements.
- [x] Direct Lean, axioms, umbrella, index and lint audits.

## Lean audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ConformalClockMatrixRecovery.lean`
contains seven proved theorems. Direct `lake --old env lean` passed, including
the emitted leaf object. Imported `#print axioms` checks for all seven use only
`propext`, `Classical.choice`, and `Quot.sound`. The prose-corrected
`ConformalClockSpeciesMixing.lean` also passed its direct leaf audit.
The new leaf appears exactly once in `HTGeometry.lean`; index regeneration passed
and all seven theorem rows appear in `LEAN_API.md`.

Authoritative global lint was run and failed on eight unrelated unreachable modules:
`RHTower.WeilPaperCovarianceComplementarity`, `RHTower.XiGaussianOneSidedIdentityRH`,
`HTGeometry.ApertureConeCalculus`, `HTGeometry.ApertureConeWinding`,
`HTGeometry.ApertureLogTranslation`, `HTGeometry.ApertureOpenHistoryIdeal`,
`HTGeometry.BoundaryCoronaCStarAlgebra`, and `HTGeometry.OneSidedLaplaceAtomRigidity`.
No proof-debt or reachability error was reported for this leaf. Unrelated work was
left untouched; no full or umbrella build was run.

## Assessment

This is a new connection between existing corpus interfaces, not a claim of external
scientific novelty. It removes a procedural diagonalization requirement for full
matrix observations, while retaining the actual nonscalar-mass condition.

## Next conjecture exposed by the bridge

Allow M=M(x) to vary with position and scale s to be continuous. The projective
matrix observation determines s at x exactly on the closure of
{y : M(y) is nonscalar}. Thus pointwise mass degeneracy need not obstruct continuous
recovery: a collision locus with empty interior is harmless for uniqueness, though
division by the local spectral gap is undefined at collisions and unstable nearby.

Paper mechanism: the algebraic classification forces competing scales to agree on
the nonscalar locus; continuity extends agreement to its closure. Outside it, a
continuous separator changes scale while supported entirely where every projective
mass observation vanishes. This combines the two completed interfaces rather than
adding a probe-existence hypothesis. This conjecture is now proved in
`ConformalClockContinuousMatrixRecovery.lean`; see the formalized card
`clock-continuous-mass-collision-recovery.md`.
