# Resolved test completeness law

- **ID:** resolved-test-completeness
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** current `HTGeometry` and `RHTower` theorem surfaces
- **Statement:** After quotienting the declared nuisance sector, algebraic recovery is separation by the joint test family, completed recovery is uniform separation, and a proper closed bi-dense invisible defect exists for two injective dense-range Hilbert legs exactly when both legs fail uniform separation.

## Goal

Replace the manuscript's collage of conservation statements by one positive law with three exact
levels: quotient separation, coefficient/ordered tomography, and stable completion.  For the RH
application this separates the already-solved source/tomography problem from the unsolved singular
Gamma-boundary test.

## Gates

- [x] 0 → 1  in-progress: well-posed internal synthesis and exact corpus witnesses
- [ ] 1 → 2  fully-proven: dependency-closed abstract theorem and shadow table
- [ ] 2 → 3  formalized: one Lean capstone assembling the existing component theorems
- [ ] 3 → 4  publication-ready: standalone theorem replaces current resolved-descent headline

## Exact candidate law

Let (E) be a normed source, (N\subset E) a closed declared nuisance sector, and
(A=(A_i)_{i\in I}) a joint family of linear tests which vanishes on (N).  Write
(\bar A:E/N\to\prod_iF_i) for the induced analysis map.

1. **Algebraic completeness:** observations determine the source modulo (N) exactly when
   (\ker A=N).
2. **Topological completeness:** observations determine completed source data stably exactly when
   (\bar A) is bounded below in the chosen analysis norm.
3. **Sharp two-leg singularity:** for injective dense-range bounded maps
   (P:G\to H_1), (Q:G\to H_2) between complex Hilbert spaces, a proper closed subspace
   (M\subsetneq G) with both (P(M)) and (Q(M)) dense exists exactly when neither (P) nor
   (Q) is bounded below.  A codimension-one orthogonal hyperplane suffices.
4. **Repair criterion:** an added singular test (S) repairs completion precisely when the joint
   analysis ((P,Q,S)) is bounded below on the resolved quotient; nonflatness or injectivity of
   (S) alone is insufficient.

Items 1, 2, and 4 are direct quotient/analysis-map facts.  Item 3 is the nontrivial sharp component,
already proved as `RHTower.twoSidedSingular_iff_hasProperClosedBiDenseSubspace` in
`formal/GaloisForLFunctions/RHTower/PreQuasiGelfandTwoSidedSingularDefect.lean`.

## Corpus shadows

- Maurer–Cartan normalization identifies the nuisance sector exactly: constant jets are the kernel,
  and quotient by them is the based-jet group.
- Bohr means recover every coefficient of an absolutely summable separated-frequency packet.
- Ramsey quadratures plus mixed pulse derivatives recover every ordered noncommutative correlation,
  including for regular bounded pulses with unbounded generators on a common invariant domain.
- Root-of-unity packets recover residue classes and make differential algebraicity descend through
  finite power covers; rational-power hypertranscendence is therefore retained.
- Airy diagonal-loop rigidity is recursive completeness: first deviation fixes the sign, so zero
  loop forces every local balance law.
- Infinite Kronecker averaging, Deninger power amplification, and Bessel factorial escape are three
  asymptotic coefficient-isolation mechanisms.
- The pre-quasi theorem is the completion boundary: injectivity and dense range do not prevent an
  invisible closed defect when uniform separation fails on both legs.

## RH open core

Current source, based-jet quotient, regular coefficient tomography, ordered tomography, and Xi
Green landing do not supply the needed repair test.  Exact missing object is a source-derived
singular Gamma/co-Poisson Stokes test (S_\Gamma) whose joint analysis with the existing source legs
is bounded below in the resolved graph topology and whose value on the Xi Green germ retains the
reflection-odd outer charge.  An arbitrary nonflat curvature, bounded transport, positive form, or
regular exponential carrier does not meet this criterion.

## Hostile status

- **Internal verdict:** `SURVIVES PRELIMINARY ATTACK` as a corpus synthesis; components pass direct
  Lean checks and key capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
- **External novelty:** `[NOVELTY UNVERIFIED]`; intentionally deferred under current instruction.
- **Open proof obligation:** assemble items 1–4 as one exact theorem and prove the shadow maps without
  importing RH-specific conclusions.

## Log

- 2026-08-03 — created in Stage 1 after live-corpus re-audit.
