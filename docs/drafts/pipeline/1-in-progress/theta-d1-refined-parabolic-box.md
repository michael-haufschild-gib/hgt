# Literal theta D1: refined parabolic box

[CONJECTURE] [NOVELTY UNVERIFIED]

Let `D(U,B,Q)` be the literal
`HTGeometry.modularThetaSourcePositiveReflectedEighthPolynomial`, with its
source-jet recurrence unchanged. For real `a ≥ 0`, `r² ≤ 19/10`, and `0 ≤ u ≤ 1`, set

`A=899/50+a`, `w=13/32+(19/1600)u`, `U=rw`, `B=r(1-w)/3`,
`Q=(A+6B²-6)/16`.

Claim: `Re D(U,B,Q) > 0`.

## Checked frontier

- `ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone` supplies the
  actual orbit's refined scale and clock bounds on `0<x<137/2000`.
- `ThetaCuspFullReflectionEighthProjectiveSharpThinClockCone` supplies `A<96/5`.
- `ThetaCuspFullReflectionEighthGeneralModularClosure` identifies literal D1 with
  positive mass times this source polynomial. This is the surviving finite sign edge.
- Static Hankel and generic cofinal incidence implications are false; this finite
  sign claim supplies neither a cofinal theorem nor an RH proof architecture.

## Exact outstanding verification

Scratch has a candidate hybrid power/tensor-Bernstein expansion in `(a,t,u)`,
`t=10r²/19`. Lean verifies strict positivity of its remainder-plus-floor polynomial
for all admissible variables. All 25 outer power/Bernstein identities and their
assembly now pass Lean (`evalNestedRat_explicitEvenChartD1_pos`).

Lean also verifies rational-to-complex source identity (`map_ratD1`) at every jet
order and integer normalization (`intJet_eq_scaled_ratJet`,
`intD1_eq_scaled_ratD1`). The box/source polynomial identity and actual-orbit
admission were separate obligations. Actual-orbit admission now passes Lean
(`thetaCuspSourcePositive_mem_realBox`); the source identity remains unverified.
Clean explicit jet normal forms now pass through order eight
(`/tmp/HgtTCDCleanJetForms.lean`, `/tmp/HgtTCDCleanHigherJetForms.lean`).
Earlier derivative-bearing forms were exact identities, not fully reduced
polynomials: numeral derivatives survived simplification. Unfolding `OfNat.ofNat`
before `Derivation.map_natCast` removes that elaboration blow-up.
The full source determinant normal form now passes as well
(`/tmp/HgtTCDDeterminantForm.lean`, `intD1Form.property`), with only standard
axioms. Independent source-side and coefficient-side real evaluation checkpoints
also pass (`/tmp/HgtTCDSourceRealForm.lean`, `/tmp/HgtTCDExplicitRealForm.lean`).
The unverified box-substitution identity is now one real-polynomial equality;
the final literal sign transfer has not been checked.
Gap, radial-clock, and final-box evaluation identities also pass
(`/tmp/HgtTCDParabolicRealForm.lean`, `/tmp/HgtTCDClockRealForm.lean`,
`/tmp/HgtTCDBoxRealForm.lean`, `/tmp/HgtTCDExplicitBoxRealForm.lean`).
These raw forms retain cast-wrapped natural exponents; the final comparison must
remove those wrappers before expanding affine powers. Source/certificate equality
remains unverified.

The positive floor is
`572811477238837689577075217139987617601/83886080000000000000000000000`.

[OPEN CORE] Prove the candidate polynomial equals the unchanged source recurrence,
using the now-verified actual-orbit substitution. Candidate coefficient
data alone is not evidence for the source inequality.

Scratch: `/tmp/hgt_tcd_box_probe.lean`, `/tmp/HgtTCDAllChannels.lean`,
`/tmp/HgtTCDBoxPositivity.lean`, `/tmp/HgtTCDSourceBridge.lean`,
`/tmp/HgtTCDLiteralIdentity.lean`, `/tmp/HgtTCDPhysicalBox.lean`.

## Parent-theory audit

Bernstein positivity is established algebra, not a new mechanism
([Hamadneh–Athanasopoulos–Ali, 2019](https://doi.org/10.1109/JEEIT.2019.8717503)).
[Planat–Solé, 2026](https://arxiv.org/abs/2608.19160) treats second-level concavity,
which the corpus separates from this reflected rank-three determinant by explicit
counterexamples. No priority claim is made for this box inequality.
