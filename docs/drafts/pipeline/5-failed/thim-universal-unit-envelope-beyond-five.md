# Universal unit envelope beyond ratio five

- **ID:** thim-universal-unit-envelope-beyond-five
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Retired claim:** For some fixed real C>5, every horizon N and endpoint
  2≤k≤C N satisfy |s_N(μ,k)|≤1, or the analogous statement uniformly over
  c_ε(d)=μ(d)d^(-ε), ε≥0.
- **Status:** Disproved symbolically and in Lean. The broader research goal remains active.

## Obstruction

For each prime p>5, take N=6p−1 and k=30p. Then k=5N+5 and s_N(μ,k)=2.
The complete divisor sum vanishes, while the omitted complementary quotients
are exactly 1,2,3,5. Their coefficient signs are +1,−1,−1,−1, so the truncated
response equals two. The response persists at every positive power of k.
Unbounded primes give arbitrarily large horizons and k/N tending to five from
above. Hence every fixed ratio C>5 fails. Uniform damping fails already at ε=0.

Killing theorems in
`formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FourthBandEnvelopeAndSharpFiveHorizonBoundary.lean`:

- `sieveSeq_moebiusReal_five_horizon_counterfamily`
- `sieveSeq_moebiusReal_five_horizon_counterfamily_pow`
- `exists_ge_five_horizon_counterexample`
- `forall_moebiusReal_unit_envelope_iff_ratio_le_five`
- `forall_pmPowerDamped_unit_envelope_iff_ratio_le_five`

## Strongest positive survivor

The exact universal real-ratio classification is C≤5. For every ε≥0,
2≤k≤5N implies |s_N(c_ε,k)|≤1. The new fourth band uses squarefree absorption
when 4 divides k and one-/two-prime deletion contractions otherwise. This is
a dependency-closed paper proof, fully formalized in the same leaf.

All positive powers of certified bases, and every endpoint with horizon radical
R_N(k)≤5N, inherit this envelope. Certified prefixes and rough-start short
windows satisfy the stronger energy inequality 2D≤−E≤0. These are unbounded
families of checkpoints, even though the base interval has a sharp linear ratio.

The exact insight exposed by the obstruction is that three distinct small-prime
deletions can reinforce the truncated Möbius response, whereas the fourth-band
dyadic case compresses into the already controlled range. Classification:
New formulation; no external novelty claim.

## Verification and surviving questions

Actual source passed `lake --old env lean` without warnings. All 23 public
theorems and four private helpers have exactly the axiom closure
`{propext, Classical.choice, Quot.sound}`. Source SHA256:
`a2f410080f37a6a7ed41ceab6f42a20f532041dc23ce1f661137142393a3fec0`.
See `logs/thim-five-audit.json` and the positive-result card
`docs/drafts/pipeline/3-formalized/thim-fourth-band-sharp-five-boundary.md`
for integration, lint limitations, and complete verification evidence.

This does not disprove renormalized-defect nonpositivity beyond 5N: energy may
still dominate the larger endpoint response. It also does not classify each
fixed positive damping exponent. The additive conjecture is now resolved by
`ExactAdditiveEnvelopeAndFirstFailure.lean`: the envelope holds through 5N+4,
and the existing counterfamily is the first violation at each of its horizons.
The universal real buffer b after 5N is admissible iff b<5 (natural b iff b≤4).
Thus any proposed universal additive buffer at least five is also retired,
with the exact four-step envelope and its radical/power energy certificates as
the positive survivor. See
`docs/drafts/pipeline/3-formalized/thim-exact-additive-five-boundary.md`
and `logs/thim-additive-audit.json` for the new verification package.
