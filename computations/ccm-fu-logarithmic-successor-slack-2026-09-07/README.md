# Logarithmic successor-slack diagnostic

This is numerical research evidence, not a paper proof or a Lean premise.
The frozen question and interpretation rules are in the
[reserve-extension card](../../../1-in-progress/ccm-fu-reserve-extension-induction.md#frozen-logarithmic-successor-slack-test).

For every saved certified state with at least three unused primes, the test
asks whether the logarithmically weighted mean of
`(B-Q_next)^2-4*G_next*D_next` is nonnegative. This would be sufficient to
choose a certified successor, since the existing merger theorem already
bounds each successor's energy by B. The test retains the original budget
and does not demand that energy decrease at every step.

`screen.py` read every state in the existing
[`defect-reserve-reanalysis.json`](../ccm-fu-adaptive-prime-energy-2026-09-06/defect-reserve-reanalysis.json).
It tested all 6659 states in the declared family. There are **645 failures**,
all reachable through certified predecessors. Every failure and every
successor was independently reconstructed from the defining divisor defect,
literal Möbius signs and square-root Abel sum at 80 decimal digits. Every
failed state remained certified and every weighted mean remained below its
negative tolerance. All details are retained in `summary.json`.

The first failure is M=17, P={5,7,11}, reached through {11,7,5}.
Its original energy is approximately 0.362178444601 and its certificate
is 0.352060295807. The mean squared slack is approximately -0.0104190346962,
or -0.0794295835751 after division by the square of the original energy.

| Next prime | Successor certificate | Squared slack |
|---|---:|---:|
| 2 | 0.229968638656 | 0.0403537335196 |
| 3 | 0.373942973298 | -0.00186098025819 |
| 13 | 0.439542759937 | -0.0278053369953 |

Thus a successful next prime exists here despite the negative proposed
average. This is evidence against the frozen averaging step, not against
reserve extension, PE4, SD1 or RH. The weights were not changed after the
result; no larger screen is scheduled.

The actual oriented field at this witness has only coordinates
`h=A_empty`, `a=A_{2}`, `b=A_{3}`, `c=A_{2,3}`, `z=A_{13}`. Numerically,
`h<0` and `0<a<c<b`, `z>0`. Processing 2 leaves transverse coordinate
`b-c>0`; processing 3 creates `a-c<0`. Processing 13 only subtracts from
the already negative head. This identifies the transverse sign change
discarded by indiscriminate logarithmic averaging.

The corresponding paper-algebra comparison retains positive information:
for any such five-coordinate field with `h<=0`, `a,b,c,z>=0`, `c<=b`,
processing 2 contracts the geometric certificate exactly when
`a*sqrt((b-c)^2+z^2)<=b*c`. Both certificates are squares of nonnegative
quantities; cancelling `-h` and squaring gives that equivalence. It does
not assert that the arithmetic field satisfies this comparison at other
cutoffs. No new Lean theorem or completed formal no-go is claimed.

The completed run used eight workers on the specified RunPod host, with
one-thread BLAS and a 60-second foreground deadline; elapsed time was
0.185 seconds. An earlier invocation stopped before writing results because
the host's Python 3.8 lacks `int.bit_count`; replacing it by a population
count compatible with that version changed no test or mathematical formula.
Source generation occurred only for the mandatory independent failure
audits. The initial test reused saved states and regenerated no paths.

Downloaded script and output hashes match the remote copies. `SHA256SUMS`
records both; the reused input hash is
`c6542367707c793fcf00675252e0b67e7bf7786a7a87769971dd4c2bcc944ff5`.
The foreground process exited successfully, and its three remote files and
owned temporary directory were removed successfully. No worker remains owned
by this experiment.

No numerical value enters Lean. The route's missing output is still an
unconditional bound for the complete signed source at every cutoff.
