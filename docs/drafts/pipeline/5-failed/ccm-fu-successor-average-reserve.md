# CCM-FU: arithmetic average of successor envelopes

- **Stage:** 5-failed; analytic counterexample and positive survivor formalized
- **Type:** [NO-GO] for uniform successor averaging; exact selection remains open
- **Parent:** [exact successor extension](../1-in-progress/ccm-fu-exact-successor-extension.md).
- **Goal:** Full signed Abel bound and RH remain open.

## Frozen question

For the literal energy at cutoff M, put B=Q_empty and
Psi(P)=max(Q_P, all Q_(P+q) for available q).
At every proper actual state with Psi(P)<=B, is the arithmetic mean of
Psi(P+p) over all available primes p at most B?

This would imply an admitted successor without selecting a prime first.
The existing least-energy-choice screen does not determine this stronger
average: existence of a good choice allows arbitrarily bad alternatives.
The previously refuted independent half-subset average is a different
distribution over states. No one-step envelope average is assumed in Lean.

The motivation is the actual small-core localization of mixed costs and
the passing exact-extension screen. The question distinguishes whether
the original reserve pays those costs in aggregate, or whether the proof
must discriminate between next primes. It is a derived bridge, not a new
primary conjecture. The stronger claim that the chosen prime contracts
after every alternative is already refuted by the proved cutoff-seven
final increases; no computation will test that predictable claim.

## Frozen experiment and decisions

Read every saved subset state through cutoff32, checking JSON energies
against subset-states.csv at tolerance 1e-12*max(1,B). Regenerate no source
channels for the main screen. For every admitted proper state record the
successor-envelope average and its excess over B. Retain all failures,
all successor choices and envelopes, and the pair attaining each envelope.
Report separately whether a failure lies on the saved deterministic
least-energy path from empty. Do not change the budget or averaging law.

Independently reconstruct every flagged state, every first successor,
and every required second successor from the defining divisor defects and
Abel sums at80 digits; retain all confirmed failure margins. Cache fields
within a cutoff. A failure refutes only this average law, not exact
extension, greedy selection, PE4, or RH. A pass remains finite guidance.
Either outcome directs the next source proof: average mixed-cost control
if it passes, or the exact sign/prime dependence at confirmed failures.

Use only the supplied RunPod host, at most eight workers, one-thread
numerical libraries, and a60-second foreground deadline. Download and
hash script, inputs and output under the computation ledger; remove owned
remote files and workers. No larger repeat screen is planned.

## Outcome

The [completed RunPod experiment](../2-fully-proven/computations/ccm-fu-successor-average-2026-09-07/README.md)
finds 262 failures among 8176 admitted proper states; all are independently
confirmed at 80 digits. None belongs to the stored greedy path. The first
failure, M=22 and P={3,7,11,17,19}, is now certified analytically in Lean.
The only available primes are 2,5,13. The original budget and every
alternative are retained. Exact extension, least-energy selection, PE4,
SD1, the signed Abel bound, and RH remain open.

## Dependency-closed analytic proof

Write K_d for the literal unsigned dilation channel at cutoff 22. Expanding
every source term from 1 through 22, using exact Möbius signs and vanishing
at squareful indices, leaves precisely the following possible fibres:

| Label | Actual coefficient | Analytic enclosure |
|---|---|---|
| empty | a=K_1-K_3-K_7-K_11-K_17-K_19+K_21 | [-0.480,-0.479] |
| {2} | b=-K_2+K_6+K_14 | [0.182,0.183] |
| {5} | c=-K_5+K_15 | [-0.127,-0.126] |
| {2,5} | d=K_10 | [0.202,0.203] |
| {13} | e=-K_13 | [-0.168,-0.167] |

All other fibres vanish by the actual support identity. These intervals
come from rational logarithm-series bounds, a corrected harmonic bound at
64 for Euler's constant, and rational square-root bounds. In particular,
0.577215<=gamma<=0.577216. Each signed interval product retains the complete
Abel sum. The initial energy equals the sum of K_d^2 over
{1,2,3,5,6,7,10,11,13,14,15,17,19,21}, giving 0.550<=B<=0.553.
No numerical experiment or assumed sign supplies any of these inequalities.

The complete energies, before and after the required mergers, are

- Q_P=a^2+b^2+c^2+d^2+e^2.
- Q_(P+2)=(a+b)^2+(c+d)^2+e^2.
- Q_(P+5)=(a+c)^2+(b+d)^2+e^2.
- Q_(P+13)=(a+e)^2+b^2+c^2+d^2.
- Q_(P+2+13)=(a+b+e)^2+(c+d)^2.
- Q_(P+5+13)=(a+c+e)^2+(b+d)^2.

The analytic boxes imply Q_P<=0.546, Q_(P+2)<=0.123,
0.540<=Q_(P+5)<=0.546, and 0.505<=Q_(P+13)<=0.546. Thus
Psi(P)+1/250<=B, and prime 2 is the unique least-energy available choice.
The same boxes give Q_(P+2+13)>=0.219 and Q_(P+5+13)>=0.743.
Each is a term in the appropriate successor envelope. Consequently

`Psi(P+2)+Psi(P+5)+Psi(P+13)>=0.219+2*0.743=1.705`,

whereas `3*B+1/25<=1.699`. Dividing by the exact available-prime count 3
proves that the mean successor envelope is strictly greater than B+1/75.
This is a counterexample to the frozen universal averaging law.

## Strongest positive survivor: persistent sign separation

At this literal source, every 2-free fibre is nonpositive and every
2-containing fibre is nonnegative, including the overlapping {2,5} fibre.
For any other prime q, the exact merger replaces a surviving coordinate
F(R) by F(R)+F(R+q). Both summands have the same membership status for 2,
so the separation survives. Induction gives separation after every finite
set T with 2 not in T; T need not consist of nonoverlapping late primes.

The full energy change upon processing 2 is twice the sum of products of
paired 2-free and 2-containing fibres. Every product is nonpositive.
Therefore, for every such T,

`Q_(P union T + 2)<=Q_(P union T)`.

Taking T={q} bounds every remaining second successor of P+2 by Q_(P+q).
Parent admission bounds those energies by B, while it also bounds Q_(P+2).
Hence Psi(P+2)<=B. The failed average exposes a source-specific choice
with hereditary contraction, not merely one favorable finite comparison.

This positive survivor has a closed paper proof above and a checked Lean
source realization. No universal existence of such a separator is claimed:
the proved cutoff-seven final increases rule out persistent contraction at
every state. General selection must also handle states with positive gains
paid by their available reserve.

## Lean certificate and audit

The new modules are
[DivisorTwentyTwoAnalyticBounds](../../../../formal/GaloisForLFunctions/RHTower/DivisorTwentyTwoAnalyticBounds.lean),
[MobiusDivisorPrimeSeparation](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimeSeparation.lean),
and [MobiusDivisorSuccessorAverageObstruction](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorSuccessorAverageObstruction.lean).
They are wired into RHTower; no umbrella build was run.

Public source capstones in namespace RHTower:

- `mobiusDivisorPrimeSeparated_twentyTwo`.
- `mobiusDivisorSelectionEnergy_twentyTwo_two_persistently_contracts`.
- `mobiusDivisorSuccessorEnvelope_twentyTwo_admitted`.
- `mobiusDivisorSelectionEnergy_twentyTwo_two_unique_minimum`.
- `mobiusDivisorSuccessorEnvelope_twentyTwo_two_admitted`.
- `mobiusDivisorSuccessorEnvelope_twentyTwo_average_exceeds`.
- `not_mobiusDivisorSuccessorEnvelope_average_law`.

All three exact files passed `lake env lean`, with only their needed
oleans emitted. One external scratch audit checked all 13 new public
proof declarations; every dependency list contains only `propext`,
`Classical.choice`, and `Quot.sound`. No old declaration was re-audited.
Generated corpus indexes were refreshed; `scripts/formal_tools.py lint`
passed with existing file-size warnings. Owned scratch files and workers
were cleaned up. Targeted Lake packaging remains pending: the previously observed rebuild
of unrelated prerequisites was not retriggered. This does not constitute
a completed RH proof or a successful `lake build` packaging audit.
