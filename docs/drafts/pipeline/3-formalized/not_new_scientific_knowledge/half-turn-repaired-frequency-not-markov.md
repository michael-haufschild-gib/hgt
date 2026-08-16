# Half-Turn Repaired Frequency Is Not Markov

- **ID:** half-turn-repaired-frequency-not-markov
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Grade:** BRIDGE / guardrail. Door-2 reduces the proof to a `2 x 2`
  determinant calculation.
- **Source:** `seam-parity-correction-is-nonlocal-half-turn.md`;
  `single-even-frequency-not-stieltjes.md`;
  `positive-source-weights-require-pointwise-hankel-kernels.md`
- **Statement:** The nonlocal half-turn supplies the missing coefficient parity
  for an FE-even frequency, but it still does not make that frequency a
  Markov/Stieltjes source. The first shifted Hankel determinant remains negative.

## Setup

Let `B>0`, `lambda>0`, and

`L(z)=B(cosh(lambda sqrt(z))-1)`.

The half-turn parity repair is

`L^H(z)=-L(-z)`.

If

`L(z)=sum_{k>=1} a_k z^k`, with `a_k=B lambda^(2k)/(2k)!`,

then

`[z^k]L^H(z)=(-1)^(k+1)a_k`.

Define the shifted seam moments after repair by

`U_k=-2k(-1)^k [z^k]L^H(z)`.

Thus

`U_k=2k a_k=B lambda^(2k)/(2k-1)!`.

In particular,

`U_1=B lambda^2`,

`U_2=B lambda^4/6`,

`U_3=B lambda^6/120`.

## Theorem

The first shifted Hankel determinant is strictly negative:

`U_1 U_3 - U_2^2 = -7 B^2 lambda^8 / 360 < 0`.

Consequently the half-turn repaired single frequency is not a
Markov/Stieltjes moment source on `R_+`.

## Proof

The coefficient computation above gives the three displayed moments. Hence

`U_1 U_3 - U_2^2
 = (B lambda^2)(B lambda^6/120) - (B lambda^4/6)^2
 = -7 B^2 lambda^8/360`.

Since `B>0` and `lambda>0`, the right side is strictly negative. A positive
Markov/Stieltjes moment sequence has every shifted Hankel square test
nonnegative, so this repaired frequency is not Markov.

## Consequence For The Half-Turn Route

`seam-parity-correction-is-nonlocal-half-turn.md` identifies the half-turn as
the nonlocal operator that finite-order local corrections cannot supply. This
card shows that supplying that parity is still not enough.

The obstruction after the half-turn is no longer coefficient sign. It is the
factorial Hankel geometry:

`m_k=lambda^(2k)/(2k-1)!`

has a negative first shifted determinant.

Therefore a source proof cannot proceed as:

1. decompose the Euler/Gamma source into positive FE-even real-frequency atoms;
2. apply the nonlocal half-turn to fix coefficient parity;
3. sum the repaired atoms with positive weights;
4. infer Markov/Stieltjes positivity.

Step 3 would be a positive-weight sum of pointwise indefinite kernels. By
`positive-source-weights-require-pointwise-hankel-kernels.md`, such a proof
cannot work uniformly over positive source weights.

## Boundary

This theorem does not rule out a special positive mixture of repaired
frequencies, an infinite/nonlocal transform beyond the half-turn, multiplicative
correlations between frequencies, or a completed boundary/index construction.
It only proves that parity repair alone is not the completed interaction.

## Theatre Test

For any proof invoking the half-turn:

1. Does it only fix the alternating coefficient sign?
2. Does it then treat each repaired FE-even frequency as a positive Markov
   source?
3. If yes, the `2 x 2` determinant above is negative.
4. What source interaction changes the factorial Hankel geometry, rather than
   only the parity?

## Novelty Status

The determinant is elementary. The significance is route control: the half-turn
is necessary for coefficient parity in the diagonal model, but it is not
sufficient for Markov positivity.

## Gates

- [x] 0 -> 1 in-progress: half-turn sufficiency loophole isolated.
- [x] 1 -> 2 fully-proven: determinant proof written.
- [x] formal core: determinant identity and strict negativity proved as
  `GaloisForLFunctions.singleEvenFrequency_halfTurn_det_identity` and
  `GaloisForLFunctions.singleEvenFrequency_halfTurn_det_neg`.

## Log

- 2026-06-24 -- Codex: created after the nonlocal half-turn routing theorem to
  prevent parity repair from being mistaken for Markov positivity.

## 2026-06-24 bounded packet extension

`bounded-half-turn-frequency-packets-fail-hankel.md` extends the obstruction from one repaired frequency to finite positive repaired packets whose squared-frequency support has ratio strictly below `(17+2 sqrt(70))/3`. The half-turn route therefore needs broad cross-scale interaction before it can pass even the first shifted Hankel gate.

## Lean formalization

Modules (namespace `GaloisForLFunctions`), both wired into the
`GaloisForLFunctions.HTGeometry` umbrella:

- `formal/GaloisForLFunctions/HTGeometry/SingleEvenFrequency.lean`
- `formal/GaloisForLFunctions/HTGeometry/EvenFrequencySeamMoments.lean`

| Paper statement | Lean declaration |
|---|---|
| the `z^k` coefficient `B lambda^(2k)/(2k)!` | `evenFrequencyCoeff` |
| the shifted seam moment `T_k = -2k(-1)^k [z^k]L` | `seamMoment` |
| `(2k)! = 2k (2k-1)!` | `factorial_two_mul_eq` |
| closed form `T_k = (-1)^(k+1) M_k/(2k-1)!` | `seamMoment_factorialCoeff`, `seamMoment_evenFrequency` |
| `T_1 = B lambda^2`, `T_2 = -B lambda^4/6`, `T_3 = B lambda^6/120` | `seamMoment_evenFrequency_one`, `_two`, `_three` |
| `det [[T_1,T_2],[T_2,T_3]] = -7 B^2 lambda^8/360 < 0` | `singleEvenFrequency_det_identity`, `singleEvenFrequency_det_neg`, `seamMoment_evenFrequency_det_neg` |
| the half-turn parity repair and `U_k = 2k a_k` | `halfTurnCoeff`, `seamMoment_halfTurn`, `seamMoment_halfTurn_evenFrequency` |
| `U_1 U_3 - U_2^2 = -7 B^2 lambda^8/360 < 0` | `singleEvenFrequency_halfTurn_det_identity`, `singleEvenFrequency_halfTurn_det_neg`, `seamMoment_halfTurn_det_neg` |
| alternating signs of a positive germ | `seamMoment_pos_of_odd`, `seamMoment_neg_of_even`, `seamMoment_neg_of_odd_of_neg` |
| positive frequency measure has positive even moments | `integral_pow_pos_of_measure_pos` |
| `T_2(mu) < 0` for a nonzero positive frequency measure | `seamMoment_measureCone_two_neg` |
| finite positive mixture `T_2 < 0` | `positiveEvenFrequencyCone_T2_neg` |
| dominant-frequency tail sign of a finite signed atom sum | `tendsto_signedFrequencySum_div`, `eventually_signedFrequencySum_pos`, `eventually_signedFrequencySum_neg` |
| infinitely many negative shifted moments for a signed atom sum | `exists_seamMoment_neg_of_signedFrequency` |
| the sharp two-frequency half-turn threshold `(17 ± 2 sqrt 70)/3` | `halfTurnUpperThreshold`, `twoFrequency_halfTurn_balanced_det_threshold_sharp` |

Audit: direct `lake env lean` check clean, targeted module builds clean, umbrella imports wired,
`#print axioms` on every declaration above returns only `propext`, `Classical.choice`, `Quot.sound`.
