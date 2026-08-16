# Finite Signed Even Frequency Atoms Are Not Markov

- **ID:** finite-signed-even-frequency-atoms-not-markov
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Grade:** BRIDGE / guardrail. Door-2 reduces the proof to finite
  exponential-sum dominance, so this is not a native theorem. Its use is to
  exclude a false source-transfer shape.
- **Source:** `positive-even-frequency-cone-not-markov.md`;
  `source-selector-repair-obligation-ledger.md`;
  `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** A nonzero finite signed sum of real FE-even exponential
  frequency germs cannot produce a Markov/Stieltjes moment sequence in the
  seam-square coordinate. Its shifted moments are negative on infinitely many
  indices.

## Setup

Let `n>=1`, and let

`0 < lambda_1 < ... < lambda_n`

and let `c_1,...,c_n` be real coefficients with `c_n != 0`. Equal frequencies
are first combined, so the displayed top coefficient is nonzero. Define

`L(z)=sum_{j=1}^n c_j (cosh(lambda_j sqrt(z))-1)`.

For `k>=1`, define the shifted seam moments

`T_k=-2k(-1)^k [z^k]L(z)`.

Set `x_j=lambda_j^2`.

## Theorem

If the signed frequency sum is nonzero, then there are infinitely many `k` for
which

`T_k < 0`.

Consequently `(T_k)_{k>=1}` is not the moment sequence of a positive Borel
measure on `R_+`. In particular, the finite signed real FE-even frequency atom
span intersects the Markov/Stieltjes target only at zero.

## Proof

The coefficient calculation gives

`[z^k]L(z)=sum_{j=1}^n c_j lambda_j^(2k)/(2k)!`

and hence

`T_k = (-1)^(k+1) (sum_{j=1}^n c_j x_j^k)/(2k-1)!`.

Let

`S_k=sum_{j=1}^n c_j x_j^k`.

Since `0 < x_1 < ... < x_n`,

`S_k / x_n^k = c_n + sum_{j<n} c_j (x_j/x_n)^k -> c_n`.

Thus, for all sufficiently large `k`, `S_k` has the sign of `c_n`.

If `c_n>0`, then for every sufficiently large even `k`,

`T_k = - S_k/(2k-1)! < 0`.

If `c_n<0`, then for every sufficiently large odd `k`,

`T_k = S_k/(2k-1)! < 0`.

In either case infinitely many shifted moments are negative. Since every moment
of a positive measure on `R_+` is nonnegative, no positive Markov/Stieltjes
representation exists.

## Consequence For Signed Counterterm Routes

`positive-even-frequency-cone-not-markov.md` ruled out positive summation over
FE-even real frequencies. This theorem rules out the finite signed atomic
escape as well. A signed correction made from finitely many real FE-even
frequency atoms cannot repair the Markov target; the dominant frequency forces
tail sign oscillation.

Therefore a completed source proof cannot be a finite signed real-frequency
counterterm patched onto the positive cone. Any viable signed correction must
be genuinely outside this finite atom class: an infinite/nonlocal source object,
an archimedean-prime interaction, a multiplicative correlation identity, or a
closed boundary/index construction.

## Boundary

This theorem does not rule out infinite signed distributions with no largest
frequency, complex or imaginary frequencies, non-frequency source terms, or the
completed explicit formula. It only closes the finite real atom model.

## Theatre Test

For any proposed signed counterterm proof of seam-log Markov positivity:

1. Does the proof reduce the completed correction to finitely many real FE-even
   frequency atoms?
2. If yes, combine equal frequencies and inspect the top nonzero frequency.
3. The top frequency fixes the sign of `S_k` for large `k`, so `T_k` is negative
   on one tail parity.
4. Which source mechanism prevents that dominance argument from applying?

## Novelty Status

The proof is elementary finite exponential-sum dominance. The significant part
is the route audit: signed finite atom corrections are not the missing
completed interaction.

## Gates

- [x] 0 -> 1 in-progress: finite signed atom escape isolated.
- [x] 1 -> 2 fully-proven: dominance proof written.
- [x] formal core: two-frequency dominant-tail signs proved as
  `GaloisForLFunctions.twoFrequency_dominant_positive_eventually` and
  `GaloisForLFunctions.twoFrequency_dominant_negative_eventually`.
- [x] 2 -> 3 formalized: arbitrary finite signed support, via `exists_seamMoment_neg_of_signedFrequency`.

## Log

- 2026-06-24 -- Codex: created after the positive-cone obstruction. Entropy
  seed `298595177235550896`; method move `change-representation`.

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
