# Finite-Order Local Frequency Operators Are Not Markov

- **ID:** finite-order-local-frequency-operators-not-markov
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Grade:** BRIDGE / guardrail. Door-2 reduces the proof to eventual sign of a
  real polynomial, so this is not a native theorem. Its role is to exclude a
  false completed-interaction shape.
- **Source:** `../../3-formalized/not_new_scientific_knowledge/positive-even-frequency-cone-not-markov.md`;
  `../../3-formalized/not_new_scientific_knowledge/finite-signed-even-frequency-atoms-not-markov.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** Applying any nonzero finite-order coefficient-local operator
  with real polynomial degree-symbol to a nonzero positive FE-even frequency
  mixture still cannot produce a Markov/Stieltjes moment sequence in the
  seam-square coordinate.

## Setup

Let `mu` be a nonzero positive Borel measure on `(0,infty)` such that all even
moments are finite. Define

`L_mu(z)=int_0^infty (cosh(lambda sqrt(z))-1) dmu(lambda)`.

Thus

`[z^k]L_mu(z)=(int lambda^(2k)dmu(lambda))/(2k)!`, for `k>=1`.

Let `q in R[X]` be a nonzero real polynomial. Think of `q` as the degree-symbol
of a finite-order local operator in the Euler operator `D=z d/dz`: on a power
series, `q(D)` multiplies the `z^k` coefficient by `q(k)`.

Define the transformed shifted seam moments

`T_k^{q,mu}=-2k(-1)^k q(k)[z^k]L_mu(z)`.

Equivalently,

`T_k^{q,mu}=(-1)^(k+1) q(k) (int lambda^(2k)dmu(lambda))/(2k-1)!`.

## Theorem

If `q` is nonzero and `mu` is nonzero positive, then `T_k^{q,mu}<0` for
infinitely many `k`.

Consequently `(T_k^{q,mu})_{k>=1}` is not the moment sequence of a positive
Borel measure on `R_+`.

## Proof

For every `k>=1`, positivity and nonzero support on `(0,infty)` give

`M_k=int lambda^(2k)dmu(lambda)>0`.

A nonzero real polynomial has only finitely many real roots and has a constant
sign for all sufficiently large real arguments. Hence there is `K` and a sign
`eps in {+1,-1}` such that

`eps q(k)>0`

for every integer `k>=K`.

For those `k`,

`sign(T_k^{q,mu}) = (-1)^(k+1) eps`,

because `M_k/(2k-1)!` is strictly positive. Therefore one tail parity has
negative transformed shifted moments:

- if `eps=+1`, every sufficiently large even `k` has `T_k^{q,mu}<0`;
- if `eps=-1`, every sufficiently large odd `k` has `T_k^{q,mu}<0`.

A positive measure on `R_+` has nonnegative moments. Thus no positive
Markov/Stieltjes representation exists.

## Consequence For Local Completed-Correction Routes

`../../3-formalized/not_new_scientific_knowledge/positive-even-frequency-cone-not-markov.md` kills direct positive summation over
FE-even frequencies. `../../3-formalized/not_new_scientific_knowledge/finite-signed-even-frequency-atoms-not-markov.md` kills a
finite signed real-atom patch. This theorem kills a different escape: applying a
finite-order local operator whose coefficient action is polynomial in the degree.

The obstruction is parity, not scale. Polynomial degree multipliers can change
amplitude and finite initial data, but they cannot supply the alternating factor
needed to move a positive FE-even frequency source into the Markov cone.

Therefore a source proof of seam-log Markov positivity cannot be a finite-order
local correction of the positive frequency source. It must use an all-order or
nonlocal completed interaction, a multiplicative correlation identity, or a
closed boundary/index construction.

## Boundary

This theorem does not rule out infinite-order operators, operators with
non-polynomial degree-symbol carrying an explicit parity factor, nonlocal
transforms, complex/imaginary frequencies, or the completed explicit formula.
Those are precisely the mechanisms still outside this finite-local obstruction.

## Theatre Test

For any proposed completed-correction proof:

1. Does the correction act coefficientwise as multiplication by a real
   polynomial `q(k)`?
2. Is the source being corrected a nonzero positive FE-even real-frequency
   mixture?
3. If yes, `q(k)` has a tail sign and the FE parity forces negative moments on
   one tail parity.
4. Which line of the proof uses an all-order/nonlocal mechanism that escapes a
   polynomial degree-symbol?

## Novelty Status

The proof is elementary. The significance is route-local: it prevents a finite
local differential or finite-part multiplier from being presented as the
completed interaction needed by the seam-log Markov target.

## Gates

- [x] 0 -> 1 in-progress: finite-order local operator escape isolated.
- [x] 1 -> 2 fully-proven: polynomial tail-sign proof written.
- [ ] 2 -> 3 formalized: optional eventual-sign lemma for real polynomials plus
  positive moment factor.

## Log

- 2026-06-24 -- Codex: created after the positive-cone and finite signed-atom
  obstructions. Entropy seed `3021681132552638468`; method move `revisualise`.

## 2026-06-24 parity companion

`seam-parity-correction-is-nonlocal-half-turn.md` records the positive routing fact behind this no-go. The missing coefficient parity is the half-turn `Hf(z)=f(-z)`, with eigenvalue `(-1)^k` on degree `k`. It is not any finite polynomial `q(D)` in `D=z d/dz`.

Thus finite-order local operators fail for a precise reason: they cannot implement the nonlocal FE half-turn in the seam-square coordinate.

## Lean formalization

Module: `formal/GaloisForLFunctions/HTGeometry/EvenFrequencySeamMoments.lean`
(namespace `GaloisForLFunctions`), wired into the `GaloisForLFunctions.HTGeometry` umbrella.

| Paper statement | Lean declaration |
|---|---|
| closed form `T_k^{q,mu} = (-1)^(k+1) q(k) M_k/(2k-1)!` | `seamMoment_factorialCoeff` |
| `M_k = int lambda^(2k) dmu > 0` for a nonzero positive frequency measure | `integral_pow_pos_of_measure_pos` |
| a nonzero real polynomial has a constant tail sign | `exists_eventual_sign` |
| one tail parity carries strictly negative transformed moments | `exists_seamMoment_neg_of_polynomialMultiplier` |
| the parity sign lemmas feeding it | `seamMoment_neg_of_even`, `seamMoment_neg_of_odd_of_neg` |

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
