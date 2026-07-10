# Single Even Frequency Is Not Stieltjes

- **ID:** single-even-frequency-not-stieltjes
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `seam-log-markov-pick-rh-equivalence.md`;
  `positive-source-weights-require-pointwise-hankel-kernels.md`;
  `seam-division-source-split-cancellation.md`
- **Statement:** A positive FE-even exponential frequency contributes an
  alternating shifted seam-moment string. Therefore the seam-log Markov/Stieltjes
  positivity cannot be proved termwise from positive Euler frequencies.

## Setup

Let `B>0` and `lambda>0`. Consider the even local log-germ

`L_lambda(z)=B(cosh(lambda sqrt(z))-1)`.

Equivalently,

`L_lambda(z)=B sum_{k>=1} lambda^(2k) z^k/(2k)!`.

As in the seam-log RH coordinate, define shifted moments

`T_k(lambda)=-2k(-1)^k [z^k] L_lambda(z)`, for `k>=1`.

These are the moments that would feed the Markov candidate

`G_lambda(x)=sum_{n>=0} T_{n+1}(lambda) x^n`.

## Theorem

For every `B>0` and `lambda>0`,

`T_k(lambda)=B (-1)^(k+1) lambda^(2k)/(2k-1)!`.

In particular,

`T_1=B lambda^2`,

`T_2=-B lambda^4/6`,

`T_3=B lambda^6/120`.

Thus the first nontrivial shifted Hankel block is indefinite:

`det [[T_1,T_2],[T_2,T_3]]
 = -7 B^2 lambda^8 / 360 < 0`.

Consequently a positive single even frequency is not a positive
Markov/Stieltjes source in the reciprocal seam coordinate.

## Proof

The coefficient of `z^k` in `L_lambda` is

`B lambda^(2k)/(2k)!`.

Substitution in the seam moment definition gives

`T_k(lambda)
 = -2k(-1)^k B lambda^(2k)/(2k)!
 = B (-1)^(k+1) lambda^(2k)/(2k-1)!`.

The displayed values for `k=1,2,3` follow immediately. The determinant is

`B^2 lambda^8 (1/120 - 1/36)
 = -7 B^2 lambda^8 / 360`.

Since a positive Stieltjes/Markov moment block must be positive semidefinite,
the single even frequency fails the target cone.

## Consequence For The Euler-Product Transfer

The Euler side supplies positive amplitudes such as `Lambda(n)>=0`, and a single
frequency has a natural FE-even local shape through `cosh(lambda w)`. This card
shows that the corresponding pointwise seam kernel is not positive
semidefinite.

Therefore the source theorem cannot be a termwise positive-frequency proof.
Positive Euler weights cannot be pushed through the seam-square Markov coordinate
one frequency at a time. The proof must use a completed source mechanism:
functional-equation cancellation, archimedean coupling, multiplicative
correlation among the actual weights, or a closed boundary/index theorem.

In the language of `positive-source-weights-require-pointwise-hankel-kernels.md`,
the pointwise kernel test fails for the simplest FE-even frequency. Any viable
Euler transfer must therefore use more than positivity of the frequency weights.

## Extreme-Case Reading

This is the one-tooth gear test. If a proposed gear train from prime frequencies
to Stieltjes positivity already slips on a single isolated even tooth, then the
actual transfer must depend on global meshing among teeth, the archimedean
budget, or the completed explicit formula.

The theorem does not say the completed `xi` source is a positive sum of these
bad pieces. It says a proof cannot prove the completed positivity by assigning
Stieltjes positivity to each positive FE-even source frequency separately.

## Novelty Status

The calculation is elementary. Its significance is source-side routing: it
locates exactly why a termwise Euler-frequency positivity proof cannot discharge
the seam-log Markov/Pick target.

## Theatre Test

For any proof claiming Euler positivity implies the seam-log Stieltjes cone:

1. Does the proof decompose the source into positive frequency contributions?
2. Does it require each frequency contribution to be Stieltjes-positive after
   the seam-square transform?
3. If yes, this card gives a counterexample at one frequency.
4. Which completed interaction replaces termwise positivity?

## Gates

- [x] 0 -> 1 in-progress: single-frequency extreme case isolated.
- [x] 1 -> 2 fully-proven: coefficient and determinant calculation written.
- [x] 2 -> 3 formalized: arithmetic determinant identity and negativity proved
  in `formal/GaloisForLFunctions/SingleEvenFrequency.lean`; analytic coefficient
  extraction remains paper-level.

## Log

- 2026-06-24 -- Codex: created under the active RH continuation. Entropy draw:
  seed `1550289540000607138`, method `extreme-cases`, analogies
  `crystal-defects` and `gear-trains`.

## 2026-06-24 positive cone upgrade

`positive-even-frequency-cone-not-markov.md` extends this one-frequency obstruction to every nonzero positive mixture of FE-even frequencies. The obstruction becomes even simpler at cone level: `T_2<0`, so the positive cone cannot be a positive Markov/Stieltjes source on `R_+`.
