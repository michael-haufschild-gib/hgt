# Failed: independent scale-wise KL sum is the universal source action

- **ID:** ULF-CRG-FAIL-2
- **Stage:** 5-failed
- **Status:** `[FAILED AS UNIVERSAL MODEL] [THEOREM RETAINED] [STRONGER SURVIVOR PROMOTED]`

## Conjecture

Given scale-wise native laws `mu_n` and renewals `nu_n`, the universal source action is

```text
sum_n D(nu_n || mu_n).
```

The sharp exponential-aperture / polynomial-work theorem proves this sum diverges through degree
two.

## Hostile failure

The theorem is correct for a sequence of separately charged interventions.  It is not automatically
the action of one arithmetic source operation.  A single global change of measure may replenish
many scale apertures simultaneously; summing its marginal prices can overcount shared information.
Therefore the scale-wise sum cannot be installed as universal field action without a path-space
chain rule or independent-increment theorem.

## Positive survivor

Use one source law `mu`, one renewed law `nu`, and pairwise-disjoint apertures `A_n`.  Exponential
aperture decay makes the height partition function finite.  The entropy inequality then gives

```text
lambda sum_n n nu(A_n)
 <= D(nu||mu)+log integral exp(lambda N)dmu.
```

Finite **one-law** KL action forces a finite first aperture moment.  Persistent work `O(n^d)` is
therefore impossible for `d<=2`, and an explicit single global renewal proves sharpness for every
`d>2`.

Promoted survivor:

`../../../2-fully-proven/universal-law-field/cofinal-renewal-geometry/disjoint-aperture-global-renewal-moment-properness-and-cubic-threshold-law.md`.

The original scale-wise theorem remains valid and useful when source construction really supplies
independent increments or an additive path-space KL chain rule.

## Re-entry condition

Use a KL sum as source action only after proving that it is the exact relative entropy of a literal
source path law or product/projective formation.  Otherwise use the one-global-renewal theorem.
