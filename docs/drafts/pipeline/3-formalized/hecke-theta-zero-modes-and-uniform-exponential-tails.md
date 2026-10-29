# Hecke theta zero modes and uniform exponential tails

- **ID:** hecke-theta-zero-modes-and-uniform-exponential-tails
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Classify the physical and finite-Fourier zero terms and prove uniform exponential decay of the remaining actual Hecke theta series on bounded place profiles.

## Exact targets

The parity Gaussian at zero is one when every coordinate parity is zero, and
zero otherwise. The physical constant is this value times the actual finite
weight at zero. The dual constant is the same parity value times the finite
character sum; character orthogonality determines that sum.

For every actual nonzero fractional ideal and parity profile, the sum of the
norms of its nonzero parity-Gaussian terms decays exponentially as the positive
Gaussian parameter tends to infinity, uniformly over all upper-bounded place
profiles. Apply this proved bound to actual finite Hecke weights (norm at most
one) and actual Fourier coefficients (norm at most `N(𝔪.fin)`). No uniform
summability or decay hypothesis may be assumed.

## Dependency-closed route for decay

Use the already proved parity majorant at parameter one. Factoring off the
remaining Gaussian shows that for every `t ≥ 1`, the same constant majorizes
the parity kernel by the Gaussian of parameter `t/2`. Removing the zero term
and summing reduces the tail to `C*(θ_I(y,t/2)-1)`. The existing uniform
Gaussian ideal-tail theorem applies for `t ≥ 2`, giving exponential decay
with half its exponent. This suffices for the entire Mellin tail at infinity;
the bounded parameter interval is handled by normal convergence.

## Corpus audit

`NumberFieldIdealThetaDecay.lean` is source-inspected: positive actual-ideal
minimum, bounded-profile norm comparison, exact zero-term removal, and uniform
exponential Gaussian tails are all formalized. The current Hecke modules prove
actual finite weights, parities, physical/dual absolute convergence, and finite
Fourier coefficient bounds.

The completed semantic query for nontrivial finite multiplicative-character
sums returned finite additive-character identities and group-character
results. The relevant general multiplicative-character API remains to be
checked in Mathlib after that corpus search.

Unit-domain integration, exact Mellin unfolding, primitive finite Gauss
evaluation, and full Hecke continuation remain open.


## Lean declarations and audit

In [HeckeThetaTailsDecayExponentially.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeThetaTailsDecayExponentially.lean):

- `parityDegree_eq_zero_iff`, `parityGaussian_zero`
- `exists_uniform_parityGaussian_majorant`, `idealParityNormTail`
- `exists_uniform_exponential_idealParityNormTail`
- `integralHeckeWeight_zero`, `heckeThetaConstant`, `heckeThetaKernel_zero`
- `finiteHeckeFourierCoefficient_zero`, `heckeDualThetaConstant`, `heckeDualTheta_zero_term`
- `heckeDualIdealTheta`
- `exists_uniform_exponential_heckeIdealTheta_tail`
- `exists_uniform_exponential_heckeDualIdealTheta_tail`

The physical constant is one exactly when the finite modulus is the unit ideal
and the parity degree is zero. The dual constant is the number of units of the
residue ring exactly when the finite character is trivial and the parity degree
is zero. Otherwise the respective constant vanishes. Both formulas also handle
the trivial residue ring. The character-sum identities use the source-inspected
Mathlib `MulChar.sum_eq_zero_of_ne_one` and `sum_one_eq_card_units`.

The physical tail theorem covers every integral ideal, including zero. The dual
tail theorem covers the actual trace dual of a nonzero ideal times the finite
modulus. Every coefficient bound is discharged from the actual character or
finite Fourier sum. Decay is uniform for all upper-bounded place profiles and
all `t ≥ 2`, with positive constants.

The complete scratch and final direct `lake --old env lean` source audit pass
without warnings. Six transitive axiom audits, including both actual tail
theorems, contain only `propext`, `Classical.choice`, and `Quot.sound`. The module
is wired into the Hecke umbrella; no umbrella was compiled. No proof limits
were raised. Both dependency oleans are built. The completed scratch is
removed. Its olean is built for the written measurability and Mellin consumer.

Lean coercion note: a function on fractional-ideal elements must use
`↥(I : FI) → ℂ`; writing `(I : FI) → ℂ` parses as a binder with domain `FI`.
The actual applications transport integral elements through the proved
`integralIdealEquivFractional` and use the real trace-dual fractional ideal.
No weight bound or decay assumption remains in the public Hecke tail theorems.
