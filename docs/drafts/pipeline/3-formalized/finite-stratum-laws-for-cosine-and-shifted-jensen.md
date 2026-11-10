# Shifted Jensen finite-stratum criterion and cosine tail criterion

- **Stage:** 3-formalized
- **Source:** review-0911 §11.6, A50.

## Shifted Jensen target

For each degree `d`, the exceptional shifts
`{n : ¬(jensenPoly xiJensenCoeff d n).Splits}` are finite by
`RHTower.eventually_splits_xiJensenPoly`. A law turning this finiteness into
emptiness gives splitting at every degree and shift. The remaining bridge
must use these exact Pólya coefficients `γ(k)=k! m(k)/(2k)!`;
the existing Jensen criterion for all Taylor coefficients of `XiC` has a
different normalization and indexing.

The squared entire function `Q(z²)=XiC(z)` supplies the bridge:
`Q(−w)=Σ m(k)w^k/(2k)!`. Scaled Jensen polynomials converge locally
uniformly to `Q(−w)`; Hurwitz makes its zeros real. For an actual spectral
zero `α`, the zero `α²` of `Q` has imaginary part `2 Re α Im α`.
Since `Re α≠0`, reality forces `Im α=0`, which is RH.

Lean: `AbscissaLaws/TheShiftedJensenFiniteStratumLawImpliesRH.lean`;
direct audit passed without warnings. All four transitive axiom lists
contain only `propext`, `Classical.choice`, `Quot.sound`.

## Cosine audit

For `A_h(z)=(XiC(z+ih)+XiC(z−ih))/2`, the heat-family finiteness input
does not transfer. Exact corpus statements:

- `cosShiftXi_finite_nonreal_of_zerosApproachLine`: ZAL implies finite
  non-real zeros at every `h>0`.
- `cosShiftXi_finite_nonreal_iff_zerosApproachLine`: under LH, that
  finiteness at every level is equivalent to ZAL.
- `riemannHypothesis_iff_eventually_cosShiftXi_real`: real zeros at all
  sufficiently small positive levels are equivalent to RH.

Thus ZAL plus a finite-stratum law on all cosine levels gives RH.
The asserted deduction from the finite-stratum law alone still needs an
argument producing finite defects near zero; it is not supplied by the
heat theorem. This is a precise missing implication, not an impossibility
claim about the actual zeta function.

Exact positive assembly:
`riemannHypothesis_iff_zerosApproachLine_of_cosine_finite_stratum_law` in
`AbscissaLaws/TheCosineFiniteStratumLawClosesZAL.lean`;
direct audit passed without warnings. Its transitive axioms are
`propext`, `Classical.choice`, `Quot.sound` only. The stronger deduction
from the cosine finite-stratum law alone remains open.
