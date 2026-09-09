# SQB: exact positive variance of the actual theta mode

The weighted logarithmic-source term now has an exact positive-variance
formula. Its integrals and endpoint terms are justified for every actual
Xi divisor and every real tilt in (-1,1). Native occurrence and RH remain
unproved.

## Theorem

Use the original two-ended theta mode u at z=b+ic=xiSpectralPoint(q),
the complete source Phi, and Q=Phi'/Phi. For a real tilt |a|<1, put

    f_a(x)=exp(a x)Phi(x),
    w_a(x)=exp(a x)|u(x)|^2/Phi(x),
    h_a=z+ia,
    V_a=integral f_a(x)|u(x)/Phi(x)+1/h_a|^2 dx.

The actual source ratio u/Phi is continuous and globally bounded. Lean
proves absolute integrability of the displayed energies and currents,
vanishing endpoints for their primitive identities, and

    V_a>0,
    integral (Q+a)w_a=2(a+c)V_a,
    integral w_a=V_a+(integral f_a)/|h_a|^2.

Thus the actual energy strictly exceeds its explicit source-mass term.
At a=0 the original current equals 2cV_0. At a=-c, the exact gauge energy
has finite positive mass and satisfies

    integral Q w_(-c)=c integral w_(-c).

Public specializations take only the actual Xi divisor copy. General
tilted statements quantify over the subtype (-1,1); their actual-domain
and positivity obligations are proved, not added as assumptions.

## Closed analytical proof

1. The complete theta envelope bounds the actual right two-ended mode
   by a constant times Phi. Reflection supplies the left tail. On the
   remaining compact interval, continuity of u/Phi supplies its bound.
2. Multiplication of the tilted theta Schwartz source, or its derivative,
   by the bounded ratio or its squared norm proves all required
   integrability. Schwartz decay and the same bounds give zero limits
   at both ends.
3. The tilted mode U_a=exp(a x)u satisfies
   U_a'=-ih_a U_a-if_a. Integrating gives integral U_a=-integral f_a/h_a.
   The denominator is nonzero because its real part is the actual
   nonzero zero ordinate b.
4. Expand the squared deviation V_a and insert this exact mean. This
   gives V_a=integral w_a-(integral f_a)/|h_a|^2.
5. Differentiate the weighted energy:
   w_a'=2(a+c)w_a-(Q+a)w_a-2 Im(U_a). Integrate and insert the same mean
   to obtain the current/variance identity.
6. The variance density is continuous and nonnegative. If it vanished
   identically, u/Phi would be constant. Its exact first-order equation
   at 0 and 1, where Q has distinct values, rules this out. Positivity
   on a nonempty open set makes the integral strictly positive.

## Audit

Module: `formal/GaloisForLFunctions/RHTower/SelbergThetaSourceVariance.lean`.
Namespace: `RHTower.SelbergThetaSourceVariance`. 23 public declarations,
540 lines, wired once into `RHTower.lean`.

- Complete scratch and canonical source checks passed using
  `lake env lean FILE`; the canonical check had no diagnostics.
- Final leaf build passed:
  `lake --old build GaloisForLFunctions.RHTower.SelbergThetaSourceVariance`.
  Only this leaf was rebuilt, in 10 seconds. Dependencies were replayed
  from existing artifacts; this is not a fresh whole-dependency audit.
  Logs: `/tmp/sqb29_preflight.log`, `/tmp/sqb29_leaf_build.log`.
- Repository formal lint passed; existing large-file warnings remain.
  Log: `/tmp/sqb29_lint.log`.
- All 23 public declarations passed the axiom audit in
  `/tmp/sqb29_axioms.lean`. Output `/tmp/sqb29_axioms.log` contains only
  `propext`, `Classical.choice`, `Quot.sound`.

No numerical computations, full builds, umbrella builds or frontier-map
edits were used.

## Quantitative continuation

The [working card](../1-in-progress/sqb-positive-occurrence-conjecturing-loop.md)
contains the stronger gauge-energy bound m/b^2<M<2m/b^2, now proved in
`SelbergThetaSourceEnergy`. That module supplies the first-moment identities,
strict negative covariance with Q, and the stronger pointwise disk bound
|1+b u/Phi|<1. Its [audit](sqb-theta-source-energy.md) states the exact
verification boundary. Transport to the complete native Gram norm remains
necessary for SQB occurrence.
