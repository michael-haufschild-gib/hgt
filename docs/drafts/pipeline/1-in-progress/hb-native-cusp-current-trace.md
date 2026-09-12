# HB: source-derived upper trace of the native nonconstant cusp current

- **ID:** HB-QNCT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; source-derived trace proof under construction
- **Parent:** [HB-QNCE](../3-formalized/hb-native-weighted-cusp-energy.md)
- **Route:** Literal theta source → Xi occurrence → retained spin two → physical causal/left-QNM action → common Hawking-clock extinction → RH

## Hard obstacle

The previous turn derived weighted integrability of the original native
nonconstant gradient energy. This controls current products in integral norm
but does not by itself give an upper cusp trace. The present target is to
produce that trace from the original forced equation, with both branches and
all signed forcing terms retained.

For the two original responses R_a,R_b, let M denote the period-one mean and
Cov(F,G)=M(FG)-M(F)M(G), a complex bilinear covariance without conjugation.
Define J_ab=Cov(∂y R_a,R_b). This is exactly the remainder after subtracting
the native mean product from the original bilinear vertical current.

The source PDE and cancellation of periodic horizontal side flux give

```
J_ab' = Cov(∂y R_a,∂y R_b) + Cov(∂x R_a,∂x R_b)
      + α_a/y² Cov(R_a,R_b) + 1/y² Cov(F_a,R_b).
```

Here F_a is the original complete cusp-subtracted forcing. No homogeneous
Maass equation, conjugacy of branches or RH consequence may replace this
forced identity.

## Conjecture → proof strategy

1. Prove the exact covariance identity with finite integrals. Keep the native
   mean current explicitly; it need not vanish.
2. The inequality 2|uv|≤|u|²+|v|² bounds covariance by centered slice energies.
   Independent Parseval identifies those centered energies with the proved
   nonconstant mass/gradient sums. Original forcing Parseval bounds its loss.
3. Source-weighted energy and mass admission then give weighted L1 control
   of both J_ab and J_ab'. Differentiating a polynomial weight introduces
   only another admitted current term.
4. Apply the installed improper-integral theorem: a function and its derivative
   integrable on a half-line force its limit to zero. This supplies the trace,
   rather than assuming one or inferring it from L1 alone.
5. Restore the exact native mean current and form the original coefficient
   combination β J_true,false − α J_false,true. Then transfer to the complete
   physical tested current, retaining theta/test derivatives, source contacts,
   retained spin two and other independent nonlinear channels.

The complete fixed-clock extinction theorem is still open. Angular tail
cutoffs are auxiliary estimates; the physical Hawking clock remains unchanged.

## Search applicability

Deep current/derivative search completed its stages but reported unavailable
semantic coverage; compiler coverage is predominantly source-only. Candidate,
method/source and ingredient views were inspected. The suggested Schwartz
field and homogeneous Maass-current theorems have unproved or incompatible
source premises here. They cannot produce native forced derivative admission.
A separate variance search returned finite deck-average results, not the
period-one complex covariance needed here. Direct installed mathlib
`tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` matches the final trace step;
its two integrability premises must be proved from this original source.

Broad arXiv virial/trace/dissipation searches returned recent observational
astrophysics and numerical cloud models, with no applicable source-current
cancellation. No source conclusion is inferred from those results.
