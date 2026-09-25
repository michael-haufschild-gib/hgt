# C2 quadrature-tail validation supplement

C2's five admissible collision points and five nearby normalization anchors agree with the independent character-theta representation only to about 108 digits for conductor 5 and 137 digits for conductor 4, despite 190-digit working precision. This precision ceiling requires diagnosis before any 160-digit independent-validation claim.

Prediction: the x=3 tail contains exp(-pi*exp(6)/q); its conductor dependence explains the observed ceilings. This is an inexpensive necessary implementation/error check, not an admitted discovery experiment. No new enlarged collision scan. Re-evaluate exactly the same ten anchors with cutoffs 3.5 and 4, retaining 40 terms and 190-digit arithmetic. Agreement between both larger cutoffs and the Hurwitz formula must improve substantially; otherwise label the independent validation inconclusive and investigate quadrature itself.

The character definitions, frozen deformation coefficients, original roots and source provenance are copied from C2. Current completion/theta corpus search is retained. Source constraints and physical limitations remain those of C2. No kernel positivity or rigorous tail certificate is claimed.

Twenty parallel integrals, <=14 workers, library threads 1. Supplement compute cap 385 seconds plus <=10 cleanup: added to C2's 152.49 seconds, even both caps total under ten minutes of computation. Preserve all original C2 results. Exact seed and parameter inputs are archived. No Lean builds.
