# Actual BM quadratic angular source: frozen experiment

Status: exploratory computation; no proof evidence is admitted to Lean.

The target chain is literal theta cusp → retained Einstein source → physical causal
response and left-QNM pairing → fixed-clock extinction → RH. The uncomputed input
is the actual Einstein Hessian, not the already constructed abstract Green kernel.

Question: for the complete fundamental scalar metric and its coexact-vector partner,
what angular tensors and radial coefficients occur in the quadratic trace-free angular
Einstein residual? Do the SS, SV and VV channels share a radial-independent scalar/vector
amplitude ratio that cancels this tensor identically, or do distinct angular structures
force additional source channels? The exact coefficients and their cancellation structure
are unknown. Generic nonvanishing alone is not the prediction target.

Inputs are the literal formulas in `ThetaCuspHawkingBMScalarLinearizedRicciJet`,
`ThetaCuspHawkingBMVectorLinearizedRicciJet`, and `CoordinateCurvatureTwoJet`.
Use an arbitrary scalar angular three-jet satisfying
`y²(Sxx+Syy)=(s+1)(s+2)S` and its first derivatives. The vector is exactly
`(Sy,-Sx)`. Retain symbolic `s,r` and all free angular jet coordinates; normalize
the common temporal/radial envelope to one and evaluate at angular height one only
after taking all derivatives. Its logarithmic radial derivative is `s/(r*(r²-1))`.

Compute the coefficient of epsilon² in Ricci from the full inverse expansion,
Christoffel derivatives, and both connection-product contractions. For this field,
the angular metric is conformal at every epsilon, so `E22-E33` and `E23` equal
`Ric22-Ric33` and `Ric23` at y=1 exactly, including the cosmological term.
Evaluate SS, VV and S+V independently, subtract to obtain the SV coefficient.
Check all sixteen background and first-order Ricci equations to detect transcription
errors. These checks validate the experiment, not new mathematics.

Execution: RunPod only, three worker processes, five-minute hard limit, no parameter
sweep and no numerical sampling. Save code, exact expressions, timings and checks.
Any observed factorization must be rederived and proved from the corpus definitions.
This local component test does not identify a gauge-invariant Teukolsky projection,
a singular-endpoint causal response, a left-QNM pairing, or an extinction law.
