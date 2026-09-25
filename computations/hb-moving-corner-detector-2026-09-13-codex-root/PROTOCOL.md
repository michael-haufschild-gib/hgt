# HB moving-characteristic corner detector: frozen protocol

Status: frozen before computation. Exact-formula numerical experiment on one retained boundary primitive; not complete action or proof.

## Question

The finite optical source transfer leaves an explicit moving-characteristic primitive `C_st(L)` with two angular invariants, `R Q` and `Delta R Q`. For complementary rates `s=rho-2`, `t=-s-3`, form the ordered difference `W=C_st-C_ts` and coefficient ratio `kappa=-W_R/W_Delta`.

If the two angular pairings are real, corner cancellation requires real `kappa`. Does the complete source-polynomial corner, including `D_star f33`, make `Im kappa=0` a critical-line detector? This tests whether a boundary term usually treated as bookkeeping can carry the diagnostic.

## Prediction audit

Complementary rates and conjugation suggest some critical-line symmetry, but do not determine the ratio after source-polynomial mixing, radial moments, Mellin powers and the `D_star` correction. No inspected theorem fixes its phase, zeros or sign. Dropping the derivative term could create a false detector. Outcome is not honestly predictable.

## Object and experiments

Use the exact `z<-1` primitive of

`h_mn(L,z)=integral_(-1-z)^(1-z) y^m(y+z)^n/(L+y)^6 dy`

obtained by expanding in `q=L+y`; retain the logarithmic `q^-1` term. Define `f11,f13,f31,f33` and `D_star` exactly as in the finite optical reduction, evaluate on `z=1-L`, and assemble both ordered corner vectors with all coefficients.

1. Cross heights `14.134725..., 50, 100`, corner scales `L=2e,10,30`, and real parts `0.2,0.35,0.5,0.65,0.8` at 80 digits.
2. For each height/scale, scan 49 fixed real parts in `[0.02,0.98]`; record sign changes and roots of `Im kappa` only when `|W_Delta|` stays nonzero.
3. Ablate only `D_star f33`, explicitly unphysical, to test whether retained derivative boundary work creates or destroys apparent critical-line selection.
4. Controls: exact primitive versus direct quadrature for all four moments at representative points; `D_star` versus shrinking finite differences; reflection `rho -> 1-conj(rho)`; 120/180-digit repeats of every candidate root.

## Gates and consequences

- Detector candidate requires `Im kappa=0` at `Re rho=1/2` across all three heights and scales, a simple sign reversal across the line, no extra interior real-part roots, and survival with the complete derivative term. Any failure kills this corner-only detector.
- An ablation-only detector is a boundary-omission artifact.
- Success motivates exact algebraic phase factorization; it still does not prove angular ratio, full causal pairing, SS/SV/VV assembly, or spacetime limits.
- Failure salvages explicit corner phase data and constrains which remaining current must supply selection.

Scientific-method mechanics: isolate boundary component; attack detector as false; mix spectral height, real displacement and corner scale; ablate retained derivative; change integration representation; perturb/refine roots; extract positive constraint after failure.

Unique `/tmp/codex-root-hb-corner-B-0913`, 14 workers, one 570-second guard, library threads one, partial output preserved. No scan extension after frozen family.
