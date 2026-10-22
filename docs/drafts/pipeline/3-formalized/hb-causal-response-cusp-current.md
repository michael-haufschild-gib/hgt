# HB: original causal cusp jets and Goursat traces

Status: the exact causal remainder, all angular cusp-jet bounds, the Goursat equation, and both first-null derivative formulas are formalized. Complete physical-current cancellation and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

[Lean source](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMCausalResponseCusp.lean), namespace `RHTower.D4BMCausalCusp`. [Current attack](../1-in-progress/hb-causal-response-cusp-current.md).

## Exact original response

For an actual Xi occurrence q, original complex source rate s and amplitude a, set

```text
U(p,r,X,k) = fullNullResponse q s a p r X k,
c_i(p,r)   = principalNullResponse q s a i p r,
alpha     = [2q,1,2-2q],
R         = U - sum_i c_i exp(alpha_i k).
```

The coefficients are the existing physical radial source integrals. The theorem `principal_coefficient_integral` identifies each c_i with the original double null integral of `principalAmplitude_i * powerCircle_i * sourceWeight`, including the factor 1/4.

`responseRemainder_integral` identifies the full uncut remainder R with the same original integral of `nativeRemainder`. `responseRemainder_jet_integral` identifies every actual ordered angular derivative with the original integral of the corresponding native cusp jet. The radius is the original continuous causal arcosh radius, including both characteristic edges; angular differentiation does not require differentiating this radius in a null direction.

## Uniform cusp admission

For every natural N, compact causal bound T >= 0, and ordered angular derivative word J, `responseRemainder_jet_uniform_bound` proves that there are D,B >= 0 such that

```text
|D_J R(p,r,X,k)| <= B exp(N(D-k))
```

for every p,r in [0,T], every real X, and k >= D. The constants control both the original radius and source weight over the complete causal rectangle.

`responseRemainder_jet_weighted_tendsto_zero` consequently proves

```text
exp(w k) D_J R(p(k),r(k),X(k),k) -> 0
```

for every complex w and arbitrary paths p,r in [0,T] and X in R. No continuity of these paths is assumed. These estimates retain all remainder modes.

## Original forced characteristic equation

Define the actual forcing

```text
F_R(p,r,X,k) = nativeRemainder q [0,X,k] sourceWeight(s,a,p,r)/4
              + (exp(2k) R_XX + R_kk - R_k)/(4 cosh((p-r)/2)^2).
```

`responseRemainder_goursat` proves `R = integral_0^p integral_0^r F_R` on the closed nonnegative quadrant. It subtracts all three original scalar Goursat equations from the full source equation. The scalar coefficient `(-alpha_i)(1-alpha_i)` equals the angular eigenvalue `alpha_i(alpha_i-1)`, so this is an exact identity at every height.

`responseRemainder_first_null` proves the actual derivative `R_p = integral_0^r F_R(p,b) db` for p > 0, r >= 0. `responseRemainder_second_null` proves the actual derivative `R_r = integral_0^p F_R(a,r) da` for p >= 0, r > 0. The derivative statements use actual `HasDerivAt`, the original source, and actual angular derivatives.

## Remaining physical step

These are compact causal estimates. Higher angular derivatives of the first-null traces have a paper proof through the Goursat forcing and finite Leibniz sums, but are not formalized here. Reconstruction, unbounded horizon limits, the independent SS/SV/VV contributions, and the complete boundary cancellation remain required.

The existing [full original onset decomposition](hb-full-source-onset-reduction.md) already supplies two explicit wave images and a specified onset pulse. It gives the incoming profile `H-s(s-1)Q/4`. The next comparison must retain this profile and the actual causal pulse response. This module does not replace the physical cutoff residual by its uncut cusp expansion globally.

## Validation

The scratch proof passed `lake env lean`. The isolated final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalResponseCusp`; it passed in 340 seconds with two jobs. Cached dependencies were frozen for the audit; no dependency or umbrella build ran.

All eight new public theorems passed the scratch axiom audit with exactly `propext`, `Classical.choice`, and `Quot.sound`. The verified source and all five compiled artifacts were installed byte-for-byte.

The module has one import in `RHTower.lean`; that umbrella was not built. Generated indexes contain all 14 new public declarations, and the affected cards' local links were checked. Global formal lint reported two unrelated modules missing umbrella wiring: `GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowThresholdSplit` and `GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairGamma`. The new HB module passed its wiring check. Those other modules were not changed by this work.

All owned Lean/Lake processes were confirmed terminal; the owned scratch directory, isolated audit cache, and seven temporary search-result files were removed.
