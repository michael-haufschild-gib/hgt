# HB: exact native angular cusp current

The full native angular Green current has exactly three principal cusp channels, with a remainder that vanishes after every complex height weight. This evaluates a boundary contribution needed by the physical-current cancellation. It does not prove that cancellation or RH.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact result

Let `F_d(X,k)=mean q d X k`, `Y=exp(k)`, and retain the original completed amplitudes `A_i=principalAmplitude q i` and exponents

```text
alpha = [2q, 1, 2-2q],
C_i(d) = powerCircle alpha_i d,
B_ij(d,e) = A_i A_j alpha_i alpha_j (alpha_j-alpha_i)
              (C_i(d) C_j(e)-C_j(d) C_i(e)).
```

The actual original-height field is `f_d(X,Y)=F_d(X,log Y)`. Its vertical coexact Green density is

```text
G(d,e;X,Y) = (partial_Y f_d) Delta f_e - (partial_Y f_e) Delta f_d,
Delta = Y^2 (partial_XX + partial_YY).
```

For any nonnegative radii `d,e`, arbitrary horizontal path `X(k)`, and any complex `w`, Lean proves

```text
exp(w k) [G(d,e;X(k),exp(k))
  - B_01(d,e) exp(2q k)
  - B_02(d,e) exp(k)
  - B_12(d,e) exp((2-2q) k)] → 0       as k → +infinity.
```

The three principal contributions are retained explicitly. There is no finite-part definition, principal-term deletion, changed measure, source replacement, or numerical premise in this result. Radius zero is included, where the existing `mean_zero` identifies the native field with the original half-square source.

## Proof

The actual circle-power/Legendre identity and positive-chart kernel smoothness give smooth principal coefficients through radius zero. The complete native mean is jointly smooth. Consequently its difference from the finite principal sum has actual coordinate derivatives, and the existing native cusp-jet estimate applies to those derivatives.

Writing `P_d=sum_i A_i C_i(d) exp(alpha_i k)`, direct differentiation gives `P_XX=0`, `P_k=sum_i alpha_i A_i C_i(d) exp(alpha_i k)` and the corresponding second derivative. The logarithmic-height Green density is

```text
H(F,G) = exp(k)(F_k G_XX-G_k F_XX)
       + exp(-k)(F_k G_kk-G_k F_kk).
```

Its principal diagonal terms cancel. Pairing the two orientations of each off-diagonal term gives `B_ij exp((alpha_i+alpha_j-1)k)`, hence precisely the displayed three channels.

For every complex weight `w`, choose a natural decay order `N>Re(w)`. The existing bound on each complete remainder jet is then bounded after weighting by a constant times `exp((Re(w)-N)k)`. Mixed principal/remainder terms use this estimate with the weight shifted by the corresponding principal exponent. Products of two remainder jets use the weighted estimate for one factor and the unweighted estimate for the other. Every term in `H(F_d,F_e)-H(P_d,P_e)` is covered.

Finally, the actual derivative identities `partial_Y=Y^(-1) partial_k` and `Y^2 partial_YY=partial_kk-partial_k` give `G(d,e;X,exp(k))=H(F_d,F_e)`. Both height Jacobian factors are retained in Lean.

## Lean ownership and validation

Owner: [ThetaCuspHawkingBMNativeAngularCurrent.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeAngularCurrent.lean), namespace `RHTower.D4BMNativeAngularCurrent`.

Six public theorems:

- `native_angular_jet_decomposition`: actual first and second angular derivatives of the complete native field.
- `principalFlux_three_channels`: exact principal coefficients and exponents.
- `weighted_native_remainder_tendsto_zero`: all ordered remainder jets, every complex height weight, arbitrary horizontal path.
- `verticalGreen_cusp_expansion`: full current in logarithmic-height coordinates.
- `originalVerticalGreen_eq`: actual original-height coordinate dictionary.
- `originalVerticalGreen_cusp_expansion`: complete original-height boundary asymptotic.

Scratch check passes without warnings. Isolated `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularCurrent` passes in 208 seconds with three jobs, reusing cached dependencies. All six new public theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. The source and five installed build artifacts match the audited files byte for byte. The umbrella imports the module exactly once; no dependency or umbrella build was run. Twelve local links across the result and two related cards resolve.

The global lint gate reports six umbrella-reachability errors outside this change: `RHTower.EulerDeletionSignatureWordExpansion`, `RHTower.Sieve.MenonHarmonicRamareLadderSwapped`, `RHTower.Sieve.MenonHarmonicRamareLadderSwappedVolume`, and `HTGeometry.WeightedMinimax.{Alternation,Coefficient,Perturbation}`. It reports no error for the new native angular-current module. The global gate is not claimed to pass.

## Remaining hard target

The full cancellation `2 Omega(B(p,p)/2,B(m,m)/2)=0` remains open. The next application must transport this native-kernel boundary formula, including the radius derivatives needed by reconstruction, through the original causal integrals. It must combine the resulting three coefficients with temporal/radial faces and source contacts, then establish the independent SS/SV/VV coefficients on the fixed Hawking clock. No vanishing of the retained principal flux or complete physical action is claimed.
