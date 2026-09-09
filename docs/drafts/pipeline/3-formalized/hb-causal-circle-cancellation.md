# HB: actual circle cancellation and regular radial remainder

Status: nine public theorems formalized in the existing source-adjoint leaf. The complete physical pairing and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalSourceAdjoint`, namespace `RHTower.D4BMCausalSourceKernel`.

## Successful cancellation conjecture

The forced circle coefficient cancels against the constant and linear radial moments of the *actual* causal Legendre kernel. This is the positive cancellation in equation (11) of [the analytical calculation](../1-in-progress/hb-causal-circle-taylor-cancellation.md).

Let `lambda=nu(nu+1)`, `K_nu` be the original direct-minus-image source kernel, and `K_0` that same kernel at degree zero. With `a_D=(L_D-2)g_(s,D)` and

```
R_nu(E,Z)=P_nu(Z)-P_nu(E)-(Z-E)P_nu'(E),
```

Lean proves

```
(lambda-2)K_nu(E)
 =2K_0(E)[E P_nu'(E)-P_nu(E)]
  -a² integral_direct a_D R_nu(E,Z)du
  +a² integral_image a_D R_nu(E,Z)du.
```

`legendre_zero` and `legendre_one` evaluate the actual terminating hypergeometric kernels. The original source-action theorem at these two degrees supplies both moments. `sourceKernel_action_circle_cancel` combines them with the general degree and discharges the integral linearity using proved continuity and integrability. It neither assumes cancellation nor replaces the original source.

## Exact regular remainder

`legendre_contDiffAt` proves smoothness of the actual kernel on the positive real chart, including the characteristic value one. `circleRemainder_eq_second` applies Taylor's integral theorem and identifies both derivatives with the corpus's actual kernel derivatives:

```
R_nu(E,Z)=(Z-E)² integral_0^1 (1-t)P_nu''(E+t(Z-E))dt.
```

The source cubic is affine in `D=d/c`. Its homogenization is

```
C_reg(s,c,d,u)=c C_(s,0)(u)+d[C_(s,1)(u)-C_(s,0)(u)].
```

`regularActionWeight` is the explicit differentiated source numerator formed from this cubic, powers of `1+u`, and polynomial coefficients in `c,d,u`. It contains no division by `c` or `d`. `regularActionWeight_eq` proves it equals `c² a_D` on each causal branch. Therefore `actionRemainderDensity_eq_regular` proves the combined density is exactly

```
u² regularActionWeight(s,c,d,u)
   integral_0^1 (1-t)P_nu''(E+t(Z-E))dt.
```

`regularActionWeight_continuousAt` proves joint continuity in `c,d,u` whenever `1+u>0`, including `c=0`. The intermediate `actionRemainderDensity_eq_second` records the exact displacement-square factorization.

These theorems do not yet establish joint continuity of the complete parameterized integral, full-angular circle-mean admission, identification with the physical causal response, or extinction. The next analytical substitution into the fixed-clock pairing is equation (13) of the linked card; its derived effective contact is `S_hat=S+2K_0(0)J`, with all terminal-time and angular Green terms retained.

## Verification

The full changed source passed `lake env lean` in scratch without warnings. Final audit ran only

```
lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalSourceAdjoint
```

The exact leaf passed in 49 seconds, three Lake jobs. Its 3,972 existing own dependency modules and external dependency caches were reused; no dependency or umbrella build ran. The temporary stub manifests produced administrative missing-manifest warnings; the Lean leaf produced no warnings.

Only these nine new public theorems received axiom checks: `legendre_zero`, `legendre_one`, `legendre_contDiffAt`, `sourceKernel_action_circle_cancel`, `circleRemainder_eq_second`, `actionRemainderDensity_eq_second`, `regularActionWeight_eq`, `actionRemainderDensity_eq_regular`, and `regularActionWeight_continuousAt`. Every report contains only `propext`, `Classical.choice`, and `Quot.sound`.

The installed source, `.olean`, and `.ilean` match the audited copies byte for byte. This existing module is already imported by `RHTower.lean`.

Generated catalogs were refreshed. Ordinary `python3 scripts/formal_tools.py lint` passed with existing corpus-size warnings; scoped whitespace checks passed. Owned scratch/audit files were removed after installing the verified artifacts. No owned Lean process remained. The frontier map was not edited by this work.
