# Quadratic ceiling for the literal Möbius–divisor Abel diagonal

- **ID:** CCM-FU-HYP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); no novelty claim
- **Statement:** The complete literal half-order Möbius–divisor diagonal satisfies `sum_(d<=M) C_d(M)^2 <= 722 M²` unconditionally for every natural M.

## Exact arithmetic object
For `D(q)=sum_(m<=q)log m-sum_(d<=q)floor(q/d)+2 gamma q`, put
`C_d(M)=mu(d) sum_(k=d)^(M-1) (sqrt(k+1)-sqrt k) D(floor(k/d))`.
These are exactly `primeFreeDivisorDefect` and `mobiusDivisorDilationChannel` in the existing corpus. No replacement source, independent sign model, zero-location assumption, convergence interface, or numerical certificate is used.

## Complete paper proof
1. For d>0, center the literal residue ramp as `a_d(k)=(k mod d)/d-(d-1)/(2d)`. Its prefix of length N is exactly `r(r-d)/(2d)`, with `r=N mod d`. The formula follows by discrete differentiation, including period wrap, and induction. The primitive lies in `[-d/8,0]`; for d=0 the defined quantities vanish.
2. Abel summation against any nonnegative decreasing weight gives response between `-d*w(0)/8` and zero. The terminal primitive is retained. Starting at d² preserves residues, and `d*(sqrt(d²+1)-d)<=1/2`. Every literal half-order channel on `[d²,M)` consequently lies in `[-1/16,0]`, including empty intervals.
3. Put `s=floor(sqrt N)` and `E_N=sum_(1<=d<=s)a_d(N)`. The symmetric hyperbola identity gives exactly `sum_(d<=N)floor(N/d)=(2N+1)H_s-s²-s-2E_N`. Finite Fubini over all time and modulus labels gives the complete centered Abel response `H(M)` in `[-floor(sqrt(M-1))/16,0]`. Birth and last-block boundaries are not discarded.
4. The logarithm bound `log x<=(x-x^(-1))/2` for x>=1 follows from its nonnegative derivative defect. It makes `H_n-log n-1/(2n)` increase to gamma. The existing complementary corrected upper sequence yields `1/(2(n+1))<=H_n-log n-gamma<=1/(2n)`.
5. Write the smooth remainder after subtracting `2E_N` as
   `[log(N!)-N log N+N]-H_s+[N log(N/s²)-N+s²]+[s-2N(H_s-log s-gamma)]`.
   For N>=1, the four contributions obey respectively `[1,1+log(N+1)]`, `[-1-log(N+1),0]`, `[0,4]`, and `[-2,1]`. The Stirling integral sandwich proves the first; the harmonic sandwich proves the last; `s²<=N<=s²+2s` and `log x<=x-1` prove the middle logarithmic boundary. Thus the smooth remainder has absolute value at most `6+log(N+1)`.
6. Sum this smooth bound against the exact telescoping half-order weight and combine it with step 3. The literal undilated channel satisfies `|C_1(M)|<=(7+log M)sqrt M<=7sqrt M sqrt(sqrt M)`. M=0 is checked separately. The last inequality follows by applying `log x<=x-1` to the fourth root.
7. For an active dilation put `Q=floor((M-1)/d)`. Exact quotient-block transport gives
   `C_d(M)=mu(d)[sqrt d C_1(Q)+(sqrt M-sqrt(Qd))D(Q)]`.
   The terminal factor remains even when the final block is exactly full. Since `Qd<=M<=(Q+1)d`, `|D(Q)|<=24sqrt Q`, and `(sqrt(Q+1)-sqrt Q)sqrt Q<=1/2`, its absolute size is at most `12sqrt d`. This yields `|C_d(M)|<=19sqrt d sqrt Q sqrt(sqrt Q)`.
8. Squaring and using dQ<=M gives `C_d(M)^2<=361M sqrt Q`. Inactive channels vanish. Since `sqrt Q<=sqrt M/sqrt d` and `sum_(d<=M)1/sqrt d<=2sqrt M`, summing all channel squares gives `sum C_d(M)^2<=722M²`.

## Lean certificates
All declarations below have namespace `HTGeometry` or `RHTower` as indicated.

| Module | Main declarations |
|---|---|
| [HTGeometry/CenteredModularAbel.lean](../../../../formal/GaloisForLFunctions/HTGeometry/CenteredModularAbel.lean) | `sum_centeredModularRamp`, `centeredModularPrimitive_bounds`, `sum_centeredModularRamp_mul_bounds`, `sum_centeredModularRamp_halfOrder_Ico_bounds` |
| [RHTower/DivisorCenteredHyperbola.lean](../../../../formal/GaloisForLFunctions/RHTower/DivisorCenteredHyperbola.lean) | `sum_floorDivisor_eq_centeredHyperbola`, `centeredDivisorHyperbolaAbel_eq_birth_channels`, `centeredDivisorHyperbolaAbel_bounds` |
| [RHTower/HarmonicHalfErrorBounds.lean](../../../../formal/GaloisForLFunctions/RHTower/HarmonicHalfErrorBounds.lean) | `log_le_half_sub_inv`, `harmonic_mascheroni_half_bounds` |
| [RHTower/DivisorHyperbolaAbelBound.lean](../../../../formal/GaloisForLFunctions/RHTower/DivisorHyperbolaAbelBound.lean) | `abs_divisorHyperbolaSmoothRemainder_le`, `divisorHyperbolaSmooth_add_centered`, `abs_divisorHyperbolaCompleteAbel_le`, `abs_divisorHyperbolaCompleteAbel_le_threeQuarter` |
| [RHTower/MobiusDivisorAbelQuadraticDiagonal.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorAbelQuadraticDiagonal.lean) | `mobiusDivisorDilationChannel_one_eq_hyperbola`, `mobiusDivisorDilationChannel_eq_full_terminal`, `mobiusDivisorDilationChannel_sq_le_quotient`, `sum_mobiusDivisorDilationChannel_sq_le_quadratic` |

## Validation
- All five new source modules passed direct `lake env lean <file>` checks without warnings. Four small named-leaf audits also passed. The final named-leaf audit was stopped when it expanded into a large dependency rebuild; it is not reported as completed. One missing existing olean was restored by checking that single source file directly.
- A `/tmp` scratch file imported the completed module and ran `#print axioms` only for the 27 new public declarations. All report exactly `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx`, added axiom, or `Lean.ofReduceBool` dependency. No numerical experiment enters these proofs.
- All five modules are wired once into their corresponding umbrellas; the research index is refreshed. `python3 scripts/formal_tools.py lint` passes, with existing large-file warnings.
- No umbrella build was run. The oversized audit and its descendants were stopped; the single-file restoration and new-declaration axiom audit completed. No further dependency rebuild is required for this certificate.

## RH boundary
The full chain remains completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → completed prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.
This theorem closes the diagonal magnitude estimate without harmonic loss. It does not control the signed cross-channel sum. The frozen SD1 claim in [the active source-diagonal card](../1-in-progress/mobius-divisor-source-diagonal-dominance.md) remains unproved. If independently established, SD1 would give the normalized complete source a constant ceiling and feed the existing RH receiver directly, without a new continuation argument.
No unconditional proof or falsification of RH is claimed.
