# CCM-FU signed divisor hyperbola cancellation

- **ID:** CCM-FU-HYP
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Remove the harmonic loss in the literal half-order dilation diagonal by summing the centered divisor remainder in time before estimating.

## Goal and proof chain
Completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → completed prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.
The literal Möbius–divisor Abel moment is already equivalent to the completed source. Its signed cross-channel inequality is open. The existing independent channel envelope gives only a harmonic diagonal ceiling. This card attacks the latter estimate; it does not assume or prove the cross-channel inequality.

## Corpus audit
Read `CCMFUSuzukiMobiusDivisorAbelProducer`, the full relevant decomposition statements in `CCMFUSuzukiMobiusDivisorDilationChannels`, `MobiusDivisorAbelDiagonalBound`, `MobiusDivisorMonotoneWeightObstruction`, `PsiDefectSqrtBound`, `DirichletDivisorAsymptotic`, and `HTGeometry/DiscreteAbelRing`.
Corpus-wide research queries covered divisor remainder, divisor summatory, divisor Abel, fractional primitive, floor integral, and periodic partial sum. No matching centered modular half-order hyperbola bound was found.
The flat/geometric-weight obstruction does not settle the literal half-order weight. Floating-point exploration through endpoint 1500 found no positive half-order source-square-minus-diagonal gap; this is guidance only and is not a proof input.

## Paper mechanism
For d>0 define a_d(k)=(k mod d)/d-(d-1)/(2d). Its prefix of length N is exactly r(r-d)/(2d), where r=N mod d. Thus every prefix lies in [-d/8,0] and every complete period sums to zero. Starting at a multiple of d preserves the formula. Abel summation against a nonnegative decreasing weight therefore retains a nonpositive response bounded below by -(d/8) times the initial weight. At the actual hyperbola birth k=d², the half-order weight sqrt(k+1)-sqrt(k) is at most 1/(2d), giving an absolute channel budget 1/16. Summing the born channels should give an O(sqrt M) bound for the centered hyperbola part.
The logarithmic-factorial and corrected harmonic smooth remainders must be bounded separately before claiming a bound for the literal divisor channel. Those bounds and the cross-channel order are not supplied by this periodic argument.

## Work plan
- [x] Audit route, shared RH constraints, and prior corpus.
- [x] Prove exact centered modular primitive and its quadratic-width range in Lean scratch.
- [x] Prove shifted decreasing-weight response and the literal square-root instance.
- [x] Sum the full moving hyperbola family, including birth and endpoint terms.
- [ ] Bound smooth divisor remainder and transfer to the complete dilation diagonal.
- [ ] Attack the remaining literal signed cross-channel inequality.
- [ ] Run each new module with `lake env lean`, targeted final module build, scratch axiom audit, lint, and umbrella wiring. No full builds or computational proof certificates.

## Status
No RH proof or falsification. No new theorem is claimed until Lean checks pass. Task remains active.

## Checked source results
`HTGeometry/CenteredModularAbel.lean` and `RHTower/DivisorCenteredHyperbola.lean` passed `lake env lean` with no warnings. Their oleans were produced individually for dependent checks; final `lake build` and axiom/lint audit remain pending. Both umbrellas import the new modules.
- `sum_centeredModularRamp`: exact quadratic residue primitive.
- `sum_centeredModularRamp_mul_bounds`: nonpositive response under nonnegative decreasing weights, bounded below by `-d*w(0)/8`.
- `sum_centeredModularRamp_halfOrder_Ico_bounds`: literal square-birth response in `[-1/16,0]` at every cutoff, with no hypotheses.
- `sum_floorDivisor_eq_centeredHyperbola`: for `s=floor(sqrt N)`, the exact literal divisor count is `(2N+1)H_s-s²-s-2E_N`.
- `centeredDivisorHyperbolaAbel_eq_birth_channels`: coefficient-faithful finite Fubini across every active modulus and time.
- `centeredDivisorHyperbolaAbel_bounds`: the complete centered Abel response lies in `[-floor(sqrt(M-1))/16,0]`, with no hypotheses.

## Next paper estimates
Let `L_N=sum_(m<=N) log m`, `s=floor(sqrt N)`, and `h_s=H_s-log s-gamma`. Prove `1/(2(s+1)) <= h_s <= 1/(2s)` using the existing corrected upper sequence and a matching monotone lower sequence. Then write the smooth divisor source after subtracting `2E_N` as
`[L_N-N log N+N] - H_s + [N log(N/s²)-N+s²] + [s-2N h_s]`.
The four bracket budgets are respectively `[1,1+log(N+1)]`, `-H_s`, `[0,4]`, and `[-2,1]`, using `s²<=N<=s²+2s`. This should give absolute smooth error at most `6+log(N+1)`.
Consequently the undilated complete half-order defect should be bounded by `(7+log M)*sqrt M`, hence `7 sqrt M sqrt(sqrt M)` for `M>=1`. Exact complete/terminal block splitting should then give a uniform dilation bound of order `M^(3/4)d^(-1/4)`. Summing its squares costs `sum d^(-1/2)=O(sqrt M)`, yielding an unconditional `O(M²)` diagonal. None of these next estimates has yet passed Lean; the signed cross-channel inequality remains open even if they succeed.

Scratch continuation: `/tmp/ccm_fu_harmonic.lean` contains the matching harmonic bound under active verification. All proof code is symbolic and analytic; no numerical certificate is imported.
