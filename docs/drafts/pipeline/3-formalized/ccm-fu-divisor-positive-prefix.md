# Positive large prefixes of the literal divisor source

- **Stage:** 3-formalized.
- **Type:** unconditional source theorem; no novelty claim.
- **Chain:** completed Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> coherent prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH.
- **Scope:** actual unsigned source orientation. The complete Möbius-signed SD1 inequality and RH remain open.

## Exact statements

For the literal `D(N)=log(N!)-sum_(d<=N)floor(N/d)+2 gamma N`, set
`A(N)=sum_(k=1..N)D(k)` and `s=floor(sqrt N)`.

Lean proves

`A(N)>=s^2/24-17s` for N>=1,
`A(N)>=0` for N>=408^2=166464,
`A(N)>=N/48-3500` for every natural N.

For the existing undilated half-order response
`K_1(M)=sum_(k=1..M-1)(sqrt(k+1)-sqrt k)D(k)`, it further proves

`K_1(M)>=sqrt(M)/48-3501` for every natural M,
`K_1(M) -> +infinity` as M tends to infinity.

These are literal source inequalities. No zero-location premise, finite numerical certificate, changed source definition, or assumed aggregate cancellation enters their statements or proofs. The stronger U1 (nonnegative A at every cutoff) and U2 (nonnegative every unsigned dilation channel at every cutoff) are closed by the [all-cutoff orientation certificate](ccm-fu-unsigned-channel-orientation.md).

## Dependency-closed paper proof

1. The rational cubic logarithm correction is
   `log x <= (x-1/x)/2-(4/3)((x-1)/(x+1))^3`, x>=1.
   The derivative of the right side minus the left side factors as
   `(x-1)^4(x^2+6x+1)/(2x^2(x+1)^4)>=0`; the difference vanishes at one.
2. At x=(n+1)/n this improves the harmonic increment bound enough that
   `H_n-log n-1/(2n)+1/(12(n+1)^2)` increases to gamma. Hence
   `H_n-log n-gamma <=1/(2n)-1/(12(n+1)^2)`.
   The correction terms tend to zero; the existing harmonic limit supplies the limit.
3. The corpus Stirling sequence has the rational logarithmic lower constant `1-1/12-(log2)/2`. Expanding its definition gives
   `log(N!)>=N log N-N+(log N)/2+11/12`, N>=1.
4. The exact centered hyperbola writes `D(N)=R(N)+2E(N)`, with
   `R(N)=log(N!)-(2N+1)H_s+s^2+s+2 gamma N`.
   The Padé lower logarithm bound gives
   `N log(N/s^2)-N+s^2 >= (N-s^2)^2/(2(s+1)^2)`.
   Use the harmonic bound from step 2, the half-logarithmic endpoint from step 3, gamma<=7/12, and `s^2<=N<=s^2+2s`. Algebra then retains
   `R(N)>=(N-s^2-s)^2/(2(s+1)^2)-5/s`.
5. In a complete square block k=s^2,...,s^2+2s, the centered squares sum exactly to `s(s+1)(2s+1)/3`. Thus the complete block sum of R is at least `s/3-91/6`. Summing complete blocks before the final one gives
   `sum_(k=1..s^2-1)R(k)>=s^2/6-(46/3)s+91/6`.
   The last partial block has at most 2s+1 terms, each at least -5/s, so its sum is at least -15. Therefore
   `sum_(k<=N)R(k)>=s^2/6-16s`.
6. Finite Fubini over the square-birth channels gives the exact ordinary centered prefix
   `sum_(k<=N)E(k)=sum_(d<=s)P_d(N+1)`,
   where `P_d(T)=r(r-d)/(2d)`, r=T mod d. Every birth prefix at d^2 vanishes, and every terminal primitive is retained. The existing bound `-d/8<=P_d<=0` gives
   `-s(s+1)/16<=sum_(k<=N)E(k)<=0`.
7. Combining steps 5-6 yields `A(N)>=s^2/24-17s`. It is nonnegative once s>=408. Since N<=s^2+2s, completing the square `(s-409)^2>=0` also gives the uniform affine floor `A(N)>=N/48-3500`. N=0 is checked directly.
8. Put `f(k)=D(k)-1/48+3500*1_(k=1)`. Every positive-index prefix of f is nonnegative by step 7. Discrete Abel summation against the nonnegative decreasing half-order weight w therefore gives `sum f(k)w(k)>=0`. Undoing the first-atom correction explicitly gives
   `K_1(M)>=(sqrt M-1)/48-3500*w(1)`.
   Since w(1)<=1, this implies the stated square-root floor. M<=1 is handled directly. Its comparison with a function tending to positive infinity proves the final limit.

## Lean certificates

All declarations are in namespace `RHTower`.

- [HarmonicSecondErrorBounds.lean](../../../../formal/GaloisForLFunctions/RHTower/HarmonicSecondErrorBounds.lean): `log_le_half_sub_inv_cubic`, `harmonic_mascheroni_le_half_sub_twelfth`, `sum_log_Icc_ge_half_log_stirling`.
- [DivisorHyperbolaPositivePrefix.lean](../../../../formal/GaloisForLFunctions/RHTower/DivisorHyperbolaPositivePrefix.lean): quadratic point floor, complete square-block floor, complete smooth-prefix floor, exact centered-prefix reconstruction and bounds, `sum_primeFreeDivisorDefect_ge`, `sum_primeFreeDivisorDefect_nonneg_of_large`, `sum_primeFreeDivisorDefect_ge_affine`, `divisorUnsignedDilationChannel_one_ge`, `tendsto_divisorUnsignedDilationChannel_one_atTop`.

Both modules pass individual foreground `lake env lean` checks and are wired once into `RHTower.lean`. Only their exact oleans are produced. No large or umbrella build is required. A single `/tmp` axiom audit of only these 13 new public theorems reports exactly `propext`, `Classical.choice`, and `Quot.sound`; no added axiom, `sorryAx`, or computational certificate axiom appears. Global formal lint passed with existing file-size warnings, and the declaration index was refreshed. No Lean process remains; completed scratch files were removed.

## Research scope

The starting points were the corpus signed hyperbola decomposition, exact modular primitive, neighboring harmonic-error bounds and mathlib's Stirling sequence. The retained quadratic square-block contribution is the additional analytic estimate. General work on integrals of divisor-problem errors is classical; see [Ivić, On the integral of the error term in the Dirichlet divisor problem](https://arxiv.org/abs/math/0510114). No result from that paper is imported or assumed here, and no literature novelty claim is made.

A direct [orientation screen](../2-fully-proven/computations/ccm-fu-unsigned-channel-orientation-2026-09-06/README.md) guided the source-shape question. Its values are not proof premises. Eventual unsigned positivity does not determine the Möbius-signed aggregate; SD1 remains a separate arithmetic obligation.
