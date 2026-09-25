# Cutoff height changes the usefulness of a scalar bound

The real normalized series is S(z)=E*(z,1/2+it)/abs(Lambda(1+2it)), where Lambda(s)=pi^(-s/2)*Gamma(s/2)*zeta(s). Its principal term is a0(y)=2*sqrt(y)*cos(arg Lambda(1+2it)+t*log y), and Q(y) is the x-mean of (S-a0)^2. Integration uses the standard modular cell |x|<=1/2, x²+y²>=1 and measure dx*dy/y², of volume V0=pi/3. For a subtraction threshold H, F_P=S²-1_(y>H)*a0²; F_C=S²-1_(y>H)*(a0²+Q). The complete square, compact curved boundary, native Fourier modes and signed cross terms are retained. F_C is a different source from F_P.

M=integral F, E=integral F², V=E-M²/V0, R=t²*M²/(2176*V0*V). If this exact source has the required modular spectral identification, the current pure-scalar kernel bounds Im K(t,0)>=t^11/2176 and Im K(t,-ell)>=-t^9 imply a positive lower bound when R>1, for t>=50. Numerical integration supplies neither that spectral identification nor a full SS/SV/VV original causal action, joint time/horizon/cusp limits, or extinction. These are source-component measurements, not an RH discriminator. The critical-line samples are cached ordinates, while t=50 is a nonzero spectral control.

| height | R_P(H=1) | R_P(H=4) | R_C(H=1) | R_C(H=4) |
|---|---|---|---|---|
| control-50 | 0.145961525 | 0.466861080 | 0.003980709 | 0.436168346 |
| zero-24 | 0.818067595 | 1.312868245 | 0.007623374 | 0.992759293 |

At zero24, principal subtraction changes from a failed coarse bound at H=1 to a successful one at H=4. Full constant-Fourier subtraction reaches0.992759 at H=4 and remains below one at all33 sampled H values. Both sources fail the bound at t=50 on that grid. The sampled maxima occur at H=4; this is not a global maximum or a proof on the full interval.

The experiment crossed33 logarithmically spaced H values from1 to4, two Fourier margins, two Gaussian resolutions and50/100/160-digit source evaluation. The energy increment retains2*a0²*Q, so it is not a principal-only energy approximation. Maximum relative-or-unit-scaled variant difference6.84e-14; exact principal-mean increment check error1.33e-16; direct finite-convolution increment check error9.1e-159. Independent pointwise integration of the entire source at H=4, for both heights and source definitions, agrees within2.21e-15, bypassing the increment formula. Double quadrature nodes and finite tails remain uncertified accuracy limits; no rigorous positivity enclosure is claimed.

Consequence: a cutoff convention can change whether an existing coarse scalar estimate is useful. This is not a mechanism choosing the actual HB source or enforcing extinction. Positive salvage is a quantitative way to test the literal smooth residual rather than a favorable threshold. Next test is the corpus transition over2<y<3, with other channels and spectral assembly still explicit missing work.

Recorded guarded execution: 189.018s, including independent validation; recorded worker tasks: 2555.410s. The supplemental validation followed a preparation gap, excluded from the execution sum. Consequently the staged run did not enforce the original protocol's ten-minute uninterrupted wall-span interpretation. New families use one guard. Original download checksums passed; owned process groups cleaned. No builds.
