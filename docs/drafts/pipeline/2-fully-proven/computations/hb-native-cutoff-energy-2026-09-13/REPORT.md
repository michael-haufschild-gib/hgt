# Literal smooth cutoff preserves the two observed scalar margins

Use S=E*(z,1/2+it)/abs(Lambda(1+2it)), a0 its constant Fourier term, and Q=mean_x(S-a0)^2. The native principal source is F=S²-chi*a0² with chi=smoothTransition(y-2). Up to a nonzero constant normalization this is the current scalar half-square residual on the modular cell; such normalization does not change R. The alternative C source subtracts chi*(a0²+Q) and is not identified as the original residual. Integrate M=integral F,E=integral F² with hyperbolic area, V=E-M²/(pi/3), R=t²*M²/(2176*(pi/3)*V).

| t | native P | early P | late P | native C |
|---|---|---|---|---|
| control-50 | 0.349601330 | 0.338292434 | 0.360063659 | 0.262559869 |
| zero-24 | 1.123171044 | 1.109424674 | 1.136442374 | 0.661458896 |
| zero-64 | 4.061487086 | 4.013592783 | 4.108083771 | 2.124467861 |

The literal native cutoff gives R>1 at ordinates24 and64; same-endpoint early/late profiles do not reverse those two margins. The t50 control fails the coarse sufficient bound. At ordinate64 even the full constant-Fourier subtraction has R>1 with this smooth cutoff, unlike H=1. This settles the defined finite source-profile comparison; it does not imply that all source choices work.

All18 precision/resolution variants, six profiles, two subtraction choices and three heights completed in225.546s under one guard. Maximum relative-or-unit-scaled variant difference0.000978; independent source-convolution identity error1.82e-158. Separately computed full-domain pointwise source integrals at160-digit Bessel precision agree within4.26e-15; this bypasses cutoff-increment and convolution methods. Gaussian nodes and final pointwise accumulation are double; no interval/tail proof or160-digit integral accuracy claimed.

Current source definitions retain both Weyl terms, full Fourier remainder, compact area and all cross terms. This is an L² source observable: it does not compute derivative action, remaining SS/SV/VV coupling, original time/horizon/corner faces, or the needed spectral-source realization. Positive scalar margin is neither extinction nor RH. User has redirected further work away from estimate optimization; this family is closed to further constant/profile refinement. Positive residue: use the literal source rather than an arbitrary favorable sharp cutoff when interpreting this component.

Raw packets, frozen protocol, source hashes, exact package versions and verified original download manifest retained. Recorded worker tasks3082.772s. No Lean builds.
