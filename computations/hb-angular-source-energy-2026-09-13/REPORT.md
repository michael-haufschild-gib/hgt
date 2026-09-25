# Finite Eisenstein source weight versus fluctuations

The real normalized series is S(z)=E*(z,1/2+it)/abs(Lambda(1+2it)), where Lambda(s)=pi^(-s/2)*Gamma(s/2)*zeta(s). Its principal term is a0(y)=2*sqrt(y)*cos(arg Lambda(1+2it)+t*log y), and Q(y) is the x-mean of (S-a0)^2. Integration uses the standard modular cell |x|<=1/2, x²+y²>=1 and measure dx*dy/y², of volume V0=pi/3. For a subtraction threshold H, F_P=S²-1_(y>H)*a0²; F_C=S²-1_(y>H)*(a0²+Q). The complete square, compact curved boundary, native Fourier modes and signed cross terms are retained. F_C is a different source from F_P.

M=integral F, E=integral F², V=E-M²/V0, R=t²*M²/(2176*V0*V). If this exact source has the required modular spectral identification, the current pure-scalar kernel bounds Im K(t,0)>=t^11/2176 and Im K(t,-ell)>=-t^9 imply a positive lower bound when R>1, for t>=50. Numerical integration supplies neither that spectral identification nor a full SS/SV/VV original causal action, joint time/horizon/cusp limits, or extinction. These are source-component measurements, not an RH discriminator. The critical-line samples are cached ordinates, while t=50 is a nonzero spectral control.

All results below use H=1.

| t | source | M | E | R |
|---|---|---|---|---|
| 50.000000000 | principal | 2.913521396 | 71.910408118 | 0.145961525 |
| 50.000000000 | constant_fourier | 0.471472399 | 61.476160733 | 0.003980709 |
| 87.425274613 | principal | 9.977512081 | 503.234670502 | 0.818067595 |
| 87.425274613 | constant_fourier | 0.941380841 | 390.761283643 | 0.007623374 |
| 169.911976479 | principal | 11.131829079 | 635.997132573 | 3.032809492 |
| 169.911976479 | constant_fourier | 0.861552034 | 491.438667671 | 0.019163773 |

Principal-only subtraction meets the coarse sufficient bound at zero64, but fails at t=50 and zero24. Removing the entire constant Fourier mode reduces the mean strongly and fails that bound at all three heights. This identifies subtraction convention as a consequential input to this scalar estimate. It does not establish an eventual-height law or the native-source estimate: current source inspection locates the literal smooth transition at heights2..3, which requires its own computation.

Validation: all18 variants finished, crossing two Fourier margins, two quadrature resolutions and50/100/160-digit special-function evaluation/accumulation. Maximum relative-or-unit-scaled variant difference 1.02e-14. Independent shifted-contour Bessel errors, normalized by abs(Lambda), were at most6.14e-142. An independent pointwise angular integration at zero64 bypassed the Fourier-convolution energy formula and agreed within5.45e-14. The latter uses double accumulation. Gaussian nodes originated NumPy doubles and the Fourier/y domains are finite;160-digit working precision is not a160-digit integral certificate. Reporting about nine digits is conservative relative to observed discretization agreement, not a rigorous error bound.

A cheap Maass–Selberg normalization check includes sin(2 arg Lambda)/t in the H=1 principal mean; omitting that retained boundary oscillation changes the check. It is an implementation identity, not a new theorem. No source term or boundary face of a complete physical action was silently set to zero; that full action was not computed.

Positive survivor: explicitly measured mean/variance budgets and a source-normalization check. Next discriminating test: use the source's literal smooth cutoff and compare equal-germ transition changes; do not select a favorable sharp H as a physical assumption.

Recorded guarded execution across pilot, parallel quadrature, zero64 extension and pointwise validation: 527.391s; recorded worker tasks: 6719.770s. Preparation gaps are excluded from this sum; separate stages were not one uninterrupted wall-clock run. The original protocol's whole-family wording therefore overstates wall-span compliance, although summed guarded execution and each owned cleanup stay below600s. Future new families use a single guard. All original downloaded checksum manifests passed; code, inputs, raw packets and original manifests retained. No Lean builds.
