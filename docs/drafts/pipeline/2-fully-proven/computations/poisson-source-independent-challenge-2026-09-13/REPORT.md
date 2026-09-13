# Independent source validation of four positive Poisson candidates

All eight checks completed. The four q41 moment-relaxed sources were evaluated at190 digits using the original theta integral with explicit pole contribution:

X_a(t)=a0/2−(1/4+t²) integral_0^infinity [theta_a(exp(2x))−a0] exp(x/2) cos(tx) dx.

The derivative retains both the derivative of the prefactor and the sine integral. Two independently generated Gauss-Legendre rules,64 nodes on32 panels and96 nodes on40 panels, cover[0,5]. The longer source interval is essential at period41; the discovery interval[0,4] was insufficient for160-digit tail control. The finite coefficient vector is inherited at160 digits, so its rounded Fourier symmetry also limits independent agreement.

The fine-rule maximum scaled F/F_t residual is 3.17e-146; nearby nonzero anchors agree with the Hurwitz representation within 3.17e-146. The coarser rule agrees to about137 digits at worst. This validates the numerical candidates well beyond50/100-digit screening, without asserting190 correct digits or a rigorous interval certificate. All second derivatives were recomputed through high-precision Hurwitz jets in the preceding run and are nonzero. Coefficient positivity survives high-precision equality correction; exact original closed-box endpoints are not certified.

The original adaptive worker failure was an implementation failure, not evidence against the source. This successful representation change salvages the four candidates without changing their parameters. It does not validate the failed full-moment hypothesis or HB physics. Guard wall time 4.132s, recorded worker time 22.349s, no builds. Original downloads checksum-verified.
