# HB: native cusp data in the physical inverse

Stage: 1-in-progress. Native cusp transport and cutoff-subtracted angular L² admission are [formalized and audited](../3-formalized/hb-native-cusp-transport.md). The native height-power circle equals the actual physical Gauss kernel in Lean, including the full-source three-channel expansion. Its original forced integral is a [strongly continuous L² family](../3-formalized/hb-native-forced-integral.md), with exact causal support and Dirichlet trace. The actual response now satisfies its [forced Goursat, mixed null-derivative and whole-line retarded Duhamel equations](../3-formalized/hb-native-source-equation.md). The original native integrals now [equal the existing physical L² responses in all three principal channels](../3-formalized/hb-native-physical-identification.md). The [full native kernel Goursat equation and causal Dirichlet decomposition](../3-formalized/hb-native-goursat-integral.md) are also proved. The integrated full source now has its [actual angular derivative interchange, forced null-wave equation and Dirichlet boundary](../3-formalized/hb-full-native-forced-wave.md) in Lean. The [exact native joint cutoff energy identity](../3-formalized/hb-native-joint-energy.md) now holds in the original product measure, with actual chart derivatives and proved product integrability. The [global native gradient energy and exact source-response identity](../3-formalized/hb-native-global-energy.md) are now formalized and audited. Native form-domain admission remains open. Equality of the complete angular causal evolutions and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains cancellation of `2 Omega(B(p,p)/2,B(m,m)/2)` with all physical boundary currents and independent tensor amplitudes. The [full-source growth result](hb-full-source-terminal-decay.md) supplies a Laplace overlap `max(kappa,3/2)<Re w<2`. The present conjecture is that the native inverse and the constructed physical response have identical cusp data, so their remaining difference can be placed in the original wave domain and killed by causal uniqueness. A convergence chamber alone does not identify the inverses.

## Exact native cusp transport

Use the actual principal exponents and amplitudes already defined in `ThetaCuspHawkingBMJointSourcePrincipalData`:

```
(alpha_0,alpha_1,alpha_2)=(2rho,1,2-2rho),
(A_0,A_1,A_2)=(a^2/2,ab,b^2/2),
Q(z)=sum_i A_i y^(alpha_i)+R(z),
R=(full scalar^2-full principal^2)/2.
```

Every inverse-height weight of `R` is bounded above any fixed positive height, uniformly in horizontal position, by `weighted_squareRemainder_bounded`. Put

```
D(d,theta)=cosh d-sinh d cos theta,
P_alpha(d)=average_theta D(d,theta)^(-alpha).
```

The exact original circle height is `Y/D`. Positivity of both factors fixes the complex powers without a branch choice. Linearity of the finite normalized integral gives

```
M_(cosh d)Q(X+iY)
 =sum_i A_i Y^(alpha_i) P_(alpha_i)(d)
   +average_theta R(circle(d,theta;X,Y)).               (1)
```

The cross term `alpha_1=1` and both completed coefficients remain in (1). No Legendre identification is assumed in defining `P_alpha`: it is the native circle integral of the actual height monomial. Its radial equation, derived by applying the circle polar identity to that monomial, is

```
P_alpha''+coth(d)P_alpha'=alpha(alpha-1)P_alpha,
P_alpha(0)=1, P_alpha'(0)=0.
```

This identifies the required principal radial equation analytically. The direct integral transformation below now identifies its Gauss-series normalization in Lean; the original expansion (1) also remains available independently.

For `d>=0`, `exp(-d)<=D<=exp(d)`. If `Y>=exp(d)`, every original circle height is at least one. For every natural `N`, the actual weighted remainder bound then gives

```
|M_(cosh d)Q(X+iY)-sum_i A_i Y^(alpha_i)P_(alpha_i)(d)|
 <= C_(q,N) exp(Nd)/Y^N.                               (2)
```

The constant is independent of `d,X,Y` in the displayed region. Thus all three cusp coefficients are transported explicitly, and the full remaining circle source is rapidly decaying in height at each bounded radius. Equation (2) retains its joint radius/height dependence; it is not a bound uniform in an unrestricted expanding radius.

For each fixed nonnegative `d`, subtract precisely the original cutoff times the transported principal sum. The difference is continuous. On the compact truncated modular cell `Y<=3+exp(d)` it is bounded by compactness. Above that height the cutoff equals one, and (2) with `N=0` bounds the difference by a constant. The original modular measure is finite, so this actual difference belongs to its L² space. This proves value admission, not membership in the joint operator's derivative graph.

## Formal principal-kernel identification

For finite `d>=0`, put `r=tanh(d/2)` and `a=(cosh(d)+1)/2`. Then `0<=r<1` and

```
D(d,theta)=a(1-r exp(i theta))(1-r exp(-i theta)).
```

Both complex factors lie in the open right half-plane. Their principal logarithms sum to the real logarithm of their positive product. Consequently, their powers with the same complex exponent `-alpha` multiply to the actual positive-height power used in `powerCircle`.

Write `c_n=(alpha)_n/n!`. The power series `B(z)=sum_n c_n z^n` converges absolutely and uniformly on every closed disk of radius less than one: its coefficient recurrence bounds `|c_(n+1)|` by `(n+|alpha|)/(n+1)|c_n|`. Termwise differentiation gives `(1-z)B'=alpha B`, with `B(0)=1`. Multiplication by `(1-z)^alpha` gives a function with zero derivative and value one, proving `B(z)=(1-z)^(-alpha)` on the unit disk. This also covers terminating parameters.

The two series on the circle therefore converge absolutely and uniformly. Their double series can be integrated term by term. The normalized integral of `exp(i(n-m)theta)` is zero unless `n=m`, when it is one. Thus

```
P_alpha(d)=a^(-alpha) sum_n ((alpha)_n/n!)^2 r^(2n)
          =a^(-alpha) 2F1(alpha,alpha;1;r^2)
          =legendreKernel(-alpha,cosh(d)).             (3)
```

The final equality uses the actual `BMCausalRiemannKernel` definition: its argument is `(Z-1)/(Z+1)=r^2`, prefactor is `((Z+1)/2)^nu`, and upper parameters are `-nu,-nu`. Both coefficient factors retain the same complex `alpha`; the diagonal coefficient is a square, not a squared norm. Since `(-alpha)(-alpha+1)=alpha(alpha-1)`, (3) has exactly the potential coefficient of the existing principal wave channel. No reflection identity in the degree is needed.

`ThetaCuspHawkingBMNativeCircleGauss.powerCircle_eq_legendre` proves (3) for every complex `alpha` and every real `d`, including zero and negative radii. The formal proof uses `r=sinh(d)/(cosh(d)+1)` and proves `|r|<1` directly. `mean_cusp_expansion_legendre` inserts that exact kernel into all three original cusp channels while retaining the entire signed Fourier remainder. Absolute summability, integral interchange, diagonal coefficient equality and complex logarithm branches are all proved. The [audit](../3-formalized/hb-native-circle-gauss.md) concerns these two public theorems.

## Quantitative principal-response comparison

The integral representation gives, analytically, for `d>=0`,

```
|legendreKernel(-alpha,cosh(d))| <= exp(|Re alpha| d).
```

Indeed, the positive circle height lies in `[exp(-d),exp(d)]`, and its complex power has magnitude `height^(Re alpha)`. Averaging preserves the uniform bound. On a static causal cone, `d=arcosh(Z)<=h`, so the Riemann kernel obeys the same bound with `h` in place of `d`. If `K_alpha(h)` denotes its whole-line retarded spatial integral with factor `1/2`, each integration interval has length `2h`. The Schur estimate therefore gives

```
||K_alpha(h)||_(L² -> L²) <= h exp(|Re alpha| h), h>=0.
```

For all three actual exponents, `0<Re alpha_i<=kappa<2`. The original forcing vectors decay as `C exp(-c tau)` for any fixed `0<c<2`, using `timeRadialSourceVector_bound` and the bounded original odd extension. Their native causal convolutions consequently satisfy

```
||U_i(tau)|| <= C tau exp(kappa tau)/(kappa+c), tau>=0.
```

This admits their Laplace transforms for `Re w>kappa`, independently of the large potential norm used in `principalResponseGrowth`. The bound is a paper consequence of the kernel identity, not yet a Lean norm-bound theorem. The exact equality with `principalTimeResponse` is now formalized, so this paper bound applies to that same response.

The finite-time identification is now proved through the exact integral equation. The scalar native formula passes to its actual L² class; the zero-mass propagator is identified with the spatial interval integral and converted to the original free mass `2*pi`. This gives the precise physical Volterra equation without requiring a separate H² argument. The proof below includes zero frequency and every source time.

## Formal native forced integral

Use the actual endpoint zero to define its continuous odd representative by

```
F(s,a,tau,x)=b(s,a,tau,min(x,0))-b(s,a,tau,min(-x,0)).
```

For `x<=0` this equals the original coefficient; for `x>=0` it equals its negative reflection. It is odd, jointly continuous, and zero for `|x|>max(tau,0)` by the original onset. This replaces the earlier generic concern about a jump at the endpoint with an exact property of this source.

Put `T=max(tau,0)` and `h=T(1-r)`. The native forced integral can be written over a fixed rectangle as

```
U_nu(s,a,tau,x)=T^2/2 integral_0^1 (1-r) integral_-1^1
 R_nu(h,x,x+h z) F(s,a,T r,x+h z) dz dr.
```

All arguments lie on the original causal cone. The affine changes `sigma=T r`, `y=x+h z` give precisely the original retarded double integral, including both Jacobians. For continuity proofs only, the kernel is extended off this rectangle using `legendreKernel(nu,max(1,Z))`; it equals the original kernel at every integrated point. Continuous compact parameter integration gives joint continuity. The support implication `|x|<=h+|y|<=T` gives compact spatial support at each time and a common support on compact time intervals.

These facts are proved in `ThetaCuspHawkingBMNativeForcedIntegral`. `radialResponse_retarded` identifies the fixed-rectangle definition with `1/2 integral_0^T integral_(x-(T-sigma))^(x+(T-sigma)) R_nu(T-sigma,x,y) F(s,a,sigma,y) dy dsigma`. `radialResponse_memLp` constructs its actual L² vector. `radialResponseVector_continuous` proves strong norm continuity using a common compact support and bound on each bounded time interval. Reflection of the full kernel and source gives `radialResponse_odd` and its zero endpoint trace. `principalForcing_ae_oddSource` proves that the integrand, including its original amplitude, is the existing `principalTimeForcing` in the L² quotient. `nativePrincipalResponse` uses degree `-principalExponent q i` and the original physical rate and amplitude in all three channels. The scalar source equations are proved for every complex degree, rate and source amplitude. `nativePrincipalResponse_eq_principalTimeResponse` now identifies the actual L² responses in all three physical channels.

## Causal characteristic integral equation

The forced comparison has a proved rectangular form. Put `p=tau+x`, `q=tau-x`, `a=sigma+y`, `b=sigma-y`. The original forcing support `|y|<=sigma` and the retarded cone together give exactly `0<=a<=p`, `0<=b<=q`; the source Jacobian is `d sigma d y=da db/2`. The null-coordinate formula for the already constructed response is

```
U(p,q)=1/4 integral_0^p integral_0^q R(p,q;a,b) F(a,b) db da,
R(p,q;a,b)=R_nu((p+q-a-b)/2,(p-q)/2,(a-b)/2),
F(a,b)=oddSource(s,a_source,(a+b)/2,(a-b)/2).
```

The kernel identity below becomes `R(p,q;a,b)=1+1/4 integral_a^p integral_b^q V(c,d) R(c,d;a,b) dd dc`, with `V(c,d)=nu(nu+1)sech²((c-d)/2)`. Reversing the two triangular integration orders gives `U=1/4 integral integral (F+V U)`. `ThetaCuspHawkingBMNativeSourceEquation.radialResponse_goursat` proves this identity for the actual response at every `p,q>=0`. The private coordinate proof uses the actual determinant `-1/2`, exact cone intersection and compact integrability of the fully coupled four-variable kernel. `radialResponse_null_wave` applies FTC twice and proves `partial_q partial_p U=(F+V U)/4` for `p,q>0`, with Lean's actual iterated derivative. Pure second static derivatives and H² admission are not asserted by this theorem.

`radialResponse_freeDuhamel` changes coordinates back for the continuous effective source `F+V U` and proves the exact scalar equation `U=D0(F+V U)` for every nonnegative time and every spatial point. Outside the source cone the entire effective source vanishes on the retarded interval; characteristic points are included. The [three-theorem audit](../3-formalized/hb-native-source-equation.md) covers these actual-object identities.

The finite characteristic identity is now proved in Lean. In null coordinates `h=(u+v)/2`, `x=y+(u-v)/2`, the actual Gauss kernel satisfies

```
R_nu(u,v;y)=1+(1/4) integral_0^u integral_0^v
  nu(nu+1) sech^2(y+(a-b)/2) R_nu(a,b;y) db da,
  u,v>=0.
```

Both characteristic values are exactly one. The mixed derivative is the actual potential times the kernel divided by four. `ThetaCuspHawkingBMCausalGoursat.riemannKernel_goursat` proves the displayed equation for the original static kernel at every `CausalPoint` and every complex degree. The [targeted audit](../3-formalized/hb-causal-goursat-integral.md) covers these two public theorems. `dirichletCausalKernel_volterra` proves the exact physical direct-minus-image decomposition into the free causal term and potential corrections, with both support cutoffs and the original factor one half. Two applications of the fundamental theorem of calculus give this formula with the source vertex retained. Its integration against the original forcing and the required scalar integral interchange are now proved in `ThetaCuspHawkingBMNativeSourceEquation`. The resulting native response is now identified with the existing massive L² evolution by the exact mass-conversion argument below.

The source normalization can be checked analytically before a distribution formalization. Write `u=h+x-y`, `v=h-x+y` and `G=H(u)H(v)R/2`. The mixed derivative of the product has the vertex term `delta(u)delta(v)R(0,0)`, two edge terms containing `R_u(u,0)` and `R_v(0,v)`, and the interior term. The characteristic values are constant one, so both edge terms vanish and the vertex coefficient is one. Since `partial_h^2-partial_x^2=4 partial_u partial_v` and `delta(u)delta(v)=delta(h)delta(x-y)/2`, the factor `1/2` in `G` gives exactly `(wave-V)G=delta(h)delta(x-y)`. The image gives the same identity with `y` replaced by `-y`; on the original negative half-line its source point lies outside the domain. Their difference therefore has the original unit source and Dirichlet trace. This distribution identity is a paper consequence, not yet a Lean theorem.

## Formal physical principal identification

`ThetaCuspHawkingBMNativePhysicalIdentification.nativePrincipalResponse_eq_principalTimeResponse` proves equality of the entire native and constructed principal response functions for every original zero copy, branch, source amplitude and `i : Fin 3`. It assumes no inverse identification or additional source equation. The [four-theorem audit](../3-formalized/hb-native-physical-identification.md) includes the exact propagator identities used in its proof.

Let `S0(t)` be the Fourier multiplier `t*sinc(2*pi*t*xi)`, with its continuous value `t` at zero frequency, and let `Sm=unitWaveSine`, with `m=2*pi`. The actual translation/Fourier identity and symmetric exponential integral prove

```
S0(T)f=(1/2) integral_-T^T translateL2(t)f dt,
S0(T)f=Sm(T)f+m^2 integral_0^T Sm(T-t)S0(t)f dt, T>=0.
```

The second formula follows from a scalar sine/cosine Wronskian and the exact squared-frequency difference `m^2`. Multiplier integration is proved by Fubini against arbitrary L² inner-product test vectors. The zero-frequency endpoint is included. A separate representative argument passes continuous scalar families through their L² Bochner integrals using the actual squared-norm integrals. For the compactly supported native source, the first formula therefore gives the original spatial interval integral almost everywhere.

The causal triangle interchange then proves, for every continuous L² source,

```
D0 F=Dm F+m^2 Dm(D0 F).
```

The previously proved native scalar equation gives `U=D0 G` in the actual L² quotient, where `G=F+P U-m^2 U` and `P=m^2+alpha(alpha-1)sech²(x)` is the existing principal potential operator. The proof identifies its representative with the original forcing plus the original native potential term. Substitution and linearity give `U=Dm F+Dm(P U)`. The original zero onset supplies the same identity at negative times. `principalTimeResponse_unique` now proves the principal-channel equality. No distribution identity, H² admission, computation or assumed propagator equivalence is used to close this step.

## Formal full-source kernel integral

`ThetaCuspHawkingBMNativeGoursat.nativeRiemannKernel_goursat` now proves the closed-cone equation for the complete native theta-source kernel. Write `R(u,v)=nativeRiemannKernel q ((u+v)/2) (y+(u-v)/2) y X k` and `Delta=exp(2k) partial_X²+partial_k²-partial_k`. Then

```
R(u,v)=fullSquarePotential q ![X,exp(k)]
       +integral_0^u integral_0^v Delta R(a,b)/(4*cosh(y+(a-b)/2)^2) db da,
u,v>=0.
```

The proof uses the actual full-source Darboux equation and literal invariant derivatives in the open quadrant. At the characteristic, the interior angular derivative tends to half the full source Laplacian and the tangent invariant derivative tends to zero. FTC with that limit, followed by FTC with the original source value on the other axis, gives the displayed identity. It includes both zero-length edges. A private continuous extension is removed on every integrated point; no endpoint value is assigned by evaluating a singular quotient there.

`nativeDirichletCausalKernel_volterra` retains the original direct-minus-image kernel, both causal supports and the factor one half. Its free impulse multiplies the complete theta half-square, and its correction is the direct-minus-image integral of the full angular action. The [two-theorem audit](../3-formalized/hb-native-goursat-integral.md) covers these identities. Their integration against the original radial forcing on the null source rectangle and the actual angular derivative interchange are now proved in `ThetaCuspHawkingBMFullNativeWave`. The cutoff residual's actual null-coordinate forcing equation and Dirichlet boundary are proved in the same module; joint-space admission and inverse identification remain open.

## Exact residual forcing to compare

For `d>0`, let `L_d=partial_d^2+coth(d)partial_d`, and let `P(d,z)` denote the full three-term transported principal sum. The native mean satisfies `(L_d-Delta)M=0`; the monomial equations give `(L_d-Delta)P=0`. For the original cutoff `chi`, product differentiation gives

```
(L_d-Delta)(M-chi P)
  =sum_i A_i P_(alpha_i)(d) cutoffCommutator(alpha_i,z).
```

The commutator is precisely the existing `Delta(chi Y^alpha)-chi alpha(alpha-1)Y^alpha`. Its support lies in the original height collar `2<=Y<=3`.

The same identity after the causal radial source integration has a useful exact form. Put `c(x)=1-radialUnit(x)^2` and let `b(tau,x)` be the original `timeReducedCoefficient`. If `V` is the native response to `b Q` and `U_i` its three principal causal coefficients, define `V_res=V-chi sum_i U_i Y^(alpha_i)`. Direct application of `partial_tau^2-partial_x^2-c(x)Delta` gives

```
wave(V_res)=b squareResidual
            +c(x) sum_i U_i cutoffCommutator(alpha_i).
```

This is exactly the source shape already constructed in `causalCuspSourceVector` and `principalCutoffTimeVector`. The native `U_i` now equal `principalTimeResponse`, so the principal coefficients in this comparison are exactly the constructed ones. The actual null-coordinate residual equation and its closed-rectangle integral form are now proved by `fullNullResidual_wave` and `fullNullResidual_goursat`; joint-space admission and the weak operator comparison remain open.

For fixed circle radius bounded by `T`, there is also a direct derivative estimate. At the image point `(X',Y')`, the basepoint invariant derivatives pull back as

```
Y partial_X -> D Y' partial_(X'),
Y partial_Y -> sinh(d) sin(theta) Y' partial_(X')+Y' partial_(Y').
```

The coefficients are bounded for `d<=T`. Repeated application gives finite combinations of invariant source derivatives with bounded coefficients. The actual Fourier family is closed under differentiation by `value_hasFDerivAt`, and every shifted family has every height-weight bound by `weighted_value_bounded`. Products with the finitely many principal powers preserve this property. Hence every fixed invariant derivative of the full remainder in (2) is rapidly decaying for bounded `d`; this is a paper consequence of the cited family theorems. Deriving the required time/radial derivative bounds for the causal integral and constructing its joint core approximation are still outstanding.

## Physical comparison to complete

In static tortoise coordinates the native invariant is

```
Z(h,x,y)=(cosh h+sinh x sinh y)/(cosh x cosh y).
```

On either original causal cone, `1<=Z<=cosh h`. The upper bound follows from `sinh x sinh y<=cosh x cosh y-1`, itself `cosh(x-y)>=1`; the reflected source gives the same inequality. Therefore each angular circle radius is at most the static delay. At time bounded by `T`, (2) controls all circles in the source integral above height `exp(T)`.

The constructed principal channels solve the original one-dimensional potential equation with exactly `alpha_i(alpha_i-1)` and the original reduced forcing, by `principalTimeResponse_wave_graph`. The fixed lift and differentiated onset remain in `timeOriginalForcing_gradient_absorption`. The native principal integrals now equal these channels. After subtracting their original modular cutoff, the remaining comparison must prove the native residual belongs to `jointDomain`, has the required modular side identifications and Dirichlet trace at zero, and solves the same forced wave as `causalJointForcedResponse` with zero initial data. The corpus's `jointEnergyOperator_core` proves differential action on the separated compact core; membership of this unseparated native response has not been supplied by that theorem.

The searches for finite propagation and wave uniqueness were inspected in declarations and proof-method views. Existing `WaveL2Uniqueness` controls smooth real Euclidean waves with a bounded potential and explicit slice/derivative/dominating bounds. Its hypotheses do not directly cover the complex radial/modular joint wave. Its energy method is useful, but it is not an already proved identification. Generated circle-mean ingredient groups concern holomorphic Euclidean means and do not establish the hyperbolic height-power identity.

The broad binomial/circle/hypergeometric search found `Mathlib.Analysis.Analytic.Binomial`. Its actual `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero` supplies the unit-disk complex-power expansion used in (3); `binomialSeries_radius_ge_one` includes terminating parameters. The formal integral proof uses the norm-summable product theorem and `integral_tsum_of_summable_integral_norm`, then proves the diagonal Gauss coefficient equality. Broad Hadamard and deep circle-product searches also retrieved matrix products, Cauchy coefficients and the norm-square Gutzmer argument; these did not supply the required complex bilinear identity. The Duhamel search retrieved the actual `principalTimeResponse_unique` and its exact integral equation, whose source was inspected. Searches inventoried 55,958 files, with incomplete semantic coverage and predominantly source-only compiler metadata; generated ingredient groups were not accepted as proofs.

The broad `Goursat` search found `ClockGoursatIntegralForm`, `ClockGoursatGlobal`, `ClockGoursatMixed`, and `WuGoursatEnergy`. Their source proofs were inspected. They concern real local/clamped solutions or bounded real Volterra data; the new proof instead differentiates and integrates the already fixed complex Gauss kernel on its entire closed forward cone. The broad OR/deep `Volterra Duhamel perturbation` search recovered the original `principalTimeResponse_unique` and several actual mild-wave constructions. Its proposed ingredient groups still require the exact source-vector integral equation. The `dAlembert` and deep retarded-source/rectangle searches did not supply the missing impulse theorem. All returned incomplete semantic coverage with mostly source-only compiler metadata; no generated group was treated as a proof.

The broad `Schur` and deep integral-operator searches found bounded functional-field operators, rather than an immediately applicable construction for this moving cone. The deep compact-support/L²-continuity search found `continuous_toLp_two_of_dominated`, whose source proof and hypotheses were inspected and used in the new leaf. The `reciprocity` intake and deep full-current search found modular side/arc cancellation and conditional retarded–advanced identities; their displayed premises do not supply the complete HB cancellation. Broad OR `dAlembert sine translation` and deep weak-wave searches found the existing smooth real wave uniqueness and the original principal Laplace weak equation. Their generated ingredient groups did not prove the native source equation. These searches inventoried 55,966 files, with incomplete semantic coverage, 48 compiled snapshots, 43 stale snapshots and predominantly source-only compiler metadata. Candidate statements and source-argument views were checked; applicability of the ingredients used in the new leaf was verified by Lean.

Broad Fubini/retarded searches and deep triangle/change-of-variable searches supplied compact integration and triangle-interchange proof methods. The exact four-variable interchange was built because the retrieved triangle lemmas used separated profiles. Mathlib's actual interval-integral swap and Jacobian theorem were verified in the new leaf. Broad OR and deep free/massive-Duhamel searches recovered scalar oscillator and massive propagator identities, but their generated ingredient group did not prove the required free-operator conversion. Search inventoried 55,969 files with incomplete semantic coverage, 48 compiled snapshots and 43 stale snapshots. Candidate and source-argument views were inspected; no generated group was accepted as a proof.

The broad sinc/convolution/shifted-frequency and deep interval-Fourier/Bochner searches supplied the exact sine, translation and Fubini ingredients used in the physical identification. The strict shifted-frequency parameter theorem did not cover zero mass; the Wronskian proof includes that endpoint. The generated L²-representative group was incomplete, and the required inner-product interchange was built. The final deep search inventoried 55,972 files with incomplete semantic coverage, 48 compiled snapshots and 43 stale snapshots. Candidate statements and source arguments were inspected; the new exact-object equality passed Lean.

The remaining inverse comparison concerns the full angular residual. After it is identified, the complete physical current pairing still has to be evaluated.

## Analytical candidate: remove the radial warp before uniqueness

The literal wave operator now gives a concrete alternative comparison mechanism. Let `c(x)=cosh(x)`, put `U=c(x) Phi`, and define

```
Delta_3 Phi=partial_x^2 Phi+2 tanh(x) partial_x Phi
            +sech(x)^2 Delta_H2 Phi.
```

Direct product differentiation, using `c''=c` and `c'/c=tanh(x)`, gives the exact analytical identity

```
(partial_tau^2-partial_x^2-sech(x)^2 Delta_H2) U
 =c(x) (partial_tau^2-Delta_3-1) Phi.
```

A second explicit substitution is `T=exp(tau)` and `psi(T,x,z)=T^(-1) Phi(log(T),x,z)`. For the differential expression

```
Box_cone=-partial_T^2-3/T partial_T+T^(-2) Delta_3,
```

the chain rule gives `Box_cone psi=T^(-3)(-partial_tau^2+Delta_3+1)Phi`. Thus the original wave equation transforms to `Box_cone psi=-F/(c(x) T^3)`. These are paper identities derived from the actual operator; they are not yet Lean theorems.

The next conjecture is that local causal uniqueness for this cone operator identifies the native residual with the constructed physical response after matching their weak equations. This requires proving the relevant weak regularity and boundary identifications; the displayed substitutions alone do not supply uniqueness. Radial reflection is compatible with the transformation because `cosh(x)` is even. The half-line Dirichlet trace, modular quotient and all physical current terms remain required. Broad Milne and Huygens/Kirchhoff search results did not supply this uniqueness statement; their semantic coverage was incomplete. This candidate has not been used in any formal proof or asserted to imply extinction.

## Formal full-source forced field

For fixed nonnegative null endpoints `p,r`, integrate the original full kernel against the original odd source:

```
U(p,r;X,k)=1/4 integral_0^p integral_0^r
  K((p+r-a-b)/2,(p-r)/2,(a-b)/2;X,k)
  oddSource(s,amplitude,(a+b)/2,(a-b)/2) db da.
```

`ThetaCuspHawkingBMFullNativeWave.fullNullResponse_wave` proves the actual differentiated equation

```
partial_r partial_p U
 =oddSource(s,amplitude,(p+r)/2,(p-r)/2) Q(X,k)/4
  +Delta_H2 U/(4 cosh((p-r)/2)^2),  p,r>0.
```

Proof: continuous angular derivatives of the complete smooth circle source permit two differentiations under each compact source integral using `hasDerivAt_parametric_intervalIntegral`; then the full-kernel Goursat identity and four-variable causal interchange give a double primitive of the displayed right side. FTC differentiates that primitive. The `max(1,Z)` extension is used only for global continuity and agrees with the actual kernel everywhere in the source rectangle. The proof uses no angular eigenfunction replacement or supplied field equation. `fullNullResponse_native` removes the extension on the full closed rectangle; `fullNullResponse_goursat` proves the integral equation with the actual angular derivatives; `fullNullResponse_boundary` gives the Dirichlet value `U(p,p)=0` by kernel reflection and odd-source cancellation. The [four-theorem audit](../3-formalized/hb-full-native-forced-wave.md) is complete. The exact cutoff-residual equation is also proved, as described below. Its identification with the constructed joint evolution and full physical-current cancellation remain open.

## Next conjecture: uniqueness through the bounded unit-frequency resolvent

The deep uniqueness search recovered the actual bounded-inverse energy mechanism in `KleinGordonStrongUniqueness`; its Euclidean Fourier operator is not the joint operator. The joint corpus supplies a concrete replacement: `J=jointEmbedding` is contractive and has dense range (`jointEmbedding_dense`). The actual `waveFormOperator J 1` is the identity, so `waveSpatialResolvent J 1=J J*` by its definition. Put `B=J J*`.

For a continuous joint-L2 difference `u` with zero initial data, form `W(t)=integral_0^t (t-s)u(s) ds`, so `W''=u`. The next target is the actual time-integrated weak identity

```
B u(t)+(I-B)W(t)=0.
```

It is not yet established for the native residual. Once established, it has a direct paper uniqueness proof: `E=norm(J* W')^2+norm(W)^2-norm(J* W)^2` is nonnegative because `J*` is contractive. Its derivative equals `2 Re inner(W',B W''+(I-B)W)=0`. Zero initial data give `E=0`, hence `J* W'=0`. Density of `J` makes `J*` injective, so `W'=0`, then `W=0` and `u=0`. This argument needs no second time derivative of `u` and no bounded inverse of `B`.

Joint-L2 continuity of the literal cutoff residual is now proved in `ThetaCuspHawkingBMNativeResidualAdmission`, including the original onset and characteristic edges. The literal residual now also has a globally modular representative with full germ agreement on every closed-cell chart, proved in `ThetaCuspHawkingBMNativeModularTransport`. The unresolved mathematical work is the displayed bounded-resolvent identity from the actual field equation, cusp estimates and Dirichlet boundary. In particular, `jointDomain` is the closure of the first-derivative energy graph; L2 membership, modular germ compatibility and an interior mixed-null equation do not yet supply its form-domain admission. Those are construction obligations, not hypotheses supplied to a proposed RH proof. The Milne/cone conjugation remains another analytical candidate; no uniqueness or extinction conclusion has been claimed from either substitution alone.


## Formal native cutoff-residual equation

In `ThetaCuspHawkingBMFullNativeWave`, put

```
P_i(p,r)=A_i radialResponse(-alpha_i,s,amplitude,(p+r)/2,(p-r)/2),
V=fullNullResponse-sum_i P_i cutoffPower(alpha_i),
F=oddSource(s,amplitude,(p+r)/2,(p-r)/2).
```

The closed theorem `fullNullResidual_wave` proves

```
partial_r partial_p V
 =squareResidual F/4
  +(Delta_H2 V+sum_i P_i cutoffCommutator(alpha_i))
    /(4 cosh((p-r)/2)^2),  p,r>0.
```

The proof subtracts the actual principal Goursat equations from the full-source equation, identifies every angular derivative of the difference and differentiates the resulting double primitive. `cutoffCommutator_height` and `principalSquare_expansion` cancel the exact eigenvalue terms while retaining all three Weyl amplitudes. `fullNullResidual_goursat` retains the closed rectangle including both characteristic edges. `fullNullResidual_boundary` proves `V(p,p)=0`. At the physical rate, `principalNullResponse_physical_ae` identifies these coefficients with the original `principalTimeResponse` in the actual radial L2 measure. The [four-new-theorem audit](../3-formalized/hb-native-cutoff-residual-wave.md) is complete.

This closes the residual forcing equation in null coordinates. The joint-L2 realization and continuity are also closed below. The actual joint operator identity, a global static-coordinate classical equation across characteristics, and complete physical-current extinction remain open.

## Formal uniform bounded-time joint L2 admission

For null endpoints in a bounded interval and source points in their rectangles, continuity of `nullRadius` on the enclosing compact box gives a common finite radius bound `D`. The literal circle/principal kernel equality expresses the cutoff residual as the integral of `nativeCutoffResidual` against the source. Above height `3+exp(D)`, `cuspMeanRemainder_rapid_bound q 0` bounds its kernel uniformly. Below that height, joint continuity on the truncated modular cell gives another common bound. The source and rectangle area are bounded on the same parameter box. The original radial support then supplies a bounded radial interval on each bounded time interval.

These estimates now give the proved majorant `B_T indicator[-T,T](x)` in the original product `radialMeasure.prod D4BMModularCore.measure`, where the radial measure is restricted to `x<0`. `fullNullResidual_eq_nativeResidualIntegral` identifies the literal residual with this bounded source integral for all real null endpoints. On the source-cone exterior and characteristic edges both expressions vanish; the endpoint argument uses continuity of the actual odd source, not an imposed boundary value. `nativeJointResidualField_memLp` constructs membership at every real time. `nativeJointResidual_continuous` applies the deep-search ingredient `continuous_toLp_two_of_dominated` locally in time. `nativeJointResidual_original_ae` retains the original field representative, and `nativeJointResidual_zero_of_nonpos` proves zero before and at onset. The seven-theorem leaf and the exact scalar null-integral formula are documented in the [joint-admission report](../3-formalized/hb-native-residual-joint-admission.md).

No uniform bound in unbounded time is claimed. Modular compatibility is closed below. Membership in the joint energy form domain and the bounded-resolvent weak identity still require their actual proofs.

## Formal source-faithful modular circle transport

`ThetaCuspHawkingBMNativeModularTransport` proves the original circle source changes by one fixed angular shift under a modular transformation (`source_modular_shift`). The shift depends on the base point and transformation; it is independent of radius and integration angle. `mean_modular` then proves invariance of the original normalized angular integral for every real radius.

Broad rotation/stabilizer/spherical search recovered the actual `realSphericalKCircleEquiv`, `realSphericalRotation` and its addition law in the principal-series corpus. With the canonical section and `sectionCocycle_identity`, the new proof identifies the literal chart as

```
circle(d,theta,z)=z.toSL2R k(theta/2) (i exp(d)),
k(phi)=[[cos(phi),-sin(phi)],[sin(phi),cos(phi)]].
```

The double-angle identity matches the original positive horizontal offset and height denominator exactly. The section cocycle is a rotation, so acting on the chart changes `theta` by a constant. The original source's modular invariance then applies pointwise. `Function.Periodic.intervalIntegral_add_eq` proves shift invariance of its actual integral over one period. The normalization `1/(2*pi)` is unchanged; no replacement Haar measure is introduced.

`fullNullResponse_modular` passes this identity through the original causal source integrals for all real null endpoints. Broad cutoff/boundary search then recovered the stronger full-germ gluing mechanism in `SquareResidualModular` and `CellGermExtension`. On translation overlaps every original cutoff power is unchanged. On all other closed-cell overlaps, `nonparabolic_cell_overlap_low` puts both charts strictly below height two, where the complete cutoff subtraction vanishes on a neighborhood. Thus `fullNullResidual_cell_compatible` proves full germ compatibility, including elliptic corners.

`globalNativeResidual` is the resulting globally invariant extension. `globalNativeResidual_germ` retains the original residual on a neighborhood of every closed-cell point; `globalNativeResidual_eq_on_fd` gives exact values there. `nativeJointResidual_global_ae` identifies this global representative with the previously constructed strongly continuous vector in the original joint L2 measure. The [eight-theorem audit](../3-formalized/hb-native-modular-transport.md) is complete. Germ agreement preserves any existing derivatives; it does not by itself assert new differentiability or energy-domain membership.

## Formal native time-primitive elliptic equation

`nativeResidualTimePrimitive q s amplitude t x X k` is the literal integral `W(t)=integral_0^t (t-u)V(u+x,u-x;X,k) du`. The [four-theorem extension](../3-formalized/hb-native-time-primitive-elliptic-equation.md) proves, for all real coordinates,

```
(-partial_x^2-sech(x)^2 Delta_H) W(t)
 = integral_0^t (t-u) nativeResidualStaticForcing(u) du-V(t+x,t-x),
partial_t^2 W=V(t+x,t-x),
W(t,0)=0.
```

`nativeResidualStaticForcing` retains the original `squareResidual * oddSource` and all three principal coefficients multiplying their original cutoff commutators. The source cone, including both characteristic edges, supplies the zero initial terms. A change of variables in the weighted first-null-derivative integral supplies the second spatial derivative without assuming pure second null derivatives of `V`. The original angular jets pass through the bounded time integral, giving the actual angular action on `W`. This closes the pointwise elliptic equation for the literal native primitive; energy-domain admission and the comparison with the constructed joint evolution remain open.

## Next conjecture: admit the time primitive through its elliptic equation

For the continuous joint-L2 difference `u`, the bounded-resolvent argument only needs form admission of `W(t)=integral_0^t (t-s)u(s) ds`. The refined construction target is the weak elliptic identity `A W=-u`, where `A` is the actual radial/modular positive spatial operator, together with the original Dirichlet trace and the now-proved modular germ compatibility. It is not necessary to begin by proving an energy bound for every time derivative of `u`.

The candidate local estimate comes from testing that actual elliptic identity with `eta^2 W` and taking real parts:

```
integral eta^2 |grad_A W|^2
 <= 2 norm(u)_2 norm(W)_2 + 4 integral |grad_A eta|^2 |W|^2.
```

Here the gradient uses the original radial derivative and the two angular derivatives weighted by `sech(x)` in the original product measure. Boundary cancellation must use the actual zero Dirichlet value, not a supplied trace assumption. Modular cusp cutoffs and radial cutoffs would then bound the approximating energy graphs. A weak limit in the closed Hilbert graph would give the required member of `jointDomain`. This estimate, the admissible testing step and the limit argument are construction targets, not installed results.

The corpus already contains `RadialEnergyFamily.graph_mem`: every smooth compact radial family valued in the original angular energy domain belongs to the original joint domain, proved by finite Hilbert-basis approximation. Its premises require an actual smooth angular-energy-valued field with compact support strictly inside `x<0`; it cannot yet be applied directly to the native time primitive at the Dirichlet boundary. The remaining proof must construct those approximants or an equally valid graph-admission argument and derive `B u+(I-B)W=0` for the actual fields.

## Native elliptic energy construction

The direct construction uses the actual primitive before subtracting the physical response. Fix `q,s,a,t`, write `W` for `nativeResidualTimePrimitive` and put

```
G(x,z) = integral_0^t (t-u) nativeResidualStaticForcing(q,s,a,u,x,z) du
         - fullNullResidual(q,s,a,t+x,t-x,z).
```

The exact equation is `A W=G`, for `A=-partial_x^2-sech(x)^2 Delta_H`. All norms and integrals below use `dx dmu_fd`, on `x<0` and the original modular cell. The three principal cutoff commutators remain in `G`.

The analytical argument to formalize is the following. It separates the local Green identity, which needs no global energy assumption, from the global limit.

1. **Finite radial support and literal trace.** The source-cone identity makes `W(t,x,z)=0` whenever `max(t,0)<=abs(x)`. For negative time the whole time integral vanishes. For nonnegative time, each integration point has one nonpositive null coordinate outside this radial interval. The exact Dirichlet theorem gives `W(t,0,z)=0`. Thus radial integration over `[-max(t,0)-1,0]` has zero endpoint product `conj(W) W_x` at both ends. This step and the resulting exact radial Green and positive energy identities are [formalized and audited](../3-formalized/hb-native-primitive-radial-energy.md), including actual derivative existence and interval integrability.
2. **Actual L2 right-hand side.** This step is [formalized and audited](../3-formalized/hb-native-elliptic-l2-localization.md). The common bounded-time native residual majorant gives `W` in the original joint L2 space. The actual integrated forcing is exactly a finite sum of separated products: the time primitive of the odd source times `squareResidual`, and all three integrated principal response coefficients times their original `cutoffCommutator`. Each radial coefficient is continuous with finite causal support, hence is in radial L2. The original angular admission theorems then give the complete integrated forcing in joint L2, and subtraction of the native residual gives `G` in joint L2. The statements hold for every real time and arbitrary complex source parameters. No Laplace convergence chamber is required.
3. **Local Green step.** Let `eta_N=modularCuspCutoff N`, with `N>=1`. Its local profile is one below height `2N`, zero above `3N`, and its hyperbolic gradient is uniformly bounded by a constant `C_eta`. Joint angular smoothness of the actual primitive, its uniform modular germs, its smooth global extension, and compact angular integration by parts are [formalized and audited](../3-formalized/hb-native-angular-green.md). For `N=n+1`, the new theorem proves integrability of both pairings and `integral frameEnergy(W,eta_N^2 W)=-integral conj(Delta_H W) eta_N^2 W`. Its proof applies the existing core Green identity to `eta_(3N) W` and `eta_N^2 W`, then removes the outer cutoff through equality of actual germs. It assumes no global gradient energy or native joint-domain admission. All seams and elliptic corners remain included. The [joint construction](../3-formalized/hb-native-joint-energy.md) now also proves the actual original frame derivatives and chart Laplacian: `D_0 W=y W_X`, `D_1 W=W_k`, and `Delta_H W=y^2 W_XX+W_kk-W_k`. These identities hold on the complete closed cell and identify the coordinate elliptic equation with the original modular operator. Step 4 supplies their joint integration.

4. **Exact localization, then global energy.** Completing the square gives a sharper construction. For each fixed radial coordinate, the actual angular identity is [formalized and audited](../3-formalized/hb-native-elliptic-l2-localization.md):

   ```
   integral_fd abs(grad_H(eta_N W))^2
     = -Re integral_fd conj(Delta_H W) eta_N^2 W
       + integral_fd abs(W grad_H eta_N)^2.
   ```

   Both the cutoff energy and its nonnegative error are integrable. The proof retains both product-rule contributions and recombines their real cross terms using the existing native compact Green identity. The error also has an unconditional joint-space limit: both `integral abs(W grad_H eta_N)^2` and the exact physically weighted integral with `sech(x)^2` tend to zero. The scale-independent cutoff derivative bound dominates the error by `C_eta^2 abs(W)^2`; native L2 admission justifies dominated convergence for this error alone.

   The [exact joint identity is formalized and audited](../3-formalized/hb-native-joint-energy.md). Both cutoff gradient energies and the complete forcing pairing are integrable in the original product measure:

   ```
   F_N = Re integral eta_N^2 conj(W) G + error_N,
   F_N = integral (abs(partial_x(eta_N W))^2
                    + sech(x)^2 abs(grad_H(eta_N W))^2),
   error_N = integral sech(x)^2 abs(W grad_H eta_N)^2 -> 0.
   ```

   Lean states the real forcing pairing as `Re integral conj(G) eta_N^2 W`, which equals the displayed real pairing since `eta_N` is real. The [global limit is formalized and audited](../3-formalized/hb-native-global-energy.md). The integrable majorant `abs(G)^2+abs(W)^2` gives convergence of the complete forcing pairings, so the exact cutoff identity and vanishing error give `F_N -> L = Re integral conj(G) W` before any global gradient admission.

   Let `E = abs(W_x)^2+sech(x)^2 abs(grad_H W)^2`, let `f_N` be the cutoff energy density, and let `e_N` be its physically weighted error density. Full cutoff-germ stabilization gives `f_N -> E` pointwise on the original cell. Fatou first proves finite integrability and `integral E <= L`. The product rule gives `f_N <= 2E+2e_N`. A second Fatou pass on `2E+2e_N-f_N` yields `integral E <= 2 integral E-L`; hence

   ```
   integral (abs(W_x)^2+sech(x)^2 abs(grad_H W)^2)
     = Re integral conj(G) W.
   ```

   Joint integrability, radial/angular interchange, the complete pairing limit, global gradient integrability and the exact global identity are closed in Lean. No mixed-derivative or global-energy premise is assumed. The next obligation is convergence in the original first-derivative graph. Dominated convergence can now control `(eta_N-1) grad(W)`, while the established error limit controls `W grad(eta_N)`.

5. **Approximate in the first-derivative graph.** First prove convergence of cusp cutoffs with their actual gradients using the new global energy and the existing error limit. For each fixed cusp cutoff and radius, `nativeTimePrimitiveCutoff` is already an angular `CoreField`. Its jointly continuous value and frame jets on compact angular support should give a continuous radial family in the completed angular energy space. Its trace at `x=0` is zero. Zero-extend this Hilbert-valued family, shift it toward negative `x`, then mollify at a smaller radial scale. The resulting family is smooth in the angular energy space and supported strictly inside `x<0`. The original angular value embedding must send its radial derivative to the mollification of the zero-extended actual `W_x`; integration by parts and the zero trace give this without mixed spatial derivatives. Prove convergence in all original graph slots and use `RadialEnergyFamily.graph_mem`. Separate angular smoothing is unnecessary because the actual cutoff fields already have angular smoothness and invariance. These approximation and convergence statements remain construction targets.

6. **Identify the actual operator.** Once the first-gradient norm convergence is proved, extend the compact-test Green identity through it. If `J` is the original joint embedding, its Riesz identity is `W_graph=J.adjoint(W+G)`. Hence `W=J(J.adjoint(W+G))` and the actual Friedrichs operator `I+A` acts on `W` as `W+G`. This is the domain statement needed by the bounded-resolvent comparison.

Status: radial and compact angular Green identities, actual joint-L2 admission of `W` and complete elliptic forcing, original chart/frame identities, joint pure-jet continuity, the exact joint cutoff energy identity with product integrability, both joint cutoff-error limits, the complete forcing-pairing limit, finite global native gradient energy and the exact global energy identity are closed in Lean. Native graph approximation and admission, operator identification, complete physical-current cancellation and RH remain open. The next construction is radial mollification of the already available angular core family, with convergence of the original first-derivative graph.


Own broad literature queries `capacity` and `compactness` were tested. The arXiv `capacity` endpoint returned HTTP 429. [Fernandez, 2609.10064, 9 September 2026](https://arxiv.org/html/2609.10064v1) keeps state and derivative together in an evolution graph when terminal atoms matter; its compact embedding hypotheses do not supply this native graph admission. [Cheng--Lin--Wang, 2609.10098, 9 September 2026](https://arxiv.org/html/2609.10098v1), Appendix D, realizes natural boundary conditions through closed forms in a rotating-star problem. The transferable question is which boundary condition the approximating form actually retains; its stellar estimates do not prove the HB cutoff estimate. Corpus deep/method searches returned relevant existing Sobolev and graph constructions, but their proposed ingredient groups did not establish the native estimate; source-only compiler metadata was not treated as verification.
