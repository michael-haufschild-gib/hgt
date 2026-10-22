# HB cusp spectrum and causal continuation

Stage: in progress. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The actual modular energy operator is `T=1-Delta_H`. Its inverse at each physical
Xi parameter is proved, but identification with the continued retarded response
is open. With doubled time rate `w=2s`, its shift is
`1-(w+1)(w+2)`. On `Re(w)=-3/2` this equals `5/4+Im(w)^2`.
This algebra alone proves neither membership in the actual spectrum nor an
obstruction to continuation of the actual source response.

The actual modular cusp family is constructed in Lean. In logarithmic height,
`f_L(t)=exp(i*tau*t)*eta((t-R_L)/L)`, where `L>0` and
`R_L=log(2)+2L+1`. Its inverse transform lies in the original operator domain.
With `A_j=integral eta^(j)(x)^2 dx`, the exact native squared norms are
`L*A_0` and `4*tau²*A_1/L+A_2/L³` for the packet and shifted residual.
The real cutoff derivatives make the mixed term vanish exactly, and `A_0>0`
is proved from the actual window. Explicit normalization with `L=n+1` gives
unit vectors whose original operator residual tends to zero. Consequently,
no bounded left inverse exists at any real `lambda>=5/4`, including the
endpoint. The same exclusion holds at the displayed doubled-time shifts.
[Proof and audit](../../../3-formalized/hb-native-cusp-spectral-ray.md).

The subsequent causal identification must derive the original retarded parameter
domain and continuation prescription using the full source projection below. Even a proved
spectral crossing would not by itself show that the original forcing sees it.
Any homogeneous cusp radiation correction must be retained in the physical metric
and left-QNM pairing. Gauge, remaining response sectors and clock extinction are
still open. No numerical experiment is needed for these symbolic identities.

The exact operator-domain and norm transfer for every compact smooth log-height
test is now constructed in Lean: `U` preserves the original native pairing and
`(T-lambda)U f=U((5/4-lambda)f-f'')`. Both U and the transformed test are actual
constructions. Full modular periodization cancels the horizontal window
derivatives exactly. The inverse height transform is smooth through zero and
has compact support strictly inside the cusp. Proof and audit status:
[native cusp operator intertwining](../../../3-formalized/hb-native-cusp-operator-intertwining.md).

Current live step: derive the original retarded continuation prescription and its
source-dependent global scattering coefficient, then determine their effect on the
physical response and left-QNM pairing. The squared scalar remainder retains both
principal–tail and tail–tail interactions; removing the two principal Weyl
powers does not justify discarding its constant Fourier component or the
cutoff derivatives. The continued source response must be identified from an
actual causal convergence chamber. The real-ray obstruction alone does not
identify that response, its continuation sheet or any required homogeneous
radiation correction. Frontier map is read-only.

The actual width-one cusp mean of the full complex squared source is proved in
Lean. At positive height y, put
`a_N(u,y)=coefficient(u,0,N)*sqrt(y)*K_u(2*pi*(N+1)*y)`.
Both `sum_N ||a_N||` and `sum_N ||a_N^2||` converge. The literal signed tail obeys
`mean(tail)=0` and `mean(squareRemainder)=8*sum_N a_N^2`, with no conjugation.
Above height three, `mean(forcing)=4*parameter*sum_N a_N^2`. At every positive
height, with C the original cutoff response at x=0 and P the two-power principal
part, the exact mean is
`(parameter/2)*(P^2+8*sum_N a_N^2)-(y^2*C''-parameter*C)`.
The native pairing with every constructed cusp test h is exactly its height
integral against `conj(h(y))/y^2`. This supplies the original operator's full
constant source projection, including the cutoff region. No positivity or
nonvanishing of the complex sum is assumed.

The original homogeneous cusp equation has powers `y^(w+2)` and `y^(-w-1)`.
Their native squared-norm densities are integrable at infinity exactly when
`Re(w)<-3/2` and `Re(w)>-3/2`, respectively; neither is integrable on the
threshold line. Both actual Xi branches have `-4<Re(w)<-2`, independently of
RH, so only the first displayed branch has finite cusp mass there. This does
not show which branch is selected by continued retarded propagation or prove
that the forced response has a nonzero coefficient of either branch.
[Exact source projection and indicial audit](../../../3-formalized/hb-native-cusp-source-projection.md).

The remaining hard step is to derive the original causal convergence chamber,
continue its full forced response, and determine any resulting homogeneous cusp
coefficient with the compact modular contribution retained. The derived cusp
mean alone does not replace that global scattering coefficient. It must then be
inserted into the actual metric and left-QNM pairing before any extinction claim.

The actual globally smooth native energy response h now has a proved cusp
mean m satisfying its literal equation `y^2*m''-L*m=Fbar`. Differentiation under
the width-one integral is justified on compact positive-height rectangles.
The original modular translation cancels the horizontal second derivative.
The full global source equals the previously derived literal mean above height
two, including all cutoff derivatives.

For roots a=w+2 and b=-w-1, put
`J_p(y)=y^p*m'(y)-p*y^(p-1)*m(y)` and `g_p(y)=y^(p-2)*Fbar(y)`.
Both actual fluxes satisfy `J_p'=g_p`. Arbitrary complex-power bounds for the
entire signed tail prove `|g_p(y)|<=C/y^2` above height three, without positivity
of the complex squared source. Thus both infinite source moments converge and
`J_p` tends to the constructed value
`J_p(4)+integral_(4,infinity) g_p`. This retains the actual boundary jet of the
global modular solution.

With d=b-a, let A=-lim(J_b)/d and B=lim(J_a)/d. The actual response is exactly
`m(y)=A*y^a+B*y^b+(y^a*integral_(y,infinity)g_b-y^b*integral_(y,infinity)g_a)/d`
for y>3. The gap d is nonzero at every Xi occurrence, and the actual dominant
coefficient satisfies `m(y)/y^b -> B`. These statements are proved in Lean.
[Native response coefficients and audit](../../../3-formalized/hb-native-cusp-response-coefficients.md).

The original native norm now selects the actual coefficient B=0 in Lean.
The full cusp rectangle inherits the global square-integrable norm with its
original density 1/y². Width-one Cauchy–Schwarz transfers this bound to m.
If B were nonzero, the proved limit m/y^b→B and Re(b)>1 would force a positive
constant lower bound for ||m||²/y² on an infinite tail. Thus ell_a=0 and
`J_a(y)=-integral_(y,infinity)g_a`. Exact reconstruction keeps A and both
source-tail integrals. A retains the global boundary jet and has not been
proved zero or nonzero. This energy-domain selection holds at every Xi
occurrence; it gives no further zero-location restriction.

The original frequency family must also retain the radial and tensor terms.
For fixed physical rate v=2s, original mixed stream P and current C, the full
master at independent frequency w obeys
`M_w=2*C-(w²-v²)*r²/(r²-1)*P`. Its complete radial derivative retains
`-2*r/(r²-1)²*P`. The actual radial Einstein component introduces an additional
term proportional to `(w-v)*C`, because reconstruction uses w outside the
master. All sixteen components of this exact frequency defect are identified
with the original cosmological Einstein metric-jet pencil in Lean.
The source, actual angular derivatives and both radial profiles remain visible.
[Native energy selection and full frequency transport](../../../3-formalized/hb-native-energy-selection-and-frequency-transport.md).

The original normalized stream psi=H/r now has its actual time-evolution
operator in Lean. With f=r²-1 and original tortoise coordinate x'(r)=1/f,
`partial_t²-D_x²` includes the differentiated radial coefficient, and the
full normalized mixed source is exactly `-2*f*C/r³`. The angular slot remains
the original rough Laplacian plus its curvature term.

The full original mixed current has the proved factorization
`C(t,r,z)=exp(v*(t+x(r)))*C0(r,z)` at fixed physical source rate v=2s.
One fixed smooth onset chi(t+x(r)) is constructed for every Xi occurrence.
Differentiating that current produces both required onset tensor blocks,
`chi'*C/r²` and `chi'*C/(r²*f)`. The complete source vanishes before onset and
equals the original literal tensor after its fixed transition interval.

The actual smoothly switched current has an absolutely convergent static-time
Laplace transform for Re(w)>0, with source rate and angular data held fixed.
It equals `N(w)/(w-v)`, where N is explicitly entire and
`N(v)=C(t=0,r,z)`. The compact onset correction is entire, so this regularized
source coefficient is retained exactly. No nonvanishing or extinction is
assumed. [Original wave equation and ingoing source continuation](../../../3-formalized/hb-original-wave-and-ingoing-source-continuation.md).

The live hard step is the full original retarded inverse and its physical
spatial domain for this source, including radial endpoints, global modular
cusp terms and the remaining source constraints. The proved transform is a
time integral at fixed geometry, not spatial admission or a continued inverse.
The source extension is constructed in the current sector; admission to the
full nonlinear problem remains separate. Existing reduced radial Green actions
must be identified with this operator, independent frequency and complete
source before use. Continue the actual response, determine its cusp coefficient
and any change from native B=0, then insert the complete response into the
original left-QNM pairing. Independent extinction and RH remain open.
Frontier map is read-only.
