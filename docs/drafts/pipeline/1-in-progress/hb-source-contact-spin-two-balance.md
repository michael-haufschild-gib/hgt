# HB: the retained spin-two contact and its angular Green balance

Status: the literal pointwise contact balance, all six actual quartic principal expansions, their physical Green flux and original cutoff-Mellin contact are closed in Lean. The original quartic residual now has an actual modular core and a certified native physical Green limit, with both outer-cutoff errors removed and all original Mellin contacts retained. The full contact balance now transports through those native physical periods, giving the exact JRQ period reduction below. Attachment to the complete nonlinear physical action remains open. No extinction or RH theorem is claimed.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → original common Hawking-clock extinction → RH.

Latest closed attachment: the original incoming radial response work has an exact
full scalar-tested cusp mean, with both actual native response coefficients and
all three tested remainders retained. Their admission is proved in the
[radial response cusp-pair leaf](../3-formalized/hb-radial-response-cusp-pair.md).
The remaining height periods and complete-action boundary cancellation stay open.

The [physical response Mellin transport](../3-formalized/hb-radial-response-mellin-transport.md)
now evaluates the finite-height response portions through actual endpoint
Wronskians and complete source moments. All six original physical testing gaps
are independently nonzero. Infinite-height finite parts and the other current
faces remain open.

The [native cusp-current trace](../3-formalized/hb-native-cusp-current-trace.md)
now derives rapid upper-trace vanishing of both native bilinear response
remainders from the original forced equations and admitted gradient energies.
The source-cell flux retains the exact original mean product. The
[complete response-current attachment](../3-formalized/hb-full-response-cusp-current.md)
now includes both original cusp particular solutions and decomposes the
complete incoming current into its full-mean flux, all three exact source
contacts and a remainder that vanishes under every complex height power.
The original physical scalar principal factor preserves that zero remainder.
[The full scalar-tested current](hb-physical-tested-centered-current.md),
mean/contact boundary cancellation and complete-action faces remain open;
fixed-clock extinction is not asserted.

The preceding [source-contact rigidity theorem](../3-formalized/hb-source-contact-differential-rigidity.md) controls the literal contact two-jet. This continuation tests its contribution to the actual retained radial face, rather than replacing that face by a square-source self-pairing. It also records why two positivity mechanisms found in recent literature do not yet apply.

## Literal contact, including spin two

Write rho for the actual Xi occurrence, lambda=rho(rho-1), f for its complete theta scalar, Q=f²/2, and Delta for the original hyperbolic Laplacian. All products and gradient pairings below are complex bilinear. Put

```
c = 7lambda-2,
J = (c Q-2 Delta Q)/8,
R Q = -Delta(Delta-2)Q,
Gamma(J,J) = y²[(partial_x J)²+(partial_y J)²],
a = c(c-4)/96,
H = 2J²+a Q².
```

The original radial characteristic face really contains `J RQ`. In `ThetaCuspHawkingBMCommonSourceGreen.lean`, `thetaAngularCoupling` multiplies the displayed contact by `thetaSpinTwo`; the latter retains both angular Laplacians. The radial trace also carries exp(-k) in logarithmic height k. Thus exp(-k) dx dk = dx dy/y², exactly the hyperbolic measure used here. This check rules out silently replacing the spin-two trace by Q or changing its angular weight.

The source eigen-equation and its product rule give

```
Delta f = lambda f,
Delta Q = 2lambda Q+E,
E = grad f dot grad f,
Delta(Q²) = 4lambda Q²+6Q E,
24 QJ = (13lambda-6)Q²-Delta(Q²).                  (1)
```

For example, grad Q=f grad f, so the product rule yields the third line involving Delta(Q²). Substitution into J gives (1). This uses the complete field, not its principal part or an angular eigenvalue assigned to Q.

Next, the definition of J itself implies

```
RQ = 4 Delta J+2(c-4)J-c(c-4)Q/4.
```

Multiply by J, use Delta(J²)=2J Delta J+2Gamma(J,J), and then (1). The result is the source identity

```
J RQ = Delta H+2(c-4)J²-4Gamma(J,J)
       -a(13lambda-6)Q².                           (2)
```

No division by a field value, eigenvalue, source amplitude, or clock defect occurs. The previously formalized fourth-power Bochner identity is not required for this lower-order balance. In particular, it must not be advertised as a new consequence of that theorem.

## Finite angular domain and the actual angular QNM test

Let psi be either the constant test 1 or the actual angular fundamental-QNM field. Write Delta psi=mu psi; mu=0 in the constant case. For the same Xi target as source, the existing definitions give

```
chi = xiSpectralPoint(rho)/2+i/4,
i chi = rho/2-1/2,
psi = scalar(i chi),
mu = rho(rho-2)/4.
```

This follows by substituting xiSpectralPoint(rho)=(rho-1/2)(-i). The angular field is common to both fundamental radial frequencies. This is only the angular part of the physical left-QNM action.

Define the ordinary coordinate vector

```
B(psi,H) = (psi partial_x H-H partial_x psi,
            psi partial_y H-H partial_y psi).
```

The hyperbolic metric factors cancel exactly in Green's formula. Equation (2) becomes

```
psi J RQ / y²
 = psi[(2mu+2c-8)J²-4Gamma(J,J)
       -a(13lambda-6-mu)Q²]/y²
   + partial_x B_x+partial_y B_y.                  (3)
```

Integrating on a finite smooth angular region Omega therefore retains the boundary term

```
integral_boundaryOmega B(psi,H) dot n_E ds_E,
```

where n_E and ds_E are Euclidean normal and arclength. Equivalently this is the hyperbolic normal Green flux. It is not an extra factor of y or a changed measure.

On the standard modular fundamental domain cut at height Y>1, the vertical sides pair by translation and the two circular half-seams pair by inversion. The fields psi and H are modular scalars, so their Green fluxes cancel under those identifications with opposite outward orientations. Smooth finite corners carry no separate point mass. The remaining angular boundary is exactly

```
B_Y = integral_(-1/2)^(1/2)
        [psi(x,Y) partial_y H(x,Y)-H(x,Y) partial_y psi(x,Y)] dx.
```

Consequently the finite-cut identity is

```
integral_FY psi J RQ dmu
 = (2mu+2c-8) integral_FY psi J² dmu
   -4 integral_FY psi Gamma(J,J) dmu
   -a(13lambda-6-mu) integral_FY psi Q² dmu+B_Y.     (4)
```

This is a balance, not a claim that any finite-cut boundary vanishes. For independent Xi targets the same finite-cut formula uses that target's actual mu; the noncollision argument below is restricted to the same source and target.

## Explicit cusp flux and the proposed finite-part passage

Keep both original Weyl coefficients A and B of f:

```
f_0(y)=A y^rho+B y^(1-rho).
```

Let i run from 0 to 2, and j from 0 to 4. Define

```
r_i = 2-i+(2i-2)rho,
q_i = binom(2,i) A^i B^(2-i)/2,
j_i = [c-2r_i(r_i-1)] q_i/8,
k_j = 4-j+(2j-4)rho,
v_j = binom(4,j) A^j B^(4-j)/4,
h_j = 2 sum_(i+l=j) j_i j_l+a v_j.
```

Thus Q has principal part sum q_i y^r_i, J has principal part sum j_i y^r_i, and H has principal part sum h_j y^k_j. Every term omitted from these principal expressions contains at least one original Fourier tail or one of its derivatives. The corpus's derivative-stable weighted tail bounds provide the method for controlling those terms; the required quartic products and the integrated Green-flux remainder limit are now proved in the [cusp-jet extension](../3-formalized/hb-angular-cusp-jet-admission.md#quartic-contact-extension-11-september-2026).

For the actual same-occurrence angular test set eta=rho/2 and first display both of its Weyl coefficients C,D. Its principal part is C y^eta+D y^(1-eta). The full principal cusp flux before using the Xi equation is

```
sum_j h_j [C(k_j-eta)Y^(k_j+eta-1)
          +D(k_j-1+eta)Y^(k_j-eta)].               (5)
```

The ten exponents are, respectively,

```
k_j+eta-1 = 3-j+(2j-7/2)rho,
k_j-eta   = 4-j+(2j-9/2)rho.
```

Neither half-integer coefficient of rho vanishes for an integer j. Since actual rho has nonzero imaginary part, none of these exponents is zero. For the constant test psi=1 the five exponents k_j-1 are

```
3-4rho, 2-2rho, 1, 2rho, 4rho-1;
```

these are also nonzero. This noncollision test does not require either Weyl coefficient to vanish. There is no constant-power contribution to the flux in either case, and no logarithmic primitive is generated by these exponents.

The literal Xi equation supplies additional information, already proved in `ThetaCuspHawkingBMPhysicalAngularCutoffCalibration.lean`: `physicalScalar_principal` sets C=Lambda(rho)=0, and the reflected coefficient D=Lambda(rho-1) is nonzero. The latter follows by the completed functional equation from the zero-free region Re(2-rho)>1. Thus only the five D terms in (5) survive for the actual QNM test. The same module's `physicalScalar_cutoff_calibration` retains a nonzero cutoff pairing on one indicial branch. Killing the other Weyl coefficient is not total boundary extinction.

The proposed canonical angular finite part subtracts every displayed nonzero power, not just growing powers. With the derivative-tail remainder tending to zero, the finite part of B_Y is zero and (4) gives

```
FP integral psi J RQ dmu
 = (2mu+2c-8) FP integral psi J² dmu
   -4 FP integral psi Gamma(J,J) dmu
   -a(13lambda-6-mu) FP integral psi Q² dmu.         (6)
```

Equation (6) is the precise next angular integral theorem to formalize. A closed Lean result still needs finite-cut Green transport and explicit principal-power evaluation for these actual fields. The quartic derivative-tail estimates, regulated L²/L¹ admission and integrated principal-subtracted flux limit are now proved. The following calculation fixes the original cutoff convention as well; it does not discard its commutators or prove a zero complete physical cusp contribution.

## Matching the original cutoff without setting a contact to zero

Use exactly the existing cutoff chi(y)=smoothTransition(y-2). Its native Mellin continuation is

```
M(w)=3^w/w-integral_2^3 chi(y)y^(w-1)dy.
```

This is `nativeCutoffMellinContinuation`, not a new regulator. For a modular field P with principal part P0=sum p_j y^k_j and a rapidly decaying remainder, put

```
I(P)=integral_F psi(P-chi P0)dmu,
N(P)=I(P)-D sum_j p_j M(k_j-eta).                  (7)
```

Here psi is the actual same-occurrence test, so its principal part is D y^(1-eta). The ordinary integral in I is absolutely convergent once the original source's weighted remainder estimates are supplied. The Fourier mean of psi on the support of chi is exactly its displayed principal part. The finite-cut tail of the principal integral is

```
integral_2^Y chi(y)y^(w-1)dy=Y^w/w-M(w),  Y>=3.
```

Thus N agrees with subtracting all principal powers of the actual finite-domain pairing, including the sign in (7).

For each principal power define its actual cutoff commutator

```
C_k=Delta(chi y^k)-k(k-1)chi y^k.
```

The existing general theorem `cutoffPowerMoment_eq_gap_mul_nativeMellin` and the physical one-Weyl identity give

```
integral_F psi C_k dmu
 =D[k(k-1)-mu] M(k-eta),                           (8)
```

when k-eta is nonzero. This is the calculation behind the previously formalized three-power source correction. Every quartic k_j above obeys this noncollision condition; in fact both factors of k_j(k_j-1)-mu are nonzero. No zero cutoff integral is used.

Now Delta(P-chi P0) is rapidly decaying, and Green transport for this remainder has zero limiting cusp flux. Retaining (8) yields

```
I(Delta P)=mu I(P)+D sum_j p_j[k_j(k_j-1)-mu]M(k_j-eta).
```

Subtract the principal correction for Delta P, whose coefficients are p_j k_j(k_j-1). Exactly, term by term,

```
N(Delta P)=mu N(P).                               (9)
```

This proves the paper cancellation of the cutoff corrections in (6), with P=H. It is a commutator balance, not a rule dropping source-contact terms. Applying (7) to Q², J², Gamma(J,J) and JRQ gives the same original five-power completion on both sides. The source's derivative-stable square-remainder bounds supply the needed analytic method: Q²-Q0² is the sum of a squared rapid remainder and twice that remainder times Q0; J and RQ follow by actual angular differentiation. Full quartic admission is now formalized, including actual finite-height flux integrability and its integrated remainder limit. Green transport with the displayed principal and Mellin corrections remains to be proved before (9) is counted as a formalized source theorem.

## Why this does not produce extinction

The key contact coupling has not vanished: (6) expresses it through three actual quartic periods. Gamma(J,J) is not |grad J|², psi is complex, and the finite-part pairing is not a positive Hilbert-space norm. The multiplier is also source-dependent and complex; for the same-occurrence test,

```
13lambda-6-mu=(51rho²-50rho-24)/4.
```

Its real part is strictly negative throughout the open strip: writing rho=sigma+i tau gives

```
4 Re(13lambda-6-mu)
 =51sigma(sigma-1)+sigma-24-51tau² < -23.
```

This independently excludes annihilation of the Q² period by that multiplier. It supplies no sign for the period itself. The QJ projection from (1) likewise reduces to a nonzero multiplier times the quartic period after its own Green flux is transported.

Equations (1)-(3) require only the literal eigen-equation and product rules. They do not use the arithmetic condition Xi(rho)=0 beyond selecting parameters and their known domain. Hence their validity must not be mistaken for a mechanism that distinguishes off-line Xi occurrences from other nonreal Eisenstein parameters.

The physical target remains Cphys(q,n)=-Sigma(q,n)|D(q,n)|², Sigma>0. A source proof of Re Cphys>=0, or of -Re Cphys<=epsilon Sigma|D|² for a fixed epsilon<1, would force D=0. None of (1)-(6) yields that estimate. The remaining calculation must transport this contact balance through the actual causal pulse and left-current pairing, the ++ and +- correction grades, independent SS/SV/VV amplitudes, changing metric weights, and the oriented temporal, horizon, exterior, cusp, characteristic and source-contact terms. Different amplitude monomials cannot compensate each other coefficientwise without an additional source identity.

## Other conjectures tested and rejected as inferences

**Fixed Hawking clock implies a stationary-horizon extinction law.** The recent [black-hole jet paper, 2 September 2026](https://arxiv.org/html/2609.02742v1), Appendix B.4, uses an actual Killing horizon, invariant degenerate electromagnetic field and its positive null stress. Those are explicit inputs to its rigidity argument. They are not consequences of assigning a common clock to the HB perturbation.

For a real twist-free four-dimensional horizon, in a fixed parameter v with nonaffinity kappa, Raychaudhuri retains

```
partial_v theta=kappa theta-theta²/2-shear²-R_kk.
```

If p'= -kappa p, its integrated balance is

```
integral_(v0)^(v1) p(theta²/2+shear²+R_kk) dv
 =p(v0)theta(v0)-p(v1)theta(v1).
```

Neither expansion endpoint is forced to zero by the clock. With the changing area density m'=theta m, the corresponding density balance instead contains shear²+R_kk-theta²/2. Thus one must not drop expansion or freeze the metric weight to infer a nonnegative completed coefficient. This is an applicability test, not a formal HB horizon theorem or a change of its clock.

**Cutting and gluing produces positivity of the oriented action.** [Lanzetta-Moult-Wang, 3 September 2026](https://arxiv.org/html/2609.04041v1), equations (8)-(11), use reflection positivity and normalizable defect states. Their discussion also explains why inserting a sharp cusp on the reflection plane invalidates an immediate Cauchy-Schwarz step. No positive Hermitian realization of the HB pairing, with its cusp/contact subtraction and FE partner, has been proved. [Miller, 3 September 2026](https://arxiv.org/html/2609.03769v1), Sections 2-5, replaces a missing gluing operation by convex duality for positive density matrices and Hermitian inequalities; that domain is likewise not the present complex bilinear source pairing.

These papers were found through broad, date-sorted arXiv searches for virial and gluing. Local deep searches used source-contact/causal balances, horizon shear/translation, and the actual angular source projection with statement and proof-method views. Results had partial semantic coverage, and the last request reached its retrieval deadline. The returned cosmological `cyclicRaychaudhuri` is an algebraic model rather than the horizon equation; its source was checked and it was not imported as an HB result. The useful local hit was the actual `thetaAngularCoupling`, which fixed the retained density in (2).

## Next proof attempt

First formalize (6) using the original convention (7)-(9) and substitute it into the already constructed causal source face. Then evaluate the remaining original pulse cross terms together with the physical left-QNM current. If a real signed estimate is proposed, identify its conjugation, measure and all counterterms before claiming positivity. No isolated ring-identity leaf or conditional extinction receiver is installed for this paper calculation.


## Further method tests, 11 September 2026

**Commutator regularity supplies the missing sign. Failed as an inference.** [Liang, 10 September 2026](https://arxiv.org/html/2609.11488v1) controls anisotropic Onsager commutators using an existing viscous quadratic form and regularity. HB now has the needed literal derivative regularity for these quartic angular expressions, but regularity does not identify its complex bilinear action with that positive form. [Crin-Barat, Shou and Zhu, 10 September 2026](https://arxiv.org/html/2609.11329v1) obtain decay from entropy and Shizuta–Kawashima coupling for partially dissipative systems. Those structures and their coupling condition are not supplied by declaring the Hawking clock, and long-time decay is not extinction at that clock.

**A symmetric/skew decomposition forces extinction. Not established.** [Guo and Huang, 8 September 2026](https://arxiv.org/html/2609.09599v1) use a stationary-state positive information metric and a commutator correction to relaxation curvature. Its Cauchy bound requires identified dissipative and skew operators in that metric; it does not provide the strict HB absorption coefficient below one. [Camacho et al., 10 September 2026](https://arxiv.org/html/2609.11577v1) obtain temporal localisation from explicit non-Hermitian symmetries and a switch between different topological phases. Their localisation means growth followed by a finite interval of decrease, and can be followed by renewed growth. It is not fixed-clock vanishing; the symmetry and phase-switch hypotheses are also absent from the literal nonlinear HB source equations.

**The corpus's positive Ward detector identifies the HB action. Not established.** Full-corpus deep/method search found `finiteRankCutoffWardForm_self_eq_hsNormSq` in `HTGeometry/FiniteRankCutoffWardTrace.lean`. Its diagonal pairing is exactly the squared Hilbert–Schmidt norm of a cutoff commutator. The actual HB left-current pairing has not been represented by that diagonal form. FE reflection sends rho to 1-rho, while conjugation sends rho to conjugate(rho); identifying those parameters would already require Re(rho)=1/2. No such identification is used here. The same search found `forwardTranslationBoundary_eq_projection_commutator` in `RHTower/XiThetaBoundaryCoboundary.lean`: translation of a fixed truncation retains its moving-window commutator. Its exact cocycle law does not say the boundary itself is zero, and this logarithmic source translation is not automatically the physical Hawking-clock action.

Focused searches covered quartic Green admission, strict source absorption, and integrated cusp-flux limits. After the user requested broader corpus use, unfiltered hybrid/deep searches covered uniform integral limits, smoothness-order conversion, and positive-commutator coercivity, with statement and proof-method views. The useful cross-route limit method was `tendsto_xiMassBottomArchIntegral_comoving_zero`: bound the actual integral uniformly and pass the bound to zero. Its mass-dependent extinction assertion is not imported into HB. The corpus's scalar-envelope sharpness theorem also confirms that a strict absorption margin must come from a proved signed estimate, not retuning a bound's constant. The searches reported complete source inventory in one snapshot but partial retrieval/filtering and pending compiler coverage. These results are not exhaustive nonexistence claims.


## Paper constraint on a self-adjointness shortcut

For the actual same-occurrence angular test, eta=rho/2 and the literal Xi equation gives the horizontal mean `D y^(1-eta)`, with D nonzero. Let sigma=Re(rho), so 0<sigma<1. Cauchy–Schwarz on the horizontal interval of length one gives

```
integral_(-1/2)^(1/2) |psi(x,y)|² dx
 >= |integral_(-1/2)^(1/2) psi(x,y) dx|²
 = |D|² y^(2-sigma).
```

The cusp part of its squared norm in the original measure is therefore bounded below by `|D|² integral_3^infinity y^(-sigma)dy`, which diverges. The full physical test is not in angular L². This paper deduction uses the actual one-Weyl calibration and Fourier mean, and no RH assumption; it is not claimed as a new Lean theorem here.

Subtracting its principal term gives `psi_reg=psi-chi D y^(1-eta)`. Its differential equation is `Delta psi_reg=mu psi_reg-D C_(1-eta)`, with the original nonzero cutoff commutator retained. Thus applying self-adjoint spectral reality to the full test would fail domain admission; applying it to the regularized test as though it satisfied a homogeneous eigen-equation would discard an actual source term.

A subsequent unfiltered deep search for self-adjoint resolvent signs completed retrieval and proposed an ingredient set, but that set combined boundary-coordinate and generic adjoint identities without identifying the HB response, domain or left test. It was not used as a proof. The independently available `physicalResponsePrimitive_gradient_energy` does identify a nonnegative gradient energy with a particular Hermitian forcing/primitive pairing in the full radial/angular measure. The missing step remains its relationship to the oriented complete left-QNM action, including the source contacts above.


The next transport search found and source-checked the actual `xi_scalar_modular` in `ThetaCuspHawkingBMFullSourceOverlap.lean`, `chartLaplacian_invariant` in `ThetaCuspHawkingBMModularLaplacian.lean`, and `physicalCoreCutoff` in `ThetaCuspHawkingBMPhysicalCoreCutoff.lean`. These supply modular scalar/Laplacian covariance and an independently constructed compact physical test. The private core Green proofs in `ThetaCuspHawkingBMNativeAngularGreen.lean` and `ThetaCuspHawkingBMNativeCoreTransposition.lean` identify the appropriate compact integration mechanism. That search left the quartic source core construction and transport through the explicit principal subtraction open; the construction and compact Green step are now closed below. A generic core hypothesis would not be a completed source theorem. That search had partial semantic coverage.


## Constructed compact-core physical Green identity

The new extension constructs each full quartic field as an actual modular scalar, then multiplies it by the existing modular cusp cutoff at scale N=n+1. Its physical test uses the existing `physicalCoreCutoff` at index 3n+2, so the entire test germ equals the untruncated conjugated physical test on the support of the source cutoff and its Laplacian. The original full-core Green identity then gives the exact statement

```
integral_F psi Delta(gamma_N P) dmu
 =mu integral_F psi gamma_N P dmu,
gamma_N(y)=1-chi(y/N).
```

Both integrals are admitted by constructed core fields, including all modular seams. The source cutoff Laplacian is proved to equal `gamma_N Delta P+2y² gamma_N' partial_y P+y² gamma_N''P`. All four new public declarations passed scratch Lean checking and the exact cached leaf audit (7.3 seconds, no warnings). The Green identity permits independent source and target Xi occurrences. The same-occurrence restriction applies to the following five-exponent native Mellin calculation, not to the compact Green theorem.

The following paper calculation supplies a route from that compact identity to the original native Mellin convention. For N>=2 and every nonzero exponent w, the two transitions are separated and

```
integral_2^infinity gamma_N(y) chi(y) y^(w-1)dy
 =(N^w-1) M(w),
-integral_0^infinity gamma_N'(y)y^w dy=w N^w M(w).
```

These are finite-support integrals: in the first, use `gamma_N chi=chi-chi(y/N)` and split into the original transition, the middle power interval and the rescaled transition; in the second, substitute y=Nv and integrate the original transition derivative by parts. The w=0 case instead has a logarithm in the first identity and is not covered by the displayed formula. All five same-occurrence quartic exponents w=k_j-eta are nonzero by the earlier source argument.

Write `I_N(P)=integral_F psi gamma_N P dmu` and keep the existing native N(P) from (7). Rapid remainder domination gives

```
I_N(P)=N(P)+D sum_j p_j N^(k_j-eta) M(k_j-eta)+o(1).
```

The cutoff derivative term is, after one-dimensional integration by parts in the cusp, `integral gamma_N' B(psi,P)dy`. One may take integration endpoints N and 4N, strictly outside the derivative support, so no endpoint derivative is assumed zero without proof. Replacing B by its complete principal B0 costs o(1), using the source's integrated flux remainder bounds and the scaled cutoff derivative bound. Thus the compact Green identity reads

```
I_N(Delta P)-mu I_N(P)
 =D sum_j p_j [k_j(k_j-1)-mu] N^(k_j-eta) M(k_j-eta)+o(1).
```

The identical scale-dependent terms on the two sides cancel, giving `N(Delta P)=mu N(P)`. This argument does not set a principal boundary or the original cutoff contact to zero. The scaled Mellin integral identities are now formalized below. Its remaining Lean obligations are the explicit principal expansion and the limit transport.


For all six fields, the principal coefficients can be retained explicitly in the same five-power basis. With r_i,q_i,j_i,k_m as above and
`t_i=-r_i(r_i-1)[r_i(r_i-1)-2]q_i`, the coefficient at `y^k_m` is respectively

```
Q²:          sum_(i+l=m) q_i q_l,
J²:          sum_(i+l=m) j_i j_l,
Gamma(J,J):  sum_(i+l=m) r_i r_l j_i j_l,
JRQ:         sum_(i+l=m) j_i t_l,
H:           2 sum_(i+l=m) j_i j_l+a sum_(i+l=m) q_i q_l,
Delta H:     k_m(k_m-1) times the H coefficient.
```

Here each sum retains every ordered pair i,l in {0,1,2}. The gradient coefficient follows from the actual height derivatives of J0; equivalently, symmetrizing `Delta(J0²)/2-J0 Delta J0` gives `r_i r_l`, since `k_m=r_i+r_l`. These are paper identities for the full principal evaluation, awaiting their Lean attachment. They identify the exact terms required by the limit transport rather than replacing a principal expression by an unspecified finite packet.

The follow-up deep/all-view corpus search for Mellin dilation and integration by parts completed its retrieval stages without errors. It recovered `cutoffBulkMoment_eq_nativeMellin` and the actual native transition moment. Its proposed ingredient set is not a proof: `nativeCutoffLowPower_value` requires `0<Re(w)` and the orbit-unfolding lemmas concern a different source pairing. The present five exponents cannot all be placed in that chamber. The finite separated-transition calculation above avoids that extra assumption. The preceding unfiltered dilation search was partial (local-model JSON/reranking failures); useful dilation and compact-support methods were retained, with no coverage claim beyond the reported index snapshot.

A broad recent arXiv search for “duality” led to [Gauss Law, Monodromy Defect, Magnetic Lattice Translation, and Lattice Duality, 10 September 2026](https://arxiv.org/html/2609.11417v1). Its Sections 3.3–4 distinguish operators preserving a constrained physical space from operators commuting with the Hamiltonian; field-dependent defect terms can obstruct the latter. The HB applicability test therefore requires the full action variation and boundary defects even after source/core covariance is proved. This lattice model supplies no theorem about the theta source or Hawking-clock extinction.


The compact Green extension's four public declarations are present once each in the regenerated API. The single existing umbrella import, eight local documentation links and scoped whitespace checks pass. Whole `scripts/formal_tools.py lint` returned exit 1 because the concurrently appearing, untracked `ThetaCuspHawkingBMOnsetPulseTransform` and `XiAffineCollisionControl` modules are not reachable from the RHTower umbrella; the gate reported no error for the quartic leaf. These two modules are outside this extension's write scope and were not modified.


## Finite Mellin transition proof

A new scratch file proves the two displayed cutoff scale identities directly on the finite intervals `[2,3N]` and `[N,4N]`, with `N=n+2`. First split the original cutoff integral at height three and integrate the terminal power exactly. Then substitute y=Nx on the rescaled transition `[2N,3N]`; its lower complement vanishes from the original cutoff equation. The product `gamma_N(y)chi(y)` equals `chi(y)-chi(y/N)` because the transitions are separated. For the differentiated flux, integrate the original base cutoff against the derivative of y^w on `[1,4]`, retaining both endpoint values, then apply the same positive dilation.

The public specialization uses all five `w_j=4-j+(2j-9/2)rho`, with `w_j!=0` derived from `Im(rho)!=0`. The scale N is only the angular cutoff scale; it does not alter the physical frequency or Hawking clock. The entire scratch now passes Lean checking. The new leaf `ThetaCuspHawkingBMQuarticCutoffMellin.lean` passed its exact cached leaf audit in 23 seconds, without warnings, and is wired once into the RHTower umbrella. Attachment of the five-power expansion to each actual quartic principal field and transport of the full renormalized integral remain required.


The resulting finite balance is also `flux_N-w bulk_N=w M(w)`, with `bulk_N` and `flux_N` given by the two admitted transition integrals above. Thus the scale terms match exactly before any limit is taken. This establishes a cutoff identity at the source-derived exponents, not physical time-translation invariance. The complete principal expansion and nonlinear action assembly still have to be transported into that identity.

The new unfiltered deep/all-view search for finite-interval dilation reached its deadline and proposed an unrelated compact-cutoff/sawtooth ingredient set; that set was not used. A hybrid OR query recovered actual integration-by-parts statements, the native three-power expansion and complex-power primitives. The proof uses verified finite interval substitution, integration by parts and the original cutoff equations. It supplies all regularity and endpoint values directly.

The broad single-word arXiv search “dilation” led to [Rai–Goel, normalized ground states for a weighted elliptic system, 10 September 2026](https://arxiv.org/html/2609.11494v1). Sections 1–2 distinguish prescribed-mass solutions, whose frequencies are unknown Lagrange multipliers, from the fixed-frequency problem. Their mass-preserving dilation yields a Pohozaev constraint; it is not constancy of the full energy along dilation, and its positive ground states require additional variational conditions. An HB import would need a source-derived real functional, admissible variation and complete boundary balance at the already fixed clock. These properties have not been derived here, and frequency selection from mass constraints would not meet the target.


Final verification after the Mellin leaf: the regenerated API contains all five new declarations once; both owned modules have one umbrella import, nine local documentation links pass, and scoped whitespace checks pass. The subsequent whole `scripts/formal_tools.py lint` returned exit 0 with existing large-file warnings. The two earlier concurrent umbrella-reachability errors were resolved elsewhere in the shared worktree; this extension did not edit those modules. All owned Lean/Lake/search processes completed.


## Actual principal-coefficient attachment in progress

The next proof starts from the existing exact `nativePrincipalSquare_eq_power_sum` for the original Q0, not from freely supplied coefficients. The candidate representation is closed under the actual angular Laplacian by smooth finite-sum transposition and `Delta(y^r)=r(r-1)y^r`. Consequently J0 and RQ0 receive their original differentiated coefficients. Multiplying any two three-power fields retains all nine ordered pairs in the five coefficients indexed by i+l. Applying the same sum, product and Laplacian operations as the six existing `quarticContactPrincipal` expressions should then give their full five-power expansions and differentiated principal fluxes. This is the current Lean attempt; no principal-attachment theorem is claimed yet.


The next broad arXiv reciprocity search led to [Jiang, 8 September 2026](https://arxiv.org/html/2609.10609v1). Its real-stability mechanism first proves Jacobi interlacing and hence positive residues of a real rational function; reciprocity is used later. The attempted HB transfer would need a corresponding real, interlacing source pair or a positive spectral representation of the complete left action. The original principal square already has complex Weyl coefficients, and the contact and spin-two operators multiply them by complex indicial polynomials. Reflection alone does not supply the required positive-residue representation. Thus this method does not currently prove the proposed source sign or extinction. Its useful test is precise: establish the positive representation before invoking half-plane preservation; neither reciprocity nor the existence of a finite power expansion establishes it.

Current corpus searches use hybrid retrieval and deep retrieval with all views, including source arguments and method ingredient sets. The principal-flux query reported a complete 56,964-file source inventory but unmeasured semantic coverage, pending compiler metadata and a reranking deadline. Its private gradient result was checked in source and replaced in the candidate proof by direct evaluation of the actual continuous linear map. The finite-sum Laplacian source proof was useful; generated ingredient sets remain uncertified.


The subsequent unfiltered deep/all-view query for renormalized Green transport completed retrieval without reported errors, while semantic coverage remained unmeasured. It found `d4BM_canonicalSecondStokesConstantBoundary_finitePart_zero`. Source inspection shows that theorem uses `d4BMCuspAnalyticFamilyFinitePart F = F 0`: it selects the identically-zero affine exponent before specialization. The existing specialization obstruction explains why this cannot be substituted blindly for the actual native cutoff integral. The present five same-occurrence exponents have independently proved nonvanishing, but transporting their explicit cutoff moments is still required. The generated ingredient set mixed unrelated counterterm definitions and did not establish that transport.


For the remaining native transport, only the H/Delta-H pair needs the new second Green limit: these are slots 4 and 5 of the actual quartic family. The other slots enter the resulting contact balance without an additional Laplacian transposition. The already proved `quarticContactResidual_scalar_integrable` supplies integrable domination for the physical test times each residual. The remaining finite principal integral must first use the actual horizontal mean of the physical scalar over the full cusp strip; only then may its five terms be replaced by the finite Mellin formulas. This keeps the infinite Fourier tail, original modular measure and cutoff contact in their respective exact identities.


Principal-attachment checkpoint: `/tmp/hb-quartic-principal.lean` contains the full proposed source extension; `/tmp/hb-quartic-principal-extension.lean` contains the new declarations alone. The candidate derives all six principal power sums, their actual height derivatives and Laplacians, and the same-occurrence physical principal Green flux. The gradient helper now evaluates the actual continuous linear map directly. No new principal-attachment theorem has yet been checked: scratch invocations stopped at missing cached imports. A duplicate owned dependency-repair batch was terminated after identifying another agent rebuilding the same cache target; no owned Lean or search process remains running. At that checkpoint, four required cached modules were still missing: NativeCutoffLowerAdmission, NativeCutoffUpperAdmission, NativeCutoffMellinMeromorphy and CutoffBulkMellinValue (all with the ThetaCuspHawkingBM prefix). The source leaf has not been edited for this extension. Resume by checking cache availability, then check the existing scratch with `lake env lean`; do not treat cached-index matches as certification.


## Further source-identity attack

The missing cached imports are being rebuilt in the shared worktree. The scalar differential core has no missing imports, so a separate scratch `/tmp/hb-quartic-differential-balance.lean` now attempts the complete pointwise balance (2) directly for the literal theta scalar at arbitrary complex parameter. It derives the actual product Laplacian from two-jets, the identity `Delta(Q²)=6Q Delta Q-8lambda Q²`, and then the contact and retained-spin-two balance. Every regularity input comes from the complete scalar family. This scratch is not yet certified and no new repository theorem is claimed.

The broad arXiv word search “coercivity” led to [Bothe, 6 September 2026](https://arxiv.org/html/2609.06732v1). Its §11 production identity retains all mixed gradient terms. Their cancellation requires an explicit system for the Hessian of an entropy; positivity additionally uses positive diffusion coefficients and real concentration variables. Its left eigen-covectors are proved to be exact differentials of state functions, a property stronger than pointwise diagonalizability.

The HB conjecture tested here is that the physical left-QNM covector similarly integrates to a real source entropy whose mixed-production identities survive the complete assembly. This is not established: no such entropy or exact covector identity has been derived for the independent complex scalar/vector source channels. Even a dissipative entropy balance would retain horizon and source work, and would give finite-clock extinction only after an additional exact endpoint/face balance. The source-derived contact identity (2) is therefore pursued as an actual contribution to that balance, without replacing the oriented left pairing by a Hermitian entropy pairing or dropping a boundary flux.


The entropy-covector attempt has a precise additional interface test. For a fixed symmetric pairing B and a source-work one-form `alpha_f(h)=B(h,Gret f)`, direct differentiation gives `d alpha_f(h,k)=B(k,Gret h)-B(h,Gret k)`. If the actual retarded/advanced reciprocity law is established, this equals `B(k,(Gret-Gadv)h)`. Thus reciprocity does not by itself make this particular work one-form exact. In a nonlinear problem the derivative of the response replaces Gret, and changing pairing/metric weights add `(D_h B)(k,R)-(D_k B)(h,R)`; moving-domain faces add the corresponding transport terms. A real source potential therefore requires an actual cancellation of the whole antisymmetric variation, in addition to a signed production law. This test does not rule out other source currents.

Corpus search for this test found `HBXiPeierlsRetardedAdvancedReciprocal` and the causal-jump skew theorem. Inspection shows that these carrier statements take reciprocity (and, separately, support-reversing Schwarz exchange) as premises; they do not derive the required identities for the complete physical response. The search was partial after its local worker disconnected. No such premise is added to the HB proof, and conjugation is not identified with causal reversal. The fixed original physical clock is unchanged throughout this source-variation test.


## Pointwise balance closed; proof optimization, 12 September 2026

`ThetaCuspHawkingBMQuarticContactBalance.lean` now proves (2) for the existing six `quarticContactField` expressions, at every actual Xi occurrence and every upper-half-plane point. Its private differential proof starts with the literal complete scalar equation and the actual two-jet product rule. The exported theorem takes no added spectral, covariance, sign, extinction or boundary assumption. Both retained spin-two Laplacians are present.

The proof eliminates RQ pointwise using the Laplacian of J, then cancels matching Laplacian terms while keeping the source fields opaque. It avoids expanding J inside the nested derivatives of J². No heartbeat limit was added or increased. The independent differential scratch passed; the attached source leaf passed its exact cached `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticContactBalance` audit, without warnings, and is imported once by the RHTower umbrella. This is the bulk contact identity, not the complete nonlinear physical-action sign or extinction theorem.

The principal expansion is being checked as a separate small leaf importing the already verified cusp-jet module; the original 815-line cusp-jet source is unchanged. This avoids re-elaborating its admission proofs on every principal-expansion check. The first check found reducible lambda-expression rewrites, a gradient-name resolution error and a leading-minus parse ambiguity. These were corrected using explicit target shapes, direct gradient evaluation and parentheses. After isolating and checking the finite convolution algebra, the full revised principal leaf passed scratch checking and its final targeted audit.

The deep corpus query for the contact balance reported a complete 56,990-file source inventory but partial retrieval, interrupted text/source stages and pending compiler metadata. Its method hits included the physical Laplacian pairing limit and a modular Green formula. Source inspection confirms that the former requires an actual height-weighted L² response, while the latter requires the side and circular seam identities. Neither supplies a sign for the complete left-QNM action. The existing incoming-clock source balance explicitly retains source work.

A broad September arXiv search for “symplectic” found [Gomes Da Silva, 3 September 2026](https://arxiv.org/html/2609.03329v1). Section II.1 explains that every smooth physical vector field admits a Hamiltonian lift to doubled variables. The attempted HB inference from doubled canonical structure to extinction therefore fails: the lift alone imposes no restriction on physical dissipation. For example, a doubled residual functional I(phi,eta)=pair(eta,E(phi)) vanishes at eta=0 for arbitrary E, while its first eta variation is pair(h,E(phi)). Any useful HB identity must control that physical variation and all boundary work; invariance of the diagonal functional value is insufficient. No new generic conditional Lean theorem is installed for this observation.

The corresponding deep method search for doubled action/work conservation was also partial, with interrupted retrieval and a reranking deadline. Its suggested path-work and positive-Hankel ingredient sets were not applicable to the original complex physical pairing and were not used.

## Exact next limit to prove

For the existing physical angular test psi and original cutoff chi, put

```
N(P) = integral psi(P-chi P0) dmu-D sum_j p_j M(w_j),
I_N(P) = integral psi gamma_N P dmu,
gamma_N(y)=1-chi(y/N),  N=n+2,
F_H(y) = integral_(-1/2)^(1/2) (psi H_y-H psi_y) dx,
b_j=k_j-1+rho/2,  w_j=k_j-rho/2.
```

Use the already admitted core cutoff with index n+1, so its scale is exactly N. The remaining physical Green limit can be proved by establishing, for P=H and Delta H,

```
I_N(P)-D sum_j p_j N^w_j M(w_j) -> N(P),
I_N(Delta H)-mu I_N(H) = -integral gamma_N'(y) F_H(y) dy.
```

The first formula must use the full scalar horizontal-mean theorem and native modular measure. Integrable domination applies to the principal-subtracted remainder. For the second, the two cutoff commutators combine by height integration by parts; gamma_N' vanishes at both transition endpoints. The principal flux is `D sum_j b_j h_j y^w_j`; its actual remainder has the previously proved integrated rapid decay. Each coefficient satisfies

```
k_j(k_j-1)-mu = w_j b_j.
```

The existing finite Mellin flux formula therefore cancels every N^w_j term exactly. The remaining limit would prove N(Delta H)=mu N(H), and transport (2) to the actual renormalized contact period. The equality is not yet claimed in Lean. Even after this limit, independent scalar/vector channels, solved quadratic corrections, metric variations and the remaining radial/horizon/characteristic contacts must be assembled before any complete-action sign or original-clock extinction conclusion.


## Principal attachment closed, 12 September 2026

[ThetaCuspHawkingBMQuarticPrincipalExpansion.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticPrincipalExpansion.lean) now proves the complete five-power representation of each original `quarticContactPrincipal` field, its actual height derivative and Laplacian, and the same-occurrence physical principal Green flux. The three original Q coefficients are supplied by `nativePrincipalSquare_eq_power_sum`; actual differentiated coefficients supply J and RQ. A separately checked finite convolution identity retains all nine ordered products without expanding analytic fields inside the algebra proof. These nine Weyl products do not represent the independent SS/SV/VV amplitude channels.

The checked gradient coefficient is represented directly as `k_j(k_j-1)(J0²)_j/2-(J0 Delta J0)_j`, exactly following the original field definition. Its alternative symmetrized `sum r_i r_l j_i j_l` formula above remains a paper simplification, not a separately exported Lean theorem.

The public `quarticContactPrincipal_physical_bulk_flux_coefficient` proves the final displayed indicial factor for the actual H and Delta-H coefficients. The full leaf passed `lake env lean /tmp/hb-quartic-principal-leaf.lean` without diagnostics. Its exact cached final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticPrincipalExpansion` passed without warnings in 38 seconds. Source and five artifacts were published byte-identically, with one RHTower umbrella import. Source SHA-256: `86bf5f736cfeb9a8b57ed4a2a73be731d89eef845c8d149cd1cdce1702b879a0`.

The pointwise-balance leaf's final audit passed in 65 seconds; its source SHA-256 is `7370d39abf82d3d47af937eaeba02f67614ea2c5e03a1d76184d34e319604eb4`. Neither new file contains a heartbeat setting. The earlier missing-cache and pending-principal checkpoints are superseded by these results. Native finite-part Green transport and complete physical-action extinction remain open.


Final verification for the two 12 September leaves: all seven new public declarations occur once in the regenerated API; both leaves have exactly one RHTower umbrella import; scoped whitespace and thirteen local documentation links pass. Whole `scripts/formal_tools.py lint` returned exit 1 because the concurrently present `HTGeometry.SecondEndpointMellinLaurentInterchange` and `HTGeometry.UniformSecondOrderJet` modules are not reachable from the HTGeometry umbrella. No error was reported for either new quartic leaf. These unrelated modules were not modified. All owned Lean, Lake and corpus-search processes completed; both leaf audit directories were removed after byte-identical artifact publication.


## Native Green proof attack by subtracting the principal field first

The next attempt uses R=H-chi H0. Construct compact modular approximants as the full source core gamma_N H minus the modular periodization of gamma_N chi H0. The principal height profile is smooth, compact and zero below height two; its support closure can include height two, so the existing strict `CuspHeightTest` support requirement cannot be invoked directly. A positive-height planar generator supplies the required core instead.

The actual residual differential equation is

```
Delta R = (Delta H-chi (Delta H)0)-K_H,
K_H=Delta(chi H0)-chi Delta H0.
```

The five-power attachment should identify K_H with the finite sum of the original `cutoffCommutator k_j`, with original coefficients h_j. The existing `cutoffPowerMoment_eq_gap_mul_nativeMellin` gives its physical integral exactly, since every w_j is independently nonzero. Thus the entire principal boundary contribution is retained before the Green limit. Actual weighted derivative bounds should make the two outer-cutoff commutators vanish on R. This would prove the same N(Delta H)=mu N(H) as the earlier scaled-flux argument, using the same original Mellin correction and physical clock. Neither the residual Green limit nor complete-action extinction is assumed in this construction.


## Exact quartic cutoff contact closed, 12 September 2026

[ThetaCuspHawkingBMQuarticCutoffContact.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticCutoffContact.lean) proves the actual contact for every one of the six original principal fields:

```
K_slot = Delta(chi P0_slot)-chi Delta(P0_slot)
       = sum_j p_slot,j cutoffCommutator(k_j),
integral psi K_slot dmu
       = D sum_j p_slot,j [k_j(k_j-1)-mu] M(w_j).
```

Every full-scalar contact pairing is absolutely integrable. For the actual residual R=H-chi H0, it also proves `Delta R=R_5-K_4` and absolute integrability of its full-scalar Laplacian pairing. The physical identity uses the literal incoming coefficient `Lambda(rho)=0` and independently proved noncollision `w_j != 0`; neither a zero contact integral nor a new regulator is assumed.

Scratch `lake env lean /tmp/hb-quartic-cutoff-contact.lean` passed without diagnostics. The exact cached leaf audit `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticCutoffContact` passed without warnings in 66 seconds. Source SHA-256: `a0cad9244771ec3c5cfc46cc691aa991e4c39d9044d02eecb91f8acade0a0505`; all five artifacts were published byte-identically. The leaf has one RHTower umbrella import and no heartbeat setting. Global lint/API audit remains pending for this addition.

The modular construction has been simplified further: apply the existing `cellGermExtension` to the smooth principal height subtraction. It is zero below height two; translations preserve height, and every nonparabolic closed-cell overlap lies strictly below two. These facts prove full germ compatibility, including elliptic corners. Subtracting this extension from the original modular quartic field produces the actual residual on every closed-cell germ. This avoids a separate compact planar periodization construction. The finite-core construction and physical Green identity passed an initial scratch check; the expanded candidate including smoothness and its differentiated cutoff is still being checked. No native limiting Green theorem or complete-action extinction is claimed yet.

The broad deep corpus query `physical renormalized Green limit cusp flux cutoff derivative` returned partial retrieval and pending compiler metadata. The narrowed deep query `principal cutoff Green --module ThetaCuspHawkingBM` completed retrieval, including candidate lemmas, source arguments and proposed ingredient sets. Its native radial growth-chamber results do not by themselves apply to the quartic angular residual. Direct source inspection found the reusable `squareResidual_cell_compatible` construction and the physical inverse-height L2 field. These supply concrete gluing and domination methods, not an unproved action sign.

The 8 September paper [Erman–Turgut, Renormalization of One-Dimensional Semirelativistic Bosons with Contact Interactions](https://arxiv.org/html/2609.09068v1) offers an exact operator interface: an energy-independent subtraction cancels from the principal-operator difference, leaving a factor through dressed contact maps. Its resolvent identity and large-negative-energy bounds then establish the operator. HB has not established that factorization: its native Mellin corrections depend on the spectral test, and its bilinear left-QNM pairing has not been identified with an adjoint-positive contact form. The paper therefore suggests a testable missing identity, not fixed-Hawking-clock extinction.


### Sharp energy-defect interface exposed by the broader search

The broad arXiv search `coercivity`, sorted by newest announcement, found [Vo, 2 September 2026](https://arxiv.org/html/2609.02416v1). Its nonlocal advection problem recovers an unprescribed inflow trace through an exact energy balance and a matching lower-semicontinuity bound. A positive boundary term must disappear when the remaining energy attains that bound. The proof uses a positive symmetric kernel, real positive eigenfunctions, and compactness of zero extensions; none is automatically a property of a complex left-QNM action.

A precise HB version would require source-constructed real quantities at the original fixed Hawking clock:

```
W_n = E_n + B_n,
W_n -> E_infinity,
E_infinity <= liminf E_n,
B_n -> -Re(complete_left_action(q)) = susceptibility(q)*clockDefectEnergy(q).
```

The last equality is the established transduction. If the preceding source identities and estimates are proved, then `E_n -> E_infinity-susceptibility*clockDefectEnergy`; the lower bound forces the nonnegative clock-defect term to be at most zero. This is a sufficient extinction mechanism without declaring clock covariance. It is not a closed HB theorem: no actual complete nonlinear energy `E_n` with this sharp lower bound has been derived. All SS/SV/VV, solved ++/+- corrections, changing weights and radial boundary terms must enter the displayed balance. The new angular contact and residual Green work only justifies a specific angular transport; its complex bilinear periods do not provide the required real coercive energy.


### Quartic residual core certified

[ThetaCuspHawkingBMQuarticResidualCore.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResidualCore.lean) now proves the literal residual's smoothness, constructs its modular extension, preserves its full germ on the original closed cell, and constructs compact native cores. Its physical Green identity, full differentiated cutoff formula and eventual stabilization of the entire residual germ are closed. The final cached leaf build passed without warnings in 92 seconds after scratch checking. Source SHA-256: `ac36a24de7b322a6f8578056a309c0d1c9c13346c7c2965b5bd2780c5f3ba6fc`. No heartbeat setting or transparency override was added; the leaf is imported once by RHTower.

The next candidate is `formal/.lake/hb-extinction-scratch/residual-green.lean`, checked through `/tmp/hb-quartic-residual-green.lean`. It derives weighted L2 admission of every actual residual derivative from `quarticContact_remainder_jet_bound`, then uses the independently admitted inverse-height physical scalar to control `psi*y*partial_y R`. Its proposed dominating density for the full cutoff Laplacian is

```
|psi Delta R| + 2 C |psi y partial_y R| + C |psi R|,
```

where the same source-independent C bounds `|y gamma_N'|` and `|y^2 gamma_N''|`. The exact modular core Green theorem and stabilization of full germs should then give `integral psi Delta R=mu integral psi R`. The final candidate retains the just-certified original contact integral and derives `quarticNativePhysicalPeriod q 5=mu*quarticNativePhysicalPeriod q 4`. This candidate has not yet passed Lean and is not installed as a source leaf.

The complete-action deep/method query returned the existing exact `stream_complete_action_current` and `sourceContact_differential_identity`. Source inspection confirms that the first retains temporal/radial source contacts and both angular flux components, but takes general stream two-jets; the second retains complex bilinear gradient squares. Neither identifies the complete scalar/vector nonlinear action with the particular quartic Green-exact combination. The search had partial text/source retrieval; no exhaustiveness claim is made.


## Native quartic Green transport certified

The entire [ThetaCuspHawkingBMQuarticResidualGreen.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResidualGreen.lean) candidate passed `lake env lean /tmp/hb-quartic-residual-green.lean` without diagnostics. The exact cached final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResidualGreen` passed without warnings in 25 seconds. The source is installed and wired once; all five audited artifacts were published byte-identically. Source SHA-256: `275d33f0f1f664da5b65e6972148fd1a9d9a9f8360dabfdd9da5cbd65522719b`. The new identity is

```
N_q(Delta H) = mu_q N_q(H),
mu_q = physicalAngularParameter(q)^2-1/4 = rho(rho-2)/4,
N_q(P) = integral psi_q (P-chi P0) dmu - D sum_j p_j M(k_j-rho/2).
```

The proof is closed on the actual fields. Every complex-height-weighted coordinate jet of the cutoff residual belongs to native L2. Pairing its height-squared first derivative with the full inverse-height physical scalar gives the integrable first-cutoff-error density. The original residual and residual-Laplacian pairings provide the other two terms in the dominating density displayed above. The constructed core eventually agrees with the entire residual germ at every closed-cell point, so both field and Laplacian pairings converge. This establishes the uncorrected residual Green identity even for independent source and target Xi occurrences. The same-occurrence theorem then evaluates the actual original cutoff contact and uses the exact H/Delta-H coefficient relation to cancel its Mellin correction. Neither finite-part invariance nor a zero boundary integral was an input.

Optimization: complex analytic fields remain opaque during algebra; real derivative results are typed before complex coercion; pointwise products and derivative germs receive explicit target shapes. Generic norm simplification is confined to the outer products so the proved weighted-derivative bounds remain reusable. The proof lives in small cached leaves; no heartbeat or transparency setting was added and no umbrella build was run.

Next mathematical target: transport `quarticContactField_balance` through these native periods by proving its exact five-coefficient counterpart, then attach the resulting JRQ period to the actual complete left-QNM action. The independent SS/SV/VV amplitudes, solved ++/+- corrections, changing metric weights, and horizon/characteristic/source-contact terms must be included in that attachment. The native angular identity supplies neither a positive complete energy nor fixed-Hawking-clock extinction.


Final audit for the cutoff-contact, residual-core and native-Green leaves: all 21 public declarations occur once in the regenerated API; all three umbrella imports occur once; nineteen local documentation links and scoped whitespace checks pass. Whole `scripts/formal_tools.py lint --check-generated` returned exit 1 with seven unrelated unreachable modules (`DeningerOriginalGreenXiResolventBound`, `RealPrincipalSeriesDerivedDirections`, `ThetaCuspHawkingBMHorizonCoordinateJets`, `ThetaCuspHawkingBMSelfChannelHorizonJet`, `ElementaryHorizonJets`, `SecondEndpointMellinLaurentInterchange`, `UniformSecondOrderJet`) and stale global `LEAN_API.md`/`LEAN_OVERVIEW.md` after concurrent source changes. No error was reported for the three new quartic leaves. The unrelated modules were not modified. All owned Lean/Lake/search processes completed, and all three owned audit directories were removed after artifact publication. Fixed-Hawking-clock extinction and RH remain open.


## Native contact-period balance certified, 12 September 2026

The source identity (6) is now closed in
[ThetaCuspHawkingBMQuarticNativeBalance.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticNativeBalance.lean).
For the original native period N, unchanged physical parameter mu, and the literal
fields and coefficients defined above, `quarticNativePhysicalPeriod_spinTwo` proves

```
N(J RQ) = (2mu+2c-8) N(J²) - 4 N(Gamma(J,J))
          - a(13lambda-6-mu) N(Q²).
```

The six exported theorems establish the actual five-coefficient balance, its full
principal-field evaluation, the original cutoff residual balance, native-period
transport, the H combination, and this final spin-two period law. No spectral,
boundary-vanishing, covariance or extinction premise was added. The native period
is exactly the prior integral of the original residual minus its original
five-term Mellin correction. Thus this theorem includes those cusp and cutoff
contacts, rather than assigning them zero separately.

The proof first factors each retained spin-two coefficient through the J and Q
coefficients. A separate low-degree scalar-square identity then controls the
finite convolution. This avoids expanding all analytic coefficients and their
nested polynomial expressions in one normalization. Explicit vector-component
reduction and explicit integral functions remove elaboration ambiguity. No
heartbeat, recursion-depth or transparency override was introduced.

Scratch `lake env lean /tmp/hb-quartic-native-balance.lean` passed with no
diagnostics. The exact cached leaf audit
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticNativeBalance`
passed in 121 seconds, with no warnings. Source SHA-256:
`d12f4dc95999a9e834e4eaef091bb77069d46f8d33080fe21e9c86a41a652de8`.
The leaf is imported once by RHTower; no umbrella or full build was run.

The deep corpus query `quartic principal coefficient contact native balance`
returned useful coefficient, principal-germ and contact-balance methods. Its
inventory covered 57,020 files, but text/source retrieval was partial and most
compiler metadata remained pending. Candidate and source-argument inspection was
followed by the actual Lean checks above; retrieval was not treated as proof.

## Exact action interface after the new source theorem

Define the already proved zero combination

```
Z(q) = N(J RQ) + 4 N(Gamma(J,J))
       - (2mu+2c-8) N(J²) + a(13lambda-6-mu) N(Q²).
```

An actual complete-action reduction `Cphys(q,n)=W(q,n)*Z(q)` would now imply
`Cphys(q,n)=0` by substitution. Together with the established
`Cphys=-Sigma*clockDefectEnergy`, `Sigma>0`, this would force the clock defect to
vanish. This equality is an exact remaining source-identification target, not an
assumption installed in Lean and not an established physical-action formula.
More generally, a proved remainder estimate
`abs(Re(Cphys-W*Z)) <= kappa*Sigma*clockDefectEnergy`, with a source-derived fixed
`0<=kappa<1`, would suffice: substitution gives `Sigma*energy<=kappa*Sigma*energy`,
so positivity forces `energy=0`. The present theorem supplies Z=0; it supplies no
strict remainder bound.

The correction/source comparison exposes a specific additional issue. The actual
scalar--vector source in `ThetaCuspHawkingBMQuadraticMixedSource.lean` retains its
mixed ingoing correction and full sixteen-component tensor. The exact
`master_resolvent_defect` in `ThetaCuspHawkingBMQuadraticMixedCurrent.lean` requires
an angular response satisfying a shifted resolvent equation. These response
fields and their cross-current products are not among the six local quartic
expressions just transported. They cannot be dropped or replaced by their cusp
powers. The existing `incoming_radial_mass_source_balance` still contains the
work of those responses against the complete half-square Laplacian. A further
source identity must control that work and its horizon/characteristic contacts,
and the independent SS/SV/VV amplitude coefficients, before the displayed
complete-action reduction can be asserted.

A broad newest-first arXiv search for `reciprocity` found
[Dutta's finite-time state-transfer construction](https://arxiv.org/html/2609.09654v1)
(September 2026). Its mechanism imposes a zero eigenspace and odd-pi spectral
phases, then solves an inverse spectral problem and fixes the scale. For HB the
surviving test is exact spectral-phase cancellation at the already fixed clock.
The construction does not derive such a condition for the theta source; tuning
its generator or rescaling its clock would not prove the required theorem.
No result from that paper is imported into the source proof.


The follow-up deep/method query `complete action independent scalar vector quartic
contact coefficients` returned the exact `mixedPairedCoefficient_eq`. Inspection
of that declaration and `literal_mixedPairedCoefficient_eq` confirms the two
changing bulk weights multiply the complete ++ and +- quadratic residuals,
respectively. The solved quadratic equations therefore remove those bulk terms
when attached to their actual correction fields; they do not remove the varied
boundary current or establish a sign for the remaining response pairing. This
query covered a 57,024-file inventory but reported partial text/source retrieval,
pending compiler metadata, and no verified complete-action reduction.

Final local checks for the native-balance leaf: all six public declarations occur
once in the regenerated API, its umbrella import occurs once, source SHA matches
the audited source, cached olean exists, the audit directory was removed, and all
21 local links in the two task cards pass. Scoped whitespace checks pass.
`scripts/formal_tools.py lint --check-generated` returned exit 1 only for seven
unrelated unreachable modules: `ThetaCuspHawkingBMHorizonCoordinateJets`,
`ThetaCuspHawkingBMPrincipalChannelHorizonJet`, `ThetaCuspHawkingBMSelfChannelHorizonJet`,
`AnalyticJetGerm`, `ElementaryHorizonJets`, `SecondEndpointMellinLaurentInterchange`,
and `UniformSecondOrderJet`. No error was reported for the native-balance leaf.
All owned Lean, Lake and search processes completed. The goal remains active;
fixed-Hawking-clock extinction and RH have not been proved.


## Closed radial source-work transfer, 12 September 2026

The actual incoming SV-SV radial mass contains two constructed angular responses
A and B, with Delta A=alpha(A+Q), Delta B=beta(B+Q). Set s=rho-2,
t=-rho-1, p=st, lambda=2-p, alpha=(2s+1)(2s+2), beta=(2t+1)(2t+2),
and retain the coefficients rs,rt,rQ in `incoming_radial_mass_source_balance`.
The proved source identity transfers the full Laplacian from Q to these actual responses:

```
J_new = Q [rs grad A + rt grad B + (2rQ/3) grad Q],
W = rs alpha Q A + rt beta Q B
    + [rs alpha+rt beta+(4lambda/3)rQ] Q²,
y² clockCoefficients(q,a,b,w,1,0)
  = (a²b²/16) [-p y² div(angularResponseGreen)/3
                + y² div(J_new) - W].
```

The derivation uses the complete scalar equation and
`|grad Q|_bilinear²=2Q E`, `Q DeltaQ=2lambda Q²+QE`. It retains both angular
fluxes; integrated boundary values must still be evaluated. No source work is
set to zero. Exact factorization gives the Q² coefficient

```
p (s-t) [p³+25p²-28p+20]/6.
```

This factor is nonzero at every Xi occurrence: Re(p)>2; translating p=x+2 gives
the cubic x³+31x²+84x+72, which has no zero in Re(x)>=0 by elimination of its
real and imaginary parts. Thus any cancellation must involve the actual
response-source pairings or retained faces. All three statements are now certified
in [ThetaCuspHawkingBMQuarticResponseWork.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResponseWork.lean).
The leaf also transports the balance to the actual finite-clock horizon moment
and unshifted physical horizon integral, retaining the original common rate -6,
onset endpoint, and derivative-clock energy. Scratch checking and the final exact
leaf build passed without warnings or heartbeat/depth overrides. The final build
took 100 seconds; no dependency or umbrella build ran.

The [formalized source-work card](../3-formalized/hb-incoming-radial-response-work.md)
records the complete proof and the remaining physical interface. This is the
incoming SV-SV radial component, not the complete third-order left-QNM action.
The two angular divergences still require their actual integrated cusp and
source-contact values, and the independent SS/SV/VV pairings and mixed corrections
still require comparison in the complete action.

The reciprocity attack does not yet close that gap. The actual finite-energy
response equation pairs conjugate test fields with the response. Its Hermitian
energy cannot replace the complex-bilinear response-source work above. Applying
the variational equations to both constructed residual responses gives a forced
cross-pair identity, not a zero: with residuals hA,hB and complete forcings FA,FB,
`(alpha-conj(beta))*<hB,hA> = <FB,hA>-<hB,FA>`.
Restoring the full fields also restores their principal/cutoff contributions.
Neither forcing reciprocity nor cancellation of those contributions has been
derived. No conditional closure theorem or replacement positivity premise was
added.

The 300-second deep/method query `bilinear resolvent Green full response source
contact work cancellation` returned actual Green and resolvent candidates, but
its text/source retrieval was interrupted and semantic retrieval exceeded its
deadline. The snapshot inventoried 57,028 files; most compiler metadata remained
pending, and generated ingredient sets were explicitly unverified. Direct source
inspection and the exact Lean check establish the new result, not retrieval rank.

The broader lexical query `fullAngular homogeneous cusp response` found an
important existing boundary result missed by that deep query:
`D4BMCuspResponse.responseMean_native_decomposition` in
[ThetaCuspHawkingBMCuspGrowingCoefficient.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCuspGrowingCoefficient.lean).
Its original native norm eliminates the growing coefficient, while the actual
surviving coefficient and both infinite source tails remain. Direct inspection of
`responseMean`, `root`, `limitingCoefficient` and `limitingFlux` confirms these are
the constructed global residual and its actual height-four boundary jet, not
freely prescribed asymptotic data. The decaying exponents are 2rho-2 and -2rho
for A and B respectively. This existing theorem should be reused in the angular
integration of W; its native-energy selection does not set the surviving
coefficients to zero.

The ensuing paper-level observation is specific: multiplying those surviving
response powers by the three source powers 2rho,1,2-2rho contributes exponents
`4rho-2, 2rho-1, 0` from A and `0, 1-2rho, 2-4rho` from B. Thus the complete
source-work cusp subtraction must include these terms as well as the original
particular-response powers. A proved product/period identity attaching them to
W, with the tail-response pairing admitted in the native measure, is the next
boundary target. This attachment has not yet been formalized. No physical-clock
translation is identified with a height dilation.

The new leaf's ten public declarations, single umbrella import, audited source
SHA, five cached artifacts and eleven documentation links were checked. All
owned Lean/Lake/search processes completed. The whole-tree lint reports eight
other unreachable worktree modules (the previous seven plus
`ThetaCuspHawkingBMTemporalCurrentHorizonJet`). Regeneration was repeated after a
stale-file report; the final concurrent-worktree lint still reports stale
`LEAN_GAPS.md` and `LEAN_OVERVIEW.md`. No error names the response-work leaf.
The global gate is therefore not green; complete extinction remains open.

## Current attachment: actual scalar-tested response periods

The closed cusp attachment keeps both the squared-source remainder and the Fourier tail
of the complete scalar testing field psi. If P is psi's two-term principal part,
Q0 is the original three-term principal half-square and chi is the original cusp
cutoff, define `T=(psi Q-chi P Q0) A`. The closed admission is
`T in L1(native measure)` for either constructed full response A and every full
scalar testing parameter. The proof splits T into `psi(Q-chi Q0)A` and
`chi(psi-P)Q0 A`. All complex height weights of each multiplying tail are in L2;
the actual native response is in L2, and its particular cusp response is a fixed
finite sum of powers. Hölder admission retains the complex-bilinear product.

At every height above three, the exact resulting identity is
`mean(psi Q A)=P Q0 fullResponseCuspMean+mean(T)`, where fullResponseCuspMean
retains the actual limiting coefficient and both infinite source moments from
`responseMean_native_decomposition`. This attaches the source work to the full
testing leg; it does not evaluate the remaining weighted height integral or set
any boundary coefficient to zero. No new source/current cancellation premise is
introduced.

The remaining local term has the closed companion
`TQQ=psi Q²-chi P Q0²`. The existing six-slot quartic jet theorem supplies
`psi(Q²-chi Q0²) in L1`; the difference is `chi(psi-P)Q0²`, a complete scalar
Fourier tail times the already derived five-power quartic principal expansion.
Every power-weighted tail is admitted. Consequently every term of the original
work coefficient has the exact cusp mean

```
mean(psi W)
 = P Q0[rs alpha M_A+rt beta M_B]+CQQ P Q0²
   +rs alpha mean(T_A)+rt beta mean(T_B)+CQQ mean(TQQ),
```

where `M_A` and `M_B` each retain their actual particular response, decaying
homogeneous coefficient and both infinite forcing moments. This is a proved
identity for the original source work, not a complete-action formula or a
vanishing claim. Corpus hybrid/method retrieval found the actual quartic scalar
admission (`partial=true`, compiler metadata pending for many files); source
inspection checked slot zero and the five-power principal statement. Applicability
was verified together with the new proof in one foreground scratch check.

The [formalized card](../3-formalized/hb-radial-response-cusp-pair.md) records the
closed proof and exact limitations. Scratch `lake env lean` passed without
diagnostics. Final exact-leaf `lake build` passed without warnings in 18 seconds
against cached imports. The new leaf is wired into the umbrella once; no
heartbeat or recursion-depth override and no dependency or umbrella build was
used. Its source SHA-256 is
`afb5b3652aeb0d89c1dadbab23a6cdd167af8454dd7d9c2390478a9f57488771`.

## Current attack: physical weighted response periods

The proposed shortcut from variational symmetry to complete extinction fails at
the existing Peierls polarization identity: cyclicity removes the mixed source's
self-pairing but retains the polarized ++/-- source pairing. The actual action
pairing, common propagator and boundary cyclicity remain independent obligations.
No new symmetry hypothesis is introduced. Broad recent resonance literature
also separates time-translation invariance of the forcing from stationarity of
the background: [Bonga et al., 3 September 2026](https://arxiv.org/html/2609.03732v1),
Section V, obtains zero energy jump for its stationary tide. It does not prove
invariance of the fixed theta-source onset or its complete nonlinear action.

The source-derived transport integrates the response terms in the proved cusp
decomposition. For the full response mean M, the original equation gives
`y² M''-alpha M=alpha mean(Q)`. For each original physical weight
`v_i=1-rho/2+principalExponent_i`, set
`J_i=y^v_i M'-v_i y^(v_i-1) M`. The exact finite-height law is

```
[alpha-v_i(v_i-1)] integral_a^b y^(v_i-2) M(y)dy
 = J_i(b)-J_i(a)-alpha integral_a^b y^(v_i-2) mean(Q)(y)dy.
```

All six gaps (three source powers, two constructed branches) are proved
nonzero directly from the Xi occurrence's nonzero imaginary part. This retains
the actual response jets at both ends and the complete source mean, and can
then be inserted into the scalar-tested W period. Infinite-height finite parts,
the other current faces and complete extinction are not assumed by this target.

The closed transport derives the ODE by averaging the constructed full response's
original classical equation. Its actual modular translation cancels the
horizontal second derivative; the particular response and native residual are
both retained. The weights are
`[1+3rho/2, 2-rho/2, 3-5rho/2]`. The two homogeneous roots are
`[2rho-2, 3-2rho]` for the first branch and `[-2rho, 1+2rho]` for the second.
Every weight/root difference has a nonzero rational coefficient of Im(rho), so
the occurrence's independently proved nonrealness makes all six spectral gaps
nonzero. No source-dependent physical time rate is introduced: these are
angular height weights from the original physical testing leg.

For `T=(psi Q-chi P Q0)A`, the closed finite-height attachment is

```
integral_a^b [mean(psi Q A)-mean(T)]dy/y²
 = Lambda(rho-1) sum_i principalAmplitude_i
     [J_i(b)-J_i(a)-alpha integral_a^b y^(v_i-2)mean(Q)dy]
       /[alpha-v_i(v_i-1)] ,        3<a,b.
```

The remainder T is the already admitted complete source/test remainder, not a
term declared zero. Both endpoint jets and the full forcing moment remain.
This gives a concrete source-and-boundary expression for the response portion
of the cusp period; it is not an infinite-height limit or a full left-QNM action
comparison. The [formalized transport card](../3-formalized/hb-radial-response-mellin-transport.md)
records the exact proof and remaining obligations. Scratch `lake env lean`
passed without diagnostics; final exact-leaf `lake build` passed without warnings
in 45 seconds, with default heartbeat limits and cached imports. The umbrella
imports the leaf once. Source SHA-256:
`e25a2775f9bc18a97835d036108f3419c05678c821a5baade8f49ef31cd9861c`.

## Current attack: infinite cusp flux without deleting native coefficients

The next source-level target is rapid decay of every complex height-weighted
original flux tail. For either actual indicial source F, prove
`|y^w integral_y^infinity F(t)dt|<=C_w/y` for y>3, directly from the complete
Fourier tail. Choosing the nonnegative exponent `max(Re(w),0)` bounds the
outside weight by the corresponding inside weight for t>=y. Its source-derived
inverse-square majorant has integral 1/y. This would make all weighted flux
remainders vanish while preserving their original limiting coefficients.

The application is the full-response endpoint flux in the preceding physical
Mellin transport. Its particular powers and native decaying homogeneous term
must be subtracted explicitly; only the remaining complete forcing tails may
then be sent to zero. No zero value is assigned to the native coefficient.

### Candidate endpoint law being checked

Write r_- = root false, r_+ = root true, d = r_+-r_-,
C_- = limitingCoefficient false, and I_±(y) = integral_(y,infinity) F_±.
For each original physical weight v, the candidate exact identity is

`J_v(fullMean) = J_v(cuspResponse) + (r_- - v) C_- y^(v-r_+)`
`                 - (v-r_-)/d y^(v-r_+) I_+(y)`
`                 - (r_+-v)/d y^(v-r_-) I_-(y)`.

Its paper derivation multiplies the two native Wronskians by y^(v-r_±),
solves the resulting two linear equations, inserts their original source-tail
formulas, and uses only the native-L2 removal of limitingFlux false. The value
C_- is retained. Local equality fullMean-responseMean=cuspResponse supplies
the derivative splitting without assuming a new particular-response identity.

The first scratch check is in progress at default Lean limits. The new bound
would remove exactly the last two terms in the infinite-cusp limit. The first
two terms need not vanish: v-r_+ need not have negative real part throughout
the critical strip. Any use of finite-part subtraction or cancellation with
other action faces still needs a derivation from the actual complete action.

Broad September literature search also examined Farhangi and Rodríguez Martín,
“Solutions to 6 problems in recurrence and Van der Corput sets” (7 September
2026), https://arxiv.org/html/2609.07506v1. Its operatorial recurrence framework
requires unitary representations or measure-preserving systems. It supplies no
proof of unitarity or fixed-step invariance for this literal theta action;
installing that missing property as an assumption would not solve extinction.


## Complete cusp-tail endpoint theorem certified, 12 September 2026

The preceding candidate is now proved in
[HB-QCFD](../3-formalized/hb-physical-cusp-flux-decay.md). The closed source bound
`||y^w integral_(y,infinity) F||<=C/y` holds for every complex weight and both
original indicial sources. Their Wronskian remainders have arbitrary power
decay. The exact full physical endpoint formula above and its remainder limit
are proved for both response branches at all three original physical weights.
The particular contribution and native coefficient are explicitly retained.

`ThetaCuspHawkingBMQuarticCuspFluxDecay` contains six public theorems and two
definitions. Its scratch `lake env lean` check passed without diagnostics;
final exact-leaf `lake build` passed in 25 seconds against cached imports,
without warnings or raised proof limits. Source SHA256:
`2f8ac5abed0198f4a8539d30032f9cc2323293c08023976e9b7ef7b3dfd121dc`.
The umbrella imports it once. No full or umbrella build ran.

The second deep search inspected Wronskian constancy, physical source moments,
original horizon finite-part currents and their proof methods. Its coverage
was partial; returned ingredient sets did not prove a complete-action identity.
The next mathematical obstruction is cancellation or a source-derived finite
part of the retained particular/native cusp fluxes together with the other
physical action faces and independent nonlinear channels. No fixed-clock
extinction or RH theorem has been obtained.


HB-QCFD final gate: index registered all eight public declarations; one umbrella
import and documentation links verified. Whole-tree lint reports only the
unrelated unreachable `ThetaCuspHawkingBMTemporalCurrentFundamentalFactor`;
no error targets this leaf or generated-document freshness. All owned processes
completed and the temporary audit directory was removed. The HB extinction goal
remains active.

## Current attack: source-derived cusp-period restoration

The last verified leaf removes the complete forcing-tail endpoint but leaves
particular and native cusp fluxes. To integrate the radial work against the
actual physical scalar, those fluxes must be paired with the original three
source principal powers; dropping them is invalid. The next target is an exact
restoration of each full-response cusp moment, with counterterms derived from
those particular powers and the retained native coefficient, and an admitted
complete source-tail moment. This is the input needed before the two angular
current integrations can be combined with the response work.

A separate conjecture tested during method search was a self-dual/all-plus
amplitude selection rule. The literal source has independent scalar and vector
amplitudes, whereas a self-dual helicity reduction would require a proved
relation between those modes and compatibility with every original boundary.
The August 2026 references distinguish off-shell currents, flat-space amplitudes
and AdS boundary correlators. No such identification is presently proved for
this source, so their vanishing rules cannot be installed as an extinction law.

### Precise candidate restoration law

For each original physical weight v, let e_j and A_j be the three original
half-square principal exponents and amplitudes. Put
`d_j=v+e_j-1`, `k_j=alpha A_j/(e_j(e_j-1)-alpha)`,
`gap=alpha-v(v-1)`, and retain the same native coefficient C_-.
The source-prescribed upper subtractions are

`B_source(Y)=sum_j alpha A_j Y^d_j/d_j`,
`B_response(Y)=sum_j k_j Y^d_j/d_j+C_- Y^(v-r_+)/(v-r_+)`.

Every displayed denominator is nonzero from the original Xi occurrence's
nonzero imaginary part and the already proved physical gaps. No critical-line
assumption is used. The candidate limit is

`lim_Y [integral_a^Y y^(v-2) M(y)dy-B_response(Y)]`
`  = [-J_v(M)(a)+B_source(a)-integral_a^infinity y^(v-r_-) F_-(y)dy]/gap`.

The integral on the right is absolutely convergent by the complete weighted
source bound. The proof combines the actual finite-height response law, exact
principal source integration, and the previously certified endpoint-remainder
limit. The identity `gap B_response+B_source=J_v(K)+J_v(native)` verifies that
the subtraction is the original power antiderivative, with no added constant.
The right side is retained, not set to zero.

The deeper corpus search also recovered
`ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo`: its actual same-charge
cyclic vertex is a graph-Laplacian energy and only vanishes on the diagonal.
Thus the local Jacobi shortcut was already excluded, with a nonlocal causal
Green comparison as its positive survivor. One generated search-method summary
incorrectly described `d4BMPlusPlusContinuousGreenResponse_adsBranch` as a zero
response theorem; its actual statement retains a normalizable solution times
a complete source moment. That retrieval inference was rejected.


## Original-source response cusp finite part certified, 12 September 2026

The candidate restoration above is now proved in
[HB-QRCFP](../3-formalized/hb-physical-response-cusp-finite-part.md).
`responseCounterterm_power_expansion` identifies the forced subtraction with
all three original particular-power antiderivatives and the native homogeneous
antiderivative. `response_period_restoration` is the exact finite-cutoff law;
`response_period_tendsto` proves its source-determined infinite-cusp limit.
Every original lower-boundary jet and the complete admitted source-tail moment
remain. Neither their sum nor the complete physical action is assigned zero.

The new 365-line leaf has seven public theorems and six definitions. Scratch
`lake env lean /tmp/hb-response-cusp-finite-part.lean` passed without diagnostics;
final exact-leaf `lake build` passed in 18 seconds against cached imports, with
no warnings or proof-limit overrides. SHA256:
`70c14b84874bac701d5aba6495139a57ffeffa4c6a31154385e104db0905dce4`.
No full, dependency or umbrella build ran. The umbrella imports this leaf once.

The next attachment is the complete physical scalar-test remainder. Corpus
search located `integral_cusp_field_from`; its chart/Fubini argument should
transfer the already proved native quotient L1 admission to the high-cusp mean.
The complete scalar-tested response period must retain that admitted integral
alongside the new explicit source/boundary value. The two angular-current
integrations and full independent nonlinear/action-face cancellation remain
open. Fixed Hawking-clock extinction and RH remain unproved.


HB-QRCFP final gate: all thirteen public API rows and its single umbrella import
verified. Whole-tree lint reports only the unrelated unreachable
`ThetaCuspHawkingBMTemporalCurrentFundamentalFactor` and
`ThetaCuspHawkingBMTemporalOppositeOuterCurrent`; no error concerns this leaf or
generated-document freshness. All owned processes completed and the audit
directory was removed. The original HB extinction objective remains active.

## Current attack: full scalar-tested response cusp period

The preceding source restoration controls the three physical weighted means,
but the actual scalar-tested pairing also contains the complete admitted
`testedResponseTail`. The next theorem must restore that integral rather than
replace the full test by its principal part. The source-native L1 theorem and
the original chart/Fubini map should give L1 of its high-cusp horizontal mean
with the actual factor y^(-2), and identify its period with the native quotient
integral restricted to that cusp. The full response finite part will then be
that actual remainder integral plus Lambda(rho-1) times the three original
principal amplitudes and source-determined response periods. No part of this
value is assigned zero. This is the full pairing needed by the remaining
angular-current/source-work balance.

### Full physical pairing: paper proof and scratch verification

The current attack is proved for both original quadratic response branches:
[full scalar-tested response cusp period](../3-formalized/hb-full-scalar-tested-response-cusp-period.md).
Native L1 admission transfers through the exact y^-2 chart and Fubini. Its
signed period equals the original quotient integral restricted to the cusp.
The finite part of the full physical pairing is that signed native period
plus all three original principal amplitudes times source-determined response
periods. The complete lower jet and native response coefficient remain.
Scratch Lean passes at default limits. The exact isolated leaf audit also passed (66 seconds), using cached imports; source SHA256 is `e4e2f2efc0c15ec211def51df61969ee227614025ce295ceda872a541d147bde`.

Two cached deep corpus requests were completed and inspected, including
candidate declarations, source arguments, generated methods, proof ideas and
ingredient sets. Coverage was partial (source/compiler snapshots are not all
fresh); candidate applicability was checked in source and the successful
ones in Lean. The first request supplied the exact cusp chart/Fubini bridge.
The second returned complete-source transpose currents and finite-circle
Green identities, but no theorem cancelling the physical scalar-tested
angular current. Its Eisenstein boundary cancellation hits require the
absolute-convergence parameter subtype; they do not directly instantiate the
present physical test. A generated method attached to a cusp-top definition
was treated as a definition, not a proof that the integral vanishes.

The next cancellation test must keep `grad psi dot J` in
`psi div J = div(psi J)-grad psi dot J`. Periodicity can cancel the horizontal
sides of the cusp rectangle, but does not remove that derivative work or the
upper/lower tested currents. The new result provides the actual response work
for this comparison. The complete angular-current balance and the local Q^2
period still need to be assembled with all other physical boundaries/channels.

Broad arXiv searches for Ward, symplectic, Maass, renormalized and scattering
were screened. Two recent primary sources were inspected for method transfer:

- [Sadegh, b^k-symplectic manifolds and [Q,R]=0, 23 August 2026](https://arxiv.org/html/2608.22171v1),
  sections 3.1 and 3.6–3.7: residue expansions retain a finite part; the
  reduction theorem additionally needs Hamiltonian data and odd leading
  modular type. Those hypotheses have not been established for the literal
  theta causal action with its complex cusp exponents. No vanishing theorem
  was imported from the analogy.
- [Ferretti et al., Bounds on scattering amplitudes of non-identical scalar particles,
  8 September 2026](https://arxiv.org/html/2609.09282v1), introduction and
  sections 6–7: discontinuities outside the physically constrained region
  require additional control in their bootstrap setup. Their numerical
  bounds and additional Omnes parametrisation are not unconditional source
  identities for HB. No computation or numerical bound was used here.

These searches did not produce the missing fixed-Hawking-clock cancellation.
The positive result is the source-derived full pairing above, now ready to be
compared with the retained physical current. The extinction goal stays active.

Final audit for HB-QFTCP: exact leaf passed with default limits; generated
index refreshed once (4 changed files), all ten public API rows and the single
umbrella import verified. `scripts/formal_tools.py lint --check-generated`
passed (exit 0). Source hash remained unchanged, all owned processes completed,
and the temporary audit directory was removed. No extinction theorem is claimed.

## Current attack: finite-cusp physical tested-current balance

The next source-level identity is the finite-height balance for the actual
combined angular current J=-(s*t/3) angularResponseGreen+reducedSourceCurrent.
Multiplying its original divergence law by the physical scalar test produces
both div(psi J) and grad(psi) dot J. The proposed theorem must integrate the
whole expression over the cusp rectangle, cancel only the periodic horizontal
sides, and retain upper/lower tested vertical currents and the full Q*A_true,
Q*A_false, Q^2 work. This is the direct conservation test for the physical
pairing; its remainder cannot be declared zero from periodicity or admission.

### Finite physical-clock current balance proved on paper and in scratch Lean

[HB-QTCC](../3-formalized/hb-physical-clock-tested-current-cusp-balance.md)
retains the physical scalar test on the complete incoming angular current,
proves its full source-derived horizontal side matching, and integrates its
actual divergence over the positive-height width-one strip. For l,r>3 this is
the original fundamental cusp. With B=mean(psi J_y), the exact original-clock
identity is

```
integral_l^r physicalClockDensity_h
 = h exp(-6h) (a^2 b^2/16)
   [B(r)-B(l)-integral_l^r mean(grad psi dot J+psi W/y^2)].
```

Both arbitrary amplitudes, both constructed responses, the Q source-contact
factors in J, and the local Q^2 term in W remain. The fundamental rates here
are those in D4BMModularCore (s=rho-2,t=-rho-1); the common incoming horizon
moment retains its original rate -6. No source frequency is changed.
The actual scalar-test derivative is essential. This closes the finite-cusp
current/physical-clock interface for this incoming radial sector; it does not
assert its infinite-height cancellation or the full left-QNM identification.

The scratch proof passed with default limits. Its imports were then trimmed
to QuarticResponseWork, PhysicalAngularCutoffCalibration, CuspMeanDerivative
and ComplexCoordinateDerivativeRules, and the trimmed version passed as well.
The isolated final leaf audit passed in 16 seconds, source SHA256 `ce13833079844dd9a71392bdfbcd65ed72cf5bbef7c67636bab0d8557e730c5d`. No heartbeat/depth/transparency hack
was used; intermediate elaboration failures were resolved by explicit function,
measure, endpoint and coordinate identifications.

The cached deep corpus request `tested-current-source-product-search.json`
completed with partial coverage and older-generation/compiler warnings.
Candidate lemmas, source arguments, methods, proof ideas and ingredient sets
were inspected. The actual sourceWork current, literal scalar periodicity,
full response modular invariance and cusp differentiation rules were checked
in source and applied successfully in Lean. The suggested general Green and
core Green transfers retain their own source and differentiated-test terms;
none supplies the desired vanishing of the complete physical current.

Broad arXiv searches for transgression, Pohozaev and reciprocity found recent
conservation mechanisms worth testing:

- [Campos–Killip–Visan, 25 August 2026](https://arxiv.org/html/2608.25047v1),
  equations (1.6), (1.9) and Proposition 3.2: a resolvent generating function,
  with a quartic Gram correction, gives commuting conservation laws for a
  specific Kirchhoff–Pohozaev evolution. Their shared scalar speed and fixed
  nonnegative selfadjoint operator have not been identified with the literal
  HB nonlinear assembly. The extra conservation law cannot be imported as a
  source premise. Its coercive bounds are not a fixed-clock extinction result.
- [Bambusi et al., 1 September 2026](https://arxiv.org/html/2609.01891v1):
  the same equation has commuting Hamiltonians and specified integrable
  Fourier reductions. No model identification for the actual HB channels was
  found; a formal normal-form analogy does not change the physical clock.
- [Vu et al., 3 September 2026](https://arxiv.org/html/2609.04169v1):
  passive linear mechanical reciprocity constrains a response block through
  symmetry of compliance. This is not yet an identity for the complete causal
  nonlinear HB action with its boundary/test contributions. Its numerical
  experiments were not used.

The attempted shortcut from horizontal periodicity to full action invariance
has been replaced by the exact surviving boundary/work balance above. Next
hard target: derive its original upper-cusp finite part (including the native
response products in B and differentiated-test work), match the restored
response-source periods and Q^2 term, and join every remaining physical
boundary/channel. The extinction objective remains active and unproved.

HB-QTCC final audit: exact leaf passed in 16 seconds at default limits; source
hash unchanged, 17 public API entries and one umbrella import verified. After
the initial index refresh (8 changed files), lint detected concurrent changes
to RHTower.lean and MaassLadderL2.lean. Refreshing those 2 verified changes fixed
the generated-document drift; final `lint --check-generated` passed (exit 0).
All owned processes completed and the audit directory was removed. The
finite-clock incoming radial balance is closed; complete extinction remains open.

## Current attack: native nonconstant response cusp coercivity

The complete tested upper current contains products of native angular
responses and their derivatives. The known native circle-source rapid decay
is not a theorem about these elliptic responses. Their separately known means
also do not determine the mean of their product. The next source-level target
is therefore the actual Fourier-mode equation, retaining the full forcing:

```
c_n'' = ((2*pi*n)^2 + alpha/y^2)c_n + f_n/y^2,
(|c_n|^2)'' = 2|c_n'|^2 + 2((2*pi*n)^2+Re alpha/y^2)|c_n|^2
               + 2 Re(f_n conjugate(c_n))/y^2.
```

Above a source-parameter-dependent cusp height (not a changed physical clock),
Young's inequality and the nonzero integer frequency gap should give a
coercive forced mass inequality uniform over nonzero n. The source term must
then be bounded using the literal rapid cusp remainder, and native L2
admission must eliminate the growing homogeneous alternative. Parseval and
height-derivative control are still needed before claiming decay of products
in the complete boundary current. No source-work term is assigned zero.

The existing generic Fourier differentiation and horizontal integration by
parts in SelbergMaassFourierModes apply to arbitrary smooth periodic charts;
the Maass homogeneous decay theorem does not apply to this forced equation.

### Forced Fourier attack: paper mechanism and current Lean boundary

For each original response branch let c_n be its literal period-one Fourier
coefficient, f_n the coefficient of its complete cusp-subtracted forcing, and
k_n=2*pi*n. The exact equation and real mass identity above passed scratch
Lean with default limits. Completing a square gives

```
(|c_n|^2)'' >= 2|c_n'|^2
  + (2*k_n^2+2*Re(alpha)/y^2-1)|c_n|^2 - |f_n|^2/y^4.
```

No signed forcing work has been dropped in obtaining this inequality. The
extended scratch now adds: coercivity by k_n^2 for n!=0 above
1+2*abs(Re alpha); arbitrary complex-weight bounds on f_n uniform in n;
Parseval for the full native slice mass; and integrability of each
|c_n|^2/y^2 from the original modular energy. The new height is a cusp cutoff,
not a change of clock, source frequency, or response parameter.

The proposed comparison step is: if u>=0, u''>=k^2*u-C*y^(-N), and
integral u/y^2 is finite, use an exponential lower-endpoint term plus
(2*C/k^2)*y^(-N) as a supersolution once y^2>=2*N*(N+1)/k^2.
A positive excess would have a growing positive component and contradict
weighted integrability. This is a paper argument to formalise, not a proved
Lean decay theorem. Summing the initial modal masses via Parseval and the
k_n^(-2) forcing majorant is then required, followed by derivative control
before passing products to the actual tested vertical boundary.

Three cached deep requests were inspected, including candidate lemmas,
source arguments, method descriptions, and proposed ingredient sets. Coverage
was partial; semantic coverage was unavailable, and one request reported an
older-generation snapshot. A proposed "mean zero from periodicity" step was
rejected: periodicity does not imply zero mean. The generic literal Fourier
coefficient differentiation/Green identities in SelbergMaassFourierModes were
read and successfully specialised in Lean instead. Homogeneous Maass decay
and unrelated first-order Riccati comparison lemmas were not treated as
forced native-response results.

Broad recent arXiv retrieval found
[Majdoub, 14 June 2026](https://arxiv.org/html/2606.15668v1), whose weighted
Hardy argument retains the logarithmic-coordinate weight and its critical
exponent. It supports testing weighted coercivity rather than removing a
weight by notation; its compact-support boundary assumption is not a proved
boundary condition for the HB response. Also inspected
[Shaimerdenov--Yessirkegenov--Zhangirbayev, 2 March 2026](https://arxiv.org/html/2603.02381v1)
on weighted Hardy/Rellich remainder identities. Neither supplies a complete
nonlinear Hawking-clock conservation law. The complete extinction goal stays
open.

[HB-QNCM](../3-formalized/hb-native-cusp-mode-coercivity.md) is now proved in
scratch Lean and passed its exact isolated leaf audit in 59 seconds at
default limits, source SHA256
`033761794ebf44dea4d5ca66b7602d70c005b4971dcb10f77c667339f1dd35c6`.
Its five definitions and nine theorems include both original response
branches, full signed forcing work, the nonzero-mode coercive inequality,
source-weight bounds uniform in n, Parseval, and native weighted modal
integrability. The paper comparison step, summed derivative/product control,
and complete fixed-clock action cancellation remain open.

Next comparison proof ingredient located and read:
`RHTower.suzukiSecondDeriv_nonpos_of_isLocalMax` in
`SuzukiInteriorExcursionSpectralTurningPoint.lean:119` proves the needed
second-derivative maximum test. Its short proof uses
`isLocalMin_of_deriv_deriv_pos` and local constancy; that proof can be reused
with the direct Mathlib DerivativeTest import to avoid pulling the unrelated
Suzuki dependency chain into the cusp comparison leaf. Candidate reuse is
not yet checked in a new Lean comparison theorem.

HB-QNCM final status: exact leaf passed; all 14 API entries, one umbrella
import, unchanged source hash and audit-directory cleanup verified. Global
lint did not pass: after index refreshes covering real concurrent changes,
its final result is an unreachable HTGeometry.CoordinateEinsteinDiagonalCollapse
module and stale generated API/GAPS/OVERVIEW files. RealSL2Haar's earlier
unreachability was fixed concurrently. Repeated global refreshes stopped;
no unrelated source was changed and no global lint success is claimed.
All owned processes are terminal. The extinction goal remains active.

## Current attack: forcing-to-decay comparison without an upper boundary premise

The previous turn is verified progress: HB-QNCM's source hash and actual
coercivity/admission statements were revalidated. The next proof replaces an
assumed zero upper boundary by the original integral of modal mass/y^2.
Weighted integrability must produce arbitrarily far heights with
u(B)<=epsilon*B. On each finite interval, a positive maximum of
u-b-epsilon*y contradicts its coercive second-derivative inequality. Sending
epsilon to zero yields domination by the explicit forced supersolution b.
The public target must specialise all derivative, forcing and admission
inputs to the original native modes; the generic comparison facts are only
internal proof steps. Then a bound with summable inverse-square frequency
weight will permit the complete nonconstant response to be restored.


### Source-derived comparison closed in scratch; native mean retained

The literal-mode and complete nonconstant-mass bounds now pass scratch Lean
at default limits. The proof does not prescribe an upper endpoint. For every
N in Nat put p=2N+4. The complete source bound yields C>=0 with
|f_n|^2/y^4<=C*y^(-p) uniformly in n above 3. Choose

```
Y=max(4, coercivityHeight(q,b), p+1),
L_n=(2*pi*n)^2 >= 2  (n!=0),
b_n(y)=u_n(Y)*exp(Y-y)+(2*C/L_n)*y^(-p).
```

Direct differentiation proves b_n''<=L_n*b_n-C*y^(-p) for y>=Y.
Native admission integral u_n/y^2<infinity supplies, for every epsilon>0
and every T, some B>=max(Y,T) with u_n(B)<=epsilon*B. Otherwise 1/y
would be integrable on a tail. For v=u_n-b_n-epsilon*y, both endpoints
on [Y,B] are nonpositive and v''>=L_n*v. A positive interior maximum
would have v''<=0, contradiction. If u_n(y)>b_n(y), choosing
epsilon=(u_n(y)-b_n(y))/(2*y) produces the contradiction at that same y.
This proves the comparison without a radiation/decay premise.

Parseval supplies summability of all lower-endpoint masses; integer
inverse-square summability admits the complete forcing majorant. Consequently

```
U_b(y)=sum_(n!=0) u_n(y),
U_b(y)<=U_b(Y)*exp(Y-y)+C_N*y^(-(2*N+4)),
y^r*U_b(y) -> 0  (every real r).
```

This is decay of every nonconstant mode together, not a finite truncation.
The zero mode is retained; the final scratch additionally checks the exact
full native slice mass = u_0+U decomposition and its weighted remainder.
The common Hawking clock and original spectral parameter remain unchanged.

Corpus use this turn: cached deep comparison, inverse-square summation and
Caccioppoli/derivative-current requests, including source/method views and
proposed ingredient sets. All report partial coverage; snapshots can lag the
active generation and semantic coverage is not measured. Inverse-square
summability is verified against Mathlib's actual PSeries source and in Lean.
The derivative search located the relevant native
`localDistribution_derivative` in BMInteriorEllipticRegularity: it retains the
cutoff derivative and the completed frame derivative divided by height.
Generic dissipative Hodge/wave estimates are not an identification for this
elliptic native response and were not imported as one.

Broad recent arXiv searches also inspected
[Wang--Zhu, 10 June 2026](https://arxiv.org/html/2606.11957v1)
on scalar-curvature/bottom-spectrum rigidity. Its equality and geometric
assumptions are not supplied by the HB source. No complete physical-clock
invariance follows from that analogy. Hyperbolic-shell rigidity
[Chen--Yao, 14 June 2026](https://arxiv.org/html/2606.15827v1)
was also retrieved; no applicable HB identity was extracted.

Next hard interface: identify the literal smooth response gradient with its
completed native energy components, transfer their integrability to the cusp
rectangle, and combine it with U_b's rapid decay. Weighted Cauchy--Schwarz
then offers an integrable majorant for response/derivative products. To deduce
an actual endpoint limit, one must additionally use the exact tested-current
derivative balance; weighted L1 alone does not give pointwise decay. The
native zero-mode products, source contacts and source periods remain. Full
independent-channel action identification and fixed-clock extinction remain
unproved.


The isolated native-mass decomposition now passes scratch Lean. Proof
engineering uses the explicit `tsum_congr_subtype` reindexing and a composed
equality, avoiding repeated simplifier attempts through a dependent sum's
index type. Earlier normalization problems were resolved by typed `change`
statements and small local algebraic identities; no resource limits changed.
The assembled final scratch is checking all six public declarations together.

For the next weighted derivative step, `jointCuspWeight_energy` was read as
a method, not used as an angular-response theorem. It concerns a different
completed joint wave domain. Its useful exact pattern is that testing with
a squared multiplier leaves the negative squared gradient-of-weight error;
that error cannot be suppressed in transferring a weighted estimate to the
literal angular response.

### Next source attack: finite-cutoff energy before derivative identification

A more direct route uses the already classical source equation on finite
periodic rectangles. Put R_perp=R-mean_x(R) and F_perp=F-mean_x(F). Subtracting
the proved mean equation gives

```
Delta R_perp=(alpha*R_perp+F_perp)/y^2.
```

For any real smooth height multiplier m supported strictly inside a finite
positive-height interval, integration by parts gives the exact identity

```
integral |grad(m*R_perp)|^2
  + Re(alpha)*integral m^2*|R_perp|^2/y^2
= integral (m')^2*|R_perp|^2
  - Re integral m^2*F_perp*conjugate(R_perp)/y^2.
```

All integrals here are over a complete horizontal period and the height
interval. Horizontal faces cancel by literal periodicity. At the two vertical
faces m vanishes by construction. Expanding grad(m*R_perp) completes the cross
term exactly, retaining both the gradient-of-weight error and signed forcing
work. This is a dependency-closed paper identity using smoothness, periodicity
and the original forced PDE, not yet a Lean theorem in this leaf.

Use m=y^r times a fixed lower cutoff and an upper cutoff scaled to [R,2R].
Young's inequality bounds the forcing work by the original full forcing
mass and response mass. The proved rapid nonconstant response mass, together
with literal forcing decay, bounds the entire right side uniformly in R.
The upper cutoff derivative contributes at most a constant times
integral_R^(2R) y^(2r-2)*U_b(y), which tends to zero. Fatou then gives
polynomially weighted gradient-square integrability of R_perp. This avoids
first transferring the completed gradient representation: the finite classical
identity produces the needed gradient admission directly. Formalising its
Parseval identification, finite integration by parts and cutoff limit is the
next source-level theorem to prove.

If this succeeds, weighted Cauchy--Schwarz controls the nonconstant
response/derivative products. The exact current divergence contains first
response gradients, source forcing and test/source jets, so its corresponding
weighted remainder should be integrable as well. Integrability of a current
remainder and its derivative then forces its endpoint limit to zero; the
retained zero-mode current must be evaluated separately. None of these next
Lean conclusions, or complete fixed-Hawking-clock extinction, is claimed yet.


[HB-QNCD](../3-formalized/hb-native-nonconstant-cusp-decay.md) passed the
assembled scratch and its exact isolated leaf audit in 43 seconds at default
limits. Source SHA256 `3a1955a582f89e686f5a79c3ed04e78640c97d664baa93b50890b348fe5f334a`.
One definition and five public theorems are closed, retaining both original
branches and their complete forcing; the original zero-mode mass is restored
exactly alongside the rapid nonconstant remainder. The finished module is
wired once. No additional source hypotheses, boundary vanishing, clock
covariance or resource-limit changes were introduced. Fixed-clock extinction
and RH remain unproved.

A Lean-efficient implementation of that next energy step can reuse the proved
literal modal mass identities and sum only finite sets before taking a limit.
For w=m^2, the exact finite-height multiplier identity is

```
integral_A^B w*(2|c_n'|^2+2*(L_n+Re(alpha)/y^2)*u_n+2*W_n)
= [w*u_n' - w'*u_n]_A^B + integral_A^B w''*u_n.
```

It follows from the exact mass second derivative and two integrations by
parts. For the auxiliary compact multiplier, m=0 at A,B makes w=w'=0
there; no condition on the original response or physical boundary is imposed.
The source-derived coercive inequality then gives, for each finite nonzero
index set E above the original coercivity height,

```
integral w*sum_E (2|c_n'|^2+L_n*u_n)
<= integral |w''|*U_b + integral w*sum_E |f_n|^2/y^4.
```

Parseval for the literal forcing bounds the last finite sum by its full
source slice mass; a uniform bound on individual f_n alone must not be summed
as a constant over infinitely many n. The already proved U_b decay controls
the cutoff error. Taking the finite-index and upper-cutoff limits by positivity
would then admit both vertical derivative mass and horizontal frequency
energy without differentiating an infinite series. This is the preferred
next formalisation target; its exact signed identity and all auxiliary
endpoint terms must be proved before the limits are used.


Final verification: all six public API rows, the single umbrella import,
unchanged audited source hash and audit-directory cleanup were verified.
All owned Lean and search processes completed. Index refresh covered three
changed files; lint first reported stale API/OVERVIEW generation. A second
refresh covered one new change. Final `lint --check-generated` failed solely
on the then-unreachable
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetQuadraticEinstein`.
No global lint success is claimed and no unrelated unfinished source was
changed. The exact new leaf audit passed. Log:
`formal/.lake/hb-extinction-scratch/native-cusp-comparison-final-lint.log`.

## Current attack: original modal multiplier energy and derivative admission

The previous turn is progress: HB-QNCD's audited source hash and actual public
rapid-decay theorem were revalidated. The target now is weighted derivative
admission for the same original response, not an assumed cusp trace. Use the
exact modal second-mass identity with polynomial multiplier squares, retaining
[w*u'-w'*u] at both finite endpoints and the signed work in the identity.

For the upper-cutoff limit, an explicit polynomial family suffices:

```
m_B(y)=y^N*(y-A)*(1-y/B),  A<=y<=B,
w_B=m_B^2.
```

Both w_B and w_B' vanish at A,B. On [A,B], y/B<=1 controls every upper-cutoff
coefficient by polynomial powers of y independently of B. At fixed y>A,
m_B(y) tends to y^N*(y-A). The already proved U_b rapid decay and literal
forcing bounds should therefore admit the uniform energy majorants needed
for Fatou. This avoids introducing a new smooth-cutoff domain or presuming
an upper response boundary condition. Complete forcing Parseval must be
proved before infinite-index passage; the uniform single-coefficient bound
is insufficient for that sum.

## Weighted native derivative admission proved (HB-QNCE)

[HB-QNCE](../3-formalized/hb-native-weighted-cusp-energy.md) closes the
weighted derivative-admission step for both original angular-response branches.
The exact signed polynomial multiplier identity retains its finite endpoints,
y^-2 metric potential and signed source work. Completing a square reduces
the coercive cutoff error to the first multiplier derivative. Literal forcing
Parseval controls the entire source loss. The previously proved rapid
nonconstant mass then bounds every finite-mode cutoff energy uniformly.

For P_B(y)=y^(N+1)(y-A)(1-y/B), endpoint fluxes vanish from P_B's explicit
factors. Interior comparison with B=2T gives a uniform bound on [A+1,T].
The improper-integral criterion admits every finite-mode energy; positivity
and summability restore all modes. Independent Parseval identifies the result
with the literal native gradient slice minus its retained zero-mode derivative
energy. No response trace or clock covariance is assumed.

Eight definitions and ten public theorems passed assembled scratch and the
exact isolated leaf build in 38 seconds at default limits. Source SHA256
`bc4fbd314c92c817eeeb7d6cfee618e714fa90029e5903485bdd7da02df7e975`.
One umbrella import is wired. No full/umbrella build or resource-limit override.

Next: use weighted Cauchy–Schwarz for the nonconstant native-native
response/derivative products, then the exact tested divergence for the current
remainder's derivative. Integrability of both remainder and derivative would
force its upper trace to zero. Signed source/test terms and the native mean
current remain. The other nonlinear channels and physical faces still need
complete action identification and cancellation. Fixed-clock extinction and
RH are unproved.

Final shared-tree verification: index refreshed six changed files; all eighteen
new API rows and the single umbrella import were verified. The source hash
remained unchanged. `scripts/formal_tools.py lint --check-generated` exited 1
with the sole error:

```
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries
```

This is a different shared-tree module; no unrelated unfinished source was
modified. Global lint success is not claimed. All owned Lean, search, index
and lint processes have completed.
