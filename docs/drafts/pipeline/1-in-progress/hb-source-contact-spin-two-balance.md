# HB: the retained spin-two contact and its angular Green balance

Status: the literal pointwise contact balance, all six actual quartic principal expansions, their physical Green flux and original cutoff-Mellin contact are closed in Lean. The original quartic residual now has an actual modular core and a certified native physical Green limit, with both outer-cutoff errors removed and all original Mellin contacts retained. The full contact balance now transports through those native physical periods, giving the exact JRQ period reduction below. Attachment to the complete nonlinear physical action remains open. No extinction or RH theorem is claimed.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → original common Hawking-clock extinction → RH.

Latest closed attachment: the original incoming radial response work has an exact
full scalar-tested cusp mean, with both actual native response coefficients and
all three tested remainders retained. Their admission is proved in the
[radial response cusp-pair leaf](../3-formalized/hb-radial-response-cusp-pair.md).
The remaining height periods and complete-action boundary cancellation stay open.

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
