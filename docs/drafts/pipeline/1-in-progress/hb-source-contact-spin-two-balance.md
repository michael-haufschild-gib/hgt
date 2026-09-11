# HB: the retained spin-two contact and its angular Green balance

Status: paper derivation of the literal contact balance, finite angular boundary terms, and matching original cutoff-Mellin correction. The six quartic regulated periods have closed Lean L²/L¹ admission and integrated principal-subtracted cusp flux decay. Constructed modular core cutoffs and their actual physical-test Green identity now pass scratch Lean checking and the exact cached leaf audit. Native finite-part transport and attachment to the complete physical action remain open. No extinction or RH theorem is claimed.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → original common Hawking-clock extinction → RH.

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
