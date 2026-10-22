# HB: original onset-pulse Green action

Status: full-angular and original onset-pulse circular Green transfers are [formalized](../../../3-formalized/hb-full-angular-circle-green.md), as are their [literal-source reconstruction](../../../3-formalized/hb-full-angular-circle-reconstruction.md), [full angular wave action](../../../3-formalized/hb-full-angular-circle-action.md), and [closed-cone pulse kernel identity](../../../3-formalized/hb-full-angular-goursat.md). The [finite original-forcing Green reconstruction](../../../3-formalized/hb-onset-green-reconstruction.md) is also formalized. Physical pulse/current pairing, cancellation and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The full incoming wave-image current is [formalized](../../../3-formalized/hb-full-incoming-current.md). The hard target is its signed combination with the original pulse response, both cross terms and all other physical faces. The pulse is fixed by `fullSourceOnsetPulse_transition`; it cannot be chosen to cancel a current.

The actual seed and lift are recovered by integrating their actual wave operators against the original causal kernel, retaining all characteristic data; the finite reconstruction is proved below. Broad concomitant/method searches recover existing projected concomitants and general source equations, but no supplied boundary equality is usable as a premise for extinction.

Second test: for `nu=2s+1`, the two angular inverse parameters are `nu(nu+1)` and `(nu+3)(nu+4)`. Test a three-step differential ladder against the literal forcing and unchanged physical operator. Parameter similarity alone does not identify a physical intertwiner.

A direct Green mechanism to test in parallel: the circular mean of the constructed full angular response satisfies a forced Darboux equation. Its initial value is the full response and its forcing is the literal half-square mean. Derive a finite-radius variation-of-constants identity, then carry it into the original radial/onset integral. This could evaluate the pulse's response contribution without assigning any angular or incoming datum to zero. The finite Green-current identity has a dependency-closed paper proof and a closed Lean proof. Its use in the physical pairing remains open.

## Finite angular transfer

Put `s = physicalRate q branch`, `alpha = (2s+1)(2s+2)`, `nu = 2s+1`. Let `h(d)` be the literal circular average of the constructed full angular response `H`, and let `m(d)` be the existing circle average of `Q = scalar²/2`. The polar metric identity, averaging of the periodic angular second derivative, and the already proved full equation `Delta H = alpha(H+Q)` give

`(sinh d)² h″ + sinh d cosh d h′ = alpha (sinh d)² (h+m)`.

For the existing original Legendre kernel `p(d) = legendreKernel nu (cosh d)`, its actual differential equation gives

`sinh d p″ + cosh d p′ = alpha sinh d p`.

Consequently the actual current `W(d) = sinh d (p(d) h′(d) - p′(d) h(d))` obeys, for positive radius,

`W′(d) = alpha sinh d p(d) m(d)`.

Both factors and their first derivatives are continuous at zero; hence `W(0)=0`. The fundamental theorem on `[0,D]`, requiring the derivative only on its interior, proves

`W(D) = alpha integral(0,D) sinh d p(d) m(d) dd`.

This retains `h(0)=H(z)` and requires no inverse of `p`, no zero of an unevaluated remainder, and no altered source. It evaluates a full-response boundary current directly in the literal theta half-square. It does not yet evaluate the full pulse convolution or its physical mixed pairing.

Insertion into the unchanged direct/image causal circle kernel and finite source integration are proved below. The retained angular datum, pulse response and every physical face remain part of the current-pairing target.

## Search applicability

Broad corpus searches used `concomitant`, `ladder`, `Legendre`, and a mechanism query about causal Green recovery. Declaration, candidate, method/source-argument and ingredient-group results were inspected. The cached index reported partial/pending coverage and source-only compiler metadata; generated ingredient groups were not accepted as proofs. The usable ingredients are the existing circle-chart polar identities, differentiation of compact circle averages, full angular forcing equation and actual Legendre differential equation. Polynomial-degree recurrences do not yet supply the required physical complex-degree intertwiner.

Independent arXiv searches used `homotopy`, `transgression`, `intertwining` and `caustic`, including June–September 2026 filters. [Caustic beamforming (10 June 2026)](https://arxiv.org/abs/2606.12321) concerns shaped wireless propagation and supplies no proved transfer for this operator. The older [Kerr conserved-current paper (2022; revised 2024)](https://arxiv.org/abs/2210.15935) gives a metric/Weyl symmetry-operator mechanism, but its homogeneous equations and renormalized mode pairing have not been identified with this forced physical action. [The charged two-dimensional black-hole paper (August 2026)](https://arxiv.org/abs/2608.21406) likewise does not supply the present full angular identity. These are analytical leads, not proof dependencies.

## Original pulse substitution

Write the already fixed pulse exactly as `C_H H + C_Q Q`, where

`C_H = -2 sourceSeedFieldFirst(s,0,a,1,alpha,t) chi′(tau+t) exp(2s(tau+t))`,

`C_Q = 2 alpha radialLiftFirst(s,0,a,1,t) chi′(tau+t) exp(2s(tau+t))`.

Linearity of the actual circular average gives `pulseMean = C_H h + C_Q m`. Its actual radial derivative follows from smoothness, so the finite transfer above yields

`W_p(pulseMean)(D) = C_H alpha integral(0,D) sinh d p(d) m(d) dd + C_Q sinh D (p(D)m′(D)-p′(D)m(D))`.

The response channel is therefore replaced by a literal-source integral in this pulse current. The half-square current remains explicit, with both original coefficients and the original onset derivative. This identity is paper-proved and kernel-checked in `onsetGreenCurrent_transfer`. It is a circular transfer identity, not yet an evaluation of the complete causal convolution or its SS/SV/VV pairing.

## Full causal-kernel reconstruction

The actual full angular mean is recovered before insertion into the direct and reflected causal kernels. For the existing physical Legendre kernel `P(z)` the coefficient `alpha` is nonreal on both Xi branches. Its actual ODE gives the finite imaginary-flux identity

`(Z²-1) Im(conj(P(Z)) P′(Z)) = Im(alpha) integral_1^Z |P(z)|² dz`.

With `P(1)=1`, continuity and nonnegativity make the integral strictly positive for `Z>1`. Therefore `P(Z)` cannot vanish for `Z>=1`. This proves that division by the original radial Legendre function is valid at every real circle radius, without a new spectral assumption.

The resulting reconstruction is

`h(D)=p(D)[H(z)+alpha integral_0^D (integral_0^u sinh a p(a)m(a) da)/(sinh u p(u)²) du]`.

The inner source integral is literal. The existing smooth quotient `h/p` and its actual derivative identify the displayed outer integrand away from zero, proving interval integrability through the apparent singularity. Inserting `D=arcosh(invariant)` separately into the original direct and image terms gives the circular pulse kernel from the retained datum `H(z)` and source-only integrals. These identities passed scratch checks, the exact-module build of `ThetaCuspHawkingBMFullAngularCircleReconstruction`, and all six new public theorem axiom checks. Only `propext`, `Classical.choice` and `Quot.sound` occur.

## Actual angular wave action

Exact base-Laplacian commutation is proved for the constructed full field. For `F(theta,x,k)=H(logCircle(d,theta,x,k))`, the corpus's original chart coefficient identities and the chain rule give

`exp(2k) F_xx + F_kk - F_k - (Delta H)(logCircle) = -2 exp(k) partial_theta(partial_x F)`.

The right-hand side averages to zero by periodicity. Differentiation of the compact circle integral is justified by the already constructed field's smoothness. Thus the actual base action is `Delta_base h = alpha(h+m)`. Together with the proved radial forced equation this gives the full radial/base Darboux equation. The original causal invariant's two derivative identities then yield the time/tortoise wave equation for `h(arcosh(invariant))`, with characteristic value `H(z)` and identical direct/image values at the AdS boundary. This dependency-closed paper argument is formalized in `ThetaCuspHawkingBMFullAngularCircleAction`. Its exact-module build and all six new public theorem axiom checks passed, with only the three standard logical axioms. This closes the full-angular kernel's operator identification. The finite forcing convolution is constructed below; complete physical pulse/current pairing is still required.

The full kernel's characteristic differentiation and closed-cone Goursat equation are now kernel-checked in `ThetaCuspHawkingBMFullAngularGoursat`; the original pulse's kernel identity retains both source channels. Its finite time/source integral is constructed below. The next dependent target is the physical signed combination with the full incoming wave image, both cross terms and every physical face.

The reconstruction searches used `transmutation`, `nonreal Dirichlet` with OR matching, `Darboux`, and mechanism queries describing causal recovery and Laplacian commutation. Candidate lemmas, method/source arguments and proposed ingredient sets were inspected. The usable positive mechanisms are imaginary flux for the actual nonreal physical parameter, the existing full-field Green current, and the native chart's explicit periodic derivative defect. The index reported partial/pending coverage and source-only compiler metadata. The generated groups involving unrelated telescoping sums or Euclidean harmonic averages were not used as proofs.

Independent broad arXiv searches used `impedance`, `disconjugacy`, `port-Hamiltonian` and `reciprocity`, with recent-date filters. The [August 2026 interconnection paper](https://arxiv.org/html/2608.29731v1) supplies a constructive regularity mechanism in Lemma 5.2: splitting a constant matching matrix's kernel and applying a fixed left inverse reconstructs omitted port trajectories with the required regularity. Lemma 5.4 extends lifting under a constant-rank intersection condition. A possible application is explicit recovery of omitted physical boundary variables after the complete mixed-current matching equations are derived. No such finite-rank identification with the present PDE has been proved. The [June energy-model representation paper](https://arxiv.org/abs/2606.21544), [September revision of the interaction-dynamics paper](https://arxiv.org/abs/2606.08281), and [August graphene-impedance paper](https://arxiv.org/abs/2608.28836) are contextual leads, not dependencies of either Lean proof.

## Closed-cone pulse kernel identity

Proved identity: the actual full angular circle kernel equals its original characteristic datum plus the double null-coordinate integral of `alpha (Hcircle + Qcircle)/(4 cosh(x)^2)` on the entire closed causal cone. Smooth radial Darboux regularity gives `h′(0)=0` and `h″(0)=alpha(H+Q)/2`; the right derivative in the invariant coordinate is therefore finite. Its product with the null-axis invariant derivative vanishes. Two finite fundamental-theorem identities then recover the kernel, including both characteristic axes.

Linearity transfers this identity to the existing onset-pulse kernel with its original two coefficients, clock, direct/image gates and factor one half. This is the kernel formation step needed before evaluating the original pulse/current pairing. The finite source convolution is constructed below. Signed cross terms, independent physical faces, QNM pairing and extinction remain open.

## Dependent response and current identity

The existing `timeOriginalForcing_full_onset_decomposition` fixes the sign and normalization:

`F = wave(lift) - wave(seed H)/alpha + P/alpha`.

Let `W = lift - seed H/alpha` and let `R_P` be the original finite causal integral of the actual onset pulse. The identity `R_F = W + R_P/alpha` is now [proved in Lean](../../../3-formalized/hb-onset-green-reconstruction.md), with the original past and AdS data justified from the actual fields. Two finite triangle Green identities and justified integral linearity supply the result. Its physical use requires operator-domain identification and all four bilinear-current terms: incoming/incoming, incoming/pulse, pulse/incoming and pulse/pulse, with the branch-specific factors `1/alpha`. Each remains attached to its original physical face.

An external analytical lead from a broad **backstepping** search is [Belhadjoudja, May 2026, §3.2](https://arxiv.org/html/2605.25217v1): an invertible triangular integral transform removes nonlocal transport terms; its boundary kernel equation enforces a target trace, and uniformly bounded characteristic transit times yield finite-time disappearance. A possible HB test is to derive the boundary equation satisfied by the already fixed pulse/current combination. No free boundary controller or transit-time premise has been transferred into this proof. The June 2026 [optimization backstepping paper](https://arxiv.org/html/2606.27722v1) concerns designed feedback and supplies no identified lemma for the physical pulse. Neither paper is a Lean dependency.

### Source-integration admission

Direct substitution into the existing source profiles gives the AdS source trace

`P(tau,0,z) = -2 a^2 alpha H(z) chi′(tau) exp(2s tau)`.

Indeed `radialUnit(0)=0`, `sourceAmplitude(s,0,a,1,0)=a^2`, `sourceSeedFieldFirst(s,0,a,1,alpha,0)=a^2 alpha`, and `radialLiftFirst(s,0,a,1,0)=0`. This is a paper derivation from the exact definitions; a separate Lean endpoint theorem has not yet been added. For source formation, integrate the fixed pulse on the original negative-tortoise half-domain with direct and image terms, or split its odd extension at zero. The existing full-native response's globally continuous odd-source argument cannot be reused without checking this trace. The finite triangle/Fubini mechanism has been adapted below: the two AdS diagonal terms cancel after the original direct/image subtraction. Identification with the physical joint operator remains a separate domain obligation.

### Constructive Green reconstruction

The invariant is symmetric in target and source radius: `invariant(h,x,y)=invariant(h,y,x)`, directly from its displayed formula. Therefore the already proved target-radius wave equation yields the corresponding source-radius equation for both `K_H` and `K_Q`. For a scalar coefficient `beta(tau,y)`, the circular image of `wave(beta H)` is

`(beta_tautau-beta_yy) K_H - beta sech(y)^2 K_(Delta H)`.

The source-radius kernel equation identifies this as the two-dimensional Green divergence obtained from `beta` and `K_H`; the same mechanism applies to `Q`. Integrating over the original backward causal half-domain recovers `beta(T,x) H` from the characteristic vertex and the explicitly retained past/AdS faces. For the prescribed incoming wave image `W`, the initial field and initial time derivative vanish because its onset is zero for `tau+y<=0`, while both seed and lift vanish at the AdS scalar boundary. This gives a concrete route to `R_F = W + R_P/alpha` through finite integrations by parts. It does not require a supplied global inverse or a supplied extinction identity. The finite moving-domain Green integration and characteristic admission are formalized below. The original vector reconstruction, physical operator-domain identification and complete current pairing remain open.

For this Green proof, first use reciprocity to make the original target radius the fixed center in the new Goursat identity. The backward source null coordinates then occur only as the upper integration limits. Differentiating the public double-integral formula gives continuous single-integral characteristic derivatives directly, with zero edge values. This avoids rederiving private singular-coordinate derivative limits: the new closed-cone identity already contains the needed first-derivative admission in primitive form. The mixed derivative follows from two finite FTCs. This is the mechanism used in the closed Lean proof for the moving source domain.

### Direct/image triangle Green identity

Use target null coordinates `0<=p<=r`, source coordinates `(a,b)` with `a<=b`, and `x=(p-r)/2`. The direct backward source domain is `0<=a<=p, a<=b<=r`; the reflected domain is `0<=a<=p, a<=b<=p`. For a radial seed coefficient `c`, put `beta(a,b)=c((a-b)/2) timeOnset(2s,a)`. Both actual seed and lift have `c(0)=0`, so `beta(a,a)=0`; the fixed onset gives `beta_b(0,b)=0`.

For the reciprocal kernel `K(a,b)`, the exact identity `K beta_ab-beta K_ab = partial_a(K beta_b)-partial_b(beta K_a)` integrates over the direct triangle to `H beta(p,r) + integral_0^p K(a,a) beta_b(a,a) da`. The reflected triangle contributes precisely that same diagonal integral. Their difference therefore recovers the actual original wave image. This cancellation retains the AdS term until the two original images are combined. It needs neither a continuous odd forcing nor a missing inverse assumption. The public Goursat double primitive supplies the continuous kernel first derivatives and mixed action required by the two FTCs. The Lean proof instantiates the actual full angular seed and half-square lift, then combines them with the fixed pointwise source/onset decomposition.

### Original forcing reconstruction

The triangle identity is instantiated with the actual radial lift and the constructed full angular seed. Write the observation point as `T=(2p+w)/2`, `x=-w/2`, with `p,w>=0` and `r=p+w`. Source coordinates remain `tau=(a+b)/2`, `y=(a-b)/2`. The direct source integral has `0<=a<=p`, `a<=b<=r`; the reflected integral has `0<=a<=p`, `a<=b<=p`. The circular-source integrals carry factor `1/4`, from the original kernel factor `1/2` and source null Jacobian `1/2`.

For each of the actual fields `U=lift,seed`, source-circle averaging of its literal differential wave equals `4 beta_ab M_U - beta DeltaM_U/cosh(y)^2`. The reciprocal Goursat primitive identifies this expression with the two Green integrands. Their signed integral is exactly `U(T,x,z0)`. The existing source identity then gives the closed finite-convolution theorem

`R_F(T,x,z0) = lift(T,x,z0) - seed(T,x,z0)/alpha + R_P(T,x,z0)/alpha`.

Here `F` and `P` are the existing `timeOriginalForcing` and `fullSourceOnsetPulse`. The circular source is integrated directly; it is not redefined by the desired reconstruction. Continuous extensions use `arcosh(max(1,Z))`; the triangle causal inequalities prove `Z>=1`, removing the extension on both physical domains. Continuity of the actual wave-circle expressions and pulse coefficients justifies all finite integral linearity. The full assembly is formalized in `ThetaCuspHawkingBMOnsetGreenReconstruction`; its foreground scratch check, exact-module build and three new public theorem axiom audits passed. Only the three standard logical axioms occur.

This closes the finite original-forcing reconstruction bridge. Identification with the physical causal radial/left-QNM operator domain, complete signed current with all cross terms and faces, and fixed-clock extinction remain outstanding.

Searches used the broad term `Green`, a deep field-recovery mechanism query, and OR exploration `integral reconstruction reciprocity`. Available declaration, candidate-lemma and method/source-argument sections were inspected. All three searches reported partial coverage with a pending generation; the latter two also reported local deadline/disconnection failures. The direct proof uses the checked corpus Goursat and triangle integration mechanisms, not proposed search groups. Broad recent-paper leads [continued-fraction telescoping](https://arxiv.org/html/2609.07092v1) and [Abel summation](https://arxiv.org/html/2607.15327v1) were inspected; neither supplied an additional applicable lemma. No numerical experiment was run.

### Next physical operator comparison

The corpus already has [classical Green transport](../../../3-formalized/hb-physical-response-classical-green-transport.md) for the actual complete physical cusp response on its original positive-frequency overlap, together with endpoint Green identification and same-copy continuation to the fundamental QNMs. The next attack is to identify the Laplace transform of this newly constructed, unprojected finite causal action with that physical response on the overlap, using actual operator-domain admission and uniqueness. Then transport the complete current, preserving the pulse and both cross terms. The existing scalar profile transport alone does not supply the physical adjoint residue, spin-two reconstruction or independent Hawking-clock extinction.

The [native/physical causal equality](../../../3-formalized/hb-native-causal-equality.md) now identifies the complete residual almost everywhere in time. Its [physical double primitive and current](../../../3-formalized/hb-physical-primitive-current.md) retain the original Friedrichs domain, strong time derivatives, classical radial trace, full gradient energy and exact finite-time source balance. The smaller frequency chamber still needs a growth or continuation transfer. The [principal energy estimate](../../hb-principal-growth-energy.md) gives a concrete analytical candidate for a rate below 7/4; landing that bound on the actual principal responses and then the full residual remains open.
