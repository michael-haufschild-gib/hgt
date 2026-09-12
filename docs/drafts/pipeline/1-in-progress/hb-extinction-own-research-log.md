# HB: own research facts and no-gos

Started 12 September 2026. Consolidated from my research record and checked source files.
**Lean** = checked theorem from this work; **scratch** = checked algebra, not an installed theorem; **paper** = derivation recorded, not formalized. Domains and limits below are part of each result. A no-go rejects only its stated inference.

Notation: `rho=x+it` is an actual Xi occurrence; `delta=x-1/2`; `S` is the literal theta scalar; `Q=S²/2`; `E` is its original complex-bilinear gradient energy. Physical time and the predeclared Hawking clock are unchanged throughout.

1. **Source reflection transports the source, but changes the diagonal reader. [Lean]**
   `rho -> 1-rho` exchanges the two branches of the four-amplitude raw metric/source family. The constructed mixed response, Einstein action and source contact transport at a fixed independent reader. Diagonal action transport leaves exactly the difference between the two readers. Their parameters satisfy `u_R=-u-1/2`; their eigenvalues differ, and the full reader fields are unequal even on the critical line.
   **No-go:** source branch exchange alone does not cancel the diagonal physical projection. **Survivor:** fixed-reader transport, including contacts, plus an explicit reader-change remainder.
   Evidence: [SourceReflectionTransport](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceReflectionTransport.lean), `full_source_reflect`, `physicalProjectedModeAction_reflect`, `physicalProjectedModeAction_diagonal_defect`, `physical_reader_reflect_ne`.

2. **The tested first-order reader repair has an unavoidable forcing. [Lean]**
   At unchanged frequency, its reflected radial residual is `d(rho) sech²(tau) tanh(tau) f(tau)`, where `d(rho)=3(2rho-3)(2rho+1)/32 != 0`. In the admitted band `Re w>1/2`, the two original modes cannot both have zero residual at any negative tortoise coordinate.
   **No-go:** this derivative-cancelling Darboux transform is not an intertwiner. **Survivor:** the exact transported current equals integrated source work plus reader-defect work, with both endpoint currents retained. No claim about all possible intertwiners.
   Evidence: [PhysicalReaderDarboux](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhysicalReaderDarboux.lean), `reflectedResidual_eq`, `reflectedResidual_pair_ne_zero`, `transportWork_integral`.

3. **The reader's Hermitian current has the wrong spectral center for the proposed extinction proof. [Lean]**
   `div J_psi=i(x-1)t |psi|²`; hence `-t Im(div J_psi)=(1-x)t²|psi|² >= 0`. Divergence vanishes exactly at reader nodes and is not identically zero at any Xi occurrence.
   **No-go:** this reader current cannot be treated as a conserved positive clock-defect current, including on the critical line. **Survivor:** exact positive density and node classification.
   Evidence: [SourceHermitianCurrent](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceHermitianCurrent.lean), `divergence_eq_spectral_density`, `divergence_eq_zero_iff_reader_eq_zero`, `not_divergence_free`.

4. **The literal nonlinear theta source does have a local positive defect identity. [Lean]**
   `div J_S=4i delta t |S|²`. With `B=conj(Q)E-Q conj(E)`, `div J_Q-B=8i delta t |Q|²`, and `delta t Im(div J_Q-B)=8 delta² t² |Q|² >= 0`.
   **No-go:** deleting gradient work changes the source identity; local positivity alone supplies no vanishing. **Survivor:** a source-level positive defect density retaining the complete quadratic gradient term. No identification with the complete physical action or infinite-cusp flux is proved here.
   Evidence: [SourceHermitianCurrent](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceHermitianCurrent.lean), `source_divergence`, `square_divergence_sub_gradient_contact`, `square_oriented_contact_balance`.

5. **A null source contact still couples to the physical left field. [Lean]**
   The onset tensor `N` has `P(N,N)=0`, but an actual stream test obeys `P(M[Psi],N)=-(2 chi'/r²) sum_A C_A (partial_r-partial_t/f)Psi_A`, `f=r²-1`. The switched-source pairing is the cutoff bulk pairing plus this explicit contact.
   **No-go:** null self-pairing does not justify deleting source-contact work. **Survivor:** its exact coupling to an independent physical reader. No universal nonvanishing of that coupling is asserted.
   Evidence: [CurrentSourceAction](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCurrentSourceAction.lean), `onset_self_action`, `physical_left_onset_action`, `physical_left_switched_action`.

6. **Changing metric weights have an exact exchange defect. [Lean]**
   The exchange is `(tr(G^-1 H)/2) raised(M) - (tr(G^-1 M)/2) raised(H)`; contraction with an arbitrary tensor residual retains every component. Literal vector fields have zero volume trace. Vector/vector weight exchange therefore vanishes; a vector test against a scalar/vector source retains the scalar trace term. Corrected-field exchange is also included.
   **No-go:** cyclicity at frozen weights does not establish cyclicity of the complete action. **Survivor:** explicit defect and its exact vector/vector cancellation; this cancels a weight term, not the bulk source or boundary action.
   Evidence: [ActionWeightExchange](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMActionWeightExchange.lean), `literal_corrected_weight_exchange`, `literal_weight_residual_exchange`, `literal_vector_weight_exchange`, `literal_vector_test_weight_exchange`.

7. **The moved null cut has zero first expansion and a retained spin-two deformation. [Lean]**
   The original one-sided metric horizon limit is explicit for independent scalar/vector amplitudes. Writing `e=exp(s(v+log 2))`, the displacement is `R=-s aS e S/2`; it solves the first null-cut equation. The deformation is `K=s e (aS TF(Hess S)/2+aV sym(nabla *dS))`, with `tr K=0`.
   Its pairing with an independent reader retains SS, SV and VV terms. For the same angular source, the mixed terms cancel and the coefficient is `aS cS/4+aV cV`. The spin-two square is complex-bilinear, not a positive norm.
   **No-go:** zero first expansion does not remove shear; its quadratic contraction does not identify the quartic corrected action. **Survivor:** the full first-deformation tensor and independent-reader pairing. No global event-horizon or nonlinear Raychaudhuri theorem is asserted.
   Evidence: [OriginalHorizonDeformation](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalHorizonDeformation.lean), `original_metric_horizon`, `displacement_null_equation`, `deformation_eq`, `deformation_trace_zero`, `deformation_pairing_general`, `tracefreeHessian_square`.

8. **Native quartic periods retain an exact spin-two/contact balance. [Lean]**
   Let `lambda=(rho-1/2)²-1/4`, `c=7lambda-2`, `a=c(c-4)/96`, `mu=((rho-1)/2)²-1/4`. The native periods satisfy `N3+4N2-(2mu+2c-8)N1+a(13lambda-6-mu)N0=0`. Principal coefficients, residual integrals and cusp contacts satisfy the underlying balance separately; `N4=2N1+aN0` also survives the finite part.
   **No-go:** this angular period identity is not an identification with the complete causal action. **Survivor:** the exact native relation, retaining both spin-two Laplacians and gradient/contact terms.
   Evidence: [QuarticNativeBalance](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticNativeBalance.lean), `quarticNativePhysicalPeriod_balance`, `quarticNativePhysicalPeriod_H`, `quarticNativePhysicalPeriod_spinTwo`.

9. **The full reduced future integral is admitted without changing the clock. [Lean]**
   For `a=1+2|Re(rho-1/2)|`, choose only a majorant exponent `c=(a+2)/2`; then `1<=a<c<2`. The original Dirichlet kernel times the complete reduced source is absolutely integrable. Its actual Bochner integral `R` admits Fubini and satisfies `|R(tau,x,X,k)|<=C exp(-c tau+a|k|)`, uniformly in radial and horizontal coordinates. It has zero Dirichlet value and zero ingoing-horizon value.
   **Survivor:** an admitted full reduced future response, retaining the theta remainder and onset derivative. The wave equation, differentiated boundary flux and physical left-QNM identification are not proved by this admission theorem.
   Evidence: [FullSourceAdvancedAdmission](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceAdvancedAdmission.lean), `density_integrable`, `response_fubini`, `response_bound`, `response_dirichlet`, `response_ingoing_horizon`.

10. **Adding that future response leaves the original lift's horizon trace. [Lean]**
    At fixed ingoing time `v`, `lift+R -> [-s(s-1) 2^(2s) amplitude²/4] timeOnset(2s,v) Q`. This is the exact trace, not a claim that it is nonzero at every point or amplitude.
    **No-go:** finite retarded lift reconstruction cannot silently be transferred to a future inverse with its boundary contribution deleted. **Survivor:** the explicit boundary datum that such a comparison must account for. No advanced Green reconstruction is asserted.
    Evidence: [FullSourceAdvancedAdmission](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceAdvancedAdmission.lean), `lift_plus_response_ingoing_horizon`.

11. **The physical radial source reduces to an endpoint period with a retained remainder. [Scratch + paper]**
    With `alpha=2s-w`, `beta=2s+w+2`, `A=(5s²+15s+4)/4`, `C=s(s-1)(alpha+2)(beta+3)/8`, the actual transformed density is `2 amplitude² y²(1-y)^w(1+y)^(2s)(A+C y²)dy`. A denominator-cleared cubic primitive has residual `R=c1+alpha c0`; the polynomial identity and source factorization passed scratch Lean checks. The paper finite-part result is `fundamentalSourceMoment=-amplitude²(c0+R I(w,s))/[beta(beta+1)(beta+2)]`, under its stated endpoint conditions.
    At each actual source/target branch choice, the denominator is nonzero. Target exchange preserves `C` at fixed source rate; the two source branches give a product containing `x0(x0-1)v0(v0-1)`, `x0=5rho/2-1`, `v0=3rho/2`.
    **No-go:** a primitive plus a retained period is not source extinction; matching completion factors is not cancellation. **Survivor:** exact reduction and original endpoint subtraction. The integral identity is paper-only.
    Evidence: [radial reduction and coefficients](hb-radiative-source-period-attack.md#actual-radial-source-without-setting-w--2s).

12. **Differentiating the Weyl family retains the derivative of its vanished coefficient. [Paper]**
    For `p_u=A(u)y^(1/2+u)+B(u)y^(1/2-u)` at `u0=(rho-1)/2`, `A(u0)=0`, the exact principal-family Wronskian is `p partial_y partial_u p-(partial_u p)partial_y p=2u0 B(u0)A'(u0)-B(u0)² y^(-2u0)`.
    **No-go:** specializing to the surviving Weyl power before differentiating loses the constant term. **Survivor:** the displayed boundary coefficient, with no assumption of simple zeros or nonzero `A'`. Its identification with the complete reader integral remains unproved.
    Evidence: [reader-pairing calculation R1](hb-radiative-source-period-attack.md#whole-chain-test-causal-reciprocity-source-periods-and-the-actual-reader).

13. **Fixed-clock Bianchi work yields a boundary-charge balance, not zero charge. [Paper]**
    For the full metric density, `P^{ab}=vol(g)g^{ai}E_ij g^{jb}`, `J^a=vol(g)g^{ab}E_b0`, direct expansion gives `2 partial_a J^a=P^{ab} partial_0 g_ab`. Its fourth coefficient is `2 div J4=P3:partial_0 h+P2:partial_0 k+P1:partial_0 l`; `P3` includes the varying-weight term `W1(h)E2`. Independent plus/minus polarization retains all three quadratic-correction work terms.
    **No-go:** conservation neither sets the full boundary charge to zero nor identifies the clock test with the marked left reader. **Survivor:** the explicit boundary/work ledger, including changing weights, residuals and contacts. The geometric derivation is on paper; complete physical-action incidence is unproved.
    Evidence: [clock-work identities W, W4, W22](hb-radiative-source-period-attack.md#whole-chain-recheck-cyclicity-clock-work-and-causal-onset).

14. **A switched correction is not automatically an unswitched on-shell metric. [Paper algebra]**
    If the retained first field is uncut and `Lk=-chi B(h,h)/2`, its unswitched quadratic residual is `(1-chi)B(h,h)/2`; specified contact forcing adds its own residual. Cutting the first field instead introduces first-order derivative contacts. Also `s_minus-conj(s_plus)=1-2 Re(rho)`.
    **No-go:** neither the cutoff nor a Hermitian identification of the two branches can discharge the complete residual for free. **Survivor:** exact onset residual and exact branch-conjugacy defect. These statements do not classify the full corrected metric.
    Evidence: [onset and conjugacy calculations](hb-radiative-source-period-attack.md#whole-chain-recheck-cyclicity-clock-work-and-causal-onset).

15. **Stream-source conservation retains an angular overlap. [Paper]**
    Integration by parts in the original source/stream pairing leaves temporal and radial divergences plus `(2/r^4) sum_A (chi C_A)(R Psi_A-A Psi_A)`. An admitted homogeneous physical left mode removes `R Psi` but leaves `A Psi=(mu-2)Psi`.
    **No-go:** source conservation alone does not make this physical pairing pure boundary work. **Survivor:** its explicit overlap and all angular/cusp fluxes when the angular operator is transferred. A time-zero evaluation during zero onset also cannot erase a time-integrated contact.
    Evidence: [source-contact Green identity G](hb-radiative-source-period-attack.md#source-contact-conservation-and-the-physical-left-test).

16. **Trace-free angular tensors need not be transverse. [Paper]**
    On the original curvature-minus-one angular metric, `div(TF Hess S)=d(Delta S)/2-dS`; for an eigenfield it is `(lambda-2)dS/2`.
    **No-go:** trace-freeness alone does not identify the retained source with a holomorphic/transverse cusp-form sector. **Survivor:** the exact divergence defect. No classification of the complete tensor is asserted.
    Evidence: [angular rigidity calculation](hb-radiative-source-period-attack.md#whole-chain-comparison-variational-elimination-angular-rigidity-reader-transport).

17. **Causal variational elimination retains a domain obligation. [Paper]**
    In the symmetric expansion recorded in the research card, the `e²d²` coefficient is `L(a,c)+L(b,b)/2+T(p,p,c)/2+T(p,m,b)+T(m,m,a)/2+U(p,p,m,m)/4`. Algebraic stationary substitution produces `-L(a,c)-L(b,b)/2+U(p,p,m,m)/4` using stationary identities on the same variational domain.
    **No-go:** radial kernel symmetry does not exchange retarded and advanced time domains or remove final caps and source contacts. **Survivor:** the exact coefficient and the boundary/domain terms exposed by attempting the exchange. This is a comparison calculation, not a new physical transpose theorem.
    Evidence: [variational elimination](hb-radiative-source-period-attack.md#whole-chain-comparison-variational-elimination-angular-rigidity-reader-transport), [causal reciprocity test](hb-radiative-source-period-attack.md#whole-chain-test-causal-reciprocity-source-periods-and-the-actual-reader).

18. **Reflection does not preserve the marked QNM frequencies. [Direct source comparison]**
    `w_plus(1-rho)=w_minus(rho)+1/2`, `w_minus(1-rho)=w_plus(rho)-1/2`. The four-Lambda coefficient theorem used in this attack also has a half-strip domain; its reflected label lies outside that domain. Values known only at discrete Xi occurrences do not license an identity-theorem continuation.
    **No-go:** source reflection supplies neither an unshifted marked-frequency exchange nor the reflected coefficient formula outside its proved domain. **Survivor:** exact frequency comparison and a precise domain boundary; the common physical clock has not been replaced.
    Evidence: [actual source-reflection test](hb-radiative-source-period-attack.md#actual-source-reflection-test-12-september-2026).

**Result of this research:** no complete radiative extinction theorem, fixed finite physical-clock invariance theorem, or RH proof has been obtained. None of these scoped no-gos disproves HB.
