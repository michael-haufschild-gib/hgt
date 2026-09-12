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
    The source-derived correction to this value is now proved in item 20.
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

19. **The original future kernel has an explicit source-horizon limit. [Lean]**
    With source ingoing time `v` fixed and source radius tending to the horizon, the full Dirichlet kernel tends to half the direct-minus-image means at `Z_D=(exp(v-tau)-sinh x)/cosh x`, `Z_I=(exp(v-tau)+sinh x)/cosh x`. Their supports remain `v>=tau+x` and `v>=tau-x`, including characteristic values. At delay `h>=0`, the direct argument is `1+(exp x/cosh x)(exp h-1)`; its full theta mean tends to `Q` as the target approaches the ingoing horizon.
    Evidence: [FutureHorizonCap](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFutureHorizonCap.lean), `native_kernel_source_horizon`, `halfKernel_at_delay`, `horizonMean_ingoing`.

20. **A convergent source cap integral cancels the retained lift value. [Lean]**
    Let `A_s(v,x)=integral_0^infinity g_s'(v+h) mean_Q(arcosh[1+(exp x/cosh x)(exp h-1)]) dh`. This integral is absolutely admitted with a radial-uniform bound; `A_s(v,x)->-g_s(v)Q` at the ingoing horizon. The image arm `A_s(v-2x,-x)` tends to zero. With the original lift coefficient `l_infinity`, the field `H=-l_infinity[A_s(tau+x,x)-A_s(tau-x,-x)]` has zero Dirichlet value and horizon trace `l_infinity g_s(v)Q`. Therefore `lift+reduced_future_response-H -> 0` at fixed ingoing time.
    **Scope:** source-derived field-value cancellation; no differentiated Einstein flux, complete SS/SV/VV action, or left-QNM extinction is proved by it.
    Evidence: [FutureHorizonCap](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFutureHorizonCap.lean), `boundaryDensity_integrable`, `boundaryArm_bound`, `onsetFirst_future_integral`, `capBoundaryField_ingoing`, `lift_response_sub_cap_ingoing_zero`. Scratch check and cached exact-leaf audit passed; module wired; formal lint passed.

21. **The finite future Green calculation isolates one null-cap correction. [Paper]**
    For source coordinates `a<=b<=B`, target `p=tau+x<=r=tau-x`, and the original lift `beta(a,b)Q`, direct-minus-image integration gives `G_B(L lift)=lift+integral_p^B beta_a(a,B)K_D(a,B)da-integral_r^B beta_a(a,B)K_I(a,B)da`. The diagonal contributions and cap corners cancel exactly. Source-rate decay and full theta growth admit the cap limit `lim_B G_B(L lift)=lift-H`, with `H` from item 20.
    **Scope:** this Green cap identity remains a paper proof. It is not yet a Lean identification with a separately constructed advanced wave inverse or the complete physical action.
    Evidence: [finite identity FG and cap limit FH](hb-radiative-source-period-attack.md#future-null-cap-green-calculation-12-september-2026).

22. **The original stream current has a sharper contact-corrected horizon interface. [Lean]**
    For ingoing covector jets, `f=R²-1`, `D_R=f partial_R+partial_v`, and original angular operator `A=rough Laplacian minus one`, the actual Einstein current plus original master-source contact obeys `(J+B)_R=R^(-2) sum((D_R P) A Q-(D_R Q) A P)`. All four components are identified; time and angular faces retain their normal/mixed-curl terms. At `R=1` the regular expression is `sum(P_v A Q-Q_v A P)`.
    **No-go:** evaluating a regular horizon jet does not establish a limit of differentiated integral fields. **Survivor:** only time/angular traces and weighted normal remainders are needed for this radial contact-corrected limit; separate second-normal limits are unnecessary there. No other face or complete nonlinear channel is removed.
    Evidence: [CapTraceAction](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCapTraceAction.lean), `physical_current_add_contact`, `contact_is_original`, `radial_horizon`; [finite-radius defect CD](hb-radiative-source-period-attack.md#cap-trace-and-physical-contact-12-september-2026).

23. **The literal cap trace retains the lift's angular clock pairing. [Lean]**
    The derived scalar trace `l_infinity g(v)Q` has actual coexact trace `l_infinity g(v)*dQ` and proved time/angular derivatives. Its two-branch radial angular pairing equals `horizonFactor(s,a,b) exp(-6v) chi(v)² angularPair(q,z)`, exactly the lift's contact-corrected trace expression. Here `angularPair=(2lambda-2) angularSquare+2 gradientPair`; the original normalization is `*dE=2 fullGradientCovector`. Its finite time integral retains `clockMass(V)`. For `v>=1` and any fixed `T>=0`, the pairing at `v+T` is `exp(-6T)` times its value at `v`.
    **Scope:** exact trace-field expression, with no universal nonzero claim. It is not yet the differentiated cap integral's flux, a complete-action invariance law, or extinction. Scratch, exact-leaf audit and formal lint passed; module wired; no heartbeat or transparency override was added.
    Evidence: [CapTraceAction](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCapTraceAction.lean), `covectorTrace_is_coexact`, `traceAction_original`, `traceFlux_eq_lift_angular`, `traceFlux_square_gradient`, `traceFlux_finite_integral`, `traceFlux_physical_step`.

24. **The same cap has an explicit opposite-horizon datum. [Paper]**
    At fixed outgoing time `v`, `tau=v+x`, `x->-infinity`, the cap tends to `-l_infinity[integral_0^infinity g'(u) M_Q(1+2exp(u-v))du-integral_v^infinity g'(u) M_Q(2exp(u-v)-1)du]`. The direct-arm substitution gives `1-c(x)+c(-x)exp(u-v)`, `c(x)=exp x/cosh x`; the image retains its `u>=v` support. Zero onset removes negative `u`. The existing source bound admits both integrals and their limits with majorant `C exp((a0-c0)u)`, `a0<c0<2`.
    **Survivor:** an explicit past datum to include when comparing the cap with the advanced, seed and pulse fields. Its vanishing, nonvanishing, and complete causal-action cancellation are unproved. This limit is not yet Lean-formalized.
    Evidence: [opposite-horizon formula PH and admission](hb-radiative-source-period-attack.md#opposite-horizon-of-the-actual-cap-paper-calculation).

25. **The original reduced advanced response has an admitted past-horizon datum. [Lean]**
    In source ingoing coordinates `a=t_source+y`, at target `tau=v+x`, its original Bochner integral equals the integral of `K_D(a-y-v-x,x,y) timeReducedCoefficient(s,amplitude,a-y,y)` on `a>0,y<0`. Both kernel invariants are bounded by `5 exp(a+|v|)`, uniformly in target `x`; the full density is bounded by `C exp(a0(|v|+|k|)) exp((a0-c0)a) exp(2y)`, with `a0<c0<2`. Its limit is the absolutely admitted integral of the direct/image kernel (PK) against the same original source coefficient, including both characteristic supports.
    **Survivor:** an exact source-derived past datum and uniform majorant for comparing the reduced response with the cap. These field-value results do not prove their cancellation, derivative admission, the advanced wave equation, or complete left-QNM extinction. Scratch check and cached exact-leaf audit passed; module wired.
    Evidence: [PastSourceResponse](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPastSourceResponse.lean), `response_null_coordinates`, `null_kernel_bound`, `nullDensity_bound`, `pastDensity_integrable`, `response_past_horizon`; [kernel PK](hb-radiative-source-period-attack.md#original-advanced-response-at-the-past-face-12-september-2026).

26. **Fixed time translation leaves an explicit source defect on an ingoing-time strip. [Lean]**
    Set `d_T g(u)=g(u+T)-exp(2sT)g(u)`. For `T>=0`, this defect and its actual derivative vanish outside `[-T,1]`. The original reduced forcing defect is exactly `reducedCoefficient*d_T g+2 radialLiftFirst*d_T g'`; the unreduced forcing retains its square and gradient factors. The difference `R_adv(tau+T)-exp(2sT)R_adv(tau)` equals the absolutely admitted full Dirichlet integral of this defect.
    For `x<0`, `tau+x>1`, the original future response, lift and both cap arms scale by `exp(2sT)`. At fixed outgoing time their reduced defect integral instead tends to `pastResponse(v+T)-exp(2sT)pastResponse(v)`; no zero value is asserted.
    **Boundary:** the late-region law cannot be applied along the past-horizon limit, where `tau+x=v+2x->-infinity`. The finite ingoing-time strip is not compact spacetime support. **Survivor:** the exact source defect, its admitted response and its past datum, at the unchanged physical clock. Complete-action invariance and cancellation remain unproved. Scratch and cached exact-leaf audit passed; module wired.
    Evidence: [SourceTimeTranslation](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceTimeTranslation.lean), `onsetDefect_hasDerivAt`, `onsetDefect_zero_outside`, `reducedDefect_eq`, `originalForcing_translation`, `response_translation`, `corrected_future_late_translation`, `defect_response_past_horizon`.

27. **The original weighted mixed source changes affinely with the full corrections. [Lean]**
    For original first jets `P,Q`, quadratic discrepancies `A_pp,A_pm` and cubic discrepancy `B_ppm`, the actual mixed coefficient changes by `W0(M)*(L B_ppm+E2(P,A_pm)+E2(Q,A_pp))+W1(P,M)*L A_pm+W1(Q,M)*L A_pp`, contracting every tensor entry. `W1` retains the determinant-volume and both inverse-index derivatives. Original Xi modes supply the vacuum/linear equations; scalar/vector amplitudes are independent; no equation for the correction discrepancies is assumed.
    **Survivor:** the exact local work to project after a fixed-clock translation. No boundary or physical projection is set to zero. Scratch and cached exact-leaf audit passed; module wired.
    Evidence: [WeightedCorrectionDiscrepancy](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMWeightedCorrectionDiscrepancy.lean), `physical_coefficient_change`, `physical_mixed_discrepancy`.

28. **Exchanging an inhomogeneous correction exposes its source pairing and boundary defect. [Lean for original Xi modes]**
    For two original physical Xi modes `H,M` and a full symmetric correction `A`, `W0(M)*E2(H,A)+W1(H,M)*L A = W0(A)*E2(H,M)+D_H D_A Theta(M)-D_H D_M Theta(A)`. `Theta` is the original weighted connection-current divergence.
    **No-go:** on-shell-only Hessian exchange does not discard `W1(H,M)*L A` for an inhomogeneous correction. **Survivor:** the exact correction/source pairing and boundary defect. No identification of the second source mode with the physical left test, boundary admission or integrated cancellation is asserted. Scratch and cached exact-leaf audit passed; module wired.
    Evidence: [InhomogeneousCorrectionBoundary](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMInhomogeneousCorrectionBoundary.lean), `physical_mode_correction_exchange`.

29. **The independent full test retains one additional Einstein-residual term. [Lean]**
    With only the original first source `H` on shell, the right side of item 28 gains exactly `W1(H,A)*L M`. The general bulk product rule retains both first-residual terms; its test derivative is the actual determinant-volume and inverse-index slope. The original mixed ingoing correction is instantiated at the actual exterior radius/height without setting its residual to zero.
    **Survivor:** an exchange applicable before proving the actual left metric's full equation. It specifies precisely which extra term that equation must remove. Scratch and cached exact-leaf audits passed; both leaves wired.
    Evidence: [CoordinateEinsteinOnShellPairing](../../../../formal/GaloisForLFunctions/HTGeometry/CoordinateEinsteinOnShellPairing.lean), `testCoefficient_first`, `bulk_second_eq_hessian_and_weights`; [InhomogeneousCorrectionBoundary](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMInhomogeneousCorrectionBoundary.lean), `physical_correction_exchange`, `original_mixed_correction_exchange`.

30. **The current's first metric jet is not a complete metric derivative realization. [Source inspection; derivative formula now Lean]**
    `mixedJet` sets its second metric slot to zero; `streamMetricJet` uses this because the action current needs only the first metric jet. That placeholder cannot justify the full Einstein residual used in item 29. For the original lift `c(r)=r*Y(tortoise(r))`, differentiating the proved second derivative gives `c'''=(r*Y'''-3*(r^2+1)*Y''+8*r*Y')/(r^2-1)^3`. The original radial ODE gives the third derivative of `Y` by differentiating its smooth-potential right side.
    **Survivor:** the exact missing derivative level and formula (LJ), feeding the original vector Einstein `master`/`masterFirst` contraction. Item 32 now closes the actual full left metric realization and its residual on the original action slice.
    Evidence: [MixedRadialActionCurrent](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedRadialActionCurrent.lean), `mixedJet`, `streamMetricJet`; [LJ derivation](hb-radiative-source-period-attack.md#actual-weighted-correction-discrepancy-12-september-2026).

31. **The actual mixed nonlinear discrepancy has a closed two-channel boundary exchange. [Lean]**
    Combining items 27 and 29 gives `Delta C=W0(M)*L B_ppm+W0(A_pm)*E2(P,M)+W0(A_pp)*E2(Q,M)+(W1(P,A_pm)+W1(Q,A_pp))*L M+boundaryDefect(P,A_pm,M)+boundaryDefect(Q,A_pp,M)`. Both quadratic channels originate in the actual mixed derivative; all four correction slots are retained before differentiation. The full symmetric test is independent, and scalar/vector amplitudes and changing metric weights remain explicit.
    **Survivor:** a source-proved local identity specifying every term that complete projected cancellation must control. No causal-field derivative admission, integrated face/contact cancellation, test equation or extinction is assumed or produced. Scratch and cached exact-leaf audit passed; the 38-line leaf is wired.
    Evidence: [MixedCorrectionBoundary](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedCorrectionBoundary.lean), `complete_mixed_exchange`.

32. **Both prescribed left QNMs supply their complete metric equation. [Lean]**
    For either original fundamental frequency and either ingoing/normalizable radial normalization, the continued source mode satisfies `Y''=(w^2-lambda*horizonCoordinate)Y`. Its smooth potential gives all radial derivatives, including item 30's third lift derivative. The original `master` and `masterFirst` reduce exactly to `c*(D-lambda*A)` and `c'*(D-lambda*A)`; the literal angular equation removes both defects. The reconstructed field equals the metric obtained from the original `physicalLeftModeStream` on the entire exterior; its complete ordered metric two-jet has zero cosmological Einstein linearization in all 16 components at the original time-zero action slice.
    **Scope:** original clock, frequencies and normalizations; no supplied smoothness or field equation. This removes the left-test residual in item 31, not its source work or integrated boundary terms. Scratch and isolated cached exact-leaf audit passed (133 seconds, 2 jobs); 526-line module wired.
    Evidence: [LeftQNMMetricEquation](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLeftQNMMetricEquation.lean), `profile_derivatives`, `profile_smooth`, `radius_master_defect`, `radius_derivatives`, `metricField_jet`, `metricField_einstein`, `metricField_is_original_stream`.

33. **The actual left QNM removes both test residuals from the complete correction exchange. [Lean]**
    Item 31 becomes `Delta C=W0(M)*L B_ppm+W0(A_pm)*E2(P,M)+W0(A_pp)*E2(Q,M)+boundaryDefect(P,A_pm,M)+boundaryDefect(Q,A_pp,M)`. Item 32 supplies `L M=0` for either frequency and radial normalization at the original action slice. Every actual left metric derivative slot is symmetric. Source copies, scalar/vector amplitudes and full correction jets remain independent; changing weights are retained through the proved exchange.
    **Survivor:** exact remaining local work for the translated causal corrections. No boundary admission or integrated cancellation is obtained. Even vanishing of a change would still require the original clock value to be controlled. Scratch and isolated cached leaf audit passed (290 seconds, 2 jobs); 95-line module wired. Formal lint passed. No heartbeat, depth or transparency setting was added.
    Evidence: [LeftQNMCorrectionExchange](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLeftQNMCorrectionExchange.lean), `leftJet_symmetric`, `testResidualWork_zero`, `complete_mixed_exchange`.

34. **Different angular eigenvalues leave a current, whose same-reader contraction is a divergence. [Paper]**
    For the normalized trace-free symmetric tensor `X=[(dS tensor dT+dT tensor dS)/2]^TF`, direct covariant differentiation gives `div X=(lambdaS+lambdaT)*d(ST)/4+(lambdaS-lambdaT)*(S dT-T dS)/4`. The literal same-copy source and marked reader have `lambdaS-lambdaT=rho*(3rho-2)/4`, a nonzero coefficient at each Xi occurrence. This does not show the current is nonzero. With the original bilinear coexact convention, `J=S dT-T dS` obeys `<J,*dT>=-div(ST *dT)`; against a different scalar response, `<J,*dU>=-div(ST *dU)+2S<dT,*dU>`. The horizontal upper-edge flux of `ST *dT` is `-ST T_x dx`.
    **No-go:** the one-eigenvalue tensor cancellation does not by itself remove the cross-source current; a nonzero mismatch coefficient does not obstruct integrated cancellation either. The actual scalar/vector source instead contains coexact/coexact contractions: `<*dF,*dT>=div(F*dT)-lambdaT*F*T`, retaining item 15's scalar overlap. **Survivor:** exact divergence plus Jacobian decomposition, retaining the reader/response distinction and edge flux. These paper identities have not been identified with the complete Einstein source, admitted on every boundary, or formalized here.
    Evidence: [calculations XP, XF, XFU](hb-radiative-source-period-attack.md#actual-weighted-correction-discrepancy-12-september-2026).

35. **The original cap has an admitted time derivative. [Lean scratch]
    The original onset obeys `|g'|+|g''| <= B exp(-d*u)` at the existing source-admission exponent `a0<d<2`. Differentiation under the original cap integral gives `partial_v A=integral g''(v+h)*M(x,h) dh`; its majorant is uniform in `x`. No theta derivative bound, frequency change or supplied field equation is used.
    **Scope:** actual time derivative only; normal identification, differentiated horizon limits and complete boundary cancellation remain pending. Verified by `lake env lean /tmp/hb-cap-normal-trace.lean`; no installed leaf or final audit yet.

**Result of this research:** no complete radiative extinction theorem, fixed finite physical-clock invariance theorem, or RH proof has been obtained. None of these scoped no-gos disproves HB.
