Mission: turn exact black-hole scattering dynamics into unconditional Xi divisor-incidence constraints forcing RH.

New Lean module:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint.lean
- wired into formal/GaloisForLFunctions/RHTower.lean immediately after ThetaCuspHawkingAIMECrossBranchTeukolskyResidue.
- No git used.

Core correction:
- Existing cusp BM continuation has rho=1/2+i z and xi_cusp=z/2+i/4=i(1-rho)/2.
- At every XiZeroCopy, 0<Re rho<1 and Re z != 0.
- Lean proves Im xi_cusp>0 and Im(1/4+xi_cusp^2)!=0 at every Xi divisor, including under RH.
- Therefore existing continued angular Q cannot be physical spectrum of self-adjoint horizon Laplacian. It is analytic resonance continuation.

Positive survivor / new endpoint:
- Thermally de-aliased complex QNM branch gap is (omega_+ - omega_-) - i/2 = z, independent of overtone.
- Candidate physical BM angular eigenvalue Q_H=1/4+z^2.
- At Xi divisor, Im Q_H=0 iff Im z=0 because Re z!=0.
- Global all-divisor reality of Q_H is Lean-proved equivalent to RiemannHypothesis.
- On line Q_H.re>1/4.
- Open producer remains: derive -i/2 subtraction from nonlinear chiral Teukolsky/helicity horizon-backreaction return and prove landing in physical self-adjoint angular spectrum. Current theorem is exact receiver, not proof.

Key declarations:
- d4ThetaTeukolskyThermallyDealiasedQNMBranchGap_eq
- thetaCuspHawkingBMContinuedAngularEigenvalue_xi_im_ne_zero
- d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff
- riemannHypothesis_iff_d4ThetaTeukolskyThermallyDealiasedSpectrumIsReal

Verification:
- targeted source compile passed.
- targeted olean generation passed.
- all new theorem axioms are only propext, Classical.choice, Quot.sound.
- formal_tools lint sees new module reachable but exits on unrelated pre-existing unreachable owned modules (ApproximationNumberUnitary, XiDeterminant..., LogHarmonicResidueTransfer, etc.).
- /tmp scratch removed.

Bulk-edge idea audit:
- Not stupid as architecture, but coarse signed Chern/Fredholm index is already dead in corpus.
- Existing ThetaCuspHawkingCausalHardyIndexEndpoint proves each upper resonance has Hardy defect/index 1 equal Wigner-Smith winding; bulk-edge protects rather than excludes resonance.
- HedenmalmThetaKakutaniBalancedIndexNoGo proves reflection-balanced signed index is 0 while unsigned defect energy is 2.
- ThetaCuspHawkingFullMirrorCouplingWindingEndpoint gives RH iff every noncentral sector has unit local winding, but dynamics does not force unit order.
- Family/local C0-valued index avoids total cancellation in principle, but actual cusp critical Q lies in continuous spectrum and black-hole outgoing Teukolsky operator is nonselfadjoint; standard gapped IQHE bulk-edge hypotheses do not apply.
- Credible only if actual nonlinear Teukolsky family supplies a local Gohberg-Sigal/bulk-edge boundary map tying each de-aliased divisor Q to physical angular spectral class, plus theta-specific zero/trivial bulk class. That is essentially same unresolved incidence, not independent producer.
- Cold-horizon family alternative: false RH gives dark winding surface gravities kappa_n=-Im omega/n accumulating at 0. A Fredholm family completion at kappa=0 with same-sign local crossings would contradict local finiteness, but extremal/cold horizon is gap-closing/singular; no credible completion currently.
