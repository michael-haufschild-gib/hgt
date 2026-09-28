# Full Pauli uniform replica sublevel law — 2026-09-28

## Completed, checked
New `formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliSpectralSublevelLaw.lean` (352 lines), wired in HTGeometry.lean immediately after TwoLocalPauliSpectralJetLaw. Imports jet law, KM.Prop23, SpectralCharacterReplicaHeightLaw. No heartbeat or recursion options.

16 new public theorems verified in `/tmp/hgt-pauli-sublevel.Kc6jmo/Sublevel.lean` using `lake env lean`, then all 16 #print axioms audited in same scratch: ONLY propext, Classical.choice, Quot.sound. Compile exit0, no warnings. Integrated source byte-equal checked scratch after removal of scratch-only axiom commands. One owned Lean process at a time. No umbrella/full build, no lake build, no git, no subagents. Only missing TwoLocalPauliSpectralJetLaw olean generated with `lake env lean -o ...`. Scratch deleted and directory removed; owned Lean sessions terminated normally, process check empty.

## Exact mathematics
- Number full weight<=2 Pauli real coefficient source by Fin D, D=card(PauliBoundedLabel n 2)>0.
- Anchor spectral differences at all-false bitstring. Finite-type theorem `pauliProjectiveSpectrum_finiteType`: derivatives of positive orders <=n+1 span target. This uses existing actual full-Pauli jet detection; no assumed rank condition.
- `pauliProjectiveSpectrum_uniform_good`, `pauliBalancedAction_uniform_good`: KM Proposition3.4 gives uniform good-function exponent alpha=1/[D(n+1)].
- `pauliProjectiveSpectrum_uniform_smallBall`: local radius rho>0, K>0; for any affine coefficients (c,w) with supnorm>=1, volume{|c+w.F|<eps} <= K eps^alpha volume(ball rho). Compactness + independence supplies uniform positive sup lower bound; no unknown supremum remains in denominator.
- `pauliBalancedIntegerAction_uniform_smallBall` at line276: same rho,K before all real translations c and all nonzero balanced integer k. Nonzero balanced integer tail has norm>=1. Literal commonReferencePauliAction is used.
- `pauliReplicaAction_allOrders_smallBall` at line335: same rho,K before ALL replica orders r and characters realized at r; obtains balance from equal positive/negative counts. Constants independent of r/character height.

## Honest scope boundaries
Estimate for EACH character, NOT their infinite union. Local parameter ball around fixed diagonal reference, not a global random local-Hamiltonian ensemble. Constants existential, dependent on n, no useful explicit size control proved. This is spectral-action small-ball suppression, NOT growing-replica observer-Jacobian/coarea/incidence suppression. Retains no fibre sheets or occupied circuit-image estimate. NO circuit exclusion, first-return, plateau, Brown–Susskind or physical black-hole theorem closed. Underlying generic sublevel theorem is known KM1998, not claimed novel. Concrete finite-type application is checked; external novelty not certified.

## Optimization
Default limits throughout. Explicit source-equivalence derivative transfer avoids expanding derivatives. Final elaboration fixes were explicit Fin.cons dependent function type and reducing Pi-zero integer casts before exact_mod_cast. Earlier StarSpectralJetFrame heartbeat removal remains as previously verified; not re-audited.

## Search/literature
Broad hybrid/deep vector corpus searches performed; partial coverage/semantic deadlines reported, not exhaustive. Useful exact sources: KM.NonDegenerate.prop_3_4, Prop23.indep_of_nondegenerate, exists_supGe; existing SpectralCharacterReplicaHeightLaw reused (not duplicated). Coarea receiver, BetaThresholdIncidenceLaw still do not supply suppression. KM original https://arxiv.org/abs/math/9810036, HTML Proposition3.4 checked. Broad recent arXiv spectral/nonconcentration search: 2607.28882 geometric-flow nonconcentration and 2605.17513 Markov hitting times not directly transferable to once-drawn deterministic Hamiltonian.

## Lint status
`scripts/formal_tools.py lint` exit1 ONLY 21 unrelated unreachable owned modules (other concurrent work), plus pre-existing large-file warnings. New leaf reachable. Unreachable list: RHTower CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, ChebyshevLagWindow, ChebyshevLagZeroWindowTerm, ChebyshevShortWindowLowerBound, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ThetaRateLaplaceBernstein, ThetaRateMobiusSourceTransfer, ZetaZeroDensityPowerSaving; HTGeometry AbelianZetaGas.SocleChamberLaw, SocleExchangeWork, SocleMomentGenerating; ChronologicalTensor.CubicRecoveryEnergyMinimizer; GaussianFrullaniLogKernel; RateMobiusInversion. Left untouched, no global lint success claim.

## Next actual hard step
Do not mistake scalar bounds for missing core: need quenched incidence-normalized coarea mass with fibre multiplicity and occupied endpoint image after budget-dependent initial removal, strong enough for complete circuit union. N_inc*A_exc < [c*(eps_w-eps_n)/(v*T)*(1-eps_w^2)^r]^2 remains unproved. Scalar all-order estimate may support quantitative detuning/Fourier suppression, but coefficient/circuit multiplicity, determinant lower tails, and n-explicit constants need genuine new arguments. Goal remains active/unsolved.

Requested hgt-fields-medalist skill path absent; available L7 skill read and 3-phase assessment presented before implementation. No new skill claims.