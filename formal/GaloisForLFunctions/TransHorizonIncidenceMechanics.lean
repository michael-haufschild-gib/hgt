import GaloisForLFunctions.TransHorizonIncidenceMechanics.ValuationClockChainBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonRoughAbsorptionAndReset
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabHorizonFiltrationAndSawtoothEvolution
import GaloisForLFunctions.TransHorizonIncidenceMechanics.QuotientSpectralGapAndOddChainCoercivity
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonMartingaleTelescopeAndPrimeCheckpoints
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SecondAndThirdBandRenormalizedDefectCalculus
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TwoPrimeDeletionAndFullThirdBandEnvelope
import GaloisForLFunctions.TransHorizonIncidenceMechanics.InterCheckpointSawtoothExcursionAndPronicSandwich
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ClockScheduleSynthesisAndPrimePowerPhaseRecovery
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeClockWaveletTensorAndPhaseRecovery
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonGramMatrixAndRadicalProjection
import GaloisForLFunctions.TransHorizonIncidenceMechanics.AllHorizonRadicalSawtoothAndDefectReduction
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonRadicalStateAndDefectNormalForm
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RadicalCheckpointSignRigidityAndGaugeLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ActiveSawtoothPowerSamplingAndCalibratedRecovery
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ActiveSawtoothInterpolationAndSharpConditioning
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteMultiplicativeObservationState
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SuccessorStateObstructionAndPhaseRefinement
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ArithmeticUncertaintyAndSpikeCancellation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiPointDefectAveragingAndPeriodConservation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PrimeChainSieveBridgeAndSpectralCutoff
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SlidingPeriodPoincareCoercivityAndHarmonicDecomposition
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabFermiCovarianceAndQuotientChainBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TotientObservabilityThresholdAndValuationFiberCollision
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification
import GaloisForLFunctions.TransHorizonIncidenceMechanics.NonnegativeWeightEndpointOrderAndCalibratedDefect
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DownwardBuchstabL2TelescopeAndSawtoothCoupling
import GaloisForLFunctions.TransHorizonIncidenceMechanics.OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.GlobalPrimeChainHyperbolicCoercivityAndClockStepBound

/-!
# Trans-Horizon Arithmetic–Archimedean Incidence Mechanics (`GaloisForLFunctions.TransHorizonIncidenceMechanics`)

Umbrella module for **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**: a formalized
theory of truncated divisor sums $s_{N,c}(k) = \sum_{d \mid k,\, d \le N} c(d)$, $L_N$-even and
primorial-even arithmetic observation states ($\gcd(k, L_N)$ and $\gcd(k, N\#)$), totient
observability thresholds and valuation-clock fiber collisions, short-window shifted correlation
defects and iso-state endpoint classifications, downward Buchstab $L^2$ telescopes, composite
squarefree horizon steps, and sawtooth fractional-part couplings, off-line hyperbolic prime-chain
variance excesses and valuation-clock step lower bounds, and Ramanujan/Selberg quadratic-form
identities bridging `BezoutValuationIncidence` with `RHTower` and `BiScaleUncertainty`.

## The Modules

1. `ValuationClockChainBridge`: Valuation-clock to prime-chain bridge ($\Lambda(d) = \log(d / \tau_{\mathrm{vis}}(d))$, pronic composite clock quotients, and `chainVariance`).
2. `TransHorizonRoughAbsorptionAndReset`: Multiplicative monoid of $N$-rough integers (`IsTransHorizonRough N r`), exact sieve/sawtooth absorption, and cofinal defect non-positivity at $N$-rough checkpoints.
3. `BuchstabHorizonFiltrationAndSawtoothEvolution`: Buchstab horizon band evolution ($N_1 \le N_2$), tail closure at $N_2 = M$, and the first-octave identity.
4. `QuotientSpectralGapAndOddChainCoercivity`: Odd-sector spectral window $\lambda \in (1/2, 1)$ on `SourceGraph ⧸ signedRadical` and prime-chain Poincaré equivalence of `RiemannHypothesis`.
5. `TransHorizonMartingaleTelescopeAndPrimeCheckpoints`: Active-deleted martingale variance telescope, variance floor, and prime checkpoint identities.
6. `ComplementaryQuotientAndSecondOctaveLaw`: Complementary quotient tail operator (`complementaryQuotientTail`), Dirichlet hyperbola divisor pairing ($d \leftrightarrow k/d$), $B$-rough extension to $(B+1)N$, and second/third band closed forms.
7. `SecondAndThirdBandRenormalizedDefectCalculus`: Endpoint envelope control via prime-quotient contraction across the second band $M + 1 \le 3N$ (parity-free) and third band $M + 1 \le 4N$ (`¬ 2 ∣ M + 1 ∨ ¬ 3 ∣ M + 1`).
8. `InterCheckpointSawtoothExcursionAndPronicSandwich`: Inter-checkpoint Dirichlet excursion identity, boundary-bounded monotonicity, and rough-neighbor pronic localization (`pronicSeq (r - 1)` and `pronicSeq r`).
9. `ClockScheduleSynthesisAndPrimePowerPhaseRecovery`: Prime-power evaluations of Ramanujan sums at divisor lags, two-level differences (`clockWaveletMultiplier`), and dipole cancellation (`clockWaveletRamanujan`).
10. `CompositeClockWaveletTensorAndPhaseRecovery`: Multiplicative tensor factorization of Ramanujan lag differences across coprime moduli.
11. `TransHorizonGramMatrixAndRadicalProjection`: All-horizon squarefree divisor collapse (`sieveSeq N c (d * k) = sieveSeq N c k` for $d \mid k$ and `sieveSeq N c (k ^ m) = sieveSeq N c k`) and horizon-band $L^2$ Gram expansion.
12. `AllHorizonRadicalSawtoothAndDefectReduction`: Radical sawtooth invariance under divisor-multiplication and arbitrary powers at every horizon, plus damped first-octave power-checkpoint defect non-positivity.
13. `HorizonRadicalStateAndDefectNormalForm`: Primorial-even squarefree observation state (`horizonRadicalState N k = Nat.gcd k (primorial N)`), squarefree observation classification, and defect normal form.
14. `RadicalCheckpointSignRigidityAndGaugeLaw`: Unit-coefficient shift (`sieveUnitShiftWeight`), active sawtooth invariance, and converse classification proving that $N$-rough endpoints (`horizonRadicalState N (M + 1) = 1`) are the unique weight-universal non-positive checkpoints.
15. `ActiveSawtoothPowerSamplingAndCalibratedRecovery` & `ActiveSawtoothInterpolationAndSharpConditioning`: Power-checkpoint sampling and interpolation of active sawtooth sums.
16. `FiniteMultiplicativeObservationState`: $L_N$-even observation state (`horizonObservationState N k = ((Icc 1 N).filter (· ∣ k)).lcm id = gcd(k, L_N)`), universal weight indistinguishability classification, and multiplicative quotient monoid descent.
17. `SuccessorStateObstructionAndPhaseRefinement`: Exact horizon boundary classification ($N \le 2$) for successor congruence of $L_N$-even states and residue phase refinement (`horizonObservationPhase`).
18. `ArithmeticUncertaintyAndSpikeCancellation`: Endpoint-spike cancellation via consecutive correlation ($2\widetilde{\mathcal{D}}_N(M; c) = -E_{N,c}(M-1) + 2 s_{N,c}(M) s_{N,c}(M+1) - s_{N,c}(M)^2 - s_{N,c}(1)^2$), predecessor-zero absorption, two-point averaging, and finite-path Cauchy–Schwarz lower bounds.
19. `MultiPointDefectAveragingAndPeriodConservation`: Phase-independent period Dirichlet energy (`horizonPeriodDirichletEnergy`), linear defect drift along phase subsequences, and full-period moving-average conservation (`horizonPeriodDefectWindow`).
20. `PrimeChainSieveBridgeAndSpectralCutoff`: Prime-chain horizon step ($s_{H,c}(p b) - s_{H,c}(b) = s_{H/p, c(p\cdot)}(b)$), cutoff of `CHMDPrimeChain.varianceEnergy` for $p > H$, excited-shell collapse (`scatter chainRight = 0`), rank-1 ground-state reduction for $p \le H$, and terminal-band evaluation on `sievePrimeTail H`.
21. `SlidingPeriodPoincareCoercivityAndHarmonicDecomposition`: Complete-period Selberg/Ramanujan variance and Dirichlet-energy identities in coordinates $Y_q = \sum_{q \mid d \le N} c(d)/d$ without `ker P` restriction (with excess $\sum_{e=2}^N (\varphi(e) - 2\mu(e)) Y_{N,c}(e)^2 \ge 0$), sliding-period translation invariance, and the complete-period unit-constant inequality $\operatorname{Variance} \le \operatorname{DirichletEnergy}$.
22. `BuchstabFermiCovarianceAndQuotientChainBridge`: Single-horizon $L^2$ step identity, non-squarefree horizon invariance, prime-horizon quotient reduction via $N$-roughness, and quadratic-window ($p \le M < p^2$) evaluation $\mathcal{E}_p(M; \mu) - \mathcal{E}_{p-1}(M; \mu) = \lfloor M / p \rfloor - 2$.
23. `TotientObservabilityThresholdAndValuationFiberCollision`: Sharp totient observability threshold ($W \ge \varphi(p^a) = p^a - \tau_{\mathrm{vis}}(p^a)$), valuation-clock fiber collision counterexamples ($k = 1, \ell = 1 + p^{a-1}$) below $\varphi(p^a)$, and strictly sub-$N$ phase recovery thresholds $\Phi_{\max}(N) = \max_{p^a \le N} \varphi(p^a) < N$ (general weights) and $\Phi_{\mathrm{rad}}(N) = \max_{p \le N} (p - 1)$ (squarefree weights).
24. `ShortWindowCorrelationDefectAndIsoStateClassification`: Short-window renormalized correlation defect $\widetilde{\mathcal{D}}_N(M_0, M; c)$ for arbitrary starting phase $M_0$ and window length $M \ll L_N$, sharp iso-state endpoint classification (`forall_weight_shortWindowRenormalizedDefect_nonpos_iff_state_eq` and `forall_squarefree_shortWindowRenormalizedDefect_nonpos_iff_radicalState_eq`), starting-phase-free right-zero-cone contraction for $\mu$, and matched-assumption domination over classical $\ell^1$ remainder bounds.
25. `DownwardBuchstabL2TelescopeAndSawtoothCoupling`: Top-horizon sub-horizon closure ($\mathcal{E}_{N_2}(M; \mu) = 1$ for $1 \le M \le N_2$), downward squarefree Buchstab $L^2$ telescope, prime-horizon Buchstab–sawtooth fractional-part identity (`sieveL2PrefixEnergy_prime_horizon_sub_eq_sawtooth`), and universal scale-halving $L^2$ energy subadditivity $\mathcal{E}_N(M; c) \le \mathcal{E}_{N+1}(M; c) + \mathcal{E}_N(\lfloor M / (N + 1) \rfloor; c)$.
26. `OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence`: Polar-phase edge factorization on $p$-adic prime chains, exact functional-equation pair $(+\beta, -\beta)$ hyperbolic excess over the critical-line ($\beta = 0$) `varianceEnergy` (`varianceEnergy_symmetrized_offline_sub_critical_eq`), strict positivity on every non-empty prime-chain cut for $\beta \ne 0$ (`strict_pos_symmetrized_offline_excess_of_mem_cut`), and second-order prime-chain recurrence (`offlineChainWaveCos_step_recurrence`).
27. `CompositeSquarefreeStepAndMultiOctaveL2Energy`: Universal first-band step $\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = -\mu(n + 1)^2$ and second-band $2$-adic parity dichotomy ($-2\mu(n + 1)^2$ for $2 \mid n + 1$ via radical divisor absorption, $0$ for $\neg(2 \mid n + 1)$ via second-octave valuation switching) without primality hypotheses, closed-form two-band $L^2$ energy evaluation ($M < 3(N + 1)$), and general composite-step dilated energy subadditivity (`sieveL2PrefixEnergy_le_succ_add_dilated`).
28. `GlobalPrimeChainHyperbolicCoercivityAndClockStepBound`: Global von Mangoldt-weighted `chainVariance` lift of the functional-equation $(+\beta, -\beta)$ hyperbolic excess over the critical line (`globalOfflineChainVariance_symmetrized_sub_critical_eq`) and explicit quantitative valuation-clock step lower bound $\log p \cdot r_\beta(b)^2 (e^{\beta \log p} - 1)^2 > 0$ (`chainVariance_offlineRadialEnvelope_ge_clock_step`, `globalOfflineChainVariance_symmetrized_sub_critical_ge_clock_step`).

See `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md` for the classical
baseline ledger, central mathematical problem, organizing principle, matched-assumption comparison,
and open research agenda.
-/
