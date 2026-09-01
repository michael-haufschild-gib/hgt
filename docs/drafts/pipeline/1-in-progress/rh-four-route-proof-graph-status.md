# RH four-route facts

Frontier map read-only. Facts only; cards hold proofs.

## Closed

- Common charge `C(q)=1-2 Re(q)` controls HB, FZZ-P, all-grade PW-B, RBH receivers; universal extinction iff RH.
- Literal source-FE gain is `>1/=1/<1` left/on/right of wall; reflected gains multiply to `1`. Unit gain, fixed physical pairing, clock covariance, and receiver extinction are equivalent.
- HB full causal orbit is `K_n(q)=-Sigma_n(q) normSq(D_n(q))`, `Sigma_n(q)>0`; source→clock→four-route transduction is closed.
- Global target-independent Peierls incidence, causal QNM residue extraction, source range-cohomology invariance, and literal unsquared-source orientation are closed.
- HB analytic perturbative QNM-clock route is dead: triangular towers always absorb source; arbitrary analytic all-order backreaction has one continuous pole germ per Xi QNM, so nontrivial zero-coupling resonance collision cannot escape. Off-wall partner germs stay distinct.
- HB finite/discrete phase passports, projective QNM normalization, diagonal adjoint-QNM positivity, generic KMS/passivity, FE-invariant response repair, bounded/global source response classes, and unbounded self-adjoint angular exclusion are dead.
- HB bounded nonnormal passive extinction is dead: dissipative/antidissipative half-plane shifts give unique nonzero responses for both exact sources on every tilted Schwarz pair.
- HB closed order-maximal unbounded passive extinction is dead: any range defect yields a proper dissipative extension; maximality forces unique nonzero reflected responses.
- HB arbitrary-domain passive diagonal response is dead: every existing exact response has strict standard-passive polarity, opposite to HB's needed sign; no closedness, maximality, density, or surjectivity is needed.
- HB jointly analytic complex-bilinear left-QNM/right-response compensation is dead on every nonempty open strip patch: dual evaluation stays holomorphic and cannot equal the forced horizontal AIME/third-mass susceptibility. Dimension and response-space completeness are irrelevant.
- HB finite-dimensional Schwarz-polarized/Hermitian compensation is dead: exact AIME/third-mass susceptibility has infinite separation rank on `(0,1/2)^2`; no regularity of separated legs is assumed.
- FZZ-P all-level selection premise is overstrong: `k=4` square-reality plus `k=3` nonpositivity already forces `Re ω=0`; full chambers at these two levels iff wall. One level never suffices.
- FZZ-P cross-level transport is unnecessary: reciprocal higher-genus holonomies at cycles `n,2n` of one fixed CFT have odd parts `sinh z,sinh(2z)`; for `n≠0`, their reality/passivity chamber iff real twist iff zero radial monodromy iff unit holonomy. Canonical Mellin twist makes cycles `1,2` the dyadic character and its square; chamber iff `Re ρ=1/2`.
- FZZ-P unmarked Haar selector is dead: squared cycle-`n` odd holonomy has exact compact charges `{0,±2n}`; nonzero-cycle zero mode is `-1/2`, so averaged cycle-`n,2n` chamber is automatic off wall. Continuous backgrounds couple only through charges `0,±2n`; normalized marked `±2n` modes recover reciprocal radial holonomy, and positive marked unit norm iff zero radial monodromy.
- FZZ-P scalar tempered generalized occurrence is dead: for every `S∈𝓢'` and `E∈ℝ`, `(x-E)T=S` is solvable; solution fibre is exactly `T₀+ℂ·δ_E`. Occurrence set is `ℝ`, hence nonselective.
- PW-B unbounded absolutely endpoint-admissible positive matrices are dead: all-scale darkness forces every antidiagonal and row to vanish. `K(i,j)=2ⁱ2ʲ` is an unbounded admissible witness, so this strictly extends bounded tomography.
- RBH separated architecture is terminal. PW-B bounded pairwise-positive kernels and closed Hilbert dark relations are dead. Finite tensor/Gamma-ghost and finite source-decoder classes are dead.

## Open core

Derive source-specific physical Ward/orientation from actual dynamics:

- **HB:** prove opposite sign `0 ≤ K_n(q)` from literal Einstein--Teukolsky source. Schwarz/Hermitian compensation must have infinite separation rank; remaining legs are genuinely infinite-dimensional/nonseparated, distributional, support- or sheet-changing, or outside scalar pairing. Linear extinction can only use non-maximal deficiency/domain exclusion; other survivors are nonpassive, nonlinear, or source-fixed off-diagonal cancellation.
- **FZZ-P:** derive torus replica-area resonant Fourier modes at charges `±2,±4` with required cycle signs, or source-derived nonlocal boundary/renormalization law fixing Dirac fibre, singular branch-cut, matrix/interacting carrier. Unmarked/resonance-gapped sources and scalar tempered occurrence are dead. Then close reflected divisor incidence.
- **PW-B:** nonclosed/domain-excluding, indefinite, non-absolutely-summable/singular, nonlinear, or nonpointwise global source law.
- **RBH:** nonseparated, nonlinear, or singular source law.

HB collision survivors: nonanalytic zero-coupling behavior or remote strong-coupling exceptional points only.

## Certificates

- HB: `d4HBPreDivisorFiniteSchwarzPolarizedRouteKilled`.
- FZZ-P: `fzzReplicaLevelsThreeFourKreinSign_iff_re_eq_zero`, `fzzHigherGenusCyclePairKreinSign_iff_im_eq_zero`, `fzzCigarParityMellinCyclePairKreinSign_iff_re_eq_half`, `fzzHigherGenusOddHolonomy_sq_fourierCoefficient`, `fzzAveragedHigherGenusCyclePairKreinSign_off_radialWall`, `fzzHigherGenusOddHolonomy_sq_weightedAverage_resonance`, `fzzPunctureTemperedScalarOccurrence_set_eq_univ`.
- PW-B: `schwarzschildParikhWilczekAbsolutelyAdmissiblePairwisePositiveEndpointDarkRouteKilled`, `summable_pwMatrixEndpointEnergy_of_absoluteAdmissible`, `pwExponentialGramKernel_absolutelyAdmissible`, `pwExponentialGramKernel_not_uniformlyBounded`.

Direct Lean/targeted builds PASS; axioms `propext`, `Classical.choice`, `Quot.sound`; umbrellas wired.
