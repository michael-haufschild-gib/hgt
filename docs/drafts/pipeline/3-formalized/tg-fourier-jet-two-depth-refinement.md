# TG-C9.10b: finite refinement failure and complete cubic graph classification

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Main leaf:** `PrimeBurnolFourierJetTwoDepthRelation`
- **Parent:** `../1-in-progress/tg-fourier-jet-mixed-cubic-closure.md`
- **Predecessor:** `tg-complete-fourier-jet-cubic-saturation.md`

## Exact answer

Let G be the completed even Fourier-jet graph, retaining both source coordinates and
both physical outputs. For every finite injective prime-depth packet F use its actual
two-output Gram C_F, canonical inverse, prime-dependent theta Q_F, original neutral
P_F and COMPLETE cubic

A_F=(C_F⁻¹Q_F C_F−P_F)³−(C_F⁻¹Q_F C_F−Q_F)³−(Q_F−P_F)³.

Let L_a be the linear span of all actual graph pairs (E_F x,E_F A_F x).

**Unconditional parameter classification:** L_a is single-valued iff a=0. Its closure
is G×{0} at zero and G×G at every nonzero parameter. No linear action can retain all
finite packet actions away from zero, even before completion. No closedness premise
is needed for this obstruction.

The mechanism is actual finite refinement, not an inference from a nonclosable theta
factor. For F_n=((p,n),(p,2n+1)), the COMPLETE two-depth cubic minus its two COMPLETE
singleton actions is invertible for every sufficiently late n, whenever a is nonzero
and unbalanced at p. Every parameter has an unbalanced prime, proved using Euclid's
theorem and the existing uniqueness of a balanced prime.

## Dependency-closed paper proof

1. Write λ=(n+1)log p and depth ratios r=(1,2). Actual column amplitudes A_i are nonzero.
   Exact mixed physical inner products, with both Euler amplitudes retained, are
   4A_i A_j/(λ_i+λ_j)³ and 1440A_i A_j/(λ_i+λ_j)⁷ for the ordinary and square-position
   outputs. The actual Fourier cross term is
   2A_i A_j/(λ_i²λ_j²) I(1/(λ_iλ_j)), where the certified source integral I tends to 2.
   The exact jet norm and Fourier isometry control the retained jet cross term;
   after λ⁴ normalization it tends to zero. No numerical experiment is used.
2. With the actual channel-amplitude diagonal D_n, normalize
   Cbar_n=λ³ D_n⁻¹ C_n D_n⁻¹. This is an equality, not a replaced Gram.
   Its blocks are [[G_n,H_n],[H_n,G_n]], with
   G_n→G=[[1/2,4/27],[4/27,1/16]] and λH_n→H=[[4,1],[1,1/4]].
   Hence Cbar_n→diag(G,G), and its inverse tends to diag(G⁻¹,G⁻¹).
3. The actual P and Q commute with D_n. The canonical modular action and COMPLETE
   cubic therefore conjugate exactly: Abar_n=D_n A_n D_n⁻¹. The singleton assembly
   also commutes with D_n. No bound on inverse amplitudes is assumed or needed.
4. Put Q=[[uI,wI],[wI,(1−u)I]], u=visibility², w=visibility·contrast.
   The diagonal Gram block commutes with Q exactly. Consequently
   λ(Cbar_n⁻¹ Q Cbar_n−Q)→(2u−1) skew(G⁻¹H), where skew(B)=[[0,B],[−B,0]].
   The full noncommutative cubic increment retains all linear and quadratic terms.
   With Δ=Q−P, Δ²=(1−u)I and Δ skew(B)=−skew(B)Δ. Thus
   λ Abar_n→k skew(G⁻¹H), k=(2u−1)(1−u).
5. The actual singleton limits are λ_i A_i→8kJ. Their source-coordinate assembly,
   scaled by the common λ, tends to k skew(T), T=diag(8,4). Therefore the EXACT
   amplitude-conjugated refinement defect Bbar_n has limit
   λ Bbar_n→k skew(G⁻¹H−T).
6. The source-forced identity G(G⁻¹H−T)=[[0,11/27],[−5/27,0]] proves invertibility
   of the residual. For nonzero a unbalanced at p, k≠0. Determinant continuity gives
   eventual invertibility of Bbar_n and exact conjugacy transfers it to B_n.
7. The sum of the singleton graph pairs is exactly (E_F x,E_F S_F x). Subtract it
   from the full packet graph pair to obtain (0,E_F B_F x) in L_a. Invertibility
   gives every vertical packet source vector exactly. Subtract such a vertical
   vector from a packet graph to obtain every horizontal packet source vector.
8. In particular every sufficiently late first-depth cell supplies both its horizontal
   and vertical graph columns. Every prime-depth tail is graph-dense in G, so
   closure(L_a)=G×G. A single nonzero vertical column already disproves finite
   single-valuedness. At zero the full cubic is identically zero, giving G×{0}.

## Lean interfaces

- `primeBurnolFourierCross_inner_pair`: actual mixed Fourier integral.
- `primeBurnolTwoDepthNormalizedGram_tendsto` and `_inv_tendsto`: complete Gram limits.
- `primeBurnolTwoDepthNormalizedCubic_conjugate`: exact full-cubic amplitude transport.
- `primeBurnolTwoDepthNormalizedCubic_scaled_tendsto`: actual two-depth boundary symbol.
- `primeBurnolTwoDepthNormalizedRefinement_scaled_tendsto`: exact surviving refinement symbol.
- `primeBurnolTwoDepthRefinement_eventually_isUnit`: original refinement defect invertibility.
- `primeBurnolFourierJetCubicRelation_refinement`: exact finite vertical graph identity.
- `primeBurnolFourierJetCubicRelation_closure_classification`: complete parameter classification.
- `primeBurnolFourierJetCubicRelation_single_valued_iff`: finite compatibility iff zero.

## Positive survivor and scope

At every nonzero parameter, every completed source/response pair is simultaneously
approximable by finite sums of actual packet graph pairs. The stronger finite result
supplies exact horizontal and vertical directions on each sufficiently late cell.
The full skew boundary symbol and the invertible refinement residual are also
certified; no summand of the cubic or physical output was discarded.

This retires the all-packet finite-compatible completion candidate. It does not rule
out a separately specified cofinal relative construction that changes the finite
actions by a source-derived joint prime–Gamma correction. Gamma–Xi identification,
Hardy-index transfer and sub-unit production remain open. RH goal remains unmet.

## Verification

The source integral search completed without errors. Conjugacy and subsequent
relative-source searches returned partial results with declared reranking or semantic
retrieval timeouts; available source arguments were used, with no absence inference.
All six new leaf proofs and both changed precursor proofs pass scratch/production
checks as recorded in the working log. All eight affected production leaves have current oleans and umbrella imports. The
final relation production check and separate /tmp API/axiom audit pass all 124 public
declarations across these leaves. The only printed axioms are propext, Classical.choice
and Quot.sound. Final exact-name corpus search refreshes and retrieves the classification.
All checks use foreground `lake --old env lean <leaf>`; no full umbrella build.
Scope whitespace is clean. Global `scripts/formal_tools.py lint` exits one only for
the same ten unrelated unwired modules: CCMApertureChainProfile,
CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. No TG leaf error.
No new axiom, proof hole, numerical experiment, heartbeat increase, full/umbrella
build, subagent, commit or push.

All owned processes exited; temporary proofs/searches/audit logs were removed after
recording results. Next hard source-construction card:
`../1-in-progress/tg-joint-prime-gamma-relative-lift.md`. Scalar prime–Gamma/Xi
log-derivative identities already exist; the operator/relative-class realization
and its Hardy cubic remain the hard construction target.
