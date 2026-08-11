Formalized finite spectral chord action in formal/GaloisForLFunctions/HTGeometry/FiniteSpectralPhaseActionLaw.lean.

Proved:
- phaseNormalize is unit norm and 2-Lipschitz relative to a unit target.
- spectralPhaseAction is vertex-error stable, L2 stable with loss 4 sqrt(D) sqrt(sum error^2), subadditive under pointwise phase multiplication, globally phase invariant, and <=2(D-1).
- full matrix entrywise error controls recovered diagonal phase action.
- unitaryTraceAlignmentPhase gives exact projective identity ||W-cT||_HS^2 = 2D - 2 |tr(T^*W)|.
- finiteUnitary_choiPhaseAction_lower: for diagonal unitary T, Choi/normalized trace overlap yields exact recovered centralizer phase action with explicit Hilbert-Schmidt loss.
- alternatingSpectralPhase attains maximal action 2(D-1), proving this invariant alone cannot lower-bound circuit depth; a one-bit carrier can saturate it.

Validation: direct lake env lean passed; lake build GaloisForLFunctions.HTGeometry.FiniteSpectralPhaseActionLaw passed; axiom audit only propext, Classical.choice, Quot.sound. Global formal_tools lint presently fails only because unrelated concurrently added RHTower/HTGeometry modules are umbrella-unreachable; target module is umbrella-reachable and forbidden-token scan is clean.

Interpretation: closes operator-norm-to-Choi extraction gap in centralizer phase branch, but does not close Brown O4. Exact remaining core is quenched selector-aware finite-scale undistortion/Bellman escape inside the moving centralizer after return and fast-forwardable carrier removal. See mem:quantum_recurrence/pauli_xor_kurtosis_bridge_2026_08_11.