# Fourth-moment return-residual near-action bridge (2026-09-08)

## Actual status
Main goal remains OPEN: prove quenched complete-circuit incidence-action suppression after a circuit-budget-dependent initial cutoff, continuously until a system-size-controlled first re-entry. No same-draw Brown–Susskind growth–plateau–first-recurrence or black-hole physical identification has been proved by this work.

Latest user request was wider custom corpus searches, remembering multi-term default AND. Used broad single terms, --any OR, pagination, and exploration across coarea, incidence, recurrence, anti-concentration, transport, hypercontractivity, entropy and Krylov. New theorem below is a corpus connection, NOT an externally established novelty claim.

## Added Lean
`formal/GaloisForLFunctions/RHTower/StaticChoiKurtosisNearActionLaw.lean`, namespace `RHTower`; wired into RHTower.lean immediately after StaticChoiPhysicalActionTransportLaw.

Let D be Hilbert dimension, Q = D^-1 HS([diag energy,U])^2, M4(a)=D^-1 sum_i (energy_i-a)^4, beta=D^-1 sum_{i!=j}|Uij|^2, S=D^-1 sum_i|Uii|. Existing unistochastic transport yields Q^2 <=16 M4(a) beta; existing centralizer Cauchy gives beta<=1-S^2. Therefore near-action <=exp(-r Q^2/(16 M4(a))). Includes arbitrary centering, zero fourth moment, empty dimension, scalar spectra, all replica counts and thresholds, all unitaries. Lean total division at zero is explicit, no positivity or source-tail assumption added.

More directly relevant return-removed theorem: `directStaticChoiTargetNearActionMass_anchorResidual_le_quarticDefect` (line ~187). For every positive dimension (n+1), energy, anchor time, center a, unitary U, r, delta, residual := staticChoiAnchorResidual energy anchor (choiVector U),
`nearAction residual <= (norm residual^2 - Q^2/(16*M4(a)))^r`.
Proof retains exact residual norm, uses off-diagonal mass invariance under subtraction of the diagonal orbit anchor, existing diagonal/off-diagonal Pythagoras, and new quartic transport. Nonnegative base is derived, not assumed.

Fixed-locality physical theorem `localPauli_directStaticChoiNearActionMass_le_exp_physicalEnergyRatio` (line ~323): for arbitrary n,q, real Pauli cube coefficients projected explicitly to weight<=q, H=pauliHamiltonian, every U,r,delta,
`nearAction <= exp(-r * HS([H,U])^4 / (16 * (9^q)^4 * (tr(H*H).re)^2))`.
The exponent ratio has no explicit dimension/global spectral-width factor. Uses existing `PauliXorIncidenceHypercontractivityLaw.pauliHamiltonian_eigenKurtosis`. This is NOT a uniform activation bound: Q/source energy can be small and is zero for commuting targets. Nor does it give complete action, occupied-image capacity, fibre sheets, time ordering, a first cutoff, or circuit-budget union suppression.

## Validation / build caution
Complete scratch proof and final leaf compiled successfully with `lake env lean`. Eight new theorem axiom checks all reported ONLY propext, Classical.choice, Quot.sound. No sorry/admit/new axioms/computations. Formal lint passed before final residual addition. Final rerun exited 1 only for concurrent unrelated module `GaloisForLFunctions.RHTower.SelbergModularCellUnfolding` unreachable from RHTower umbrella; no failure in the new module. Did not touch that concurrent work. Final leaf compile and all eight new axiom audits succeeded.

Tried ONLY `lake build GaloisForLFunctions.RHTower.StaticChoiKurtosisNearActionLaw` for final audit; Lake replayed large cached closure then spawned two transitive rebuilds concurrently. Stopped parent and exact owned children. It invalidated ProjectiveWeightedTargetVolumeLower.olean and ReplicaCrowdingCentralLimitFloor.olean; restored BOTH sequentially using `lake env lean <exact file> -o <exact olean>`. Then compiled new module the same way and ran scratch #print axioms import successfully. No umbrella/full build, git, or subagent use. Do not repeat automatic dependency rebuilds; use cached scratch and leaf checks. All owned Lean processes completed or were explicitly stopped; final filtered process inspection found none. Scratch Names.lean/Proof.lean/Audit.lean were removed after proof and audit, leaving the integrated source and its leaf olean.

## Broader-search findings to avoid false closure
`PairQubitProjectiveResidualDesignCubicFirstReturnLaw.exists_pairQubitProjective_growth_noCompleteTargetReturn` still ASSUMES hmoment and hselect and finite supplied endpoints. Its title is not proof that the decisive moment/complete circuit budget has been produced. Residual D-optimal and Bures/coarea receivers retain proper geometry but consume the missing source estimates. Fourth-moment activation is auxiliary, not a route around that mathematical core.

No paper updated; no Nature/novelty completion claim. Next frontier remains a source-level quenched bound retaining occupied target image, source-sheet multiplicity and ordered post-initial interval; commutator-only estimates discard phase/time information on the weakly commuting carrier.
