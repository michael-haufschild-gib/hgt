# Infinite mixed Euler-deletion decomposition — Lean closed

Current user task `formalize the infinite decomposition` is complete for the exact fixed-modulus complex equality, ordinary-cutoff convergence, and absolute convergence of the literal remainder. This is a [BRIDGE]; RH and arithmetic vanishing remain open. User's research-method steering preserves frozen conjectures and labels weaker claims [BRIDGE].

Modules in formal/GaloisForLFunctions/RHTower, all wired into RHTower.lean:
- EulerDeletionPowerSumRemainder.lean: actual R_s(N)=S_N-zeta(s)-N^(1-s)/(1-s)-N^(-s)/2; norm_powerSumRemainder_le gives norm ≤ norm(s*(s+1))/(Re(s)+1)*N^(-Re(s)-1), weighted decay, conjugation from centered continuation, summable_norm_remainder, tendsto_remainderPrefix.
- EulerDeletionMixedDecompositionFinite.lean: subtract unit deletion; exact half-endpoint cancellation, endpointError_decomposition, mixedPrefix_decomposition_with_error.
- EulerDeletionInfiniteDecomposition.lean: tendsto_endpointError, tendsto_boundaryDifference, tendsto_mixedPrefix_blocks, tendsto_mixedPrefix (ALL ordinary cutoffs), infiniteMixed_eq_decomposition, infiniteMixed_eq_strict, infiniteMixed_eq_critical, infiniteMixed_one, infiniteRemainder_eq_conjugate_exponent. Namespace RHTower.DeletionMixedRefinement.

Equality for 1/2≤sigma=Re(s)<1, p>0: T_p=(c_p-1)|zeta(s)|² + zeta(2sigma-1)/(1-conj(s))*(p^(2-2sigma)-1) + B_sigma(p) + W_p-W_1. B=(p^(1-2sigma)-1)*zeta(2sigma)/2 in strict-right strip, B=-log(p)/2 on critical line. T uses limUnder atTop of actual mixedPrefix; never unordered tsum. W uses absolutely convergent tsum with actual conjugated R_s, identified with R_conj(s).

No higher 1/12 expansion needed: uniform remainder bound suffices. Critical harmonic-sum difference yields log; fixed residue classes extend complete-cell convergence. Unit p=1 checked symbolically. No experiment, axiom, placeholder, or computational certificate.

Verification: scratch lake env lean and published final leaf check passed; serialized LEAN_NUM_THREADS=1 lake build --old for all 3 leaves passed, only each leaf actually rebuilt. Scratch #print axioms audit all 55 public declarations: only propext, Classical.choice, Quot.sound. Index refreshed; theorem searchable. No owned Lean process remains. Global lint --check-generated FAILED solely on unrelated new shared-tree HTGeometry.DigammaMittagLeffler module missing from HTGeometry umbrella (plus existing large-file warnings); did not modify that unrelated module. Do not claim global lint passed.

Docs updated: in-progress/euler-deletion-growing-modulus-decomposition.md, euler-deletion-refinement-arithmetic-identity.md, rh-current-frontier-map.md, universal-law-field/STATUS.md MIXED-SCALE-001. Certificate: docs/drafts/pipeline/3-formalized/euler-deletion-infinite-decomposition.md. Stronger W_p 1/12 asymptotic, Re W_1 identity, growing-p limits, bounded-correction characterization remain PAPER results, explicitly separated. No RH implication/annihilation theorem or no-go for all identities.

Workspace contains extensive other uncommitted work. Preserve it; no commit/push requested. Goal was PAUSED user-controlled; did not change it. User forbids full/umbrella builds and excluded classic RH machinery; use one owned foreground Lean process, lake env lean scratch, narrow final leaf build only.