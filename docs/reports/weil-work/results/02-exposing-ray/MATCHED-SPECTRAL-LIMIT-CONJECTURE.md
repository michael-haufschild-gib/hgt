# Next gate: the complete spectral density of exact matched rays

Cycle18 decision: DEFERRED, not disproved. The proposed density limit controls constructed upper families only. PRIMITIVE-SHARPNESS-PROOF.md identifies a concrete uniform debit in an existing lower method without adding a routine density limit; the joint arbitrary-family lower bound remains the priority.

Status: OPEN source conjecture / paper and utility audit required. Not a lower-bound proof. Do not formalize merely to package another known near-null argument.

## Exact candidate

Use the actual full real polar Riemann profiles P_c Phi, c_k=1/(k+1), and the current paperFT normalization. Define

    D(tau) = sum_(k>=0) 2^(-k)/(2*pi) * |paperFT(P_(c_k) Phi)(tau)|^2.

Conjecture fixed constants C,K>0 such that every sufficiently large N admits one actual nonnegative finite C2 polar family with aperture <=log(N)/2+C, exact complete trace w_N, energy <=T+2*tau_N, AND

    integral |sum_i alpha_i*|paperFT f_i(tau)|^2-D(tau)| d tau <= K*tau_N.

All properties must hold for the same repaired family. D must be proved integrable and nonzero. No convergence of arbitrary matched families is conjectured.

## Literal mechanism to audit

The existing FiniteRealization proof retains its entire positive source family and appends one signed two-point resonator per integer residual r_n. Its coefficient is |r_n|/(4*pi*resonatorMass n). If the disjoint-support identity M(twoPointResonator n,+/-1)=2*resonatorMass n is verified, Plancherel gives EXACT added spectral L1 mass sum_n |r_n|. Every repair density is nonnegative. The existing weighted residual estimate can then control this mass using log(n)+boxConst>=log(2)>0.

For the source rows, use actual L2 convergence of Phi_L to Phi, uniformly under P_c for 0<=c<=1, and the inequality |||F|^2-|G|^2||_1 <= ||F-G||_2*(||F||_2+||G||_2). Sum the complete finite and infinite dyadic tails; verify the error rate against the literal tau_N lower envelope. Do not replace the signed archimedean energy by an unsigned surrogate or omit any residual atom.

The present existential repair API does not retain the source inclusion or repair mass. Prove an appropriately stronger construction without duplicating its entire proof and preserve its current clients. Every claimed identity needs verification against the literal resonator profile and current Fourier normalization.

## Utility / hostile gate

If closed, bounded spectral debits V can be tested on the SAME exact matched families: their integrals converge to integral V*D. In particular a nonnegative debit with positive D-pairing would violate the original threshold after subtraction, despite exact all-integer matching. This would sharpen the constant-mass precision boundary and locate the surviving debit.

Do not yet claim every nonzero continuous nonnegative V has positive D-pairing. That needs a proof about the full actual Fourier profile's zero set. Do not confuse real-axis spectral L1 convergence with convergence against the unbounded signed gamma symbol, nor infer a lower energy sign.

Before committing to Lean, compare this consequence against the existing near-null margin and critical-zero-carried/exposure results. If the only new output is routine regularity for an already paid obstruction, defer it and attack a joint trace-dependent gamma certificate instead. A successful lower certificate must compensate its spectral losses using the actual matching identities; the failed fixed mass margin supplies no such compensation.

## Corpus evidence

Cycle17 deep query `exposing finite realization repaired spectral density L1 mass convergence resonator` completed non-partial with68,557 indexed/inventoried files. All20 candidates and20 source-argument statements inspected. Retrieved actual repair, pole, Gram realization, tail budget and generic spectral normalization results; the proposed ingredient set establishes no density limit. Compiler enrichment mostly pending/stale, refresh background_indexer_running. Exact source reads verified current repair coefficients and the resonator definitions; the mass identity and complete density limit remain unverified. No absence claim or external scientific novelty claim.
