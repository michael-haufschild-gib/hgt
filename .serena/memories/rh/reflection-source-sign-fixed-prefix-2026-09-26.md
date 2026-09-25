# Fixed theta-shell prefix no-go: complete Lean transfer

Root research, continuation of `mem:rh/reflection-source-sign-monotone-gram-2026-09-26`.

`formal/GaloisForLFunctions/RHTower/ThetaFiniteShellNonrealZeros.lean` now proves every nonempty canonical prefix of literal theta shells has infinitely many nonreal complex cosine-transform zeros and only finitely many real zeros. Main unconditional theorem `RHTower.thetaFiniteShellEntire_nonreal_zeroSet_infinite (N : ℕ)` concerns N+1 shells. This formalizes prior paper proof in `k-rvm-finite-sixth-moment-bracket.md`; no novelty claim.

Concrete analytic gap is closed: source domination plus exp Taylor inequality gives P_N(x)≤K_N exp(-x³-x). All exponential weights are integrable; the exact source cosine transform is entire with exp(C_N(1+norm z)^(3/2)) growth. Existing two-ray-decay Hadamard theorem forces infinitely many zeros. Existing exact slope asymptotic gives eventual strict negative real transform, hence finitely many real zeros by compact analytic isolation.

Whole route: every fixed shell cutoff fails as a real-zero foundation. Does not prove a concrete negative Hankel test or settle full theta sign/RH. Positive survivor already formalized in ThetaFiniteShellFourierBoundary: complete omitted tail exactly cancels the finite-prefix boundary slope term at every cutoff. Generic evenness/seam cancellation still cannot provide the source sign (prior compact-tail source-class countermodels remain paper-only).

Own card: docs/drafts/pipeline/5-failed/theta-fixed-prefix-nonreal-zeros.md. Own fact log: docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26-facts.md, F11–F13.

Verification: scratch proof clean; named leaf build succeeded; all ten public #print axioms reports only propext, Classical.choice, Quot.sound. Wired into RHTower.lean, index refreshed, lint --check-generated passed with existing large-file warnings, git diff --check clean. No numerical experiment. Owned search/Lean processes exited. No commit command by root. Other workers may commit the shared tree concurrently; preserve their changes.

Research frontier remains full arithmetic source all-polynomial logarithmic Hankel sign. No RH proof/falsification and no new universal producer conjecture. Do not duplicate finite-prefix formal transfer or polynomial zero isolation.
