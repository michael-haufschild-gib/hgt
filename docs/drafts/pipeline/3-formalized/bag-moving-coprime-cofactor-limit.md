# BAG growing coprime cofactor limit — Lean audited

Paper: [growing cofactor law](../2-fully-proven/bag-moving-coprime-cofactor-limit.md).
Source: ChiRamanujanMovingCofactorLimit.lean, 454 lines, eight public theorems,
two definitions. The complete complex Euler ratio and original coprime
cofactor retain the growing cutoff and logarithmic Mellin displacement.

Production46118: lake --old env lean on the leaf with its own -o target,
exit0, empty output. Axiom53987: all eight public declarations use only
propext, Classical.choice, Quot.sound. Umbrella import occurs once.
Index18802 passed; all eight public API entries verified. Lint50302 reports
38 unrelated unreachable modules and 174 existing warnings; no finding
in this leaf. Global lint is NOT clean.
No numerical experiment, subagent, full build, or proof-budget override.

This closes a growing cofactor asymptotic, not the whole labelled source
or the physical axes saving. Those remain the active BAG obligations.

Current01ap source exports its proved complex prime-window and Mertens
normalization limits for the actual labelled source. Production95159 empty
PASS; combined axiom71945 checks all10 current API entries, standard3 only.
Index69878/API10/10/import once. Lint66470:23 unrelated unreachable modules,
174 warnings; no finding in this leaf, global NOT clean. The labelled source
limit is now proved in P3 bag-growing-labelled-near-pole-source; physical saving
remains open.
