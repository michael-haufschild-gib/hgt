# Classical baseline theorems in CTF, BAG, TH, and RB

- **ID:** classical-baselines-ctf-bag-th-rb-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (formalization of classical theorems)
- **Source:** user attachment `94c10467-3b24-4880-934a-2f85291fdcbe/pasted-text-1.txt`, items 9–11.
- **Statement:** Unconditional classical approximation, recurrence, mean-square, Jensen–Hermite, and extremal divisor-sum theorems, with their exact RH gaps preserved.

## Scope and acceptance obligations

1. CTF: formalize Burnol's lower bound, raw Möbius nonconvergence in the actual Báez–Duarte carrier, and the supported Selberg row `μ(k) log(N/k)/log N`; connect the row to existing CTF/PM carriers.
2. Resolve the attachment's stronger raw-error `liminf ≥ Σρ 1/|ρ|² > 0` statement. Do not silently identify it with the optimized-distance logarithmic bound or with a positive limsup.
3. BAG: finite Dirichlet polynomial self-return with positive lower density; Carlson's L² mean-value theorem in the domain needed by Bagchi; state the exact tail conditioning still required.
4. TH: fixed degree, increasing shift Hermite asymptotics for the actual Xi Taylor coefficients, including all analytic coefficient estimates. A theorem with those estimates assumed is insufficient.
5. RB: define actual colossally abundant integers and prove the classical reduction, with quantifiers and any threshold made explicit.
6. Verify each delivered leaf with `lake --old env lean <module>`, audit axioms in `/tmp`, wire leaves into their area umbrellas, regenerate indexes and run `scripts/formal_tools.py lint`. No full/umbrella builds, numerical experiments, added axioms, proof holes, heartbeat increases, commits, or unrelated edits.

## Plan

- [x] Read task, project instructions, relevant route evidence and memories.
- [ ] Audit exact classical statements and current dependency coverage.
- [ ] Complete CTF/PM statements and Selberg row.
- [ ] Complete BAG finite recurrence and mean-square baseline.
- [ ] Complete TH Xi-specific Hermite asymptotics.
- [ ] Complete RB colossally abundant reduction.
- [ ] Kernel, axiom, wiring, lint, and cleanup audit against every obligation above.

## Evidence and statement audit

- Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Theorem 1.3, https://arxiv.org/pdf/math/0103058: `liminf D(λ) sqrt(log(1/λ)) ≥ sqrt(Σ mρ²/|ρ|²)`. The logarithmic factor and multiplicities cannot be discarded. This alone does not establish a constant raw-error liminf.
- Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable Reformulation*, Proposition 4.4, https://arxiv.org/pdf/math/0011254: natural raw sums do not converge in L². This does not by itself state the stronger raw liminf claimed in the attachment.
- Griffin–Ono–Rolen–Zagier, https://arxiv.org/pdf/1902.07321: actual Xi coefficient asymptotics and the general finite-difference Hermite limit must both be covered. Fixed degree and sufficiently large shift do not establish all-degree hyperbolicity at every shift.
- `RHTower/BaezDuarteBurnolMultiplicityAllZeros.lean`: multiplicity-weighted logarithmic lower bound over all critical zeros already present, using eventual lower bounds below an extended sum.
- `RHTower/BaezDuarteMobiusCriticalTailObstruction.lean`: raw full-error nonconvergence and a positive cofinal floor already present; a cofinal floor is not a liminf floor.
- `RHTower/Sieve/LinearMollifierGcdForms.lean`: exact unsupport-truncated coefficient formula, `S₀(N) log N → 1`, and `S₁(N) → 1` already present.
- `RHTower/SimultaneousPhaseRecurrence.lean`: arbitrarily late simultaneous returns; density is a separate obligation.
- `RHTower/RobinExtremalNumbers.lean` and `RobinCriterionRiemann.lean`: global penalized extremal comparison and eventual Robin criterion already present. Existing source does not use the name colossally abundant.

## Session state

Serena symbol lookup rejects the Lean tree as ignored; use exact source text and compiler checks for Lean operations. No callable `update_plan` tool is exposed; this card is the persistent plan. Independent reads use concurrent tool calls. Preserve existing unrelated dirty files, including frontier-map changes.

Research search `Jensen Hermite asymptotics fixed degree xi coefficients --mode deep --no-refresh --budget-seconds 40` completed (exit 0), partial after 40.03 seconds, coverage generation 1451831 pending. No directly applicable Xi/Hermite limit was returned; hits were source-only. Broad initial search completed without its output being retained after tool-output truncation; do not count it as coverage evidence.

## Verification

`RobinColossallyAbundantReduction.lean` compiled with `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.olean GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean`, exit 0, no warnings. It defines actual global penalized maximizers, proves `robinExtremalAt x` belongs to this class, and proves the unconditional eventual reduction and corresponding RH equivalence. It does not assert a checked numerical cutoff of 5040. Axiom/wiring/final audits remain.

`SelbergMobiusApproximation.lean` compiled: supported row, unit coefficient bound, first/last coefficients, fixed-index convergence, actual CTF/Nyman/Fermi errors and dyadic transfer. Final direct leaf and axiom audits remain.

User replied “do all. decide yourself”. Use the documented classical normalization. The stronger raw constant-liminf assertion is not supplied by either classical source and must not be reported as proved.

`BaezDuarteClassicalBaseline.lean` compiled, exit 0: strict positivity of the multiplicity-weighted critical mass using Hardy, the extended-real logarithmic liminf lower bound, and raw full-energy nonconvergence in one unconditional theorem. Wired into `RHTower.lean`.

`HTGeometry/AlmostPeriodicReturnDensity.lean` compiled, exit 0: every continuous Bohr almost-periodic function has return sets with positive lower Lebesgue density. Application to actual finite Dirichlet polynomials is in progress.

BAG tail audit: for `1/2 < Re(s) < 1`, the unsmoothed finite head need not approximate the fixed starting value. The required conditioned error is the centered tail increment `(ζ(s+iτ)-D_N(s+iτ))-(ζ(s)-D_N(s))`; unconditioned Carlson mean square alone does not supply this on finite-head return sets.
