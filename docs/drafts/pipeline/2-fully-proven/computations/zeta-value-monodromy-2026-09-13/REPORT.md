# Zeros as inverse branches of zeta

**Question.** When w travels around a loop based at 0, which zero is reached by continuously solving zeta(s)=w from a chosen zero?

**Outcome.** All 128 specified 50-digit continuations completed. For w(u)=1-exp(2 pi i u), zeros 2..64 ended at the preceding positive zero; zero 1 ended at the trivial zero-4. Reversing the circle sent each tested zero 1..16 to its successor. Flattening or stretching the circle vertically by.5 or 1.5 preserved the tested first 16 endpoint map. The smaller circle .35(1-exp(2 pi i u)) instead exchanged 9/10 and 13/14 and fixed the other tested first 16 zero labels.

**Validation.** Seven selected paths repeated at 100/160 digits with parameterstep.012 rather than.035. An independently implemented Euler--Maclaurin formula, using two truncations, checked 9 spread path locations. The first-zero-to-4 connection, both small-loop selected swaps, and 60-to 59 connection survived. At 160 digits the worst selected independent target residual was below 8.2 e-148. Validation is selective; it is not a certificate for all 128 paths.

**Interpretation for the landscape and RH.** Actual zeros participate in a value-plane transport structure; trivial/nontrivial labels do not define separated components of that structure. Loop choice matters. Neither transport away fromRe=.5 while w!=0 nor a link to a trivial zero violatesRH, which constrains nontrivial solutions at w=0. A proof based on this viewpoint would need a source-derived rigidity law for that distinguished fibre. The finite connection graph alone does not provide it.

**Positive salvage and next test.** The attempted neighboring-only picture survives the large-circle first 64 sample but does not describe every critical-value connection. Test reserved heights and trivial components, then determine which critical values cause each exchange. Same winding around 1 is insufficient to claim equal monodromy without accounting for all relevant singular values.

**Reproduction.** Run `python guard.py experiment.py` in this folder using the package versions in environment.json. Full paths, failures, pilots and checksums retained. Companion independent challenge contains 14 repeats and explicit Euler--Maclaurin implementation. Prior definitions and mechanical 24-operation worksheet are included.

Evidence: finite numerical observation, no Lean builds or interval certificate. Original zeta evaluated; no physical HB action, corrections or boundary terms have been identified. Numerical continuation can miss sheet switching between nodes, despite refinement and independent function checks. Searches have partial/source-only coverage; this report makes no priority or new-theorem claim.
