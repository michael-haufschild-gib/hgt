# Actual Maass strip energy and modular cap comparison

- **ID:** selberg-maass-strip-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SelbergMaassFlux.gradientEnergy_ge_first_frequency`, actual trace Stokes and cusp decay, Mathlib's literal modular cell.
- **Statement:** Every original exceptional principal-congruence Maass source obeys lambda >= 3 pi^2 / (2 L^2), L = N + 1. Principal levels one through seven have no exceptional sources. At every level the original scalar deck trace and finite regular average vanish, and full deck displacement energy equals the source density.

## Goal

Produce an actual quantitative source theorem, then attack the level dependence toward the uniform quarter bound. No lift, endpoint positivity, spectral gap, or terminal boundary value is supplied as an extra assumption. The uniform Selberg goal remains open until the level dependence is removed by a proved source argument.

## Conjecture and paper proof

Let D be the existing full congruence trace density and G its actual planar gradient density. Let F be the standard closed modular cell and S the strip |x| <= 1/2, y^2 >= 3/4 in the upper half-plane.

1. Existing literal Parseval and the proved zero constant term give k^2 M_q(y) <= E_q(y), k = 2 pi / L. Summing over the actual quotient and using translation invariance identifies these normalized sums with unit-period trace integrals.
2. The original trace PDE and the actual Mobius Laplacian pullback imply invariance of y^2 G under the full modular group.
3. F is contained in S. The part of S inside the unit circle maps directly into F under z -> -1/z: its squared modulus becomes the reciprocal, and 2 |x| <= x^2 + y^2 follows from (|x|-1/2)(|x|-3/2) >= 0. Consequently every nonnegative invariant integrable source has strip integral at most twice its cell integral, with actual hyperbolic volume.
4. Original truncated Stokes gives integral_F(Y) G = sum_q J_q(Y) + lambda M_F(Y). Proved cusp flux decay and monotone exhaustion give full integrability and integral_F G = lambda M_F. Original nonvanishing gives M_F > 0.
5. Integrating step 1 on S and using y^2 >= 3/4 gives integral_S y^2 G >= (3/4) k^2 integral_S D >= (3/4) k^2 M_F. Step 3 gives the upper bound 2 lambda M_F. Cancel the actual positive mass.

All five complete scratch modules and needed-source checks pass. The full original-source bound, the empty exceptional-source types at principal levels one through seven, and exact all-level deck cancellation passed their final builds and axiom audits.

## Second conjecture: exact all-level deck cancellation — proved

The bound excludes principal levels one through seven. The second positive conjecture, now proved, is exact cancellation of the scalar full-deck trace at every original congruence level. The actual finite sum is C2, has the original eigenvalue, decays at every cusp, and is invariant under the full modular group by quotient permutation. If it were nonzero, it would construct a literal level-one exceptional Maass form, contradicting the new exclusion theorem. Thus its sum is zero at every point.

The corpus OR search for deck averages, Reynolds operators, averaging projections, and invariant projections returned 44 declarations in 18 modules. Inspected `HTGeometry/FiniteRegularReynolds.lean` identifies the actual finite regular average with the constant-coordinate mean and proves its exact displacement-energy identity. The completed instantiation uses the original deck-value vector V(z), proves its squared norm is D(z), identifies modular transport with the actual right regular action, and proves its finite regular average is zero. The corpus displacement identity then gives (1 / (2 |Deck|)) sum_g ||U_g V(z) - V(z)||^2 = D(z) at every point. The subsequent comparison with local physical energy must still be proved; no uniform operator comparison is supplied as a premise.

## Gates

- [x] Corpus discovery and prior-work check: reuse the existing first-frequency theorem rather than proving it again.
- [x] Dependency-closed paper argument with explicit period, covering factor, positive mass, and cusp boundary limit.
- [x] Original-source Lean theorems and serialized single-module final audits.
- [x] Axiom audit, umbrella wiring, corpus index, formal lint.

The congruence-uniform quarter bound remains a separate open goal.

## Log

- 2026-09-09: Positive quantitative candidate selected following the user's request for a conjecture/proof/pivot loop. The evaporation and entropy searches retrieved all 78 and 1076 matching declarations, respectively. The exact bistochastic variance identity remains a candidate mechanism for the subsequent arithmetic strengthening.

## Lean certificate

All modules live in `formal/GaloisForLFunctions/RHTower/` and are imported exactly once in its umbrella.

| Module | Public declarations | Result |
|---|---:|---|
| `SelbergMaassFullGradient` | 16 | Actual modular gradient covariance; full energy identity and positive mass |
| `SelbergModularStripComparison` | 7 | Literal inversion cap and factor-two integral comparison |
| `SelbergMaassStripSlice` | 4 | Exact unit-period energy normalization and original-source Fourier lower bound |
| `SelbergMaassStripGap` | 18 | Full strip integration, explicit eigenvalue bound, principal levels 1–7 exclusion |
| `SelbergMaassDeckAverage` | 13 | Original scalar trace cancellation, zero finite average, exact source displacement energy |

The main declarations are `SelbergMaassStripGap.eigenvalue_lower_bound`, `SelbergMaassStripGap.small_level_no_exceptional`, `SelbergMaassDeckAverage.scalarTrace_eq_zero`, and `SelbergMaassDeckAverage.deck_displacement_energy`. The small-level result quantifies only over `Fin 7` and the exceptional eigenvalue interval; it takes no purported gap, lift, boundary-limit, or averaging-cancellation premise. The all-level results take the original `MaassCuspEigenform`, with its original smoothness, eigen-equation, nonvanishing, invariance, and cusp conditions retained.

All 58 public declarations passed the post-build `lake env lean /tmp/selberg_strip44_axioms.lean` check. Dependencies are only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. All five source hashes remained unchanged. Audits: `/tmp/selberg_strip44_axioms.log`, `_audit.json`, `_hashes.json`, `_counts.json`, and `_coverage.json`. The audit parser was corrected to strip whitespace from multiline axiom lists; this required no Lean change or repeated Lean check.

Final commands were serialized `lake build` calls naming one module each. Each rebuilt only its named target: FullGradient 13s, StripComparison 4.4s, StripSlice 25s, StripGap 9.6s, DeckAverage 24s. Logs: `/tmp/selberg_{fullgradient,stripcomparison,stripslice,stripgap,deckaverage}44_build.log`. Cached EvenL2LogUnitary informational output was replayed; none of these five modules emitted build warnings. No full or umbrella build ran.

The corpus contains all 58 public declarations and all 58 API rows; the search also returns the three private helpers. The five umbrella imports occur exactly once. Index refresh and repository formal lint passed, with pre-existing large-file warnings: `/tmp/selberg_strip44_index.log`, `/tmp/selberg_strip44_lint.log`. No added axioms, admissions, numerical experiments, commit, or push.

## Next positive target

The actual finite-group operator and its identification with source mass are now established. The next comparison to prove, directly from the original congruence source, is that integrated averaged deck displacement is at most four times the physical cell gradient energy. Its left side is exactly the original cell mass, while the right side is exactly four times lambda times that mass. A level-independent comparison would therefore close the quarter bound. It is a proof target, never an assumed endpoint. The current strip argument supplies an explicit level-dependent comparison; neither its constant nor the new finite-group identity alone is claimed to be uniform.

- 2026-09-09: Both positive conjecturing loops completed in Lean and passed all targeted final audits. The full Selberg goal remains active and unproved.
