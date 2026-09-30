# Joint finite-source arithmetic cancellation on moving clock windows

- **ID:** LI-CLOCK-JOINT-ARITHMETIC-CANCELLATION-WINDOW
- **Stage:** 3-formalized
- **Type:** THEOREM (two new leaves/two public declarations; full paper, proof and exact formal certificates PASS)
- **Source:** [literal cancellation boundary](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md)
- **Statement:** For one common actual radius family0<r<r0<=1/128, fix0<c<r/4. Every sequenceN_l→infinity,t_l→infinity with eventual0<=t_l<=c log(2N_l+1) satisfies complexexp(-2t_l/5)H_{N_l}(r,t_l)→-1/5 and H_{N_l}(r,t_l)/C(r,t_l)→-1. Consequently realH_{N_l}(r,t_l)→minus infinity.

## Goal

Formalize the moving finite-source cancellation exposed by the fixed-clock obstruction. Keep the stricterc<r/4 approximation condition explicit. This gives no actual growing-window sign estimate and does not retire the orientation route.

## Gates

- [x] Complete literal finite-source, model and completion normalization identified.
- [x] Dependency-closed paper and primary/independent source audits; overlap recorded.
- [x] Exact model moving-clock decay and actual finite joint cancellation formalized.
- [x] Named/final-direct/all-public foundational axiom checks and full independent proof audit.
- [ ] Publication/novelty audit.

## Paper certificate

Independently derived `/tmp/hgt-li-actual-partition-compensation-paper.md`, section4 (lines128–162), proves the joint limit using the installed uniform finite-minus-actual clock approximation for0<c<r/4. Root and pole read the complete286-line note, and the399-line author note, before new Lean. The exact identity isF_N=C-K_N+H_N. Complete C has normalized complex limit1/5; actual complete F has normalized limit0. Uniform approximation gives the same normalized zero limit forF_{N_l}(t_l). Complete model K_N tends uniformly to zero on smaller positive logarithmic windows, including the chosen actual approximation window. Subtraction gives the normalized gap limit-1/5; dividing by normalized completion gives-1. Real negative escape follows multiplication byexp(2t_l/5). All contour/source identities hold eventually byN_l→infinity and the actual finite eta denominator floor.

Prior-source coverage and limitations are inherited from the primary cancellation card: documented research completed with full63196 inventory, all20 candidate/source arguments inspected, older coverage/background refresh reported, no worldwide novelty claim. Existing finite uniform approximation and complete-source asymptotic APIs are reused. The model and actual interval-union partitions remain distinct.

## Direct model-decay helper

FINAL `LiClockPairedEtaContiguousSource.lean` gives the full quarter-circle envelopeB_L=L exp(-L/4)/(1-exp(-L/4)), normK_L(t)<=B_L sinh(4 normt). ForN>=1,log(2N+1)<=log(2N)+log(3/2). Therefore, onnormt<=c log(2N+1),
`normK_log(2N)(t) <= exp(4c log(3/2))*L*exp(-(1/4-4c)L)/(1-exp(-L/4))`.
For0<c<1/16 the right side tends zero asN→infinity, retaining the complete clock and requiring no lattice truncation. The quarter-envelope relative-window argument already passed current/root independent paper audit; the odd-endpoint constant conversion receives an additional independent audit before its Lean helper. The sharper O/lattice estimates remain separately required by the comparison card.

## Formal scope

Pole: new `LiClockPairedEtaArithmeticJointCancellation.lean`, actual finite eta/gap joint consumer only. Root: independent proof audit, cards and umbrella wiring. Producer: completed model moving-clock helper; now read-only full comparison audit. Current: reserved contiguous comparison O/lattice/window targets. Frozen literal source and completed cancellation leaves remain unchanged.

## Final model helper certificate

`LiClockPairedEtaContiguousMovingClock.lean`: 108 lines, one public theorem; SHA256 `608107095eb3c1200232168ab1f6f63f39d1c6050098b3532c20153d661ed52e`. Exact named build, final direct Lean (empty output), and every public axiom check PASS; only `propext`, `Classical.choice`, `Quot.sound`. Logs `/tmp/hgt-li-contiguous-moving-clock-build.log`, `/tmp/hgt-li-contiguous-moving-clock-direct.log`, `/tmp/hgt-li-contiguous-moving-clock-public-axioms.log`. Root and independent pole read every helper proof before promotion.

The full model tends zero for any complex clock sequence with eventual norm bound `c*log(2*ν+1)`, whenever `ν→atTop` and `0<c<1/16`. No clock escape, reality or index monotonicity premise. The odd endpoint is retained via the exact `log(3/2)` constant. Research returned all 20 candidates and source arguments, plus the sole two-step ingredient set; each inspected. Coverage reported full63215 with older generation1150362 and incomplete background freshness relative to generation1150366; no absence or novelty claim.

## Log

- 2026-09-30 06:03 UTC — Created before joint Lean work. Primary joint paper already passed complete root/pole and author/producer audits; separate card preserves stronger window premise while fixed-clock cancellation leaf undergoes final checks. No route retirement or RH proof claim.
- 2026-09-30 06:32 UTC — Full model moving helper FINAL and wired. Actual joint consumer delegated exclusively to pole; common radius precedes window and sequence choices. Actual joint formal gate remains pending.
- 2026-09-30 06:40 UTC — Actual joint consumer FINAL: 181 lines, one public eight-conclusion capstone `exists_liClockPairedEtaFiniteArithmeticJointCancellation_radius`; SHA256 `e5ac0123511bc3babcbc9d5d116d5139cc09314b09e4f9867f8f36ba174f80a3`. Root read all168 frozen proof lines and final header-only delta. Exact named build, final direct Lean (empty output) and all-public foundational axioms PASS. Logs `/tmp/li_pole_joint_named_build.log`, `/tmp/li_pole_joint_final_direct.log`, `/tmp/li_pole_joint_axioms.log`; full ledger `/tmp/li_pole_joint_public.tsv`. Wired; closure index/lint pending before Stage3 move.
- 2026-09-30 06:44 UTC — Wired closure index PASS (0 changed, 0 removed after managed research refresh); actual capstone and comparison declaration entries verified in generated API. Authoritative global lint FAILED on13 unrelated unreachable modules and no proof-debt errors. Logs `/tmp/hgt-li-comparison-joint-index.log`, `/tmp/hgt-li-comparison-joint-lint.log`. Scoped tracked whitespace check PASS; joint new-leaf check empty. MovedStage3; RH and the actual residual pointwise sign remain OPEN.

## Exact joint formal conclusions

One radius `r0>0`, `r0<=1/128`, precedes all choices `0<r<r0`, `0<c<r/4` and arbitrary sequences `ν:ℕ→ℕ`, `τ:ℕ→ℝ`. Assuming both sequences tend infinity and eventual `0<=τ<=c*log(2ν+1)`, the capstone proves unscaled finite-minus-actual clock error tends zero; completion-scaled finite completed clock tends zero; both literal finite eta and actual-to-contiguous gap clocks have scaled limit `-1/5`, completion ratio `-1`, and real part tending minus infinity. These are eight conclusions. Source regularity and `ν>0` are derived eventually from the actual finite eta floor. No monotonicity, globally nonzero eta, clock-sign or zero-location premise.
