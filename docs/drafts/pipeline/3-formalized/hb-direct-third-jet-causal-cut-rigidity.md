# HB direct-third-jet causal-cut rigidity

- **ID:** HB-DTJ-CUT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · HB full `++-` Einstein--Teukolsky source burden
- **Statement:** With Einstein Hessian and retarded/advanced quadratic response maps fixed, the zero set of the complete `++-` cokernel causal cut is independent of every common local direct third jet; the cut vanishes exactly when the projected `+-` and `++` response jumps anti-align.

## Goal

Kill the direct-local-cubic-counterterm branch of HB before computing the full third-order Einstein vertex.  In the RH chain

`Xi divisor -> AIME simple pole -> full ++- cokernel source -> retarded/advanced causal cut -> BM optical/clock defect -> RH`,

the theorem removes the direct third variation from the causal-cut proof burden.  Only the stationary `+-` and radiative `++` quadratic response discontinuities can cancel the cut.

## Gates

- [x] 0 → 1  in-progress: exact corpus-derived statement, route scope, hostile boundary, proof idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit

- `ThetaCuspHawkingAIMEThirdOrderSourceCohomology`: full `++-` source contains AIME, charge-orthogonal stationary cascade, second-harmonic cascade, and direct third variation.
- `ThetaCuspHawkingTotalThirdOrderCokernelSchurSection`: a one-sided total section can be shifted arbitrarily by a target-grade third jet, so lower-order data alone cannot settle that section.
- `ThetaCuspHawkingTotalThirdOrderCausalCut`: retarded minus advanced subtraction cancels the common direct third jet and leaves exactly two bilinear response-jump terms.
- No corpus theorem classifies the exact zero set of that sum or packages direct-third-jet causal cancellation as a killed HB route.

## Literature audit (through 2026-08-31)

- Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168: AIME is a third-order secular mass-backreaction effect; no retarded/advanced full-cokernel zero-set theorem.
- Spiers--Pound--Moxon, arXiv:2305.19332: formulates second-order Kerr Teukolsky source and gauge control; no cubic Schur causal-cut classification.
- Ben Achour--Roussille, arXiv:2406.08159: quadratic Schwarzschild zero modes encode mass/spin corrections; does not identify them with a one-Green cubic cut counterterm.
- Lestingi--Sberna--Green, arXiv:2607.19492: all-order QNM perturbation theory includes continuous spectrum; no direct-third-jet independence or HB consequence.
- Aruquipa--Casals--Nolan, arXiv:2604.21219: regularized retarded Teukolsky Green function/direct Hadamard part; no nonlinear retarded-minus-advanced third-order source theorem.

## Conjecture and hostile audit

Let

`K_C = ell(B(p, (R_+-^ret-R_+-^adv) q_+-)) + ell(B(m, (R_++^ret-R_++^adv) q_++))`.

The corpus Schur expansion implies the displayed expression contains no `C`.  Conjecture:

1. `K_C = 0` iff the first projected jump is the negative of the second.
2. For any common local third jets `C1,C2`, `K_C1 = 0` iff `K_C2 = 0`.
3. Hence changing only the direct local cubic vertex cannot kill a nonzero HB causal cut.

Hostile boundaries:

- False for a one-sided retarded section: corpus proves an arbitrary third-jet correction can prescribe its scalar cokernel value.
- Requires the same local Einstein action in retarded and advanced problems.  Orientation-dependent `C_ret != C_adv` is a nonlocal/causal-action modification, outside this route.
- Does not freeze changes to `B` or to response maps.  Such changes belong to the two surviving quadratic-response channels.

## Paper proof `[PROVED HERE]`

Write `q_+- = (1/2)(B(p,m)+B(m,p))` and `q_++=(1/2)B(p,p)`.  The retarded total Schur source is

`B(p,R_+-^ret q_+-) + B(m,R_++^ret q_++) + C_++-`,

and the advanced source is the identical expression with `R^adv` in both response terms and the same local `C_++-`.  Subtraction and linearity of `B` give

`B(p,(R_+-^ret-R_+-^adv)q_+-) + B(m,(R_++^ret-R_++^adv)q_++)`.

Thus the common direct third jet is absent before applying the left resonant state `ell`.  Set the two projected terms to `a,b : C`.  The cokernel cut is `a+b`, hence it vanishes iff `a=-b`.  This formula is identical for every pair of common local third jets `C1,C2`, proving equality of their cuts, equality of their zero sets, and preservation of nonvanishing.  No analytic, spectral, or positivity premise is used.

## No-go closure

- **Exact killing theorem/mechanism:** common direct third jets cancel identically under retarded-minus-advanced subtraction; Lean theorem `d4HBDirectThirdJetCausalCutCancellationRouteKilled`.
- **Strongest positive survivor:** exact anti-alignment law for the two projected quadratic response jumps.
- **New insight:** full Einstein cubic vertex is necessary for a one-sided QNM residue but irrelevant to the HB retarded/advanced causal cut.  HB computation should target stationary and second-harmonic resolvent discontinuities instead.
- **Status:** paper and Lean proved in `ThetaCuspHawkingHBDirectThirdJetCausalCutRigidity`; targeted build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Formal lint reaches the module and reports only unrelated unreachable `ConstitutiveEvenPositiveWeightedReflection`.

## Log

- 2026-08-31 — created in 1-in-progress after blanket zero-frequency exclusion was falsified by corpus moving-horizon mass memory.
- 2026-08-31 — paper proof closed; exact survivor is response-jump anti-alignment.
- 2026-08-31 — formalized existential tuning no-go and exact anti-alignment survivor; targeted build and axiom audit passed.
