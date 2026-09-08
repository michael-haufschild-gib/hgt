# Actual Maass pair and phase currents, modular transport, and retained nodal curvature

- **ID:** SELBERG-PAIR-PHASE-CURRENT-CURVATURE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Original-source current candidate](../1-in-progress/selberg-original-source-conserved-currents.md), [Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 40.
- **Statement:** The actual congruence Maass source has conserved pair and phase currents; their full squared energy and the explicit regulator-gradient term exactly reconstruct its regularized curvature, with actual modular transport and source zeros included.

## Scope and gates

- [x] Source-pure statement and corpus-derived mechanism.
- [x] Dependency-closed paper proof below.
- [x] Complete Lean scratch and needed-source checks; all three final single-module builds passed.
- [x] All 29 public declarations have only standard Lean axiom dependencies.
- [x] Final index, source/umbrella wiring, and documentation checks.
- [ ] Repository lint: four unrelated concurrently introduced modules are unwired (details below).
- [ ] Publication and external novelty audit.

This proves source identities, not Selberg's quarter inequality. Parameters are an arbitrary natural N, real eigenvalue lambda, and an original `MaassCuspEigenform` for Gamma(N+1). No extra lift, gap, entropy bound, nonvanishing assumption, or endpoint comparison is supplied as a premise. The source objects themselves carry the original eigen-equation and C² regularity. At-node statements specify that the actual source density vanishes; they do not construct a node or an exceptional eigenform.

## Dependency-closed proof [PROVED HERE]

Let F_q be the literal complex planar chart of `quotientForm N f q`, indexed by the finite actual deck group. Write d_v for its real Fréchet derivative evaluated on v. For each direction define

- D = sum_q |F_q|²;
- E_v = sum_q |d_v F_q|²;
- B_v = sum_q (d_v F_q)*conjugate(F_q), with phase current j_v=Im(B_v);
- J_qr,v = F_q*d_v F_r-F_r*d_v F_q;
- P_v = (1/2)*sum_q,r |J_qr,v|².

All values and derivatives here are evaluated at the same original source point. These quantities involve no division by the amplitude.

### Finite complex identity and actual source energy

For finite complex families a_i,b_i, put p_i=b_i*conjugate(a_i). Direct real/imaginary polynomial expansion gives

`|a_i*b_j-a_j*b_i|² = |a_i|²|b_j|²+|a_j|²|b_i|²-2*Re(p_i)*Re(p_j)-2*Im(p_i)*Im(p_j)`.

Sum over both indices. Each product sum factors exactly, so

`(sum |a_i|²)*(sum |b_i|²)-(sum Re(p_i))² = (1/2)*sum_i,j |a_i*b_j-a_j*b_i|²+(sum Im(p_i))²`.

Apply this to the literal source values and derivatives. The existing actual derivative identity identifies the scalar density current I_v=d_v D with 2*Re(B_v). Hence

`D*E_v-I_v²/4 = P_v+j_v²`.

The original multiplied radial decomposition gives `D*radialResidual=P_v+j_v²` at every point, including D=0. Summing the two coordinate directions resolves the complete original angular energy. Substitution into the actual trace Laplacian gives the exact source Fisher identity with both current contributions and its original spectral term `-2*lambda*D²/y²` retained. The imaginary square is necessary: the pair sum alone has no term for phase variation in a single complex component.

### Actual phase conservation

Real differentiation and complex conjugation commute by the actual real continuous-linear conjugation map. Differentiating `(d_v F)*conjugate(F)` and taking the imaginary part removes the real term `|d_v F|²`. Thus

`d_v Im((d_v F)*conjugate(F)) = Im((d_v d_v F)*conjugate(F))`.

Each literal quotient component has the original planar equation `Delta F=-(lambda/y²)*F`. The factor is real, so the sum of the horizontal and vertical phase-current derivatives is the imaginary part of `-(lambda/y²)|F|²`, which is zero. Finite summation proves total phase-current conservation. No local phase, logarithm, or division is chosen. The predecessor module already proves full pair-current conservation by the same actual source equation and antisymmetric cancellation.

### Exact modular transport

The original quotient-form pullback identifies `F_q(A*z)=F_(q*[A])(z)`. The actual Möbius chart is differentiable at every upper-half-plane point, with real derivative applied to v equal to `(1/denom(A,z)²)*v`. The chain rule therefore gives the corresponding derivative identity. Substitute these two actual identities into the bracket: both pair indices are permuted and the tangent vector is transformed by the full reciprocal-square Jacobian.

Right multiplication by [A] is an actual equivalence of the finite deck group. Reindexing the finite phase sum and both indices of the pair-energy sum proves total phase-current covariance and pair-energy covariance under simultaneous point/tangent transport. This supplies no assertion about quotient periods or exactness of a closed form.

### Retained regulator energy and curvature at source zeros

Let e>0 and R_e²=D+e², the original positive regularized radius. Existing exact regularized square completion and the proved finite identity give

`R_e²*directionalRemainder_v = P_v+j_v²+e²*E_v`.

Put `C=P_x+P_y+j_x²+j_y²` and `G=E_x+E_y`, the actual planar source gradient density. Sum the directional identities and use the original definition `curvatureWeight=remainder/R_e`. Positivity of R_e permits exact cancellation, yielding

`R_e³*curvatureWeight = C+e²*G`.

Consequently the original curvature splits into the two nonnegative terms `C/R_e³` and `e²*G/R_e³`. Both numerators and denominator have their signs proved directly from the actual source and positive regulator.

At an original common source zero, D=0. The all-point multiplied angular identity gives C=0. Positive R_e and e with equal squares give R_e=e. The exact cubic identity then yields

`curvatureWeight = G/e`.

The source gradient need not be inferred to vanish from vanishing D or C. This formula retains precisely the contribution that a pointwise current-only limit would discard. No limit of integrals, support theorem for the limiting measure, or nodal mass estimate has been inferred from it.

## Lean certificate

All modules are under `formal/GaloisForLFunctions/RHTower/` and wired exactly once into its umbrella.

| Module | Public declarations | Main results |
|---|---:|---|
| `SelbergMaassPairPhaseEnergy` | 12 | `finite_pair_phase_identity`, `source_pair_phase_identity`, `density_mul_angularEnergy`, `trace_fisher_pair_phase_identity`, `regularized_pair_phase_identity`, `phase_current_conservation` |
| `SelbergMaassCurrentTransport` | 5 | `field_dir_modular`, `bracket_modular`, `phase_current_modular`, `pair_energy_modular` |
| `SelbergMaassCurrentCurvature` | 12 | `radius_cube_mul_curvatureWeight`, `curvatureWeight_split`, `curvatureWeight_at_node` |

The energy module also has two private helpers. Scratch files `/tmp/selberg_pairphase40.lean`, `/tmp/selberg_transport40.lean`, and `/tmp/selberg_currentcurvature40.lean` passed in full, followed by needed source olean checks using `lake env lean`. Name checks passed in `/tmp/selberg_pairphase40_names.lean` and `/tmp/selberg_transport40_names.lean`.

Final serialized `lake build` audits rebuilt only their named targets: PairPhaseEnergy 4.6 seconds, CurrentTransport 3.5 seconds, CurrentCurvature 3.2 seconds. No full or umbrella build ran. Logs are `/tmp/selberg_pairphase40_build.log`, `/tmp/selberg_transport40_build.log`, and `/tmp/selberg_currentcurvature40_build.log`. Existing EvenL2 informational output was replayed; the new modules produced no warnings.

The post-build `/tmp/selberg_pairphase40_axioms.lean` scratch audit printed every public declaration's dependencies. All 29 use only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms or admissions. The log was parsed against the complete source declaration list, and all three source hashes remained unchanged. Audit artifacts: `/tmp/selberg_pairphase40_axioms.log`, `/tmp/selberg_pairphase40_counts.json`, `/tmp/selberg_pairphase40_hashes.json`.

The final index refresh passed (`/tmp/selberg_pairphase40_index.log`). Every public declaration is present in `formal/LEAN_API.md`; each new module is imported exactly once, and source/card whitespace and links passed. Repository lint (`/tmp/selberg_pairphase40_lint.log`) failed on four unrelated concurrent additions: `RHTower.SelbergScatteringNativeResidual` and `HTGeometry.FokasLenellsRawBounds`, `FokasLenellsRawEvolution`, `FokasLenellsRawInteraction`. All four errors are umbrella reachability; none concerns these three source-current modules. Existing large-file warnings also remain. This task did not modify those other modules or their wiring. All task-owned Lean/build handles are terminal; another agent's Hawking mixed-source build was observed and left untouched.

## What changes in the open route

The retained scalar curvature now has an exact original-source representation in conserved pair and phase currents plus the regulator-gradient term. This uses component information absent from the cycle-39 scalar family. The new identity does not imply a positive uniform comparison with amplitude mass.

Next test: construct the corresponding limit-measure decomposition using source-derived domination or monotone convergence for the current term, while retaining any nodal remainder. The original scalar toy `SelbergNodalCurvature.nodal_curvature_survives_integration` proves that a term tending to zero almost everywhere can retain positive integral, so pointwise disappearance is insufficient. Then seek a genuinely quantitative constraint from the original equation, congruence transport, zero means, and nodal geometry. Selberg and cycle 40 remain open.

## Log

- 2026-09-08 — Finite pair/phase identity, actual source conservation and energy, modular transport, and exact curvature/node formulas proved and formally audited. No task commit or push.
