# Route L: retained-source commutator comparison

- **ID:** RH-L-C61
- **Stage:** 1-in-progress
- **Target:** Full-source fixed physical-reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

C60 isolated the strict-tail multiplier variation in the actual tensor-source divided difference. It supplied no new Lean closure. This turn tests whether that term is the image of a physical commutator with an admitted, source-derived boundary identity. Original prime provenance, native Tate depth, all multiplicity copies, the nonzero Xi coefficient, Gamma normalization and horizontal anchor must remain present.

## Actual source identity: kernel checked

Conjecture tested: the logarithmic translation commutator of the complete arithmetic source supplies the retained variation and an independently vanishing physical pairing. The source-identity part has a direct proof below. The physical-annihilation part remains unproved; writing a commutator does not supply it.

Use the literal residual packet `f_j` from `mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m j`, with shift `t_j = m (log(p+j)-log p)`. Write `E_delta(x) = exp(-I*delta*x)` and define the local modulation before selecting a Fourier reader:

```
L_delta(x) = sum'_j E_delta(x-t_j) f_j(x)
C_delta(x) = E_delta(x) sum'_j f_j(x) - L_delta(x).
```

This is external modulation minus modulation inside every translated packet. All Möbius coefficients and all labels `p+j` remain. The first packet has shift zero and cancels between the two operations.

Put `w=v+delta`, `M=M_{p,m}` and `X_k=iteratedDeriv k XiC`. The exact identities are

```
integral exp(-I*v*x) L_delta(x) dx = M(v) X_k(w)
integral exp(-I*v*x) C_delta(x) dx = (M(w)-M(v)) X_k(w).
```

For the first identity the sufficient domain is `p>0`, `m!=0`, `|Im w|<1`, and `Re(1/2+I*v)>1/m`. The second additionally requires `Re(1/2+I*w)>1/m`. No theta-strip condition at `v` is needed: the theta packet is evaluated at `w`, while its arithmetic coefficient is evaluated at `v`.

Proof: the locally modulated integrand is exactly `c_j(v) thetaJetIntegrand_k(w,x-t_j)`. Its integral norm equals `norm(c_j(v))` times the integral norm of the unshifted theta jet. The existing coefficient-summability and theta-integrability theorems therefore admit the complete sum and permit the integral/series exchange. External modulation combines the exponential weights into `w`; both full integrals are admitted separately before subtraction. This avoids differentiation under an integral and leaves no ignored cross term.

For C60's complete Gamma-six tensor remainder, let `J_k(w,v-w)` denote this commutator integral evaluated at `w` with local modulation `v-w`. Then the retained term is exactly

`X_k(v) Delta_wv M = -J_k(w,v-w)/(w-v)`.

Consequently its complete divided difference can be written on paper as

```
Delta_wv F_m(·,z) = h_m^2 X_l(z) *
  ((M_m(w) M_m(z)-1) Delta_wv X_k
    - M_m(z) J_k(w,v-w)/(w-v)).
```

This retains both leading–tail cross terms through the existing complete tensor formula. The final tensor rewrite is a paper consequence. The new source integral identities are kernel checked in `formal/GaloisForLFunctions/RHTower/MobiusThetaFullSourceModulationCommutator.lean`:

- `mobiusThetaResidualLocalModulationSource_fourierLaplace_data` proves absolute admission and the mixed-parameter evaluation.
- `mobiusThetaFullSourceModulationCommutator_fourierLaplace_data` proves absolute admission and the complete multiplier-difference evaluation.

The definitions use the original physical arithmetic packets. No Xi zero or preselected spectral value enters source construction.

## Annihilation attempt and surviving boundary

The corpus's `positionMult_compressedShift_commutator` supplies the actual logarithmic-position mechanism at finite aperture. `commutator_finitePlaceMultiplier` differentiates a finite Euler multiplier on its differentiable core. Neither identifies the complete physical reader here. The new source construction uses finite modulation instead of importing those finite-source derivative conclusions.

The suggested trace route does not close the gap. `crossBoundary_trace_zero` uses finite matrices. `deningerGreenForm_antisymm` explicitly assumes the trace kills the derivation; `deningerGreenTransgression_cutoff_independent` explicitly assumes the cutoff-difference pairing vanishes. Its model trace is evaluation at the multiplicative unit, not the fixed Gamma reader. These are not annihilation producers for the requested comparison.

There is a concrete retained positive survivor already formalized: `trace_sourceHorizontalGammaSixSuspensionLeg_commutator` is zero for every character, while the forward and reflected corner traces are respectively minus and plus the paired curvature. `sourceHorizontalGammaSix_commutatorTraceFlat_but_curvature_pos_iff` makes that curvature strictly positive exactly off center. The actual equal-depth Gamma/co-Poisson boundary in `DeningerGammaSixActualGammaBoundaryLogTransgression.lean` also retains its nonzero oriented exterior coefficient. No new no-go theorem or duplicate algebraic wrapper is being added.

## Broad literature screen

The newest-first arXiv search for `transgression` failed to fetch; the broad single-word search `cocycle` returned current papers. Read the weight-variation mechanism in Basdouri–Ben Ammar, [Deformations of the osp(n|2)-action on the superspace of symbols](https://arxiv.org/html/2609.02426), 2 September 2026, particularly Sections 4–5 and Proposition 5.3. Their affine family of coboundaries yields cocycles by differentiating the square-zero identity; this does not make the resulting classes zero. No source action on those density modules, preservation of the physical anchor, or compatible full-source pairing has been constructed here. No theorem from the paper is used in Lean, and its partly computer-assisted nontriviality argument is not used.

## Corpus audit

Three direct deep searches used 120-second budgets and cached indices. Every set of 20 candidate lemmas and 20 source-method entries, including their assumptions, was inspected. Definitions were not treated as proved analytic statements.

- `route-l-source-commutator-search.json` and `route-l-source-boundary-transgression-search.json`: index generation `880260`; coverage snapshot `880274`, current generation `880275`. The snapshot reports 57,080 files, 47,455 Lean files, and 735,598 declarations. Both partial, with interrupted text/source retrieval and unfinished expansions. The first has one generated logarithm transfer proposal and one ingredient group; the second has one trace-cancellation ingredient group. The groups' actual assumptions were inspected above.
- `route-l-full-source-moment-search.json`: index generation `880318`; snapshot `880334`, current generation `880337`, enrichment counts pending. It reports 57,084 files, 47,458 Lean files and 735,656 declarations. Partial; interrupted text/source retrieval and unfinished expansions/filtering. No proof ideas or ingredient groups. Its useful hits include the complete internal-jet and strict-tail admission theorems; none identifies the fixed physical pairing.
- All three search processes terminated with exit code zero. Cached/source-only retrieval is not new kernel verification and does not establish exhaustive absence.

## Remaining target

Identify and evaluate the retained modulation commutator in the original fixed Gamma/BV pairing, with the native nonzero Xi coefficient and horizontal anchor retained. Ordinary evaluation of an unpromoted Xi-zero source is insufficient: the theorem retains `X_k`, and the selected leading jet is nonzero. Full-source reader agreement and RH remain unproved.

## Verification

- `lake env lean /tmp/RouteLModulationCheck.lean`: passed; verified the exact imported summation/integration helpers against this toolchain.
- `lake env lean /tmp/MobiusThetaFullSourceModulationCommutator.lean`: passed after resolving a pointwise-function rewrite and an explicit measure annotation. No heartbeat or recursion limit was raised.
- `lake build GaloisForLFunctions.RHTower.MobiusThetaFullSourceModulationCommutator`: passed; the new leaf took 4.7 seconds. Dependency messages were replayed. No full or umbrella build was run.
- Wired the leaf into `GaloisForLFunctions/RHTower.lean`. The existing root path is `GaloisForLFunctions.lean` → `MainTheorems.lean` → `RHTower.lean`.
- `scripts/formal_tools.py lint`: failed on the separate owned module `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMUniversalOnsetDuration`, reported unreachable from its theorem-area umbrella. The new module was not reported. Existing large-file warnings also remain. This is not a globally clean lint claim.
- All owned search and Lean process handles are terminal. No axiom-print command, numerical experiment, new axiom, placeholder, commit, or full build was used.
- No new route-independent rule was added to `universal-law-field/STATUS.md`; its existing parameter/domain and fixed-reader requirements already cover the lesson.
