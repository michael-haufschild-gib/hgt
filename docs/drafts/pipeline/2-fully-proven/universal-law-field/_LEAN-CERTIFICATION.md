# Universal-law-field Lean certification boundary

Project rule: **paper proof does not count as proved until its exact significant theorem is closed in
Lean**.  Files remaining in this Stage-2 folder are therefore research claims awaiting certification,
even when their paper argument is dependency-closed.

Dedicated Lean umbrella:
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Certified and promoted to Stage 3

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PIR-1 | Positive doctrine, additive nondescendence, faithful response coframe, recurrence/open lift | `HTGeometry.ConstitutivePositiveResponse` |
| ULF-CFL-1 | Complete passive equivalence versus injective marked intervention | `HTGeometry.ConstitutiveInterventionSeparation` |
| ULF-SLOT-1 | Independent-slot transitivity; invariant phases trivial; invariants constant | `HTGeometry.ConstitutiveIndependentSlotNoGo` |
| ULF-RADIUS-2 | Serial-radius counterexample and hidden-pair/diameter survivor | `HTGeometry.ConstitutiveReconstructionNoGo` |
| ULF-AEEC-1 | Adaptive mimicry, coherent non-effective boundary, finite effectivity-classifier no-go | `HTGeometry.ConstitutiveAdaptiveProcompletion` |
| ULF-AMCC-1 | Minimal adaptive transcript support, universal additive-cost minimizer, exhaustive coercivity | `HTGeometry.ConstitutiveAdaptiveCost` |
| ULF-GCP-1 | Exact response-kernel persistence, Gamma Bockstein death set, critical survival, and lifetime | `HTGeometry.ConstitutiveGammaResponseLifetime` |
| ULF-RBD-PREFIX-1 | Prefix observer stabilization, non-effective horizon, recurrent phase, positive erasure, singleton production, open action | `HTGeometry.ConstitutiveEffectivityHorizon` |
| ULF-RBD-JET-1 | Exact DA/HT finite-jet double realization, mutual density, empty interiors, nonclosed strata, continuous-classifier no-go | `HTGeometry.ConstitutiveFiniteJetBoundary` |
| ULF-REG-KONIG-1 | Locally finite realization tower has a global section; finite-local/global gap requires noncoherence, nonproperness, or extra admission | `HTGeometry.ConstitutiveRealizationKonig` |
| ULF-REG-SEID-1 | Surjective erasure forces infinite dimension; fixed-corona Gamma-Bockstein death has no faithful finite-dimensional linear model | `HTGeometry.ConstitutiveSurjectiveErasure` |
| ULF-HISTORY-1 | Nonnegative additive groupoid costs vanish; complex real-cost part vanishes; directed histories admit nonzero additive cost | `HTGeometry.ConstitutiveHistoryPolarization` |
| ULF-PRD-PUMP-1 | Observer unitization forces recurrence, injective open history, linear action, and cost nondescendence | `HTGeometry.ConstitutiveObserverUnitization` |
| ULF-DEFECT-2 | Same endpoint defects and size admit split/nonsplit events distinguished by carry and lifted-period holonomy | `HTGeometry.ConstitutiveExtensionCarry` |
| ULF-NFD-2 | One periodic producer and quotient force recurrent observation, nonclosed lift, carry, decoder failure, and unbounded prefix history | `HTGeometry.NomogenicFixedPointCalibration` |
| ULF-NPG-PIN-1 | Natural free-monoid interventions are uniform powers; ramification comparisons are inverse-depth; power naturality does not select radial origin | `HTGeometry.ConstitutiveNaturalPowerNormalization` |
| ULF-CTX-1 | Exact parity contextuality criterion, one-dimensional total-charge obstruction, proper-face blindness, and compatible uniform positive state without a global law | `HTGeometry.ConstitutiveParityContextuality` |
| ULF-IRR-1 | Minimal irreducible `N`-ary law with all composites zero, abelian proper colour faces, non-homotopy-abelian total law, interaction order `N`, and non-locally-compact unbounded spectrum | `HTGeometry.ConstitutiveIrreducibleInteraction` |
| ULF-TORS-1 | Acyclic based two-term complexes, determinant history as a complete based invariant, multiplicativity, positive shadow as the exact phase quotient, and closed observation with open logarithmic lift | `HTGeometry.ConstitutiveDeterminantTorsion` |
| ULF-FILL-1 | Van Kampen area of `aⁿbⁿa⁻ⁿb⁻ⁿ` is exactly `n²` with trivial endpoint, length `4n`, and orientation-blind cost | `HTGeometry.ConstitutiveQuadraticFilling` |
| ULF-OPM-2 | Failed unary exchange generates the least preserved congruence; induced quotient laws commute; every commuting observer factors uniquely through it; no smaller strict repair exists | `HTGeometry.ConstitutiveExchangeStrictification` |
| ULF-OPM-3 | One exchange residual admits strict quotient and nonsplit central promotion; cocycle coherence, exact commutator carry, fixed lift residual, and no-section theorem | `HTGeometry.ConstitutiveExchangeCentralPromotion` |
| ULF-OPM-4 | Reporter descends exactly when constant on generated exchange congruence; critical-pair detection forbids commuting strictification with reporter preservation; Heisenberg history reporter selects central promotion | `HTGeometry.ConstitutiveExchangePromotionSelection` |

Formalized cards and declaration-level records live in
`docs/drafts/pipeline/3-formalized/universal-law-field/`.

## Partially certified, not promoted

`ULF-MPTB-1` has a certified coordinate-free core in
`HTGeometry.ConstitutiveProcessTomography`: exact annihilator blind sector, reconstruction iff
spanning, nonzero blind-direction existence, affine record equality, and qualitative open-interior
robustness. Product-slot dimension formula and quantitative PSD spectral bound remain uncertified,
so card stays in Stage 2.

`ULF-EQG-1` has a certified local and finite core:

- `HTGeometry.QPochhammer`: q-Pochhammer convergence, shift, nonvanishing; normalized q-Gamma
  translation; positive local weights; mass one; every nonnegative-integral moment;
- `HTGeometry.EulerQGammaFiniteProcess`: finite response/divisor telescopes and genus-one exchange.

Its global prime probability, zeta ladder, meromorphic divisor, hypertranscendence, and recurrence
claims remain uncertified.  The card therefore stays in Stage 2.

## Rejected by formal attack

`ULF-DISTORTION-1` claimed monotonicity of internal-centre reconstruction radius under serial
postprocessing.  A Lean-certified three-point counterexample shows strict decrease from two to one.
The rejected card is in `docs/drafts/pipeline/5-failed/universal-law-field/`; ULF-RADIUS-2 records
the exact survivor.

## Session 2026-08-09 additions (inverse-theory layer)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-INV-N8-J | Source involution `f ↦ conj(f(-x))` is involutive and realizes the sharp operation on `e^{-izx}` transforms, hypothesis-free (junk-value exact); eigen-transform compatibility | `RHTower.XiWeilSourceInvolution` |

Axiom print: `[propext, Classical.choice, Quot.sound]` on all three declarations; module wired
into the `RHTower` umbrella; `lake build +GaloisForLFunctions.RHTower.XiWeilSourceInvolution`
green (8937 jobs). This certifies the involution-existence half of the N8 gate analysis
(ULF-INV-11 §4): the involution is free in Lean too; the open content is the positivity of its
pairing, exactly as re-typed.

| ULF-INV-D4A | Theta-cusp seed evenness; Gaussian half-moments 1/(4π), 3/(8π²) via the cold-moment recursion; **zero half-line mean of the seed** (the D4a cancellation) | `RHTower.ThetaCuspSeedZeroMean` |
| ULF-INV-7-CORE | Two-point pattern cap \|b\| ≤ a (Page's ρ(ℤ/2)=1, tight); circle witness 3+4cosθ+cos2θ ≥ 0 with ratio 4/3 > 1; width-cap inequality (the 1/𝔏 shape forced) | `HTGeometry.FiniteAmplifierPatternCap` |

`ThetaCuspSeedZeroMean`: build green (9051 jobs), axioms `[propext, Classical.choice,
Quot.sound]` on all printed declarations. `FiniteAmplifierPatternCap`: clean elaboration;
umbrella build and axiom print recorded in the session log on completion.

| ULF-INV-1-CORE | The compensation is forced (normalizer convergence derived from product convergence, A ≠ 0); **cross-system blindness in derived form** — same nonzero leading coefficient + one convergent regularization ⟹ identical limits | `HTGeometry.MultiplicativeRegularizationBlind` (extended) |

Build green (8655 jobs); axioms standard. This is the abstract engine of ULF-INV-1
(Beurling cross-system blindness); the arithmetic instantiation (Mertens-normal systems, the
generator-swap comparison pair) remains paper-level in the stage-2 card.

| ULF-INV-10-S1 | Stage 1 of the eigen-pair identification's prime half: real vonMangoldt summability at σ>1; line-kernel continuity and exact modulus n^{−σ}; per-term integrability and exact integral norms; **termwise LSeries line integration against any integrable weight** | `RHTower.VonMangoldtLineSeriesSwap` |

Build green (8826 jobs); axioms standard. Stages 2–5 (boundary vanishing, residue collapse,
double pole, assembly) remain per the staged plan in the promoted card.

| ULF-INV-10-S2A | Stage 2, Lemma A: exponential substrip decay of `deriv XiC` by Cauchy transfer from the XiC strip bound (strip-shrink, slack absorbed into the constant) | `RHTower.XiCDerivStripDecay` |

Build green (8941 jobs); axioms standard. Remaining prime-half stages: 2B (vertical-segment
vanishing for the single-pole integrand), 3 (one-pole residue), 4 (matched/double case),
5 (assembly).

| ULF-INV-10-S2B | Stage 2B: vertical-edge vanishing under exponential horizontal domination, both sides (the widening-rectangle boundary engine) | `HTGeometry.VerticalEdgeVanishing` |

Build green (2580 jobs); axioms standard. With the corpus-owned rectangle Cauchy formula
(stage 3) and today's XiC' bound (2A), the prime-half chain's remaining new work is stage 5
(assembly) plus at most a stage-4 bridge.

| ULF-INV-10-S5A1 | The convention bridge: the Hedenmalm eigen transform equals the mathlib Fourier integral of the imaginary-part-tilted flow at frequency `z.re/(2π)` — the linchpin linking the corpus's `e^{-izx}` normalization to mathlib's convolution/inversion machinery | `RHTower.HedenmalmLineTransformBridge` |

Build green (8937 jobs); axioms standard. Remaining in the chain: 5a-2 (line-product
integrability from the 18a bounds — assembly-level), 5a-3 (inversion application), 5b (final
assembly), stage-4 bridge if the two-pole variant needs adaptation.

| ULF-INV-10-S5A2 | Eigen-pair line integrability: the product of a removable quotient with the conjugate-reflected partner quotient is integrable on every substrip line, dominated by the (18a) bounds at doubled rate | `RHTower.EigenPairLineIntegrable` |

Build green (8946 jobs); axioms standard. Chain: 1, 2A, 2B, 5a-1, 5a-2 certified; 3 owned;
4 likely owned; remaining new work: 5a-3 (inversion application) and 5b (assembly).
