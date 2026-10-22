# Completed-Eisenstein continuum excludes QNM-only HB completion

- **ID:** C-HB-QNM-1
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `ThetaCuspHawkingEKGCompletedEisensteinOpticalIncidence` · HB finite-carrier producer audit
- **Statement:** Every Xi divisor has strictly positive integrated completed-Eisenstein continuum mass, so no finite QNM/Maass sector can be the complete nonlinear EKG optical response.

## Goal

Kill the finite-QNM-only realization of the remaining HB retarded/advanced producer.  The full RH
chain needs a source-derived causal Green pair whose jump supplies the fixed FE--Schwarz Ward law.
If the finite Xi/QNM carrier were the complete nonlinear response, adding the physical continuum
would not change optical energy.  The proposed theorem proves the opposite at every Xi divisor and
therefore forces every surviving producer to construct a genuine direct/continuum response before
attempting Ward extinction.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `not_thetaCuspHawkingEKGUniversalFiniteQNMOnlyComplete`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Proof chain being closed

1. HB needs an actual retarded/advanced Einstein--Teukolsky response, not an abstract receiver.
2. A QNM-only proposal identifies the complete response energy with one finite discrete sum.
3. The corpus constructs the completed-Eisenstein continuum density `D(q,t,r)` for every Xi copy.
4. C-HB-QNM-1 aims to prove `0 < ∫ r, D(q,t,r)` unconditionally for every `q,t`.
5. Hence `E_discrete + 2π ∫ D > E_discrete`; universal QNM-only completeness is impossible.
6. Surviving HB work must include continuum/direct-arc data and then derive FE--Schwarz extinction
   for that completed response.  The theorem does not assume or restate RH.

## Approach

Corpus inputs are already unconditional:

- `thetaCuspHawkingCompletedEisensteinContinuumDensity_nonneg`;
- `continuous_thetaCuspHawkingCompletedEisensteinContinuumDensity`;
- `integrable_thetaCuspHawkingCompletedEisensteinContinuumDensity`;
- `exists_thetaCuspHawkingCompletedEisensteinContinuumDensity_pos`.

For fixed `q,t`, let `D(r)` be this density.  If its integral were zero, nonnegativity and
integrability would force `D = 0` almost everywhere.  Continuity and full support of Lebesgue
measure would then force `D = 0` everywhere, contradicting the corpus-proved bright point.  Thus
the continuum mass is strictly positive.  Multiplication by `2π > 0` gives strict excess over
every finite discrete energy.

## Novelty / hostile audit

- **Internal search:** no theorem states strict integrated continuum mass, strict excess over the
  discrete sector, or impossibility of a QNM-only completed EKG response.  Existing results prove
  pointwise brightness and a pointwise Weisskopf--Wigner identity.
- **External SOTA through 2026-08-31:** current Kerr/QNM work explicitly requires continuous
  spectrum and warns that QNM sums can diverge (`arXiv:2607.19492`); nonlinear Kerr tails also use
  far-field Green/continuum response (`arXiv:2603.20379`).  No source proves this exact
  completed-Eisenstein continuum theorem at every Xi scattering pole.
- **Circularity:** statement quantifies over existing `XiZeroCopy` support but assumes no placement
  law, no RH, no Ward extinction, and no target-fitted coefficient.
- **Failure mode checked:** positivity at one point alone would not suffice without continuity;
continuity plus Lebesgue full support closes that gap.  The conclusion kills completeness, not
existence of useful finite QNM approximations.

## Paper proof

**[PROVED HERE]** Fix `q : XiZeroCopy` and `t : ℝ`, and abbreviate
`D(r) = thetaCuspHawkingCompletedEisensteinContinuumDensity q t r`.

1. The corpus proves `D(r) ≥ 0` for every `r`, `D` continuous, and `D` integrable on `ℝ`.
2. The corpus also proves existence of `r₀` with `D(r₀) > 0`.
3. The support `{r | D(r) ≠ 0}` is open by continuity and contains `r₀`.
4. Lebesgue measure has full support, so every open neighborhood of `r₀` has positive measure.
   Hence the functional support of `D` has positive measure.
5. The nonnegative-integral support criterion gives `0 < ∫ r, D(r)`.
6. Since `2π > 0`, for every finite mode set and every amplitude family,
   `E_discrete < E_discrete + 2π ∫ D`.
7. Therefore equality of continuum-completed and finite-QNM energy is false copywise.  Since the
   Xi divisor is nonempty, no single finite QNM/Maass sector can satisfy that equality globally.

No step assumes critical-line placement, RH, a dark-mode law, or a target-dependent response.

## No-go closure

- **Exact killing theorem/mechanism:** strict positive integrated continuum mass forces a strict
  optical-energy excess over every finite discrete sector at every Xi divisor.
- **Strongest positive survivor:** the completed-Eisenstein continuum is an irreducible positive
  response channel at every Xi divisor; a viable HB producer must retain it.
- **New insight:** finite Xi/QNM Peierls carriers can only be projected receivers.  Physical
  producer search must move to a continuum-completed Green pair before imposing FE--Schwarz laws.
- **Status:** dependency-closed Lean proof in
  `ThetaCuspHawkingEKGContinuumQNMOnlyCompletenessNoGo`.  Direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEKGContinuumQNMOnlyCompletenessNoGo`
  pass.  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.  Module is
  wired into `GaloisForLFunctions.RHTower`.  Global lint reaches this module; current lint failure
  is confined to three unrelated concurrent unreachable modules.

## Log

- 2026-08-31 — created in 1-in-progress after internal corpus and 2026 literature audit.
- 2026-08-31 — `[PROVED HERE]`; promoted to 2-fully-proven before Lean formalization.
- 2026-08-31 — Lean formalization and targeted build passed; finite-QNM-only producer moved to
  5-failed with irreducible positive continuum mass as survivor.
