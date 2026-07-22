# Critical-half-weight co-Poisson cocycle unitarization

- **ID:** `critical-half-weight-copoisson-cocycle-unitarization`
- **Stage:** 1-in-progress
- **Type:** RESEARCH SPECIALIZATION / EXISTING GENERAL SOURCE-REALIZATION PROBLEM
- **Source:** `suzuki-source-realization-knowledge-ledger.md`, rows `SR-13`--`SR-14`
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE] [EXPERIMENT INSIDE EXISTING OPEN CORE]`
- **Statement:** Explicit compactly supported co-Poisson summation should induce a source-fixed
  one-sided causal metric for the reflection-reversible dilation cocycle at critical half-weight.
  Its contractive defect would be a negative square modulo the co-Poisson multiplier ideal and
  would prove RH.

## Goal

Specialize corpus's already-named cofinal source-bornology/stable-synthesis problem to final Suzuki
edge: when does source-generated quotient of reflection-reversible dilation system admit a
canonical one-sided dissipative metric?

For Burnol's source quotient, desired theorem must be constructed on compact seed functions before
annihilator specialization and imply

```text
A_+ A_+^* <= A_- A_-^*,
```

or its weaker Berezin-diagonal form on right-half annihilator characters. Existing corpus then
proves RH.

## Gates

- [x] 0 -> 1: exact RH consumer, parent collisions, minimal hostile model, and falsifiers recorded
- [x] finite source operator exists as `trueApertureMuntzMap`; do not reconstruct it
- [x] exact finite Möbius reconstruction and local frame law exist; do not reconstruct them
- [x] reject finite-adjoint/Stieltjes insertion: source domains do not match
- [ ] construct or refute BV-prime-window to co-Poisson singular graph connector
- [ ] derive exact common-interior/two-boundary-strip block decomposition
- [ ] identify Hermitian boundary defect before introducing a zero or annihilator
- [ ] prove negative-square-plus-multiplier-ideal factorization, or prove exact positive obstruction
- [ ] if positive factorization succeeds, formalize source theorem and compose to RH in Lean
- [ ] if obstruction succeeds, classify maximal source class killed and extract positive survivor

## Corpus collision and surviving experiment

Douglas factorization, Schur realization, quotient Berezin diagonal, Hardy model-space defect,
safe-width causal contraction, true finite Müntz map, finite Möbius inversion, and cofinal
source-bornology wording are already in corpus. This card adds no conjectural knowledge.

The proposed finite-aperture adjoint experiment does not survive type audit. `trueApertureMuntzMap`
acts on Sonin `L2`, whereas the existing Stieltjes pairing acts on lag profiles and
autocorrelations. Finite Möbius inversion supplies no canonical source map between those objects.

Surviving experiment uses the fixed BV prime-window dilation orbit, where finite coefficient
Stein positivity and exact horizontal Laurent covariance coexist. Construct or refute a closable
map from that orbit into the co-Poisson quotient graph which intertwines decimation with compressed
dilation and retains the off-multiple boundary principal part. This is the singular-boundary
representation problem recorded in the knowledge ledger, not another adjoint calculation. Its
broad prime--Gamma form is already developed in
`prime-gamma-reflection-decimation-defect-resolvent-rh.md`; only the direct co-Poisson
specialization is under test here.

## Geometric coordinate (control only)

Put logarithmic seed interval `I_A=[-A,A]`, where `A=-log a`, and translation size `t=log r`.
Forward and inverse source windows inside enlarged interval `I_(A+t)` are

```text
I_+=I_A-t=[-A-t,A-t],
I_-=I_A+t=[-A+t,A+t].
```

Their common interior and unmatched boundary strips are explicit:

```text
I_+ intersect I_-=[-A+t,A-t]                  when t<=A,
I_+ minus I_-=[-A-t,-A+t),
I_- minus I_+=(A-t,A+t].
```

For `t>A`, common interior is empty. This window geometry is a control, not next theorem: aperture
layer decompositions are already formalized. Reflection swaps boundary strips and cannot order
them.

## Named open core

`COPOISSON-CRITICAL-BOUNDARY-DISSIPATION`:

This is existing `(ER12)`/stable-synthesis core in specialized language. After common-interior
cancellation, right boundary channel factors contractively through left boundary channel in
source-fixed norm, modulo range of completed co-Poisson multiplier. In Hermitian form,

```text
D_(A,t)=S_(A,t)^* S_(A,t)
        +R_(A,t) M_Lambda+M_Lambda^* R_(A,t)^*.
```

Sign convention must be fixed by matching safe-width positive control. No claim of novelty or
truth is made until source-fixed synthesis vector and uniform norm are proved.

## Falsification protocol

- attack `t>A` first: absence of common interior exposes any hidden dependence on overlap;
- test endpoint `t=A`: boundary strips meet at one point and no positive mass may be smuggled into
  null overlap;
- replace co-Poisson summation by identity operator: desired orientation must fail;
- replace source-fixed norm by arbitrary equivalent norm: result is rejected even if contraction
  can be forced;
- retain multiplier variable throughout; specializing to `Lambda=0` before factorization is a
  circular failure.

## No-go closure

- **Exact killing theorem/mechanism:** pending explicit boundary calculation.
- **Strongest positive survivor:** exact characterization of the maximal singular graph on which
  coefficient Stein positivity, one-sided decimation contraction, and Laurent principal-part
  continuity coexist; or `NO POSITIVE SALVAGE FOUND` after second pass.
- **New insight:** generic reflection-reversible cocycles are insufficient; only critical-weight
  source causality can select horizontal orientation.
- **Status:** conjecture; no mathematical claim here is promoted as new scientific knowledge.

## Log

- **2026-07-22 — created.** Generic `SUZUKI-COPOISSON-KREIN-CONTRACTION` retired as a research
  description: corpus already had its Douglas and Hardy forms. Replaced by explicit source-window
  boundary-dissipation problem with positive/negative controls and exact falsifiers.
- **2026-07-22 — reclassified after ledger collision.** Broader source-bornology/passivity core,
  exact co-Poisson Douglas target, finite Müntz map, and Möbius recovery were already present.
  Card is now a specialization only. First admissible experiment is uniform adjoint synthesis of
  actual Stieltjes boundary functional.
- **2026-07-22 — object-type correction.** Müntz adjoint and Stieltjes lag functional have no
  corpus-defined common source domain, so their proposed insertion is retired before formalization.
  Experiment moves to the BV coefficient-decimation orbit, whose finite Stein defect and Laurent
  character already match the live horizontal orientation. Required new object is a concrete
  BV-to-co-Poisson singular graph intertwiner.
- **2026-07-22 — broader-form collision.** Prime--Gamma reflection-decimation research already
  constructs the finite all-depth balanced packets and isolates its remaining infinite-rank
  off-diagonal Green--Schur/Euler identity. This card claims neither that general problem nor its
  finite packets as new; it tests only whether Burnol's explicit co-Poisson quotient realizes the
  missing singular graph.
