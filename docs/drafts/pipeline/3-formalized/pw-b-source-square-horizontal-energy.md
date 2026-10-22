# PW-B original-source-square horizontal energy

- **ID:** PW-B-SOURCE-SQUARE-2026-09-10
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; unconditional closed capstone)
- **Source:** PW-B source-orientation attack; exact singular Gamma reflection carrier
- **Statement:** The squared original Gamma log profile is a positive reflection-unitary density admitting a strictly positive horizontal fixed section with finite positive energy.

## Goal and exact scope

Test whether global adapted energy or an averaged rigidity argument can produce
the missing PW partner balance. The candidate implication is false even for the
square of the original Gamma source profile. This does not retire PW-B, prove RH,
identify the physical Hilbert space, or determine an adjoint or Fredholm index.

## Dependency-closed paper proof

Use the existing source functions

\[
q(t)=e^{t/2-e^t},\qquad
\phi(t)=\sinh t-t/2,\qquad
g(t)=e^{\phi(t)},\qquad a(t)=g(t)^2.
\]

The exact singular reflection is `Tf(t)=a(t)f(-t)`. The corpus proves
`g'=(cosh(t)-1/2)g` and classifies every solution of this horizontal equation as
`f=cg`. Oddness of `phi` gives `Tg=g`.

For an arbitrary density core `h`, put `w_h=a^(-1)h`. Then

\[
w_h(t)(c g(t))^2=c^2h(t).
\]

The existing density classification says that positive even cores give positive
reflection-unitary densities. With `h=1`, the weighted energy of any interval
`[A,B]` is exactly `(B-A)c^2`. Thus bounded mean energy does not force vanishing
of a horizontal section.

Now choose the actual source square `w=q^2`, without introducing a Gaussian
cutoff. Direct source algebra gives

\[
a(t)q(t)^2=q(t)q(-t)=e^{-2\cosh t}.
\]

This core is strictly positive and even, so `w` is reflection-unitary. It is
integrable because

\[
e^{-2\cosh t}\le e^{t-e^t},
\]

using `e^{-t}>=1-t`; the majorant is the existing integrable Gamma log integrand
at parameter one. Hence every horizontal amplitude `c` has finite adapted
energy, and `c=1` has strictly positive total energy. The existing neutral
square-integrability exclusion proves that `g^2` is not Lebesgue integrable.
All statements are analytic; no numerical estimate is used.

## No-go closure and positive survivor

- **Failed implication:** bounded adapted mean energy, or reflection invariance
  together with finite total energy in the original-source-square weight,
  forces a horizontal section to vanish.
- **Exact witness:** `g=exp(sinh(t)-t/2)`, with weighted square
  `q(t)q(-t)=exp(-2*cosh(t))`.
- **Strongest positive survivor:** full horizontal-section classification and
  exact weighted-energy density `c^2 h` for every core, plus finite positive
  admission in the literal source-square density and exact interval growth for
  the flat core.
- **New insight:** the neutral `L2` exclusion cannot be transferred to this
  source-derived norm. A global energy proof needs a separate classification and
  exclusion of its admitted homogeneous solutions. This construction supplies
  an actual surviving solution, not merely an unspecified boundary term.
- **Remaining PW-B obstacle:** derive source-forced fixed-grade partner balance,
  rather than impose a finite-energy or equilibrium condition that does not
  force it.

## Corpus and external-method audit

Four deep searches covered recoil/source orientation, entropy production,
Mellin tangency and monotone singular flux. The saved
[search evidence](../1-in-progress/pw-b-source-orientation-searches.json)
includes candidates, proof-method descriptions, proposed ingredient sets and
coverage. Reported inventory was 56,355 files and 722,314 declarations;
706,071 method records were ready. All four responses were partial. No claim
of exhaustive semantic coverage or corpus-wide theorem absence is made.

Exact text searches found the existing horizontal classification and density
classification in `ThetaCuspHawkingParikhWilczekSingularGaugeConnectionIndexNoGo`.
The prior theorem excludes nonzero horizontal sections in the neutral Lebesgue
norm; it does not assert that exclusion for every reflection-unitary density.
The original profile is `GaloisForLFunctions.expShift (1/2) 0`, already used in
the singular PW carrier. No new source model is postulated.

Broad arXiv searches used entropy, holonomy, rigidity, fluctuation, transport
and resonance, preferring June--September 2026. The useful external mechanism
was the separation of averaged bounds from zero-defect tangent rigidity in
[Chen et al., August 30, 2026](https://arxiv.org/html/2608.29664v1), especially
Sections 1.3 and 3.2. Their Navier--Stokes theorem is not a PW theorem. The
transfer attempt fails because this connection has an explicit nonzero
admitted homogeneous profile. [Schaffer--Exl, September 3, 2026](https://arxiv.org/html/2609.04530v1)
also separates dissipation from equilibrium; its structured dynamics do not
supply arithmetic stationarity. No external paper is a formal dependency.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularWeightedHorizontalEnergy`.

Main closed theorem:
`RHTower.pwLogGammaSource_exists_finiteEnergy_horizontal_fixed_section`.

Other exact statements:

- `pwLogHorizontal_weightedEnergy_classification`
- `pwLogHorizontal_flatCore_intervalEnergy`
- `pwLogGammaSourceDensity_positive_unitary`
- `pwLogGammaSourceDensity_horizontal_energy`
- `pwLogGammaSourceCore_eq_source_product`
- `pwLogGammaSourceCore_integrable`
- `pwLogSingularWeightedReflection_gauge`

Verification completed:

- Scratch and direct `lake env lean` checks passed without warnings.
- Targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularWeightedHorizontalEnergy`
  passed. Lake reported 10,677 dependency jobs; only the new leaf was compiled,
  taking 138 seconds. Cached dependency warnings were replayed.
- A separate scratch `#print axioms` audit covered all 14 new theorems and
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint` passed with existing repository size warnings.
- Umbrella import and generated indexes updated. No full umbrella build.
- One foreground Lean process at a time; all processes from this task completed.
- No numerical experiments, added axioms, or conditional RH theorem.
