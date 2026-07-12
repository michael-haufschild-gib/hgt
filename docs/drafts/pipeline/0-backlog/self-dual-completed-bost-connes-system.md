# Graded self-dual completed Bost--Connes system: the functional equation as an operator-algebra duality

- **ID:** `self-dual-completed-bost-connes-system`
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** collapse theorem and dihedral correction of
  `../3-formalized/not_new_scientific_knowledge/born-temperature-kms-factor-type-duality.md` §8;
  corpus review 2026-07-12
- **Statement:** `[CONJECTURE]` There exists a **graded** C*-dynamical system whose signed
  partition function is the half-dilated completed zeta
  `Z(beta) = Lambda(beta/2) = pi^(-beta/4) Gamma(beta/4) zeta(beta/2)` — discrete prime modes with
  Hamiltonian `log sqrt(n)` welded to one continuous archimedean scale mode — such that
  `beta -> 2-beta` is a duality of the system itself (an operation on its algebra/dynamics), not an
  identity of analytically continued scalars, with fixed locus `beta = 1`.

## Goal

The parent card proved that the ordinary Bost--Connes system cannot carry the functional equation
(symmetry group `R_+ x Zhat*` has no `beta -> 2-beta` element; the Gamma-completion is
Born-invisible; the reflected-sector duality at `xi` zeros collapses to RH verbatim). The residue
is exact: a native FE needs a *different* system in which the reflection acts on the off-diagonal
algebra. Constructing it would make the completed functional equation a Kramers--Wannier-type
operator duality, with the critical line as the self-dual locus of a genuine statistical system
rather than a label. Non-circularity transfers unchanged: `xi`, its divisor, and
square-summability assumptions must not enter the construction.

## Constraints inherited from the corpus (review 2026-07-12)

1. **Dihedral no-go `[PROVED + Lean]`.** `Lambda(beta)` itself is NOT the target partition
   function: its scalar FE reflects about `1/2`, the Born reflection acts about `1`, and carrying
   both forces `1`-periodicity — excluded by the pole at `0` against regularity at `2`
   (`completedRiemannZeta_no_born_reflection`, `doubly_reflected_periodic`,
   `formal/GaloisForLFunctions/RHTower/CompletedBornReflectionNoGo.lean`). The unique Born-self-dual
   gauge is `Z(beta)=Lambda(beta/2)` (`completedRiemannZeta_half_dilated_born_reflection`), i.e.
   prime Hamiltonian `log sqrt(n)`.
2. **Grading is forced `[PROVED + Lean]`.** `Z(1) = Lambda(1/2) = -8 xi(1/2) < 0` real
   (`completedRiemannZeta_half_eq`, `completedRiemannZeta_half_neg`): the self-dual value is
   negative, so `Z` is a supertrace datum, never an ungraded Gibbs trace. The system must carry a
   `Z/2` grading; the duality is a duality of graded KMS structures.
3. **Pole geometry.** `Z(beta)=Lambda(beta/2)` has simple poles at both temperature ends
   `beta=0` and `beta=2` and is regular on `(0,2)`: the phase diagram to construct is
   pole--regular--pole, symmetric about the regular negative self-dual point `beta=1` — unlike bare
   Bost--Connes, whose single pole sits at the transition. What thermodynamic role a *boundary*
   pole pair plays (two ends of a temperature interval, exchanged by the duality) is part of the
   construction problem.
4. **Archimedean-only duality content `[PROVED in tree]`.** The reflection cocycle of `zeta` is
   the pure Gamma quotient `h(s)=Gammaℝ(s)/Gammaℝ(1-s)` with ZERO rate-lattice content
   (`ReflectionCocycleClass.lean`): the FE datum lives entirely in the archimedean cell, and the
   prime rate lattice is weld-inert under it. Together with the parent card's Born-invisibility,
   the demanded duality must act on the **archimedean off-diagonal** structure; it cannot be
   carried by the prime lattice or by any diagonal channel.
5. **III_1 robustness `[PROVED in tree, spectral face]`.** The rate group `<log p>` is dense in
   `R` (`SeamSpectrumDensity.lean`); any extension containing the prime rates keeps a gapless
   modular spectrum, so the high-temperature type `III_1` cannot be deformed away by adding the
   archimedean mode (also the R17/R32 no-gos: no discrete Frobenius; the archimedean component of
   the symmetry group is the connected flow `R_+`). The duality therefore relates a type-`III_1`
   phase to a type-I phase and **cannot be normal** off the fixed locus: the first deliverable is
   the categorical home of a non-normal (graded, possibly antilinear) exchange functor.
6. **Clock selection `[PROVED in tree]`.** In the seam framework (`SeamClockSelection.lean`) the
   Born reflection is the affine constraint with linear part `-1` on the temperature line — the
   `feObject` pattern, unique fixed clock at `1` — while the composition of the two reflections of
   the dihedral no-go is the unit shift, the `shiftObject` with NO clock. The conjectured system
   sits at the reflection vertex of this dihedral pair; the shift face is the classical
   `s -> s+1` difference structure of `Gamma`.
7. **Hypertranscendence status.** `zeta` is hypertranscendental in-tree
   (`hypertranscendental_riemannZeta`); `Gamma`'s Hölder theorem is the named in-tree frontier
   (`GammaDifferentialFE.lean` machinery). `[OPEN CORE]` Hypertranscendence of `Lambda` (equiv. of
   `xi`) is NOT decided by differential-field closure rules — `log Lambda' = psi`-part `+`
   `zeta'/zeta` is a sum of two HT elements — and is the missing certificate that the conjectured
   system's partition function has no finite algebraic-differential handle. Candidate machinery:
   the `HTGeometry` universal prime-log palettes (differential independence under arbitrary
   rational gauges, `UniversalConstraintOrientation.lean`) to force joint independence of the
   prime-log and digamma jets.
8. **Square-root gauge echoes `[BRIDGE, explore]`.** The forced Hamiltonian `log sqrt(n)` is the
   `m=2` rung of the formalized dilation tower (`mPart`, `MFreeTower.lean`;
   `dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt`, `SqrtCarrierCertificate.lean`: the square-dilated
   carrier IS the carrier at doubled argument), and RH-ladder level `1` is exactly the existence of
   an analytic `sqrt(xi)` on the half-plane (`rhLadder_one_iff_sqrt_rightHalf`). The graded
   self-dual system is conjecturally the thermal face of the `sqrt(xi)` Kummer rung: its grading
   operator should square to the trivial one the way `sqrt(xi)^2 = xi`.
9. **Archimedean mode realization `[CONJECTURE, concrete]`.** `Gammaℝ(beta) = 2 * integral over
   x>0 of x^beta e^(-pi x^2) dx/x`: the archimedean mode is the half-line scale variable with
   Gaussian weight and Hamiltonian `-log x`. The Gaussian is the unique Fourier-self-dual weight —
   the natural microscopic carrier of the reflection — and the tree's theta-cusp modules
   (`ThetaCuspReflection.lean`, `XiThetaSourceSeam.lean`) already formalize the reflected theta
   source this mode's second quantization would produce.

## Gates

- [ ] 0 → 1 in-progress: the graded algebra carrying the archimedean mode is fixed; the candidate
  duality map is written on generators; kill tests 1--5 of the parent card re-run against it; the
  non-normal exchange functor's category is named (constraint 5).
- [ ] 1 → 2 fully-proven: existence of the system, its graded KMS_beta classification, and the
  duality with fixed locus `beta=1` proved on paper; `[OPEN CORE]` `Lambda` hypertranscendence
  settled or explicitly bypassed.
- [ ] 2 → 3 formalized: partition-function weld and duality skeleton in Lean; operator content as
  explicit hypotheses (no axioms), extending `CompletedBornReflectionNoGo.lean`.
- [ ] 3 → 4 publication-ready: novelty audit against Connes--Consani archimedean/adelic
  constructions, graded/super KMS literature (Kastler, Jaffe--Lesniewski--Osterwalder chains), and
  lattice Kramers--Wannier duality.

## Approach

1. **Archimedean mode first** (constraint 9): fix the graded one-mode system on the half-line with
   Gaussian weight whose supertrace of `e^(-beta H)` is `Gammaℝ(beta/2)`; identify what the
   grading is for this single mode (the sign of `Z(1)` must ultimately come from somewhere — the
   candidate is the eta/paired-sign structure that makes `xi(1/2)>0` with `zeta(1/2)<0`, already
   formalized in `ZetaRealStrip.lean`/`XiRealAnchorPositive.lean`).
2. **Weld** (constraints 1, 8): tensor with the `log sqrt(n)` prime system so the total signed
   partition function is `Z(beta)=Lambda(beta/2)`; verify the scalar self-duality
   `Z(2-beta)=Z(beta)` lifts to a candidate algebra map exchanging the two boundary-pole phases.
3. **Name the exchange category** (constraint 5): the duality relates `III_1` to type I, so it is
   not a normal *-isomorphism; decide among graded equivalence, antilinear (Tomita-conjugation)
   equivalence, or correspondence/bimodule equivalence, and prove which one the scalar identity
   can support.
4. **Kill tests inherited:** diagonal action is Born-invisible (parent Theorem 5) — dead; scalar
   partition identity alone — dead; measured trace — dead; declaring FE a gauge symmetry —
   circular. The map must act on archimedean off-diagonal structure (constraint 4) and be
   non-normal off the fixed locus (constraint 5).
5. **Degenerate control:** drop the archimedean mode — the parent card proves no duality exists
   for bare Bost--Connes; the archimedean mode is load-bearing or the conjecture is false. Drop
   the grading — constraint 2 proves the ungraded version false outright.

## Log

- 2026-07-12 — created in 0-backlog from the collapse theorem of the Born-temperature card.
- 2026-07-12 — corpus review (pipeline + RHTower + formal root): statement corrected by the
  dihedral no-go to the half-dilated gauge `Z(beta)=Lambda(beta/2)` with forced grading (both now
  formalized in `CompletedBornReflectionNoGo.lean`, axiom-clean); constraints 1--9 recorded with
  their in-tree Lean anchors; `Lambda`-hypertranscendence isolated as the `[OPEN CORE]`
  no-finite-handle certificate.
