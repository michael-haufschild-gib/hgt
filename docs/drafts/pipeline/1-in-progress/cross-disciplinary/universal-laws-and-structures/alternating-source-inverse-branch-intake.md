# Alternating source: inverse-branch intake and first coefficient obstruction

- **ID:** RH-ALT-INVERSE-20260906
- **Stage:** 1-in-progress
- **Type:** CANDIDATE AUDIT; exact coefficient boundary formalized; no qualifying RH architecture
- **Source:** current corpus `FormalCompositionalInverseFreeness`, literal alternating
  coefficients and their zeta boundary value; corpus search paired with `rg`.
- **Novelty:** polylogarithm mapping theory and compositional inversion are established
  subjects. No claim that an inverse-branch RH construction is absent from literature.

## Intended chain and first conjecture

Start with the actual normalized power series

    F_s(z) = sum_(n>=1) (-1)^(n-1) n^(-s) z^n.

For Re(s)>0 its radial value at z=1 is the convergent alternating series
`eta(s)=(1-2^(1-s))*zeta(s)` (s=1 is handled by its removable limit). Its derivative at
zero is 1, so formal compositional inversion exists at every s. A nontrivial zeta zero
therefore makes the distinguished boundary point z=1 have the same output as z=0.
The proposed chain would need an arithmetic obstruction to that particular inverse-branch
collision for Re(s)>1/2, independently of the zero-location conclusion.

First test: is F_s injective on the unit disk for every Re(s)>1/2? This would be a much
stronger global extension principle than the local formal inverse. A zeta zero at the
boundary cannot be rejected merely by confusing open-disk injectivity with injectivity
on its closure; any endpoint deduction must separately justify boundary behavior.

## Paper falsification test

The first coefficients are `a2=-2^(-s)` and `a3=3^(-s)`. The classical area theorem
gives the necessary condition `|a3-a2^2|<=1` for a normalized injective analytic map
of the unit disk: apply the exterior area theorem to `1/F_s(1/z)`, whose coefficient
of `z^(-1)` is `a2^2-a3`.

Put `t0=pi/(log 4-log 3)`. At `s=sigma+i*t0` the phases of `3^(-s)` and `4^(-s)`
are opposite. Consequently

    |a3-a2^2| = 3^(-sigma)+4^(-sigma).

At sigma=1/2 this is `1/sqrt(3)+1/2>1`; continuity retains the strict inequality
on a nonempty interval to the right of 1/2. Thus the global injectivity conjecture
fails inside the desired strict half-strip. This calculation uses no zeta zero input
and no numerical experiment.

## Positive survivor and limits

The strongest immediate scalar survivor is an exact horizontal coefficient classification:
for every real sigma and every real bound C,

    (forall t, |3^(-(sigma+i*t))-4^(-(sigma+i*t))|<=C)
        iff 3^(-sigma)+4^(-sigma)<=C.

The upper bound is the triangle inequality; t0 attains it exactly. The right side is
continuous and strictly decreasing in sigma and passes through 1 at one point strictly
between 1/2 and 1. This is an elementary, fully explicit admission boundary for this
necessary coefficient test, not a zero-location law.

The literal coefficient identity, formal inversion, sharp horizontal bound, unique cutoff,
and existence of a strict-half-strip violation are now closed in Lean. The geometric
area-theorem bridge was not located by the corpus searches; the full noninjectivity
claim is a paper consequence of that classical theorem, not a Lean theorem in this
module. A restricted inverse corridor aimed only at z=1 remains an unproved possibility,
with no independent construction or novelty case established. The coefficient obstruction
does not prove that F_s has a second zero inside the disk, nor does it reject every
possible argument about its distinguished boundary value.

The proposed fallback using zero motion of `F_s(r)=-Li_s(-r)` for real `0<r<1` has not
established a new architecture. [Vepstas, *The Polylog and the Riemann Hypothesis*
(2023)](https://www.linas.org/math/polylog.pdf), pages 5–7, already proposes zero-motion,
bracketing, and zero-variety questions connected with RH. That note studies a different
argument boundary and is used here only as evidence of prior proposals, not as a proved
mathematical input. No exact equivalence with the negative-argument conjecture is claimed.
The corpus's existing ordered-second-level identities also do not supply a new branch
restriction. No numerical experiment or additional formal theorem resulted from this intake.

## Formal positive result and verification

`formal/GaloisForLFunctions/RHTower/AlternatingInverseCoefficientBoundary.lean`, namespace
`RHTower.AlternatingInverseCoefficient`, contains 18 public theorems and seven definitions.

- `formalSeries_subst_inverse` and `formalInverse_subst_series`: the literal full formal
  coefficient series has both compositional inverse identities for every complex s.
- `defect_eq`: its actual third coefficient defect is `3^(-s)-4^(-s)`.
- `norm_defect_at_height` and `horizontal_bound_iff`: the stated bound is attained exactly;
  this is a complete classification for every real sigma and every real ceiling C.
- `exists_unique_cutoff`, `cutoff_spec`, and `horizontal_unit_bound_iff`: one and only one
  cutoff lies strictly between 1/2 and 1, and the uniform unit ceiling holds precisely
  on and to its right. Passing this coefficient test does not prove injectivity.
- `exists_strict_half_strip_violation`: a literal parameter with `1/2<Re(s)<1` violates
  the unit ceiling, while retaining its formal inverse.

Scratch proof and direct source check with `lake env lean <file>` passed. Scratch axiom
audit covers all 25 public declarations and contains only `propext`, `Classical.choice`,
and `Quot.sound`. No added postulate or numerical certificate enters the proof. The final
foreground build uses `LEAN_NUM_THREADS=1 lake build --old
GaloisForLFunctions.RHTower.AlternatingInverseCoefficientBoundary`; the module is wired
into `RHTower.lean`, with no full or umbrella build. Scratch files and audit output are
in `/tmp/hgt-alt-inverse-xb4oc6`.

The final narrow build passed, newly building only this leaf (3020 jobs including cached
dependencies). Index regeneration passed and the research tool retrieves
`horizontal_unit_bound_iff` from the new module. Global lint currently exits 1 solely for
two other owned-tree modules missing umbrella reachability:
`CCMRestrictedWeilPoleParityCurvature` and `CCMRestrictedWeilPrimeAgeBalance`.
Those concurrent files were left untouched. The new leaf has no lint error and is wired;
all Lean processes started for this intake finished. Lint logs are in the scratch folder.

The positive theorem is elementary and is not claimed as new scientific knowledge.
The audit stays in progress because neither a qualifying inverse-branch RH mechanism
nor a Lean area-theorem connector is established. Formalizing generic geometric mapping
theory alone would not supply the missing arithmetic branch restriction.

## Checks and dependencies

- Corpus searches: `coefficient nonlinear`, `compositional inverse`, `polylogarithm`
  with exact tokens, `alternating generating`, `univalent`, `Fekete Szego`.
- Read the universal inverse construction and its specialization in
  `HTGeometry/FormalCompositionalInverseFreeness`; this is formal local algebra and
  contains no global inverse extension theorem for the literal alternating source.
- The alternating boundary value is already formal in
  `RHTower/DQPTPartialSumRate.dqpt_altPartialSum_tendsto`. Its published decay-rate
  architecture is not being adopted.
- [Ponnusamy and Sabapathy, *Polylogarithms in the Theory of Univalent Functions*](https://link.springer.com/article/10.1007/BF03322186),
  Results in Mathematics 30 (1996), 136–150: publisher abstract opened; it studies
  geometric mapping properties for real parameter families. This is established
  parent theory, not evidence for the complex-order half-strip conjecture above.
- [Cheraghi, *Growth and Distortion Estimates*, section 6.2, Theorem 6.2](https://www.ma.imperial.ac.uk/~dcheragh/Teaching/2016-F-GCA/2016-F-GCA-Ch6.pdf):
  the exterior area theorem and its proof were opened; the preceding inversion formula
  gives coefficient `a2^2-a3`. This supplies the paper bridge to noninjectivity. Its
  use here is a proved classical obstruction, not an unresolved RH route.
- The exact phrase query `research '"area theorem"' --exact` found no declaration;
  `Bottcher/STATUS.md` separately lists Gronwall's coefficient area theorem as a next
  brick after its already formalized holomorphic area change-of-variables theorem.
  This confirms the located local infrastructure is not yet the needed geometric bridge;
  neither a search miss nor a status note proves global absence from the codebase.
