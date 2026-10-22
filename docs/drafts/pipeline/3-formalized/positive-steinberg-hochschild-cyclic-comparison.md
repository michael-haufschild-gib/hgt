# Positive Steinberg Hochschild–cyclic comparison

- **ID:** PSC-HC-20261006
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); scientific novelty UNVERIFIED
- **Parents:** `positive-rational-steinberg-square-classification.md`; `../1-in-progress/deninger-unit-amalgamation-derived-lagrangian-enhancement.md`
- **Statement:** The existing positive-depth normal unit family survives Hochschild homology of the actual Steinberg quotient with its nonzero augmentation–Kummer value, but vanishes in ordinary cyclic degree one.

## Goal and scope

Identify precisely which homological comparison retains the existing arithmetic mark. This is
an unconditional source theorem, not a proof of RH or a geometric Xi compatibility theorem.
No numerical experiment, positive metric, spectral realization, or estimate is used.

## Exact paper proof [PROVED HERE]

Let `S = C[Q^×]`, `J` be the existing positive complementary Steinberg ideal, and `A=S/J`.
The already formalized equality `J=Iplus²` gives `v_q v_r=0` for every positive rational pair,
where `v_q=[q]-1` in `A`. In particular `u_q=1+v_q` has inverse `1-v_q`.
The independent negative-rational sign sector is retained throughout. Since `A` is commutative,
every degree-one tensor has zero Hochschild boundary; Lean also checks equality of the two
degree-one faces for the exact source image.

Write `P(a,b)=a⊗b`, `T(a,b,c)=a⊗b⊗c`, and
`bT(a,b,c)=P(ab,c)-P(a,bc)+P(ca,b)`. Direct multilinearity gives, for `v²=0`,

```
P(1-v,1+v) = P(1,v) + b(T(1,1,1)-T(v,1,1)-(1/2)T(1,v,v)).
```

Indeed the three displayed boundaries are respectively `P(1,1)`, `P(v,1)`,
and `2P(v,v)`. Thus the Hochschild unit class is precisely the differential class
represented by `P(1,v)`; no cyclic relation has been imposed in this calculation.

For ordinary cyclic degree one the additional relation is `P(a,b)+P(b,a)=0`.
The stronger explicit identity is

```
P(1-v,1+v) = P(1,v)+P(v,1)
  + b(T(1,1,1)-2T(v,1,1)-(1/2)T(1,v,v)).
```

This proves vanishing in the ordinary cyclic quotient. It does not assert vanishing in
negative cyclic homology or in relative cyclic degree zero.

The positive survivor is a concrete source detector. Existing augmentation `epsilon` and
augmentation–Kummer derivative `delta` annihilate `J`, so both descend to `A`.
They satisfy `delta(ab)=epsilon(a)delta(b)+delta(a)epsilon(b)`, `delta(1)=0`.
The linear functional `L(P(a,b))=epsilon(a)delta(b)` annihilates every `bT(a,b,c)`:
expanding the middle derivative cancels the first and last terms. For `epsilon(v)=0`,
`L(P(1-v,1+v))=delta(v)`. For the existing normal direction indexed by positive depth `m`,
this is `m log(3/2)`, nonzero by the existing source theorem. Hence that exact quotient
unit cycle is not a Hochschild boundary. This detector cannot descend to ordinary cyclic
homology: its value on `P(1,v)+P(v,1)` is the same nonzero number.

## Hostile and novelty audit

- Distinguish the source coefficient-of-identity cyclic trace from augmentation. Replacing
  the trace silently would change the invariant. The survivor uses an explicitly different
  Hochschild functional and proves its exact value.
- Do not call the ordinary cyclic vanishing a nilpotent Chern-character vanishing: negative
  cyclic and relative cyclic groups are different targets.
- Corpus searches: hybrid `Steinberg tangent geometric comparison`, `square zero cyclic
  tangent`, `Kummer cyclic`; lexical `"square zero" "cyclic"`; exhaustive focused source
  text search. Hybrid reports `partial:false`, snapshot coverage, with many compiler records
  pending/stale; applicability is checked separately in Lean. No exact source comparison
  found. Existing local-divisor relative-K1 card already retains nilpotent logarithms, so
  that generic idea is not claimed new.
- External audit: [Cortiñas–Weibel, Relative Chern characters for nilpotent ideals,
  introduction and §6](https://arxiv.org/html/0807.1811v3) treats the classical relative
  character into negative cyclic homology and its agreement with Goodwillie's character.
  The finite chain proof above is independent of that theorem. Scientific novelty: UNVERIFIED;
  generic nilpotent homological mechanism is classical.

## No-go closure

- **Failed proposed comparison:** preserve the nonzero arithmetic unit mark through the
  ordinary cyclic-one homology of the static positive Steinberg quotient.
- **Positive survivor:** the same source unit has a nonzero Hochschild-one class, with exact
  augmentation–Kummer value, and an explicit representative modulo boundaries.
- **New insight:** imposing the Steinberg ideal and then ordinary cyclic relations loses
  the single-unit mark even though the tangent layer survives. A candidate geometric map
  must retain the appropriate Hochschild, relative, negative-cyclic, or derived information.
  This does not select a valid Xi comparison, and makes no global impossibility claim.
- **Paper status:** dependency-closed using existing source ideal and regulator theorems.
- **Lean implementation:** `RHTower/SquareZeroUnitCyclicBoundary.lean` and
  `RHTower/Deninger/DeningerPositiveSteinbergCyclicComparison.lean`, under
  `formal/GaloisForLFunctions/`. Generic finite tensor identities and the exact source family
  are implemented. The latter defines `normalCycle` as the canonical tensor-power image of
  `deningerSteinbergNormalKOneCycle`, proves both faces equal, proves non-membership in the full
  degree-two boundary range, and proves membership in the ordinary cyclic relation subspace.
  These are direct chain-level certificates; no independent abstract homology construction
  or negative-cyclic comparison is claimed.

## Verification

- Targeted `lake --old build +GaloisForLFunctions.RHTower.SquareZeroUnitCyclicBoundary`: PASS.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.Deninger.DeningerPositiveSteinbergCyclicComparison`:
  PASS. Both leaves wired once into `RHTower.lean`; no umbrella build run.
- Index regenerated. Final direct `lake env lean` checks on both repository source files: PASS,
  empty logs. All 37 public declarations audited transitively with `#print axioms` in a `/tmp`
  scratch import: exactly `propext`, `Classical.choice`, `Quot.sound`; no additional axiom.
- Global `scripts/formal_tools.py lint`: FAIL, six unrelated unwired leaves:
  `RHTower.WeilZetaSquareBoundaryInequality` and `HTGeometry.{ApertureConeCalculus,
  ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra}`.
  Neither new leaf is reported. The five aperture/corona findings also occurred before this
  cycle; the Weil leaf belongs to concurrent work. Global green is not claimed.
- Evidence logs: `/tmp/rh-square-zero-cyclic-build-20261006.log`,
  `/tmp/rh-steinberg-cyclic-build-20261006.log`,
  `/tmp/rh-square-zero-cyclic-final-20261006.log`,
  `/tmp/rh-steinberg-cyclic-source-final-20261006.log`,
  `/tmp/rh-steinberg-cyclic-axioms-final-20261006.log`, and
  `/tmp/rh-steinberg-cyclic-lint-20261006.log`.

## Checklist

- [x] Corpus and primary-source audit; exact paper proof; source/sign scope fixed.
- [x] Formalize finite tensor identity, ordinary cyclic vanishing, and nonzero source survivor.
- [x] Targeted build, direct source checks, all new declaration axioms, lint, umbrella wiring.
  Global lint is red for the unrelated findings listed above.
- [x] Record the still-open geometric comparison; the full RH goal remains active.

## Next research obligation

Construct an actual source-defined geometric comparison retaining the arithmetic tangent mark
in a compatible Hochschild/relative/negative-cyclic object. Neither this source comparison nor
the classical nilpotent Chern-character theorem supplies the Xi compatibility law. The result
closes a proposed ordinary-cyclic shortcut; it does not refute the open RH-equivalent geometric
compatibility statement. A further generic nilpotent lemma would not discharge that obligation.
