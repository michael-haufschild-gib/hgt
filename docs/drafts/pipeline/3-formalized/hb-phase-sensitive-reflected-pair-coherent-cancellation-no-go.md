# HB phase-sensitive reflected-pair coherent-cancellation no-go

- **ID:** HC88
- **Stage:** 3-formalized
- **Type:** CONJECTURE / PHASE-SENSITIVE GLOBAL-WARD NO-GO + CANCELLATION CLASSIFICATION
- **Source:** read-only `rh-current-frontier-map.md` · HC87 representation fracture · corpus BM phase-sensitive chiral Ward amplitude

## Goal

Attack the strongest surviving phase-sensitive shortcut after HC87. The corpus actual BM
mixed-horizon source projection is a nowhere-degenerate physical multiplier times the signed
Deninger reflect-gauge Ward charge, and copywise darkness is RH-strength. Determine whether a
physically weaker reflected-pair or globally conserved Ward amplitude can force copywise darkness.

Prove exact reflection oddness of the calibrated chiral coordinate. For the raw physical
amplitudes at a divisor copy `q` and its functional-equation reflection `Rq`, classify every
two-channel coherent cancellation. Construct explicit nonzero cross-weights from the two physical
multipliers that cancel the pair at every copy. Off the critical line, prove both raw channels are
individually nonzero while their weighted coherent sum is exactly zero.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude` proves the actual raw BM
  projection factors as `M(q) D(q)`, where `M(q) ≠ 0` for a nonzero seed and the calibrated
  coordinate `D(q)` is exactly `1 - 2 Re(q)`.
- `[CORPUS]` copywise raw darkness, calibrated Ward cancellation, FZZ-P information equilibrium,
  PW-B recoil balance, and RBH leading-multiplicity balance share the same pointwise zero locus.
- `[CORPUS]` `xiZeroCopyReflectEquiv` sends `Re(q)` to `1-Re(q)`, so the signed coordinate should be
  reflection-odd even though its raw physical multipliers need not agree.
- `[CORPUS]` HC87 proves a doubled charge-conjugate representation survives the complete scalar
  modular-superselection certificate.
- `[CORPUS]` `HTGeometry.ReflectedOrbitCharge` proves general reflection charge-doubling laws, but
  does not specialize them to the actual nonlinear HB chiral source or classify raw-amplitude
  coherent cancellation.
- `[CORPUS NEGATIVE]` mandatory searches found no theorem giving the exact reflected raw-amplitude
  factorization, all-weight cancellation criterion, explicit nonzero physical cross-weights, or
  two-bright-channel cancellation at every off-line Xi copy.

## Conjecture HC88-A: reflection-odd calibrated Ward coordinate

For every nonzero Einstein seed and every Xi divisor copy, prove

`calibrated(A,Rq) = -calibrated(A,q)`.

This must be equality in `ℂ`, not only opposite real parts or equality of norms.

## Conjecture HC88-B: exact coherent-cancellation classification

Define the reflected-pair coherent return

`P(a,b;A,q) = a Raw(A,q) + b Raw(A,Rq)`.

Prove the exact factorization

`P = (a M(A,q) - b M(A,Rq)) D(q)`.

At every off-line copy, classify

`P = 0 ↔ a M(A,q) = b M(A,Rq)`.

Thus reflected-pair cancellation fixes only a ratio of detector/channel weights and does not force
the signed Ward charge to vanish.

## Conjecture HC88-C: two bright channels cancel with nonzero weights

Choose `a=M(A,Rq)` and `b=M(A,q)`. Prove their coherent return is zero for every copy. For nonzero
seed and an off-line copy, prove simultaneously that both weights and both raw amplitudes are
nonzero. Package the universal existence of such nonzero cancelling weights as a closed theorem
with no external premise.

## Paper proof

Calibration identifies the chiral coordinate with `D(q)=1-2 Re(q)`. Functional-equation reflection
sends `Re(q)` to `1-Re(q)`, hence `D(Rq)=-D(q)`. Applying the raw factorization at `q` and `Rq`
gives

`a M(q)D(q)+b M(Rq)D(Rq)=(aM(q)-bM(Rq))D(q)`.

Off line, `D(q)≠0`, so cancellation is equivalent to equality of the weighted multipliers. The
cross-choice `(M(Rq),M(q))` cancels by commutativity. Nonzero seed makes both multipliers nonzero;
the corpus pointwise-darkness iff-line theorem makes both reflected raw channels nonzero off line.

## Hostile checks

- Use actual BM nonlinear source projections and their actual corpus multipliers.
- Prove exact complex-amplitude equalities; intensity or norm identities are insufficient.
- Prove cancellation of two individually nonzero channels off line, not a zero-plus-zero wall case.
- Do not claim physical detectors must use the constructed weights. Conclusion is logical: any
  producer asserting only existence of coherent reflected-pair cancellation is too weak.
- Keep copywise darkness distinct: corpus theorem that it is RH-strength remains valid.
- No RH hypothesis, computation, bound optimization, new axiom, `sorry`, or `admit`.

## Expected route impact

If proved, HC88 kills reflected-pair/global phase-sensitive Ward conservation as the missing
producer. Functional-equation charge conjugation supplies exact cancellation of two bright
off-line channels. Only a source law that fixes channel weights independently of the divisor and
prevents cross-weighting—or enforces copywise darkness before reflection aggregation—can carry RH.
This sharpens the remaining HB/FZZ-P/PW-B/RBH burden from “derive a Ward identity” to a local,
source-faithful no-cancellation/weight-selection theorem.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Ward,
  [*An Identity in Quantum Electrodynamics*](https://doi.org/10.1103/PhysRev.78.182), gives the
  original QED identity, not this theta-Xi reflected-pair amplitude classification.
- `[LITERATURE]` Takahashi,
  [*On the Generalized Ward Identity*](https://doi.org/10.1007/BF02832514), derives the generalized
  identity from current conservation, without the arithmetic reflection orbit or physical
  multiplier cross-weighting here.
- `[LITERATURE]` Furry,
  [*A Symmetry Theorem in the Positron Theory*](https://doi.org/10.1103/PhysRev.51.125), proves
  charge-conjugation cancellations in positron theory, not the exact Xi/Hawking bright-pair
  cancellation and RH-bearing copywise distinction.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining actual nonlinear theta-Hawking multipliers, functional-equation reflection, complete
  coherent-weight classification, and off-line two-bright-channel cancellation. This is a bounded
  audit, not an exhaustive literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveReflectedPairCancellationNoGo`.

- The signed Deninger Ward charge and calibrated actual BM chiral amplitude are proved exactly odd
  under functional-equation reflection.
- `hbXiPhaseSensitiveReflectedPairCoherentReturn_eq` factors every raw two-channel coherent return
  into a relative-weight defect times the signed charge.
- Off line, `hbXiPhaseSensitiveReflectedPairCoherentReturn_eq_zero_iff_weights` classifies all
  cancellations exactly by equality of the weighted physical multipliers.
- Opposite-channel multiplier cross-weights cancel every reflected pair identically.
- `exists_nonzero_crossWeights_cancel_two_bright_reflected_channels` proves the hostile case: for
  every nonzero seed and off-line copy, both weights and both actual raw BM channels are nonzero,
  yet their coherent return is zero.
- The closed theorem `hbXiPhaseSensitiveReflectedPairBrightCancellation` makes this universal for
  the canonical nonzero seed.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveReflectedPairCancellationNoGo`
passed all 12,004 jobs. Representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC88 finding. Module is wired into the `GaloisForLFunctions.RHTower` umbrella without running a
full umbrella build.

## Open core after HC88

Reflection-pair and global phase-sensitive Ward conservation are dead as standalone producers:
two bright off-line source channels admit exact nonzero coherent cancellation. Remaining burden is
strictly local and source-faithful: prove that physical dynamics fixes channel weights independently
of each divisor in a way incompatible with the classified cross-weight ratio, or prove copywise
chiral darkness directly. Hardest next audit is whether the corpus source-FE cocycle itself fixes
the reflected weight ratio; if it instead realizes the cancelling ratio, retire source-fixed weight
selection too.
