# SC rigged prime form: global radical and one-square classification

- **ID:** SC-RIGGED-GLOBAL-INDEX
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` route SC, `LAND ORIENT COMP`
- **Statement:** On every off-wall left fibre, the all-prime rigged Witt form has radical exactly the vectors whose real coordinates vanish on every prime axis and has exactly one negative square modulo that radical; reflection gives exactly one positive square on every right fibre.

## Goal

Replace finite prime-packet inertia data by a global classification of the literal infinite
prime--Gamma form.  This determines the only nondegenerate quotient available to an SC Xi landing:
one Pontryagin channel on the left, one anti-Pontryagin channel on the right, and no hidden
coefficient radical beyond the invisible prime-axis quadratures.  It does not assume RH, a zero
location, a finite measure, positivity, or an operator intertwiner.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `preDivisorRiggedPrimeWittPairing_globalIndexClassification`, leaf `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

**[PROVED HERE]**

Write the left-oriented quadratic value as

`Q_s(a) = D_s(a) - L_s(a)^2`,

where `D_s(a)` is the sum of the nonnegative weighted prime-coordinate squares and `L_s` is the
single shared-reservoir functional.

1. `D_s(a) ≥ 0` termwise.  Hence `Q_s + L_s^2 = D_s ≥ 0`, so two independent negative directions
   are impossible: a nonzero linear combination in the kernel of `L_s` would have nonnegative
   quadratic value.
2. Any two distinct prime deltas give the exact finite shared-reservoir block of inertia `(1,1,0)`.
   Thus one negative square exists and the upper bound is sharp.
3. If `a` lies in the global radical, pairing with each prime delta gives
   `w_p Re(a_p) = L_s(a) sqrt(w_p)`.  Off wall, `w_p > 0`, so every diagonal summand equals
   `L_s(a)^2`.  Absolute summability over infinitely many primes forces `L_s(a)=0`, hence every
   real prime-axis coordinate vanishes.  The converse is immediate termwise.
4. Critical-line reflection negates the form, exchanging positive and negative classifications.

The candidate is global: quantification is over arbitrary source vectors, not selected finite
prime packets.  The exact radical computation is needed because index-one statements with an
uncontrolled infinite radical cannot exclude spectral quartets.

## Hostile conjecture loop

- **C1 — raw Bockstein form itself is an Xi determinant:** **FALSIFIED.** Its weights depend only on
  `Re(s)` and vanish on the full critical wall, so it loses Xi height and multiplicity.
- **C2 — rank-two pinned Green inertia alone excludes an off-line Xi quartet:** **FALSIFIED.** The
  corpus cross-polarized Green law shows the relevant upper-half pair need not be boundary-orthogonal;
  exact mixed inertia therefore permits the quartet.
- **C3 — global radical-plus-index classification of the all-prime rigged form:** **SURVIVES.** The
  diagonal-minus-one-square normal form proves the index bound, and prime-axis summability removes
  the otherwise fatal hidden radical.

## Novelty audit

- **Internal corpus:** searches for `rank one negative perturbation`, `shared reservoir radical`,
  `all prime Witt form radical`, and `Pontryagin index one quadratic form` find finite reservoir
  inertia and generic finite-dimensional index lemmas, but no global radical or exact one-square
  classification for `preDivisorRiggedPrimeWittPairing`.
- **External literature:** Pontryagin/Krein theory treats finite negative index and invariant
  subspaces abstractly.  The exact prime--Gamma weight, Deninger Köthe carrier, reflection-odd
  phase form, and its radical classification were not found.  Parent theory is prior art; exact
  arithmetic application remains `[NOVELTY UNVERIFIED]` pending expert search.

## Door passport

- **Door 1:** rank-one negative perturbation of a positive all-prime diagonal.
- **Door 2:** exact source quotient and reflected inertia, before Xi selection.
- **Door 3:** no numerical constant, truncation, post-selected zero, or assumed spectral reality.
- **Door 4:** surviving burden becomes an explicit radical-separating Xi intertwiner into this
  fixed quotient; a degenerate or purely positive completion cannot substitute for it.

## Log

- 2026-08-28 — created directly in 1-in-progress after corpus and literature audit.
- 2026-08-28 — paper proof closed: rank-one kernel combination gives global index bound; two
  prime deltas give sharpness; infinite-prime summability gives exact radical.
- 2026-08-28 — formalized in
  `GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinGlobalIndex`; leaf build passed and
  capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
