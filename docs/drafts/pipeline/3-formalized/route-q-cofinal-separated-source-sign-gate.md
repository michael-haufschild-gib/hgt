# Route Q cofinal separated-source sign gate

- **ID:** `route-q-cofinal-separated-source-sign-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM / strict weakening of open producer
- **Routes:** Q primary; U diagonal-sign comparison
- **Source:** `shift-one-cassini-resolvent-source-law.md`, separated finite-source endpoint

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

The corpus asks for one separated finite prime--Gamma packet reconstruction whose source energy is
eventually nonnegative.  Is a nonnegative tail genuinely necessary, and can approximation choice
evade the negative orientation chamber if RH is false?

## Theorem Q-COFINAL-SIGN

Let `P_n` be pairwise-conjugate-separated finite continued-Cauchy prime--Gamma packets, and let
`v(P_n)` and `E(P_n)` denote their Xi-divisor evaluation vector and exact source energy.  If

```text
v(P_n) -> xiHurwitzOrientationVector,                      (1)
```

then automatically

```text
E(P_n) -> -xiHurwitzOrientationEnergy.                     (2)
```

If RH is false, the orientation energy is strictly positive and every sequence satisfying `(1)`
obeys the uniform eventual trap

```text
E(P_n) < -xiHurwitzOrientationEnergy / 2 < 0               (3)
```

for all sufficiently large `n`.

Define cofinal nonnegativity by

```text
for every N, there exists n >= N with E(P_n) >= 0.         (4)
```

Then

```text
there exists a separated reconstruction satisfying (1),(4)
  <-> RiemannHypothesis.                                  (5)
```

Thus Route Q does not need eventual nonnegativity.  Arbitrarily late returns to the nonnegative
finite-source chamber suffice.

## Heavy conjecture loop

### Q-CS-1 — a nonnegative tail is necessary

**Conjecture.** The limit-to-orientation argument needs `E(P_n)>=0` for every sufficiently large
index.

**Attack.** Under false RH, convergence itself produces an eventually strict negative gap `(3)`.
Any single nonnegative packet beyond that threshold contradicts false RH.  Therefore only
arbitrarily late nonnegative indices are needed.

**Verdict:** false.  Replaced by cofinal recurrence `(4)` and proved in Lean.

### Q-CS-2 — approximation choice can hide false-RH negativity

**Conjecture.** A different separated packet approximation to the same orientation vector might
retain nonnegative energies even if another approximation becomes negative.

**Attack.** Exact source-energy reconstruction is pointwise:

```text
E(P) = xiWeilHilbertQuadratic(v(P)).
```

The Hilbert quadratic is continuous.  Hence every evaluation-convergent sequence has same limit
`-orientationEnergy`, independently of how packets, coefficients, or separated poles were chosen.

**Verdict:** false.  Under false RH every reconstruction enters same definite negative basin.

### Q-CS-3 — cofinal source sign is enough

**Conjecture.** One unconditionally reconstructed source-first section with infinitely many
nonnegative packet energies proves RH.

**Proof.** Combine cofinal nonnegative index with eventual negative trap under assumed false RH.
Conversely RH supplies existing eventually nonnegative reconstruction, hence cofinal one.

**Verdict:** proved on paper and in Lean.

## Dependency-closed proof

For every separated packet, corpus theorem
`XiSeparatedContinuedCauchyPacket.sourceEnergy_eq_hilbertQuadratic` gives

```text
E(P_n) = Q_Weil(v(P_n)).
```

Continuity of `Q_Weil` and `(1)` imply

```text
E(P_n) -> Q_Weil(xiHurwitzOrientationVector)
       = -xiHurwitzOrientationEnergy,
```

which is `(2)`.  If RH is false, the proved equivalence

```text
RiemannHypothesis <-> xiHurwitzOrientationEnergy = 0
```

and unconditional nonnegativity of orientation energy give strict positivity.  Since

```text
-E < -E/2,
```

convergence yields `(3)`.  Given `(4)`, choose a nonnegative index beyond threshold in `(3)`, a
contradiction.  Hence `(1),(4)` imply RH.

For reverse implication in `(5)`, the corpus already constructs a separated reconstruction whose
energy is eventually nonnegative under RH.  Every eventual subset of `atTop` contains an index
beyond each prescribed `N`; selecting `max N N_0` proves `(4)`.  No unproved premise enters proof.

## Higher universal principle

**Continuous quadratic targets erase approximation choice but preserve recurrence tests.**  Once
finite source packets are identified exactly with one continuous target quadratic, every
reconstruction of same target vector has same asymptotic sign.  Choice of approximants cannot
repair orientation.  Conversely a hard tail-sign theorem is unnecessary: recurrent visits to
opposite closed chamber already determine sign of limit.

This is relevant to Route U's moving-degree problem.  When a continuous source functional has a
strict negative false-RH limit, seek cofinal sign recurrence rather than uniform eventual sign.
That reduction is lawful only after proving exact source-energy continuity, as Route Q does here.

## Significance and positive survivor

Previous exact Q endpoint demanded

```text
exists P, eventually E(P_n) >= 0.
```

New exact endpoint demands strictly less:

```text
exists P, for every N some n>=N has E(P_n) >= 0.
```

Next producer may exploit sparse arithmetic subsequences, favorable prime-separation scales, or
recurring boundary packets.  It no longer needs control of every later packet.  Still required:
the chosen section must be source-defined and converge to orientation vector; target-side choice
alone cannot supply sign.

## External novelty audit

- Classical components are continuity of a quadratic form and sign persistence near a strict
  negative limit.
- Weil-form literature studies positivity on test families and truncated forms; nearby examples
  include the spectral-triple treatment of finite Weil forms
  <https://content.ems.press/assets/public/full-texts/serials/lem/69/1/11033001/online/10.4171-lem-1049.pdf>
  and recent finite Guinand--Weil source dictionaries <https://arxiv.org/abs/2607.02828>.
- Targeted searches on 2026-08-16 found no external statement combining the Xi--Hurwitz
  orientation vector, pairwise-separated finite continued-Cauchy prime--Gamma packets, universal
  false-RH negative trapping, and the cofinal-sign equivalence `(5)`.  Novelty remains unverified
  and is not claimed.

## Gates

- [x] 0 -> 1: exact weakening, hostile approximation-choice conjecture, positive survivor
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Module:
`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationCofinalSourceSignGate.lean`.

Capstones:

- `eventually_separatedSourceEnergy_lt_neg_half_orientationEnergy_of_not_rh`;
- `xiHurwitzSeparatedSourceSequenceCofinalNonnegative_iff_riemannHypothesis`.

The equivalence theorem is premise-free.  Direct `lake env lean` check and exact leaf `lake build`
succeeded.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  Forbidden
declaration scan is clean.  Module is imported by `RHTower.lean`; no umbrella or full-project build
was run.

## Log

- 2026-08-16 — Existing eventual-sign endpoint attacked.
- 2026-08-16 — Universal false-RH negative basin proved in Lean scratch.
- 2026-08-16 — Producer weakened from eventual sign to cofinal sign recurrence.
- 2026-08-16 — Module promoted, exact leaf built, axiom-audited, and umbrella import wired without
  umbrella build.
