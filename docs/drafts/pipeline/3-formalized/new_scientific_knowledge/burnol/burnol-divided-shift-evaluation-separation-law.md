# Burnol divided shifts are quantitatively separated from zero evaluators

- **ID:** `burnol-divided-shift-evaluation-separation-law`
- **Stage:** 3-formalized
- **Formalized companion:** `burnol-divided-shift-evaluation-separation-law-formalized.md`
- **Type:** THEOREM (paper)
- **Source:** Frankenstein splice of the corpus-owned co-Poisson zero-annihilator theorem and
  strict accretivity of the critical-line Cauchy multiplier
- **Statement:** At every right-half-strip zeta zero, no nonzero closed co-Poisson source can have
  its Burnol divided shift equal the completed-Mellin evaluation vector; more strongly, their
  difference retains the full source projection of the divided shift and obeys the existing sharp
  accretive leakage floor.

## Goal

Audit the tempting cross-route identification of a Hedenmalm/Green source resolvent with Burnol's
zero evaluator.  The result kills that identification unconditionally and identifies the exact
replacement category: any viable splice needs an additional conservative boundary port whose
source component cancels the Cauchy leakage.  Direct landing inside the original co-Poisson source
space is impossible.

## Frozen theorem

Let `H` be Burnol's even physical Hilbert space, `S_b` the closed co-Poisson source space at
aperture `b > 0`, and `P_b` its orthogonal projection.  Let

```text
A_w = M_Mellin^{-1} M_{m_w} M_Mellin,
m_w(t) = 1 / (w - (1/2 + i t)),
delta = Re(w) - 1/2 > 0.
```

For `1/2 < Re(w) < 1`, `zeta(w)=0`, and the completed-Mellin evaluation vector `k_(w,b)`, every
`f in S_b` satisfies

```text
P_b k_(w,b) = 0,                                             (1)
P_b (A_w f - k_(w,b)) = P_b A_w f,                           (2)
delta ||A_w f||^2 <= ||f|| ||P_b(A_w f-k_(w,b))||.           (3)
```

Consequently, if `f != 0`, then

```text
P_b(A_w f-k_(w,b)) != 0,
A_w f != k_(w,b),
||A_w f-k_(w,b)|| >= delta ||A_w f||^2 / ||f|| > 0.          (4)
```

No RH, critical-line placement, simplicity, source-flatness, or spectral hypothesis occurs.

## Proof

Burnol's full-source zero theorem gives that `zeta(w)=0` is a co-Poisson annihilator point.  The
Riesz identity for completed Mellin evaluation then gives `k_(w,b) in S_b^perp`, hence `(1)`.
Linearity of orthogonal projection gives

```text
P_b(A_w f-k_(w,b)) = P_b A_w f-P_b k_(w,b) = P_b A_w f,
```

which is `(2)`.

The Cauchy symbol satisfies the exact Herglotz identity

```text
Re m_w(t) = delta |m_w(t)|^2.
```

After Mellin-unitary transport and orthogonal decomposition against `S_b`, this is the already
proved source-leakage inequality

```text
delta ||A_w f||^2 <= ||f|| ||P_b A_w f||.
```

Substitute `(2)` to obtain `(3)`.  Strict accretivity also proves `P_b A_w f != 0` for every
nonzero `f in S_b`; `(2)` gives both nonvanishing claims in `(4)`.  Finally, contractivity of
`P_b` gives `||P_b(A_w f-k_(w,b))|| <= ||A_w f-k_(w,b)||`; divide `(3)` by `||f|| > 0`.
`QED`

## No-go closure

- **Exact killing theorem/mechanism:** zero evaluators lie in `S_b^perp`, whereas strict
  accretivity forces every divided shift of a nonzero vector of `S_b` to have nonzero `S_b`
  projection.  Therefore a source-resolvent preimage of the zero evaluator cannot exist.
- **Strongest positive survivor:** quantitative separation `(1)`--`(4)`, not only a negated
  existence statement.
- **New insight:** Hedenmalm's first-order Green kernel and Burnol's Cauchy kernel can only be joined
  after adding a compensating boundary/source port.  Any direct same-space identification is
  mathematically forbidden.  The next legitimate conjecture must specify that port and prove a
  neutral conservative Green identity before specializing to the Xi divisor.
- **Status:** dependency-closed paper proof and exact Lean formalization in
  `GaloisForLFunctions.RHTower.BurnolDividedShiftEvaluationSeparation`.  Module-only build and
  axiom audit pass.  Stage promotion waits for the repository lint gate, currently blocked by
  unrelated newly added prolate modules missing from the `RHTower` umbrella.

## Novelty audit

Burnol's papers construct the co-Poisson subspaces, zero evaluation vectors, orthogonal quotient,
and the de Branges division property.  A targeted primary-source search found no statement of the
strict-accretive Cauchy leakage identity combined with zero-evaluator orthogonality, nor the
quantitative separation `(3)`--`(4)`.  Novelty is therefore a provisional pass as a new synthesis;
the parent ingredients are not claimed new.

Primary sources checked:

- J.-F. Burnol, *Sur certains espaces de Hilbert de fonctions entieres, lies a la transformation
  de Fourier et aux fonctions L de Dirichlet et de Riemann*, arXiv:math/0105120.
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, arXiv:math/0203120; in particular its co-Poisson orthogonal-complement theorem and
  de Branges division proposition.
- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007), 525--602.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement and attack
- [x] 1 -> 2 fully-proven: complete dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 -> 3 formalized: exact Lean projection identity, both lower bounds, and non-landing theorem
  compile, are umbrella-wired, and pass the axiom audit
- [ ] 3 -> 4 publication-ready: external mathematical audit and standalone exposition

## Log

- 2026-08-07 — frozen, proved, and passed targeted internal/primary-literature novelty audit.
- 2026-08-07 — formalized five unconditional theorems in
  `BurnolDividedShiftEvaluationSeparation.lean`; exact `lake env lean` and module-only `lake build`
  pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  Global lint is
  blocked by 17 unrelated prolate modules not yet wired into `RHTower.lean`.
- 2026-08-09 — re-verified the five theorems (clean `lake env lean`, axioms `propext`,
  `Classical.choice`, `Quot.sound`, `RHTower` umbrella import present) and promoted to stage 3.
