# CCM Rayleigh transfer collapses to the cofinal spectral-floor criterion

- **ID:** `ccm-rayleigh-transfer-collapses-to-spectral-floor`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF BY ITSELF]`
- **Parent theories:** min--max, the Rayleigh-excess identity, the fixed-depth constrained-prolate
  ladder, and the cofinal Weil-floor criterion
- **Statement:** Once two fixed-depth CCM trial vectors have Rayleigh values tending to zero, the
  determinant lane's required `O(lambda^(-1))` Rayleigh-excess/gap estimate forces the true lowest
  even Weil eigenvalue to tend to zero. Hence that estimate already proves RH through the cofinal
  spectral-floor criterion; the determinant contributes no independent final implication.

## Abstract collapse theorem

Let `A_lambda` be self-adjoint on a finite or compact-resolvent even sector, with its first two
eigenvalues

```text
epsilon_0(lambda)<epsilon_1(lambda),
Gap_lambda=epsilon_1(lambda)-epsilon_0(lambda)>0.                (1)
```

Let `g_lambda` be normalized and put

```text
r_lambda=<A_lambda g_lambda,g_lambda>,
d_lambda=r_lambda-epsilon_0(lambda)>=0.                          (2)
```

Assume

```text
r_lambda->0,
epsilon_1(lambda)->0,                                           (3)

d_lambda/Gap_lambda=O(lambda^(-1)).                              (4)
```

`[PROVED HERE]` Then

```text
epsilon_0(lambda)->0.                                           (5)
```

### Proof

Choose `C` with `d_lambda<=C*Gap_lambda/lambda`. Since

```text
Gap_lambda
 =epsilon_1(lambda)-r_lambda+d_lambda,                           (6)
```

for `lambda>2C`,

```text
d_lambda
 <=C/lambda*(|epsilon_1(lambda)-r_lambda|+d_lambda),

d_lambda<=2C/lambda*|epsilon_1(lambda)-r_lambda|.                (7)
```

Equations `(3)` and `(7)` give `d_lambda->0`; then `(2)` gives `(5)`.

## Why the second level tends to zero in the CCM lane

The fixed-depth constrained-prolate ladder supplies two orthonormal even contrasts

```text
g_(0,lambda), g_(1,lambda),                                     (8)
```

whose exterior deficits satisfy

```text
d_(1,lambda) asymptotic to C*lambda^8*d_(0,lambda),
d_(j,lambda)*lambda^N->0 for every fixed N.                     (9)
```

The exact radial prime and countable log-chirp theorems apply at every fixed depth. Consequently,
on the two-dimensional subspace `V_lambda=span{g_(0,lambda),g_(1,lambda)}`,

```text
sup_(v in V_lambda; ||v||=1)|<A_lambda v,v>|
 =O(d_(1,lambda)log lambda)->0.                                 (10)
```

The off-diagonal entry follows from the same fixed-depth phase-preserving expansion, or by
polarization after applying the uniform two-source form bound. Min--max now gives

```text
epsilon_1(lambda)
 <=sup_(v in V_lambda; ||v||=1)<A_lambda v,v> ->0.               (11)
```

The first contrast has the explicit Rayleigh law

```text
r_lambda=O(d_(0,lambda)log lambda)->0.                           (12)
```

Thus the CCM hypotheses `(3)` are proved, and any successful determinant-transfer estimate `(4)`
forces `(5)`.

## Direct RH consequence

The theorem `ccm-cofinal-weil-spectral-floor-criterion.md` proves that a cofinal sequence with

```text
epsilon_0(lambda_j)->0                                          (13)
```

implies the full Weil criterion and RH. Therefore the implication chain is actually

```text
CCM Rayleigh excess / true gap =O(lambda^(-1))
  -> cofinal true Weil floor tends to zero
  -> RH.                                                        (14)
```

The characteristic determinants, their real finite zeros, and their locally uniform convergence
to `Xi` are not needed after the first arrow.

## Consequence for proposed lower bounds

In particular, the suggested bound

```text
epsilon_0(lambda)>=-C*d_1(lambda)                               (15)
```

already gives `(13)` because

```text
-C*d_1(lambda)<=epsilon_0(lambda)<=r_lambda->0.                 (16)
```

Allowing a negative floor does not make `(15)` weaker than the cofinal Weil criterion when the
negative allowance itself tends to zero. It is an RH-sufficient theorem, not preliminary spectral
engineering.

## Positive route verdict

The determinant implementation is retired as an independent last mile. The live CCM statement is
the shorter one:

```text
prove epsilon_0(lambda_j)->0 on one cofinal aperture sequence.   (17)
```

This is not a declaration that the CCM route is impossible. It identifies what a successful CCM
proof must be: a direct cofinal Weil-floor theorem. Finite real-zero determinants may still be
constructed, but they cannot reduce the remaining RH burden.

## Novelty and significance verdict

The collapse is elementary min--max algebra once the two vanishing trial levels are available. It
is a route bridge, not new scientific knowledge.

## Lean status

**Superseded, 2026-08-03.**  The abstract collapse `(1)`--`(7)` and the composition `(14)` with the
cofinal criterion are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCM/CCMCofinalFloorCriterion.lean`.

- **`tendsto_ground_zero_of_excess_gap_ratio`** — equations `(1)`--`(7)`: from `d = r - eps_0 ≥ 0`,
  an eventual bound `d ≤ C * (eps_1 - eps_0) / lambda`, and `r → 0`, `eps_1 → 0`, it concludes
  `eps_0 → 0`.  The proof is the card's: rewrite the gap as `(eps_1 - r) + d` so that for
  `lambda > 2C` half the excess is absorbed into itself, leaving
  `d ≤ 2 C |eps_1 - r| / lambda`, which tends to zero because the numerator tends to zero and
  `lambda → ∞`; then `eps_0 = r - d`.
  Note the hypothesis is stated as the eventual inequality itself, so no `Gap > 0` assumption is
  needed — the absorption step supplies it.
- **`nonneg_of_excess_gap_ratio`** — the chain `(14)`: an `O(1/lambda)` excess-to-gap estimate on the
  floors of a nested trial family already forces nonnegativity of the energy on every trial domain.
  The determinant lane contributes nothing after this arrow, which is the card's verdict.
- The cofinal criterion consumed here is `nonneg_of_rayleighFloor_tendsto_zero`, and the floor layer
  is `CCMNestedFloorNoEvacuation.lean`; the objection that the tree had "no min--max/eigenvalue
  interface" is answered by working with the variational floor `rayleighFloor` directly, which is
  what the card's `epsilon_0` is.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized: the CCM-specific inputs `(8)`--`(12)` — the fixed-depth constrained-prolate ladder,
its exterior deficit asymptotics, and the two-dimensional min--max bound `(10)`--`(11)`.  Those are
imported analytic facts about the prolate family, not theorems of the collapse; the collapse is
stated for arbitrary real level functions and applies to them verbatim once they are available.

## Gates

- [x] abstract Rayleigh-to-floor collapse proved
- [x] two fixed-depth CCM trial levels shown to vanish
- [x] cofinal spectral-floor criterion connected
- [x] determinant last mile shown redundant
- [x] Lean: abstract collapse `(1)`--`(7)` unconditional
- [x] Lean: composed chain `(14)` to energy nonnegativity unconditional
- [ ] prove the direct cofinal true-Weil floor theorem
