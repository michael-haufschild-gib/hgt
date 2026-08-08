# Coordinate cutoff primitive flux identity

- **ID:** `suzuki-coordinate-cutoff-primitive-flux-identity`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-coordinate-cutoff-primitive-flux-identity.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/CoordinateCutoffPrimitiveFlux.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialLatticeWeight.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CoordinateCutoffCovariance.lean`

## Formal content

```text
fluxCommutatorProfile C M F L = C (M L (F L)) - M L (C (F L))      -- [C, M] F
transportApply C L D          = (2 L) • D + C D                    -- (2L I + C) applied to D
```

| Card | Lean |
|---|---|
| `(6)` `∂_L([C,M]F) = C M' F + C M F' − M' C F − M C F'` | `hasDerivAt_fluxCommutatorProfile` |
| `(2)` the primitive flux identity | `primitive_flux_identity` |
| `(3)` the same with a zero-order operator | `primitive_flux_identity_with_zeroOrder` |
| `(5)` the primitive source is the commutator of `R − B` | `fluxCommutatorProfile_sub` |
| §3 a commuting cutoff has no primitive source | `fluxCommutatorProfile_eq_zero_of_commute` |
| §3 the scalar cutoff is the degenerate case | `fluxCommutatorProfile_scalar` |
| `(15)` the exact shift commutator | `valuationCutoffCommutator_apply` (covariance module) |
| `(18)` weighted event-block summability | `summable_strip_weighted_eventSource` |
| `(14)`, `(17)` the weight and the event-time bound | `latticeEll1`, `summable_exp_neg_latticeEll1` |

## What the identity actually says

The card's point is that the cutoff defect must be kept as `∂_L([C,M]F)`, not expanded into a term
carrying `F'`.  `primitive_flux_identity` is exactly that statement: the left side is the defect of
commuting `M` past `(2L I + C) ∂_L`, and the right side has the derivative sitting on the
commutator profile and nothing else of first order.  In the Lean statement the derivative data
`Md` and `Fd` are supplied as parameters, so the identity is visibly a linear-algebra identity in
`M L`, `Md`, `C`, `F L`, `Fd` — closed by `module` after expanding additivity and homogeneity.
That is the content: no cancellation depends on any property of `C` beyond linearity, and no second
derivative appears.

`hasDerivAt_fluxCommutatorProfile` is the companion analytic statement, that the right-hand side's
first term really is the derivative of the commutator profile.  It needs `M` differentiable as an
operator-valued map and `F` differentiable, both object regularity.

`fluxCommutatorProfile_scalar` records why the predecessor card's scalar case is not a special case
of interest: a scalar cutoff is a multiple of the identity, so its commutator with everything
vanishes and there is no primitive source at all.  The whole phenomenon is created by coordinate
dependence.

## The finite-recurrence bound

`summable_strip_weighted_eventSource` is `(18)`: given the exponential valuation weight `(14)`, the
block bound `(16)`, and the linear event-time bound `(17)`, the strip-weighted event source is
square summable as soon as `kappa > sigma * Ca`.  The arithmetic is exactly the card's — the strip
gain `exp(2 sigma Ca (1 + |ν|₁))` is beaten by `exp(-2 kappa |ν|₁)` — and the summability it
reduces to, `∑_{ν ∈ ℤ^d} exp(-c |ν|₁) < ∞`, is proved from scratch
(`summable_exp_neg_abs_int`, `summable_exp_neg_latticeEll1`) by induction on the dimension through
`Fin.consEquiv`; mathlib carries no lattice-weight summability lemma.

## Hypotheses

A real normed space, a bounded operator `C` (and `Z`), an operator-valued multiplier `M`
differentiable at the point, and a differentiable profile `F`.  The identity is stated over `ℝ`
rather than `ℂ`, which is a generalization: a complex-linear operator is in particular real-linear,
and no step uses complex scalars.  For `(18)`, the card's `(14)`, `(16)`, `(17)` as stated.  No
hypothesis is a theorem proved elsewhere in the corpus.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.

## Open boundary

Equations `(19)`–`(23)` of §4 chain the identity to two inputs owned by other cards — the Gamma
cutoff-commutator tail bound `(19)` and the undifferentiated paired fixed-window solution `(20)` —
and are consequences of those, not of this card.  Section 5's three further obligations are the
card's own stated frontier.
