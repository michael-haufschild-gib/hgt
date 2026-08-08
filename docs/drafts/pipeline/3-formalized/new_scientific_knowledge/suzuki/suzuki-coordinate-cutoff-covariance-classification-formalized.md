# Coordinate cutoff covariance classification

- **ID:** `suzuki-coordinate-cutoff-covariance-classification`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-coordinate-cutoff-covariance-classification.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/CoordinateCutoffCovariance.lean`

## Formal content

```text
valuationShift alpha s Z nu L        = alpha s nu * Z (nu + s) L
coordinateMultiplier chi Z nu L      = chi nu L * Z nu L
valuationCutoffCommutator chi alpha s Z = M_chi S_s Z - S_s M_chi Z
```

| Card | Lean |
|---|---|
| `(1)`, `(2)` the two operator families | `valuationShift`, `coordinateMultiplier` |
| `(3)` the commutator identity | `valuationCutoffCommutator_apply` |
| `(4)` commutator vanishing ⟹ edge-constant cutoff | `cutoff_eq_of_commutator_vanishing` |
| `(4)` converse | `commutator_eq_zero_of_cutoff_eq` |
| `(4)` `Sigma` generates ⟹ one scalar cutoff | `cutoff_eq_zero_of_generating` |
| `(5)` unbounded terminal times admit no adapted scalar cutoff | `no_adapted_scalar_cutoff` |
| `(6)` no zero-order `L²` bound | `sq_norm_valuationCutoffCommutator_twisted_ge`, `no_zero_order_bound` |

Supporting declarations: `linearTestProfile`, `linearTestProfile_self`,
`linearTestProfile_eq_zero`, `differentiable_linearTestProfile`, `deriv_linearTestProfile_self`,
`twistedBump`, `twistedBumpDeriv`, `hasDerivAt_twistedBump`, `normSq_twistedBumpDeriv`,
`norm_twistedBump`.

## Three points the formalization sharpens

**The test profile has to be a derivative.**  The card's hypothesis is that the commutator kills
`∂_L F` for smooth finitely supported `F`, not that it kills every profile — the two differ, since
derivatives of compactly supported profiles are constrained.  `cutoff_eq_of_commutator_vanishing`
takes the hypothesis in the card's form and instantiates it with `F` supported at the single
coordinate `ν + s` and equal to `L` there, whose derivative is `1`.  That is the minimal witness.

**"`Sigma` generates" is used as a subgroup argument, not a path argument.**  The paper
concatenates generator edges from `0` to `ν`.  The Lean proof forms the subgroup
`{g | ∀ μ, χ (μ + g) = χ μ}`, checks it contains `Sigma`, and concludes it is everything.  The
inverse-closure step — that invariance under `+g` gives invariance under `−g` — is what a path
argument leaves implicit.

**`(6)` needs no Minkowski inequality.**  Taking the bump `φ` *real* makes the modulus square of
the twisted derivative split exactly: `|φ' + iNφ|² = φ'² + N²φ²`, so the frequency gain is visible
termwise and the reverse triangle inequality in `L²` is never used.  `norm_twistedBump` shows the
twist leaves the profile's mass alone, so the ratio grows like `δ²N²` and no constant `C` survives.

## Hypotheses

`G` is an additive commutative group (the card's `ℤ^d` is an instance), `α s ν ≠ 0` on the edge in
question, `Sigma` generates, and for `(6)` a real bump with positive mass, a lower bound `δ` on the
cutoff increment where the bump is nonzero, and integrability of the two profiles.  All are the
card's own data.  No hypothesis is a theorem proved elsewhere in the corpus.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.

## Open boundary

The card's closing remark — that Suzuki's two-ended valuation orbit has event families
`tau_nu = [-log|ell(nu)|]_+` and `tau'_nu = [-log|2a - ell(nu)|]_+` whose unboundedness triggers
the theorem — is a statement about that concrete orbit and belongs to the orbit cards; the theorem
formalized here is the classification it feeds.
