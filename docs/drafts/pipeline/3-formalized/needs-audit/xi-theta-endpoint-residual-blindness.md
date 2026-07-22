# Xi theta-endpoint residual blindness

- **ID:** `xi-theta-endpoint-residual-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE FIREWALL
- **Status:** `[PAPER-PROVED] [EXACT CORE LEAN-PROVED] [NEEDS NOVELTY AUDIT] [NO RH CLAIM]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiThetaEndpointResidual.lean`

## Statement

Let `Lambda_0(s)=completedRiemannZeta₀(s)` be the entire theta--Mellin completion used by the
corpus, so

```text
xi(s) = s(s-1) Lambda_0(s)/2 + 1/2.
```

Away from `s=0,1`, define the endpoint residual

```text
E(s) = Lambda_0(s) + 1/[s(s-1)].
```

Then

```text
E(s) = 2 xi(s)/[s(s-1)],

Lambda_0(s) = -1/[s(s-1)]  iff  xi(s)=0.                 (1)
```

On every fixed closed vertical strip, standard Stirling and polynomial vertical-strip bounds for
`zeta` give

```text
E(sigma+it) = exp(-pi |t|/4) |t|^O(1).                  (2)
```

Consequently `Lambda_0(sigma+it)` and the rational zero anchor `-1/[s(s-1)]` have the same full
inverse-height asymptotic expansion: their difference is smaller than every power of `1/|t|`.
No finite integration-by-parts endpoint expansion can distinguish an Xi zero from a nonzero point
in a bounded strip.  A valid zero-location argument must resolve the exponentially small residual
itself or use independent arithmetic structure.

## Proof

Equation `(1)` is a rearrangement of the defining completion identity.  Since `s(s-1)` is nonzero,
the second equivalence follows immediately.

For `(2)`, away from the two completion endpoints,

```text
xi(s)=s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)/2.
```

Uniform Stirling on a closed vertical strip contributes `exp(-pi|t|/4)` times a fixed power of
`|t|`.  Classical vertical-strip growth of `zeta` contributes only another fixed power.  Dividing
by `s(s-1)` preserves exponential decay.  Exponential decay is `O(|t|^-N)` for every fixed `N`,
which proves the all-orders blindness claim.

## Version-26 hostile audit

Yukitaka Abe's unreviewed Version 26 preprint, *A rigorous proof of the Riemann hypothesis*, tries
to obtain a high-height zero-free region from four or five integrations by parts of precisely this
theta endpoint integral.  Two independent failures occur:

1. equation (5.5) drops the factor `I(s)` when computing a tangent's horizontal intercept;
2. Section 8 again treats higher-order poles of `1/(zeta(s)g(s))` as simple residues.

Restoring the missing tangent factor turns its Section-5 condition into the exact two-circle
intersection identity.  More structurally, `(1)--(2)` show why extending the same endpoint
expansion to more orders cannot repair the proof: all algebraic orders are zero-blind.

The detailed tangent and residue corrections are recorded in
`../../5-failed/finite-offline-euler-contour-pole-order-contradiction.md`.

## Positive survivor

The exact residual `E` is the smallest possible analytic carrier of zero information left after
endpoint asymptotics.  Any future theta-integral route can be audited by one test:

```text
does the proposed source theorem control E itself at exponential scale,
or only another finite inverse-height jet?
```

Only the first can add zero-location content.  This gives a reusable, source-independent firewall
without asserting RH.

## Lean declarations

- `xiThetaEndpointResidual`
- `xiThetaEndpointResidual_eq`
- `completedRiemannZeta₀_eq_neg_inv_mul_iff_xi_eq_zero`

Direct verification:

```text
lake env lean GaloisForLFunctions/RHTower/XiThetaEndpointResidual.lean
```

## Gates

- [x] exact residual identity proved on paper
- [x] exact zero-anchor equivalence proved on paper
- [x] exact algebraic core formalized in Lean
- [x] direct module check passes
- [ ] full vertical-strip exponential estimate formalized
- [ ] novelty audit beyond the cited preprint and standard completion literature

## Log

- 2026-07-22 — exact residual isolated and formalized; all-orders endpoint-asymptotic firewall
  proved on paper; Version-26 tangent error audited.
