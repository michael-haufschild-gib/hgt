# Route-P geometric KL--Burnol holonomy virial

- **ID:** `P-G55`
- **Stage:** `1-in-progress`
- **Type:** exact source-information/co-Poisson identification / producer diagnostic
- **Status:** `[PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-mobius-prime-cell-parity-fibre-chirality-no-go.md`
- **Corpus weld:** `hedenmalm-gamma-sewn-burnol-holonomy-mass-shell.md`

## Conjecture

P-G53's geometric-valuation KL chirality and normalized Burnol co-Poisson holonomy may be two
forms of one source quantity.  Put

```text
V(u) = u cosh(u) - sinh(u).
```

For `c<0`, `|s|<-c`, conjecture the exact prime-power expansion

```text
chi_geo(c,s) = sum_(k>=1) 4 exp(kc)/k V(ks).             (P-G55a)
```

At physical prime center `c=-log p`, `s=2t log p`, set

```text
H_(p,k)(t) = 2 sinh(2kt log p).
```

Then `t H' - H = 2V(2kt log p)`, so `(P-G55a)` should become a positive weighted sum of
renormalized scale derivatives of actual prime-power holonomies.

## Hostile novelty boundary

Already present:

- P-G53 geometric KL chirality, parity split, and strict orientation;
- normalized Burnol co-Poisson holonomy on an actual zeta-zero fibre;
- Route N/R holonomy mass shell;
- Wold/Gauss virial with profile `u sinh u`.

New delta is exact full prime-power information virial `u cosh u-sinh u`, its weighted sum to the
geometric KL chirality, and equality of every physical prime-power clock with actual normalized
Burnol holonomy.  This is not another hyperbolic rewrite of the mass shell.

## Result

Lean proves `(P-G55a)` as `HasSum`.  It also proves

```text
t H_(p,k)'(t) - H_(p,k)(t) = 2 V(2kt log p),              (P-G55b)

chi_geo(-log p, 2t log p)
 = sum_(k>=1) 2 p^(-k)/k (t H_(p,k)'(t)-H_(p,k)(t)).      (P-G55c)
```

For `t>0`, every term `tH'-H` is strictly positive.  If `w` is an actual right-half zeta zero,
`t=Re(w)-1/2`, and `r=p^k`, Lean proves

```text
BurnolNormalizedHolonomy(w,r) = H_(p,k)(t).               (P-G55d)
```

Thus P-G53 information chirality is positive dilation-by-dilation virial of literal co-Poisson
quotient transport.  KL, Sonin/Burnol holonomy, and Julia displacement cannot be combined as
independent positive pressures: they count same horizontal mode.

## Conjecture loop verdict

### Conjecture P-G55.A

Add KL chirality to Burnol holonomy energy to obtain stronger completed-source coercivity.

**Killed.** `(P-G55c)` identifies KL chirality as weighted scale virial of that holonomy itself.
Adding both double-counts one displacement and supplies no opposite source sign.

### Strongest positive survivor

Missing producer is an unconditional source passivity/order law for actual co-Poisson quotient
transport.  Such a law must act before positive information completion and must force all
prime-power scale virials to vanish.  Fixed metric, moving connection, and positive KL aggregation
cannot supply it.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRoutePGeometricKLBurnolHolonomyVirial.lean`

Headline declarations:

- `sourceHorizontalGeometricKLPrimePowerTerm_eq_virial`;
- `hasSum_sourceHorizontalGeometricKLHolonomyVirial`;
- `sourceHorizontalPrimePowerHolonomy_scaleVirial`;
- `sourceHorizontalPrimePowerHolonomy_scaleVirial_pos`;
- `hasSum_sourceHorizontalPrimeGeometricKL_scaleVirial`;
- `burnolCoPoissonNormalizedHolonomy_primePower_eq_sourceHorizontal`.

## Gate

- [x] exact geometric KL prime-power expansion
- [x] exact holonomy scale-virial identity
- [x] strict off-wall term positivity
- [x] actual Burnol prime-power zero-fibre weld
- [ ] unconditional quotient passivity/order producer
- [ ] final module build, lint, axiom audit

## Honest boundary

P-G55 is not RH.  It proves representation and strict sign conditional on off-wall displacement;
it does not prove a source law of the opposite sign or exclude actual right-half zeros.

## Next hard gate

Audit full dyadic valuation tower.  Either find exact sign reversal under Gamma/co-Poisson action,
or prove coefficientwise that alternating dyadic Gamma primitives collapse to one positive virial
unit at every prime-power clock.  In latter case, pivot from dyadic scalarization to noncommutative
source order before quotient evaluation.
