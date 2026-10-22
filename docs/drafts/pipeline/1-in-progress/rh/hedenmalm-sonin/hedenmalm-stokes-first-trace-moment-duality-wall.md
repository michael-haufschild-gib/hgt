# Hedenmalm Stokes first-trace moment-duality wall

- **Label:** `P-G140`
- **Route:** P
- **Parents:** `P-G139`, `GammaSewnMobiusApertureStokesSubcriticalPassiveResponse`
- **Stage:** 1-in-progress
- **Type:** heavy-conjecture loop / passivity no-go / positive-moment renormalization
- **Status:** `[PROVED IN LEAN] [POSITIVE SURVIVOR EXTRACTED] [NOT RH]`

## Universal-principle conjecture

Unconditional Stokes anti-Herglotz response and RH-bearing first-trace current are moments of same
positive atoms but at opposite ends of spectral scale.  If physical weight is `b`, Stokes gap is
`g>0`, and Euler intensity is `bg`, then one-subtracted response is

```text
R(z)=b z/(z-g).
```

Passivity/convergence uses negative moment `b/g`; first-trace coefficient at infinity is positive
moment `bg`.  Conjecture: in critical chamber `0<s≤1`, negative moment is summable but positive
moment is not.  Therefore ordinary boundary extraction from passive response cannot prove P-G139
right-source dissipativity.

## Heavy conjecture loop

### P-G140.A — exact atom moment duality

Prove `b g` is literal von Mangoldt prime-power coefficient and

```text
z(R(z)-b) = (bg) z/(z-g).
```

Thus first trace is coefficient at infinity, not response value or zero derivative.

### P-G140.B — positive-moment divergence wall

For every real `0<s≤1`, prove prime-power family `primePowerFluxTerm(s)` is not summable.  Depth-zero
prime slice already dominates positive multiple of prime harmonic series.

### P-G140.C — no ordinary passive extraction

Combine summability of `b/g` for `0<s<1` with nonsummability of `bg`.  Record exact moment-order
reversal: passive thermodynamic limit exists, while first high-frequency trace moment has no
ordinary all-prime landing.

### P-G140.D — positive survivor

Locate required counterterm.  P-G139 proves higher valuations and `D2` cancel exactly and cannot
renormalize divergent valuation-one positive moment.  Any surviving source theorem must provide a
Gamma/polar counterterm at infinity before limit, preserving anti-Herglotz sign after
renormalization.

## Non-theatre gate

Card succeeds only with exact atom algebra, full `0<s≤1` divergence proof, and explicit comparison
to existing inverse-moment summability.  Generic statements that moments differ do not count.

## Lean outcome

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmStokesFirstTraceMomentDualityWall.lean`.

Closed results:

1. Depth-zero norm is exactly
   `‖primePowerFluxTerm sigma (p,0)‖ = log(p) p^(-sigma)`.
2. For every real `sigma ≤ 1`, this norm dominates `log(2)/p`; therefore full prime-power family
   is not summable.  This strengthens proposed `0 < sigma ≤ 1` wall.
3. Exact centered atom identity
   `z(R(z)-b) = primePowerFluxTerm(s,pk) z/(z-g)` exposes first trace as positive moment `b g`.
4. Literal real family `b g` is not summable for `0 < s ≤ 1`.
5. For `0 < s < 1`, inverse moment `b/g` is summable while positive moment `b g` is not.

No zero set, RH premise, new axiom, or numerical computation enters proof.  Divergence comes from
Euler's prime harmonic theorem already in mathlib; Stokes coefficient identification is exact
source algebra.

## Positive survivor

P-G139 and this wall together force one sharply specified missing producer:

```text
sign-preserving finite-part extraction of the positive Stokes moment at spectral infinity,
with Gamma/polar counterterm inserted before the all-prime limit.
```

Ordinary passive evaluation cannot supply this coefficient: it is controlled by inverse moment.
Higher valuations cannot supply counterterm: P-G139's identity-theorem weld removes them exactly.
Next conjecture must test canonical Gamma/polar finite part on finite prime truncations and prove
whether anti-Herglotz order survives subtraction.

## Gates

- [x] 0 → 1: precise opposite-moment conjecture fixed
- [x] 1 → 2: Lean proof or falsifier with positive survivor
- [x] 2 → 3: exact build, targeted lint, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## Honest boundary

This no-go does not prove RH.  It determines why already-proved source passivity fails to reach
P-G139 current sign and specifies missing operation: sign-preserving renormalized positive-moment
extraction, not another passive carrier.

## Log

- 2026-08-13 — opened after P-G139 identified first-trace anomaly with continued valuation-one
  current and audit found unconditional subcritical Stokes passivity controls inverse gap.
- 2026-08-13 — exact depth-zero lower bound and full `sigma ≤ 1` nonsummability proved; exact atom
  centering identifies von Mangoldt current as positive gap moment; inverse/positive moment reversal
  closed in Lean. Direct elaboration and exact module build passed (`12414/12414`). Axiom audit:
  only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.
