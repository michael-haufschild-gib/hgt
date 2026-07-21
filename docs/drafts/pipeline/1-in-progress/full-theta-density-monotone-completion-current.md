# Full theta-density monotone-completion current

- **ID:** `full-theta-density-monotone-completion-current`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [OPEN CORE ATTACK] [UNCONDITIONAL TARGET] [NO RH CLAIM]`
- **Parent:** `xi-taylor-theta-tail-core-density-current.md`
- **Falsified predecessor:** `cofinal-completed-lee-yang-seam-defect.md`

## Actual frontier

For every source-selected superaccurate schedule `D`, every
`0 < Re sigma < 1/2`, and every `epsilon > 0`, corpus cannot prove the eventual estimate

```text
J_(U_(D(k_n)))(z_n)
  < epsilon (n+1) |P_(2 D(k_n)+3)(z_n)|^2.
```

Corpus proves this raw anisotropic finite theta-tail core-current statement is equivalent to RH.
It also proves that arithmetic/Haar refinements conserve raw current as their survivor.  Therefore
the missing theorem must alter control before that conservation split and must retain the actual
archimedean source.

## Conjecture under test

Let

```text
rho(t) = 4 T''(t),
F(z)   = integral_(0,infinity) rho(t) exp(i t z) dt,
D(z)   = integral_(0,infinity) rho(t) i t exp(i t z) dt,
h(t)   = -rho'(t).
```

For `Im z > 0`, conjecture:

1. the exact positive completion satisfies
   `G_h(z) = integral h(t)(1-exp(i t z))dt = -i z F(z)`;
2. its derivative satisfies `G_h'(z) = -i(F(z)+zD(z))`;
3. strict source monotonicity gives `Re G_h(z) > 0`, hence `F(z) != 0`;
4. contraction gives
   `|Im(D(z) conjugate(F(z)))| <= (2/Im z)|F(z)|^2`;
5. using exact product-fibre reassembly, same bound controls the absolutely convergent sum of all
   actual Hermitian fibre currents, including positive prime-cube faces.

Items 1--5 are one source theorem: cross-fibre cancellation is carried by full continuous density,
not by scalar prime-polynomial stability.

## Scientific-method protocol

### Predictions

1. Two integrations by parts have no boundary residue: `1-exp(i t z)` vanishes at `t=0`, while
   `rho(t)` and `t rho(t)` vanish at infinity.
2. `-rho'(t)>0` for every `t>0`, already exposed by corpus density monotonicity.
3. No divisor-fibre term is estimated separately; product-fibre theorem is used only after full
   current bound is proved.
4. Result does not imply RH: finite Taylor core `U_d` is not `F`, and no norm comparison may replace
   its denominator.

### Kill criteria

Retire immediately if:

- an integration-by-parts boundary term survives;
- required source is not pointwise nonnegative;
- current bound applies only to a surrogate packet rather than named full density transform;
- product-fibre connector drops a seam term;
- transfer to finite Taylor core requires assuming nonvanishing or RH.

## Next conjectural connector if theorem survives

Seek a truncation-covariant positive completion for the exact finite Taylor kernel.  It must produce
an identity at `U_d` level and a defect whose current is not the conserved raw-current survivor.
This connector remains conjectural until exact symbolic source identities pass the same kill tests.

## Status

Open.  Paper derivation and Lean audit pending.

## Log

- 2026-07-21 — Created after corpus killed scalar cofinal Lee--Yang carrier and exposed continuous
  monotone-density completion as source-faithful replacement.
