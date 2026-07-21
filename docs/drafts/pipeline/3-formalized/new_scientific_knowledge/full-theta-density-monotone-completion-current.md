# Full theta-density monotone-completion current

- **ID:** `full-theta-density-monotone-completion-current`
- **Stage:** 3-formalized
- **Type:** `[THEOREM (LEAN)] [NEW CORPUS SYNTHESIS] [UNCONDITIONAL] [NO RH CLAIM]`
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

## Theorem

Let

```text
rho(t) = 4 T''(t),
F(z)   = integral_(0,infinity) rho(t) exp(i t z) dt,
D(z)   = integral_(0,infinity) rho(t) i t exp(i t z) dt,
h(t)   = -rho'(t).
```

For `Im z > 0`:

1. the exact positive completion satisfies
   `G_h(z) = integral h(t)(1-exp(i t z))dt = -i z F(z)`;
2. its derivative satisfies `G_h'(z) = -i(F(z)+zD(z))`;
3. strict source monotonicity gives `Re G_h(z) > 0`, hence `F(z) != 0`;
4. contraction gives
   `|Im(D(z) conjugate(F(z)))| <= (2/Im z)|F(z)|^2`;
5. using exact product-fibre reassembly, same bound controls the absolutely convergent sum of all
   actual Hermitian fibre currents, including positive prime-cube faces.
6. because `F` is zero-free, every final odd Taylor section has canonical factorization
   `P_d=T_d F`; its current satisfies

   ```text
   J(P_d)=|T_d|^2 J(F)+|F|^2 J(T_d),
   J(P_d)<= (2/Im z)|P_d|^2+|F|^2 J(T_d).
   ```
7. sublinear anisotropic current for `T_d` is equivalent to RH for every source-selected
   superaccurate schedule.

Items 1--5 are one source theorem: cross-fibre cancellation is carried by full continuous density,
not by scalar prime-polynomial stability.  Items 6--7 are an exact gauge bridge.  The successor
Wronskian audit proves that bridge does not isolate a finite-truncation defect: `T_d` converges to
`XiC/F` and retains the full Xi divisor.

## Paper proof [PROVED HERE]

Corpus proves `rho'(t)=4 T'''(t)<0` on `[0,infinity)`, with `rho`, `rho'`, and their first moments
integrable and vanishing boundary products.  Integrating `-rho'(t)(1-exp(i t z))` by parts gives
`G_h=-i z F`; differentiating the completion kernel and integrating by parts again gives
`G_h'=-i(F+zD)`.  No boundary residue remains because completion kernel vanishes at zero and
theta density decays faster than every required polynomial moment.

For `t>0` and `Im z>0`, `|exp(i t z)|=exp(-t Im z)<1`; since `h(t)>0`, every completion integrand
has strictly positive real part.  Hence `Re G_h>0`, so `F` cannot vanish.  Pointwise inequality

```text
t exp(-t Im z) <= (1-exp(-t Im z))/Im z
```

and `Re exp(i t z)<=|exp(i t z)|` imply
`|G_h'| <= Re(G_h)/Im z <= |G_h|/Im z`.  Substituting two exact completion identities and using
`Im z<=|z|` yields

```text
|D| <= (2/Im z)|F|,
|D/F| <= 2/Im z,
|Im(D conjugate(F))| <= (2/Im z)|F|^2.
```

Finally corpus exact reassembly identifies `Im(D conjugate(F))` with absolutely convergent sum of
all `thetaProductFiberActualPhaseCurrent k z`.  This proves aggregate seam contraction without
assigning sign to any individual fibre.

For the final odd Taylor polynomial `P_d`, define `T_d=P_d/F`.  Zero-freeness of `F` makes this
canonical throughout upper half-plane.  Quotient rule and product-current Leibniz identity give

```text
J(P_d)=|T_d|^2 J(F)+|F|^2 J(T_d).
```

Since `|J(F)|<=2|F|^2/Im z`, normalized full-density term is `O(1)` on every anisotropic mesh.
It is absorbed by every positive `epsilon(n+1)` budget.  Conversely exact same identity and
absolute bound recover transfer sublinearity from final-polynomial sublinearity under RH.  Existing
anisotropic coefficient theorem then yields formal equivalence

```text
XiCTaylorFullDensityTransferCurrentSublinearUpper D <-> RH.
```

This preserves final Taylor denominator exactly; no `|P_d|`/`|F|` comparison is used.

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

## Successor correction

The first exact Wronskian experiment falsifies a pure truncation connector.  If

```text
W_d=P_d'F-P_dF',
Omega_F=XiC'F-XiC F',
R_d=XiC-P_d,
```

then

```text
W_d=Omega_F-(R_d'F-R_dF'),
W_d(z)->Omega_F(z),
Omega_F(0)!=0.
```

Thus `T_d=P_d/F` converges to `XiC/F`, not to a truncation defect.  See
`../../5-failed/xi-taylor-full-density-transfer-wronskian.md` and
`xi-full-density-source-exchange-obstruction.md`.  Current conjecture attacks only antipodal
collision of the exact reflected density pair; it does not assert the corpus-refuted global
de Branges norm gap.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFullDensityMonotoneCurrent.lean`.

Principal theorems:

- `positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_eq`;
- `positiveTailCompletionDerivative_neg_thetaCuspTailSecondDensityDerivative_eq`;
- `thetaCuspTailSecondDensityPhaseValue_ne_zero`;
- `norm_thetaCuspTailSecondDensityPhaseDerivative_div_value_le_two_div_im`;
- `abs_tsum_thetaProductFiberActualPhaseCurrent_le_two_div_im`;
- `xiCTaylor_orientedCurrent_eq_fullDensity_add_transfer`;
- `xiCTaylor_orientedCurrent_le_fullDensity_budget_add_transfer`;
- `xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis`.

Direct Lean check and targeted module build pass.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  `scripts/formal_tools.py lint` passes.

## Novelty status

Generic monotone Fourier--Laplace completion mechanism is classical in character.  New corpus
knowledge is exact composition with canonical theta density and product-fibre reassembly: local
prime-cube sign defects coexist with strict global one-sided zero-freeness and aggregate absolute
current contraction.  External publication novelty of this source-specific synthesis is not yet
claimed.

## Status

Formalized.  Does not prove RH.  `XiCTaylorFullDensityTransferCurrentSublinearUpper` remains a valid
RH-equivalent predicate and preserves final Taylor norm, but is a gauge reformulation rather than a
finite-truncation reduction.  Actual unsolved source core is exclusion of the reflected antipodal
collision `E#=-E`, equivalently the off-axis Xi zero, without the false global de Branges gap.

## Log

- 2026-07-21 — Created after corpus killed scalar cofinal Lee--Yang carrier and exposed continuous
  monotone-density completion as source-faithful replacement.
- 2026-07-21 — Paper proof closed, Lean theorem chain and product-fibre connector audited; promoted
  to 3-formalized.
- 2026-07-21 — Successor Wronskian audit corrected interpretation: transfer tends to `XiC/F` and
  retains full Xi divisor; pure finite-truncation reading retired.
