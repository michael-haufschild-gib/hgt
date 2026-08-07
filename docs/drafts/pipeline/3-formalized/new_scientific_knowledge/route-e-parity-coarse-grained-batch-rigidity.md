# Route E parity-coarse-grained batch rigidity

- **ID:** `ROUTE-E-PARITY-COARSE-BATCH-RIGIDITY-001`
- **Stage:** 3-formalized
- **Type:** `[EXACT DECOMPOSITION]` / `[QUANTITATIVE ESCAPE RIGIDITY]` / `[OPEN-CORE REDUCTION]` / `[FORMALIZED]`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL NOVELTY UNVERIFIED]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no

## Purpose

The order-free batch polarization identifies exact escape with a constant checkerboard-signed leaf
value, but still presents (2^{|P|}) leaves as one undifferentiated variance.  This theorem resolves
that variance into three nonnegative and exhaustive mechanisms: fluctuation inside even batch
parity, fluctuation inside odd batch parity, and failure of the two parity-class means to be exact
antiscale opposites.

This is not a current bound.  It is a quantitative rigidity theorem for every possible near-escape,
and reduces the moving-boundary source problem to three explicit positive targets.

## 1. Abstract two-class law

Let (I=I_+\sqcup I_-) be finite.  Let (w_i>0) and (f_i\in\mathbb R).  Put

\[
 W_\pm=\sum_{i\in I_\pm}w_i,\qquad
 K_\pm=\sum_{i\in I_\pm}w_if_i,\qquad
 L_\pm=\sum_{i\in I_\pm}w_if_i^2,
\]

and assume both classes are nonempty, so (W_\pm>0).  Define signed observations

\[
 g_i=\begin{cases}f_i,&i\in I_+,\\-f_i,&i\in I_-\end{cases},
 \qquad W=W_++W_-.
\]

Their weighted residual is

\[
 \mathcal R={\sum_iw_ig_i^2}-{(\sum_iw_ig_i)^2\over W}.
\]

Define within-class residuals

\[
 \mathcal V_\pm=L_\pm-{K_\pm^2\over W_\pm}
 ={1\over2W_\pm}\sum_{i,j\in I_\pm}w_iw_j(f_i-f_j)^2\ge0
\]

and the coarse antiscale defect

\[
 \mathcal C={W_+W_-\over W}
 \left({K_+\over W_+}+{K_-\over W_-}\right)^2
 ={(W_-K_++W_+K_-)^2\over WW_+W_-}\ge0.
\]

Then

\[
 \boxed{\mathcal R=\mathcal V_++\mathcal V_-+\mathcal C.} \tag{1}
\]

Equivalently,

\[
 \boxed{
 {(K_+-K_-)^2\over W}
 +\mathcal V_++\mathcal V_-+\mathcal C=L_++L_-.
 } \tag{2}
\]

### Proof

The one-class weighted variance identity gives

\[
 L_\pm={K_\pm^2\over W_\pm}+\mathcal V_\pm.
\]

The remaining scalar identity is

\[
 {K_+^2\over W_+}+{K_-^2\over W_-}
 ={(K_+-K_-)^2\over W_++W_-}
 +{(W_-K_++W_+K_-)^2
   \over(W_++W_-)W_+W_-},
\]

obtained by clearing the positive denominator
((W_++W_-)W_+W_-) and expanding.  Substitution proves `(1)`--`(2)`.

## 2. Exact and quantitative escape rigidity

Every term on the right of `(1)` is nonnegative.  Therefore

\[
 \mathcal R=0
\]

if and only if all three conditions hold:

1. (f_i=c_+) on (I_+);
2. (f_i=c_-) on (I_-);
3. (c_++c_-=0).

Thus zero residual is exactly the two-class checkerboard (f_i=c) on (I_+) and
(f_i=-c) on (I_-).  More strongly, for any (eta\ge0),

\[
 \mathcal R\le\eta
 \quad\Longrightarrow\quad
 \mathcal V_+\le\eta,\quad
 \mathcal V_-\le\eta,\quad
 \mathcal C\le\eta.                                    \tag{3}
\]

In particular,

\[
 \left|{K_+\over W_+}+{K_-\over W_-}\right|
 \le \sqrt{{\eta W\over W_+W_-}}.                      \tag{4}
\]

Equations `(3)`--`(4)` are a stability theorem: approximate escape forces simultaneous
same-parity rigidity and antiscale opposition of the two class means.  There is no fourth escape
mechanism hidden among individual leaves.

## 3. Route E specialization

For disjoint finite prime sets (S,P), (P\ne\varnothing), and (x\in\mathbb R), let

\[
 m_T=\prod_{p\in T}p,\qquad
 w_T=Z_S(m_Tx)>0,\qquad
 f_T=\psi_S(m_Tx)
 \quad(T\subseteq P).
\]

Split (P)'s powerset by parity:

\[
 I_+=\{T\subseteq P:|T|\text{ even}\},\qquad
 I_-=\{T\subseteq P:|T|\text{ odd}\}.
\]

Then the signed observation is exactly

\[
 g_T=(-1)^{|T|}\psi_S(m_Tx),
\]

and the existing Gibbs batch expansion gives

\[
 \sum_Tw_T=W=Z_{S\cup P}(x),\qquad
 \sum_Tw_Tg_T=J_{S\cup P}(x).
\]

Therefore `(2)` becomes the source identity

\[
 \boxed{
 {J_{S\cup P}(x)^2\over Z_{S\cup P}(x)}
 +\mathcal V_{S,P}^{\rm even}(x)
 +\mathcal V_{S,P}^{\rm odd}(x)
 +\mathcal C_{S,P}(x)
 =\sum_{T\subseteq P}w_T\psi_S(m_Tx)^2.
 }                                                        \tag{5}
\]

The classes are nonempty because ∅ is even and any singleton {(p)} with (p\in P) is
odd.  Positivity of every Gibbs partition gives positive class masses.

## 4. Frontier consequence

`GIBBS-MOVING-BOUNDARY-NONPRODUCT-FRAME` now has an exhaustive three-way positive target.  It is
sufficient to prove, with physical-power strength and literal Gibbs weights, that at least one of

\[
 \mathcal V_{S,P}^{\rm even},\qquad
 \mathcal V_{S,P}^{\rm odd},\qquad
 \mathcal C_{S,P}
\]

captures the required fraction of leaf energy.  Conversely, failure of such dissipation forces
all of the following at once:

- `ψ_S(m_T x)` is nearly constant across all relevant even subsets;
- it is nearly constant across all relevant odd subsets;
- the two weighted constants are nearly exact negatives, with loss amplified only by the explicit
  parity-balance factor (W/(W_+W_-)).

This separates two hard phenomena previously conflated:

1. **moving-boundary same-parity variation**, carried by products (m_T) with cardinalities
   differing by two;
2. **coarse antiscale opposition**, carried by the even/odd class means.

The terminal-shell resonance can suppress the coarse term by concentrating one parity mass, but
then the explicit factor (W_+W_-/W) records that degeneration rather than hiding it.  Any proof
must either prevent parity-mass collapse or extract same-parity variance before the collapse.

## Hostile audit

1. `(5)` is an identity, not Route E closure.
2. Small residual is not contradicted without a source estimate for one of the three displayed
   terms.
3. No product, independence, random-sign, Mertens, or RH-strength assumption enters.
4. The decomposition is exhaustive because it is equality `(1)`, not a union-bound heuristic.
5. `OPEN-SOURCE-001`, `GIBBS-MOVING-BOUNDARY-NONPRODUCT-FRAME`, and RH remain open.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/GibbsBatchParityCoarseGraining.lean`.
It is imported by `formal/GaloisForLFunctions/RHTower.lean`.

Unconditional declarations include:

- `routeEScalarParityCoarseIdentity`;
- `routeEBatchMeanEnergy_add_withinClassResiduals_add_coarse_eq_leafEnergy`;
- `routeEBatchResidual_eq_withinClassResiduals_add_coarse`;
- `routeEBatchNearEscape_rigidity`;
- `routeEBatchResidual_eq_zero_iff_classConstant_and_coarse`;
- `routeEGibbsBatch_currentEnergy_add_parityCoarse_eq_leafEnergy`;
- `routeEGibbsBatch_nearEscape_rigidity`;
- `routeEGibbsBatchResidual_eq_zero_iff_parityRigidity`.

Verification on 2026-08-07:

- `lake env lean GaloisForLFunctions/RHTower/GibbsBatchParityCoarseGraining.lean`: pass;
- `lake build GaloisForLFunctions.RHTower.GibbsBatchParityCoarseGraining`: pass
  (`9712/9712`), used only for this module's missing `.olean`;
- targeted `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in module;
- no full build was run.
