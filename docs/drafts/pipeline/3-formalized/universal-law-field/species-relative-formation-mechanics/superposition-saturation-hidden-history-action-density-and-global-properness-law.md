# Superposition saturation, hidden-history action density, and global properness law

**ID:** ULF-SRFM-4  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [GLOBAL FORMATION PROPERNESS]`
`[SOURCE-GENERATED DEPTH] [NEW CORPUS CONSEQUENCE] [NOVELTY UNVERIFIED]`
`[LEAN CLOSED] [NOT RH]`

## 1. Purpose

The Poisson--Boolean--history split of ULF-SRFM-2 conserves information at one formation depth.
This card proves the missing global statement. Independent Poisson superposition supplies a
source-native depth operation. Under repeated superposition:

1. Boolean occupancy saturates and loses every off-diagonal distinction;
2. the recovered excess-count history escapes every finite history window;
3. vertical history information grows linearly;
4. its asymptotic density reconstructs complete one-copy Poisson information;
5. bounded observer mass plus bounded vertical action has compact source lift.

No coercive metric is selected by hand. Action is exact conditional relative entropy in the
already-proved formation disintegration, and depth is native independent superposition.

## 2. Formation depth and exact information split

Fix rates \(\alpha,\beta>0\). For every integer \(m\ge1\), let

\[
 P_m=\operatorname{Pois}(m\alpha),
 \qquad Q_m=\operatorname{Pois}(m\beta).
 \tag{2.1}
\]

These laws are obtained by superposing \(m\) independent copies. Their Boolean occupancy
parameters are

\[
 q_m=1-e^{-m\alpha},
 \qquad r_m=1-e^{-m\beta}.
 \tag{2.2}
\]

Let \(K_x\) be excess-count law conditional on nonvacuum,

\[
 K_x(n)=\frac{x^{n+1}}{(n+1)!(e^x-1)},
 \qquad n\in\mathbb N_0.
 \tag{2.3}
\]

Write \(J\) for Jeffreys divergence. Define

\[
 C(\alpha,\beta)
  =(\alpha-\beta)\log\frac\alpha\beta,
 \tag{2.4}
\]

\[
 B_m(\alpha,\beta)
  =J(\operatorname{Bern}(q_m),\operatorname{Bern}(r_m)),
 \tag{2.5}
\]

and vertical history action

\[
 H_m(\alpha,\beta)
 =q_mD(K_{m\alpha}\Vert K_{m\beta})
  +r_mD(K_{m\beta}\Vert K_{m\alpha}).
 \tag{2.6}
\]

### Theorem 2.1 -- extensive formation conservation

For every \(m\ge1\),

\[
 \boxed{mC(\alpha,\beta)=B_m(\alpha,\beta)+H_m(\alpha,\beta).}
 \tag{2.7}
\]

Both right-hand terms are nonnegative. History action vanishes for one, hence every, formation
depth exactly when \(\alpha=\beta\).

#### Proof

Poisson relative entropy is

\[
 D(\operatorname{Pois}(x)\Vert\operatorname{Pois}(y))
 =x\log(x/y)+y-x.
\]

Adding both directions gives

\[
 J(\operatorname{Pois}(m\alpha),\operatorname{Pois}(m\beta))
 =m(\alpha-\beta)\log(\alpha/\beta)=mC(\alpha,\beta).
\]

Apply the exact Boolean--history chain rule of ULF-SRFM-2 in both directions. This gives `(2.7)`
and nonnegativity. If \(H_m=0\), the conditional laws agree. Since

\[
 \frac{K_x(1)}{K_x(0)}=\frac x2,
\]

the map \(x\mapsto K_x\) is injective, hence \(m\alpha=m\beta\). Converse is immediate. QED.

## 3. Boolean saturation and exact hidden-action density

For \(0<r,s<1\), Bernoulli Jeffreys divergence is

\[
 J(\operatorname{Bern}(r),\operatorname{Bern}(s))
 =(r-s)\left(\log\frac r{1-r}-\log\frac s{1-s}\right).
 \tag{3.1}
\]

If \(\alpha>\beta\), substituting `(2.2)` gives

\[
 \boxed{B_m
 =(e^{-m\beta}-e^{-m\alpha})
  \log\frac{e^{m\alpha}-1}{e^{m\beta}-1}.}
 \tag{3.2}
\]

Exchange \(\alpha,\beta\) for the opposite order.

### Theorem 3.1 -- observer saturation / history-density reconstruction

For every \(\alpha,\beta>0\),

\[
 (q_m,r_m)\longrightarrow(1,1),
 \qquad B_m(\alpha,\beta)\longrightarrow0,
 \tag{3.3}
\]

and, when \(\alpha\ne\beta\), writing
\(a=\max(\alpha,\beta)\), \(b=\min(\alpha,\beta)\),

\[
 \boxed{B_m(\alpha,\beta)
 \sim m(a-b)e^{-mb}.}
 \tag{3.3a}
\]

while

\[
 \boxed{\frac{H_m(\alpha,\beta)}m
 \longrightarrow C(\alpha,\beta).}
 \tag{3.4}
\]

Boolean observation becomes asymptotically unable to distinguish source rates, but vertical
history-action density reconstructs complete one-copy Poisson Jeffreys information.

#### Proof

The occupancy limit follows from positivity. Suppose \(\alpha>\beta\). Rewrite the logarithmic
factor in `(3.2)` as

\[
 m(\alpha-\beta)
 +\log\frac{1-e^{-m\alpha}}{1-e^{-m\beta}}.
 \tag{3.5}
\]

The second summand tends to zero; the prefactor in `(3.2)` is bounded by \(e^{-m\beta}\).
Since \(me^{-m\beta}\to0\), one obtains \(B_m\to0\). More precisely,

\[
 \frac{e^{-m\beta}-e^{-m\alpha}}{e^{-m\beta}}\to1,
 \qquad
 \frac1{m(\alpha-\beta)}
 \log\frac{e^{m\alpha}-1}{e^{m\beta}-1}\to1,
\]

which proves `(3.3a)`. Symmetry handles \(\alpha<\beta\), and equality is trivial. Divide
`(2.7)` by \(m\) and use \(B_m/m\to0\) to obtain `(3.4)`. QED.

### Corollary 3.2 -- linear vertical escape

If \(\alpha\ne\beta\), then for some \(m_0\),

\[
 H_m(\alpha,\beta)\ge \frac12 C(\alpha,\beta)m
 \qquad(m\ge m_0).
 \tag{3.6}
\]

In particular, for every integer \(d\ge2\),

\[
 \sup_{n\ge0}H_{d^n}(\alpha,\beta)<\infty
 \quad\Longleftrightarrow\quad \alpha=\beta.
 \tag{3.7}
\]

#### Proof

If rates differ, `(2.4)` is positive and `(3.4)` gives `(3.6)`. Since \(d^n\to\infty\), the
forward implication in `(3.7)` follows. Equal rates give zero action. QED.

## 4. Open history over a closed observer boundary

Let \(\overline{\mathcal H}=\mathbb N_0\sqcup\{\infty\}\) be the one-point compactification of
excess-history space.

### Theorem 4.1 -- history escape

For every \(x>0\),

\[
 K_{mx}\Longrightarrow\delta_\infty
 \qquad(m\to\infty).
 \tag{4.1}
\]

Equivalently, for every fixed \(R\),

\[
 K_{mx}(\{0,\ldots,R\})\longrightarrow0.
 \tag{4.2}
\]

Hence formed Boolean observers close at common point \((1,1)\), while both marked histories leave
every finite source window. Relative history action is zero on the diagonal and infinite at the
depth boundary off it.

#### Proof

From `(2.3)`,

\[
 K_{mx}(\{0,\ldots,R\})
 =\frac{\sum_{j=1}^{R+1}(mx)^j/j!}{e^{mx}-1}.
\]

Numerator is a fixed-degree polynomial in \(m\); denominator grows exponentially. This proves
`(4.2)`, hence `(4.1)`. Final claim follows from `(3.3)` and `(3.7)`. QED.

## 5. Global formation properness

Define source-generated orbit action

\[
 \mathcal A_d(\alpha,\beta)
 =\sup_{n\ge0}H_{d^n}(\alpha,\beta)\in[0,+\infty].
 \tag{5.1}
\]

Extend it to vacuum-completed rate cone \([0,\infty)^2\) by

\[
 \overline{\mathcal A}_d(0,0)=0,
 \qquad \overline{\mathcal A}_d(\alpha,\beta)=+\infty
 \quad\text{when exactly one rate is zero}.
 \tag{5.2}
\]

### Theorem 5.1 -- source-generated global properness

For every integer \(d\ge2\),

\[
 \boxed{\overline{\mathcal A}_d(\alpha,\beta)<\infty
 \quad\Longleftrightarrow\quad \alpha=\beta.}
 \tag{5.3}
\]

Consequently, for every \(0\le M,C<\infty\),

\[
 \left\{(\alpha,\beta)\in[0,\infty)^2:
 \alpha+\beta\le M,\ \overline{\mathcal A}_d(\alpha,\beta)\le C\right\}
 =\{(x,x):0\le x\le M/2\},
 \tag{5.4}
\]

which is compact. Bounded extensive observer formation plus bounded recovered-history action has
compact source-lift set.

#### Proof

On positive cone, `(5.3)` is `(3.7)`. Vacuum extension agrees with the unique finite-action
diagonal limit; if one rate stays positive while the other tends to zero, one-copy Poisson Jeffreys
information `(2.4)` diverges, so finite orbit action cannot extend there. Equation `(5.4)` follows
from `(5.3)`, and a closed bounded interval is compact. QED.

### Corollary 5.2 -- infinite relaxed action at every new observer-boundary lift

At saturated observer point \((1,1)\), relaxed vertical action of a fixed positive source pair is

\[
 \liminf_{m\to\infty}H_m(\alpha,\beta)
 =\begin{cases}
 0,&\alpha=\beta,\\
 +\infty,&\alpha\ne\beta.
 \end{cases}
 \tag{5.5}
\]

Observer compactification creates no finite-action off-diagonal source history.

## 6. Functional-equation specialization and exact selection consumer

For a prime \(p\) and \(|t|<1\), use reflected source rates from ULF-SRFM-2,

\[
 \alpha_p(t)=\log(1+p^{t-1}),
 \qquad \beta_p(t)=\log(1+p^{-t-1}).
 \tag{6.1}
\]

Reflection \(t\mapsto-t\) exchanges rates and leaves every \(B_m,H_m,\mathcal A_d\) invariant.

### Corollary 6.1 -- bounded formation-depth history selects neutral rate

For every prime \(p\), integer \(d\ge2\), and \(|t|<1\),

\[
 \boxed{\mathcal A_d(\alpha_p(t),\beta_p(t))<\infty
 \quad\Longleftrightarrow\quad t=0.}
 \tag{6.2}
\]

#### Proof

By `(5.3)`, finite action is equivalent to rate equality. Strict monotonicity of \(\log(1+x)\)
reduces this to \(p^{t-1}=p^{-t-1}\), equivalently \(2t\log p=0\), hence \(t=0\). QED.

This is a selection **consumer**, not RH proof. Missing producer is a pre-zero source law giving one
uniform upper bound on depth-orbit history action for packet attached to every spectral state. If
derived rather than assumed, `(6.2)` forces neutral locus.

## 7. Hostile conjecture loops

1. **Boolean saturation is properness. -- False.** Boolean work tends to zero for every pair.
2. **Common recovery kernel is enough. -- False.** Parameter-independent recovery is
   information-neutral. Here conditional history laws vary with source rates.
3. **Normalized history action is proper. -- False.** `(3.4)` is finite for every fixed pair.
   Properness uses raw extensive action over unbounded source-generated depth.
4. **Clock compensation is harmless gauge. -- False in marked doctrine.** Replacing depth-\(m\)
   rates by \(\alpha/m,\beta/m\) cancels superposition and changes source schedule.
5. **Arbitrary correlated addition obeys same theorem. -- False.** Independent superposition is
   load-bearing because it produces \(m\alpha,m\beta\).
6. **All-prime summation is needed. -- False.** One marked label already makes depth orbit proper.
7. **Functional equation supplies boundedness. -- False.** Reflection preserves action; it does
   not bound a nonneutral orbit.

## 8. Relation to half-aperture reserve wall

ULF-SRFM-2 varies prime label at fixed formation depth and finds an \(\ell^1\) transition at
\(t=1/2\). This card varies formation depth at one fixed label and finds linear vertical escape for
every nonzero \(t\). The two laws are independent:

- prime cofinality decides whether Booleanization is an essentially summable species change;
- formation depth decides whether hidden multiplicity remains bounded under native superposition.

This two-axis distinction is positive survivor of failed claim that half-aperture wall selects centre.

## 9. Literature and significance audit

Ingredients have established parents:

- relative-entropy chain rules and recoverability;
- Poisson superposition and explicit divergence formulas, including Leskelä,
  [*Information divergences and likelihood ratios of Poisson processes and point patterns*](https://arxiv.org/abs/2404.00294);
- zero-truncated Poisson and hurdle models, including López--Dunlavy--Lehoucq,
  [*Zero-Truncated Poisson Regression for Sparse Multiway Count Data Corrupted by False Zeros*](https://arxiv.org/abs/2201.10014), and Agyarko et al.,
  [*Marginalised Poisson Hurdle Model for Cross-Sectional Count Data with Excess Zeros*](https://arxiv.org/abs/2606.03023);
- uniqueness of relative entropy among divergences with full chain rule, in Lacker,
  [*Law invariant risk measures and information divergences*](https://arxiv.org/abs/1510.07030).

Broad arXiv searches through August 2026 found no source stating coupled theorem `(3.3)--(5.5)`:
repeated Poisson formation makes Boolean information vanish while conditional history-action density
reconstructs complete source divergence and induces compact-lift properness. Priority remains
unverified; no external novelty claim is made.

Significance is internal and mathematical: Gate V of first species-fusion chamber is paper-closed
by source-generated mechanism. Result predicts which observer completion is harmless (only diagonal
history) and converts any future uniform source conservation bound into exact neutral selection.

## 10. Lean status

Closed unconditionally in three new modules:

* `formal/GaloisForLFunctions/HTGeometry/CountableRelativeEntropyValue.lean` — the exact atom-series
  value of relative entropy between countable laws.
* `formal/GaloisForLFunctions/HTGeometry/PoissonOccupancyHistorySplit.lean` — Poisson and
  excess-count relative entropy, the occupancy--history chain rule, and Theorem 2.1.
* `formal/GaloisForLFunctions/HTGeometry/PoissonSuperpositionSaturationProperness.lean` — Sections
  3--6.

See the companion file
`superposition-saturation-hidden-history-action-density-and-global-properness-law-formalized.md`
for the result-to-declaration table.  Every declaration depends only on `propext`,
`Classical.choice`, `Quot.sound`.
