# Observer-clock multiplier descent, interaction anomaly, and literal escape law

- **ID:** ULF-TAFM-20
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT FUSION / EXACT NON-DESCENT / INTERACTION-PROPERNESS LAW
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [PRE-ZERO] [UNCONDITIONAL] [NOT RH]`
- **Parents:** observer-clock transmutation, finite-quotient interaction cohomology,
  source-selected Fock interaction, anchored innovation phase gauge
- **Statement:** A clock change acts by pointwise multiplication. On a genuine two-organ product,
  multiplication preserves the row-plus-column marginal quotient exactly for constant clock rates.
  Every nonconstant rate creates a canonical interaction anomaly whose anchored representative is
  the product of the clock contrast and the organ contrast. The literal harmonic-to-square-root
  rate creates unbounded interaction anomaly from one fixed two-state marginal probe.

## 1. Why this is the next law

ULF-TAFM-19 proved that the harmonic-to-square-root clock rate is unbounded and that arbitrary
neutral dipoles can therefore escape. That left a loophole: perhaps quotienting by route-local or
organ-local information before changing clocks could remove the noncompact direction.

It cannot. The load-bearing fact is algebraic. Marginal observables form a linear subspace, not an
ideal of the algebra of joint observables. A nonconstant multiplier therefore fails to descend to
the marginal quotient. Its failure is exactly the interaction class which neither marginal sees.

This couples three previously separate organs:

1. observer-clock transmutation supplies the multiplier;
2. finite-quotient interaction cohomology supplies the marginal quotient;
3. source-selected Fock formation supplies the mixed interaction carrier.

Functional-equation reflection is the constant-rate subgroup and remains information-neutral.

## 2. Joint observables, marginals, and anchored interaction

Let `A` and `B` be nonempty sets with anchors `a0` and `b0`, and let

\[
 V=\mathbb C^{A\times B}.
\]

The marginal subspace is

\[
 \mathcal M=\{(a,b)\mapsto r(a)+c(b):r\in\mathbb C^A,\ c\in\mathbb C^B\}.
\tag{20.1}
\]

Define the anchored interaction projector

\[
 (\mathcal I f)(a,b)
 =f(a,b)-f(a,b_0)-f(a_0,b)+f(a_0,b_0).
\tag{20.2}
\]

### Theorem 2.1 -- exact marginal/inter-action decomposition

For every `f in V`,

\[
 f(a,b)=f(a,b_0)+\bigl(f(a_0,b)-f(a_0,b_0)\bigr)+(\mathcal I f)(a,b).
\tag{20.3}
\]

Moreover,

\[
 \boxed{f\in\mathcal M\iff \mathcal I f=0.}
\tag{20.4}
\]

#### Proof

Equation (20.3) is obtained by expanding (20.2). Its first term is a row observable, its second is
a column observable, and its third vanishes on the anchored row and column. If `f=r+c`, the four
terms in (20.2) cancel. Conversely, if `I f=0`, equation (20.3) writes `f` as a sum of one row and
one column observable. QED.

Thus `V/M` is represented exactly by anchored interaction holonomy. No choice of a complement is
needed after anchors are fixed.

## 3. Clock multiplication creates interaction

Let `lambda : A -> C` be a clock rate and `g : B -> C` an organ reporter. Their separated joint
observable is

\[
 (\lambda\boxtimes g)(a,b)=\lambda(a)g(b).
\tag{20.5}
\]

### Theorem 3.1 -- exact clock-interaction fusion law

For every `a,b`,

\[
 \boxed{
 \mathcal I(\lambda\boxtimes g)(a,b)
 =\bigl(\lambda(a)-\lambda(a_0)\bigr)
  \bigl(g(b)-g(b_0)\bigr).}
\tag{20.6}
\]

Consequently,

\[
 \lambda\boxtimes g\in\mathcal M
 \iff \lambda\text{ is constant or }g\text{ is constant}.
\tag{20.7}
\]

#### Proof

Substitution of (20.5) into (20.2), followed by factorization, gives (20.6). If either factor is
constant, the right side vanishes. If neither is constant, choose `a` and `b` for which both
anchored differences are nonzero; their product is nonzero because `C` is an integral domain.
Apply (20.4). QED.

Equation (20.6) is the genuine fusion law. Clock contrast and organ contrast are individually
marginal; their product is precisely the joint interaction invisible to both separate gauges.

## 4. Exact descent classification

Clock transmutation acts on joint observables by

\[
 (T_\lambda f)(a,b)=\lambda(a)f(a,b).
\tag{20.8}
\]

Assume `B` has a point `b1 != b0`.

### Theorem 4.1 -- only constant clocks descend through all marginals

\[
 \boxed{
 T_\lambda(\mathcal M)\subseteq\mathcal M
 \iff \lambda\text{ is constant}.}
\tag{20.9}
\]

#### Proof

Constant `lambda=c` gives `T_lambda f=cf`, so the marginal subspace is preserved.

Conversely, let `g` be the column indicator of `b1`; hence `g(b1)=1` and `g(b0)=0`. The observable
`f(a,b)=g(b)` is marginal. If `T_lambda` preserves all marginals, then
`lambda boxtimes g` is marginal. By (20.6) at `(a,b1)`,

\[
 0=(\mathcal I(T_\lambda f))(a,b_1)=\lambda(a)-\lambda(a_0)
\]

for every `a`. Thus `lambda` is constant. QED.

The quotient `V/M` is therefore not a module over arbitrary clock rates. Its full multiplier
algebra inherited from scale-only clocks is exactly the scalars.

### Corollary 4.2 -- anomaly signature reconstructs the clock modulo scalar gauge

For each marginal observable `f`, define the clock anomaly

\[
 \mathfrak A_\lambda(f)=[T_\lambda f]\in V/\mathcal M.
\tag{20.10}
\]

Then

\[
 \boxed{
 \mathfrak A_\lambda=\mathfrak A_\kappa
 \iff \lambda-\kappa\text{ is constant}.}
\tag{20.11}
\]

#### Proof

Equality of signatures says that `T_(lambda-kappa)` maps every marginal into `M`; Theorem 4.1
then makes `lambda-kappa` constant. The converse is scalar invariance of a linear subspace. QED.

Hence interaction anomalies recover every nonconstant part of an observer clock. This is joint
reconstruction, not merely a non-descent statement.

## 5. Properness and fixed-mass witnesses

Keep the column indicator `g` above. It has fixed sup norm one, independent of the clock. From
(20.6),

\[
 |\mathcal I(\lambda\boxtimes g)(a,b_1)|
 =|\lambda(a)-\lambda(a_0)|.
\tag{20.12}
\]

### Theorem 5.1 -- interaction-properness classification

The anomaly generated by this one fixed marginal probe is uniformly bounded exactly when the
anchored clock contrast is uniformly bounded. If `lambda` is unbounded, the anomaly escapes every
finite ceiling while probe mass and organ complexity stay fixed.

#### Proof

This is equality (20.12). An unbounded function remains unbounded after subtraction of its fixed
anchor value. QED.

This sharpens the neutral-dipole theorem of ULF-TAFM-19. Noncompactness is not removed by adding a
second observer organ: it becomes a cohomologically nontrivial interaction holonomy.

## 6. Literal harmonic-to-square-root anomaly

Let

\[
 \lambda_R(k)=
 \frac{\sqrt{k+2}-\sqrt{k+1}}
 {\frac1{k+1}-\frac1{k+2}}
\tag{20.13}
\]

be the completed harmonic-to-square-root clock rate. The corpus proves

\[
 \lambda_R(k)\ge k+1\qquad(k\ge3).
\tag{20.14}
\]

Take `A=N` anchored at `1`, `B=Fin 2` anchored at `1`, and the fixed sign reporter

\[
 g(1)=1,\qquad g(0)=-1.
\tag{20.15}
\]

### Theorem 6.1 -- literal interaction anomaly escapes

The anchored interaction produced by the physical clock change is

\[
 \boxed{
 \mathcal I(\lambda_R\boxtimes g)(k,0)
 =-2\bigl(\lambda_R(k)-\lambda_R(1)\bigr).}
\tag{20.16}
\]

It is unbounded in absolute value. Therefore harmonic-to-Riesz transmutation cannot descend
through even the smallest nontrivial marginal quotient.

#### Proof

Equation (20.16) is (20.6) and (20.15). Given `C`, choose `k>=3` with
`k+1>C+|lambda_R(1)|`. Equations (20.14) and the reverse triangle inequality give

\[
 |\lambda_R(k)-\lambda_R(1)|>C.
\]

Multiplication by two preserves escape. QED.

No zeta zero, divisor selection, computation, or RH premise occurs.

## 7. Functional equation, positivity, and recurrence

The law distinguishes three operations which earlier analogies blurred.

1. A constant phase or constant clock rescaling preserves `M` and descends to the interaction
   quotient. The functional-equation sign action belongs here and is information-neutral.
2. A nonconstant clock rate does not descend. It creates the interaction class (20.6).
3. Squaring the interaction amplitude preserves its magnitude while identifying opposite signs.
   Positivity is therefore a phase quotient after the anomaly has been created; it cannot recover
   anomaly orientation.

Marginal observers may each close or recur while the joint lifted history remains open: the
nonzero class in `V/M` is exactly the obstruction. This gives a literal mechanism behind the
closed-observer/open-history phenomenon, with no appeal to geometric metaphor.

## 8. Fourth-organ prediction and RH architecture

The law predicts:

> Any source formation transported by a nonconstant physical clock must acquire an irreducible
> mixed interaction sector. A proof architecture which keeps only prime, Boolean, additive,
> multiplicative, or route-local marginals cannot be stable under that clock change.

The source-selected Fock theorem supplies the fourth-organ confirmation: its prime and Boolean
layers are finite at the critical wall, while the mixed-exponent interaction layer is the unique
non-summable carrier. ULF-TAFM-20 explains why a nonconstant observer change must land there rather
than in either marginal layer.

The final RH architecture is consequently narrower:

\[
 \text{harmonic neutral completed source}
 \xrightarrow{\text{nonconstant clock}}
 \text{interaction anomaly}
 \xrightarrow{\text{source law}}
 \text{bounded bilateral interaction admission}
 \Longrightarrow \text{critical grade}.
\tag{20.17}
\]

The still-open producer is no longer generic exceptional-domain membership. It is a concrete
pre-quotient theorem controlling the clock-created interaction anomaly of the literal arithmetic
source. Applying positivity or marginalization before this control destroys exactly the class
which must be bounded.

## 9. Hostile audit and literature boundary

- **Not ULF-TAFM-19 restated.** That theorem classifies one-axis rate boundedness by neutral
  dipoles. The present theorem proves failure of clock multiplication to descend through a
  two-organ marginal quotient and reconstructs the rate modulo constants from its anomaly
  signature.
- **Not finite interaction cohomology restated.** Existing cohomology classifies the quotient
  `V/M`; it does not classify its pointwise multiplier algebra or connect multiplier failure to a
  physical clock.
- **Not ANOVA novelty.** Row/column/main-effect versus interaction decompositions are classical.
  The algebraic factorization (20.6) is elementary. Novelty is not claimed for those ingredients.
  The result is retained as a `[BRIDGE]` because it supplies the missing exact coupling between
  observer transmutation, interaction cohomology, and literal arithmetic clock escape.
- **Helson attack.** Local prime-phase laws permit extremely flexible divisor geometry; current
  Helson constructions can prescribe zeros and poles or even maximal continuation domains. This
  rules out replacing the interaction anomaly by generic phase averaging. See
  [Andersson, arXiv:2408.15713](https://arxiv.org/abs/2408.15713).
- **Positive-kernel attack.** Recent weighted Helson/Hankel spectral theory produces rich
  continuous spectra and boundedness classifications, but it does not select the literal
  arithmetic phase or make a nonconstant clock descend through marginals. See
  [Ma--Lu--Zu, arXiv:2608.22882](https://arxiv.org/abs/2608.22882).
- **Beurling attack.** Strong generic prime-number remainder behavior does not pin down classical
  zero geometry; generalized-prime systems realize broad exponent pairs. This blocks any claim
  that multiplicative feedback plus magnitude envelopes alone proves the required anomaly bound.
  See [Broucke--Debruyne--Révész, arXiv:2309.01567](https://arxiv.org/abs/2309.01567).

## 10. Gates

- [x] exact common intervention grammar identified
- [x] genuine fusion law across clock, marginal quotient, and interaction carrier
- [x] joint reconstruction modulo constant gauge
- [x] exact descent classification
- [x] literal unbounded harmonic-to-Riesz interaction anomaly
- [x] fourth-organ mixed-carrier prediction
- [ ] Lean formalization and umbrella wiring
- [ ] literal source law bounding the created interaction anomaly
- [ ] bilateral admission and RH selection

## Log

- 2026-08-31 -- Proved exact clock-interaction factorization, constant-multiplier descent
  classification, anomaly reconstruction modulo scalar gauge, fixed-probe properness, and literal
  harmonic-to-square-root interaction escape. Two attempted producers were retired first:
  absolute Selberg-clock feedback loses a factor `sqrt N`, and prime-phase/Fock averaging cannot
  select the literal phase against Helson flexibility.
