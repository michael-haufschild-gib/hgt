# Polarized Response-Completion Mechanics

- **ID:** ULF-PRCM-FIELD
- **Stage:** 1 — in progress
- **Type:** UNIVERSAL-LAW FIELD PROGRAMME
- **Status:** `[MECHANISM-FIRST] [TWO PAPER-PROVED REALIZATIONS] [LEAN GATE OPEN] [NOT RH]`

## 1. Primitive mechanism

One local response density can generate two globally inequivalent accumulation laws.

Let `I(t) >= 0` be the response carried by a one-parameter formation.  For `a <= b`, define

\[
 L_I(a,b)=\int_a^b\sqrt{I(u)}\,du,
 \qquad
 W_I(a,b)=(b-a)\int_a^b I(u)\,du.
 \tag{PRCM.1}
\]

Extend both functions symmetrically when `b<a`.

`L_I` is the positive/root accumulation read by Fisher--Rao geometry.  `W_I` is the polarized
mass accumulation read by reciprocal affine work.  They have the same infinitesimal germ,

\[
 \frac{L_I(t,t+h)}{|h|}\longrightarrow\sqrt{I(t)},
 \qquad
 \frac{W_I(t,t+h)}{h^2}\longrightarrow I(t),
 \tag{PRCM.2}
\]

but need not have the same completion or bounded sets.

This is not another route object.  It is a law for how local response produces two different
global observers.

## 2. Field laws

### Law I — local-germ agreement

Positive length and reciprocal work recover the same response density through `(PRCM.2)`.

### Law II — polarization inequality

For every finite interval,

\[
 \boxed{L_I(a,b)^2\le W_I(a,b).}
 \tag{PRCM.3}
\]

This is Cauchy--Schwarz.  It is local-to-global but one-sided: bounded work controls length, while
bounded length need not control work.

### Law III — dual-completion separation

If

\[
 \int_T^\infty\sqrt{I(u)}\,du<\infty
 \quad\text{and}\quad
 \int_T^\infty I(u)\,du>0
 \quad\text{for every finite }T,
 \tag{PRCM.4}
\]

then the positive tail collapses,

\[
 \sup_{a,b\ge T}L_I(a,b)\longrightarrow0,
 \tag{PRCM.5}
\]

while every tail has infinite work diameter,

\[
 \sup_{a,b\ge T}W_I(a,b)=\infty.
 \tag{PRCM.6}
\]

Thus positive completion can add a compact boundary point that no bounded-work completion can add.

### Law IV — neutral recovery

A common parameter-independent recovery kernel preserves directed KL, hence preserves reciprocal
work and its local Fisher germ exactly.  Recovery cannot repair the completion mismatch.

### Law V — observer deficit migration

Markov observation contracts reciprocal work.  If an observed tail has bounded work while the
complete formation satisfies `(PRCM.6)`, the missing work has unbounded tail diameter.  Compact
positive observation therefore has only two selection-relevant possibilities:

1. retain the proper reciprocal work; or
2. move it into an unbounded information-deficit fibre.

### Law VI — global reflected properness

For continuous `I>=0`, define complete reflected work

\[
 \mathcal W_I(T)=W_I(-T,T)=2T\int_{-T}^{T}I(u)\,du.
 \tag{PRCM.7}
\]

Then

\[
 \boxed{
 \sup_{T\ge1}\mathcal W_I(T)<\infty
 \iff I\equiv0.}
 \tag{PRCM.8}
\]

Any nonzero response contributes a fixed positive mass on one compact interval; amplification
multiplies that mass by the growing aperture `2T`.  This is the route-independent global
formation/properness theorem.  If `I_q identically 0` is equivalent to a reflected coordinate
`q=0`, a source bound on complete work selects the fixed locus.

## 3. First exact realization

For a finite positive escort family

\[
 p_t(i)=\frac{w_i e^{t r_i}}{\sum_jw_j e^{t r_j}},
 \]

the response is `I(t)=Var_{p_t}(r)`.  Its mean satisfies `m'=I`, and Jeffreys work obeys the exact
fusion identity

\[
 \boxed{
 J(p_a,p_b)=(b-a)\int_a^b I(u)\,du=W_I(a,b).}
 \tag{PRCM.9}
\]

The intrinsic Fisher length of the one-dimensional escort curve is exactly `L_I`.  If `r` is
nonconstant, both Fisher tails have finite length and collapse to boundary laws, while both
Jeffreys tails have infinite diameter.  Common recovery preserves the entire separation.

The dependency-closed proof is ULF-PRCM-1.

## 4. Second exact realization: noncommutative qubit formation

For `H_t=tZ+bX` with noncommuting Pauli generators, the quantum exponential family

\[
 \rho_t=\frac{e^{H_t}}{\operatorname{Tr}e^{H_t}}
\]

has BKM response

\[
 I_Q(t)\sim b^2t^{-3}.
\]

Its BKM--Fisher length is finite while quantum Jeffreys work grows linearly.  Measuring `Z`
produces an observed response `I_Z(t)~b^2t^-4` and only logarithmic Jeffreys work; the hidden
information deficit retains the complete linear scale.  This is ULF-PRCM-2.

The realization is structurally different from a finite escort: states at different parameters
do not commute, transverse spectral rotation creates a polynomial rather than exponential response
tail, and measurement changes both response exponent and work-growth grade.

## 5. Literal Wold source realization

The all-order Wold prime-clock profile `F` carries the even positive response

\[
 I_W=-F'=\cosh u-\frac{\sinh u}{u}\ge\frac{u^2}{3}.
\]

Its formal polar work is exactly

\[
 P(u)=\frac{\log2}{8}W_{I_W}(-|u|,|u|).
\]

Therefore quadratic Fisher response, cubic Wold/adaptive-information current, and quartic polar
properness are successive accumulations of one source law.  Work reconstructs the entire profile
and response by

\[
 F(u)=-\frac{2P(u)}{(\log2)u},
 \qquad
 I_W(u)=\frac{2}{\log2}\left(\frac{P'(u)}u-\frac{P(u)}{u^2}\right).
\]

This is ULF-PRCM-3 and closes the field's first literal pre-zero source-realization gate.  The
source theorem bounding complete work remains open.

## 6. Corpus-organ fusion

The mechanism couples five previously separate organs without identifying them:

| organ | induced law |
|---|---|
| positivity / Fisher | root accumulation `L_I` |
| information / KL | polarized mass work `W_I` |
| topology / completion | finite-length boundary versus infinite-work end |
| amplification / history | affine aperture `b-a` makes residual mass proper |
| recovery / observer | exact conservation or migration into deficit fibre |

This explains a recurring corpus pattern: compact or recurrent positive observers coexist with
open, costly lifted histories.  The compactness and escape are not unrelated effects; they are
different global integrations of the same local response.

## 7. Selection theorem template

Let a source produce an amplified involutive formation with response `I`.  Assume:

1. common recovery is sufficient;
2. the source orbit realizes reciprocal work `W_I`;
3. the source proves a uniform bound on complete reciprocal work; and
4. every nontrivial reflected direction has positive response mass on every tail.

Then Law VI makes every nontrivial direction impossible.  Only the fixed locus remains.  For a
lossy observer, it is enough to bound both observed work and its exact information deficit; their
sum is complete work.

Fisher precompactness is deliberately absent from the selection premise: ULF-PRCM-1 proves it is
compatible with every nontrivial finite escort direction.

## 8. Open gates

- [x] abstract response-polarization theorem
- [x] finite escort realization
- [x] common-recovery conservation
- [x] observer-deficit fourth-organ prediction
- [x] global reflected properness theorem
- [x] genuinely noncommutative quantum realization
- [x] measurement-response exponent and work-grade loss prediction
- [x] literal Wold source response/current/work fusion
- [x] joint reconstruction and jet transmutation
- [ ] Lean formalization of the dependency-closed theorem
- [ ] infinite/cofinal criterion replacing finite score gaps
- [ ] noncommutative positive-cone realization with the same response density
- [ ] literal pre-zero arithmetic formation whose complete work is source-bounded
- [ ] proof that the physical RH reflection coordinate is a faithful PRCM direction

## 9. Hostile boundaries

1. Fisher--Rao geometry, exponential-family duality, and Jeffreys/Bregman energy are classical.
2. The field claim is the coupled accumulation law and its completion/selection consequences, not
   novelty of those ingredients.
3. Finite Fisher length does not imply recurrence; it gives a compact completion end.
4. Compactness alone supplies no reciprocal-work bound.
5. Infinite families need a source-derived square-root-tail estimate; finite support is not a
   universal substitute.
6. No RH conclusion follows until a literal source proves the complete-work bound and forbids
   hidden deficit.

## Log

- 2026-08-12 — opened after corpus audit found Fisher response and Jeffreys properness proved only
  separately.  ULF-PRCM-1 proves they are inequivalent completions generated by one response law.
