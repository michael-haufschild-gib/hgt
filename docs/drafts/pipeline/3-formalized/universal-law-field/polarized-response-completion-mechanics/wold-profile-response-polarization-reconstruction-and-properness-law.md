# Wold-profile response polarization, reconstruction, and properness law

- **ID:** ULF-PRCM-3
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / LITERAL SOURCE REALIZATION / THREE-ORGAN FUSION / RECONSTRUCTION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [PRE-ZERO] [NOT RH]`
- **Statement:** The literal all-order Wold prime-clock profile is the negative primitive of a
  positive even response density, and its existing polar work is exactly a constant multiple of
  complete reflected PRCM work; work reconstructs both current and response.

## 1. Source profile

The formal frontier constructs the entire odd function

\[
 F(u)=\sum_{k\ge0}
 \frac{u^{2k+1}}{(2k+1)!}
 \left(\frac1{2k+1}-1\right).
 \tag{WPR.1}
\]

This is `sourceHorizontalWoldPrimeClockUniversalProfile`.  Its literal polar work is

\[
 P(u)=-\frac{\log2}{2}\,uF(u).
 \tag{WPR.2}
\]

The corpus separately proves oddness of `F`, positivity/properness of `P`, the cubic leading mode,
and a quartic lower bound.  The missing mechanism is what local response generates both objects.

## 2. Exact response density

Define

\[
 I_W(u)=-F'(u).
 \tag{WPR.3}
\]

### Theorem 2.1 — positive Wold response

The response is the entire even function

\[
 \boxed{
 I_W(u)=\sum_{k\ge1}
 \frac{2k}{2k+1}\frac{u^{2k}}{(2k)!}.}
 \tag{WPR.4}
\]

Equivalently, with the removable value `I_W(0)=0`,

\[
 \boxed{
 I_W(u)=\cosh u-\frac{\sinh u}{u}.}
 \tag{WPR.5}
\]

It satisfies

\[
 \boxed{
 I_W(u)\ge\frac{u^2}{3},
 \qquad
 I_W(u)=0\iff u=0.}
 \tag{WPR.6}
\]

### Proof

The series `(WPR.1)` is absolutely and locally uniformly convergent with all derivatives, by
comparison with `sinh`.  Differentiate termwise.  For `n=2k+1`,

\[
 -\frac{d}{du}\left[
 \frac{u^n}{n!}\left(\frac1n-1\right)\right]
 =\frac{n-1}{n}\frac{u^{n-1}}{(n-1)!},
\]

which gives `(WPR.4)`.  The `k=1` term is `u^2/3` and every later term is nonnegative, proving the
lower bound.

Alternatively,

\[
 \sum_{k\ge0}\frac{u^{2k+1}}{(2k+1)(2k+1)!}
 =\int_0^u\frac{\sinh v}{v}\,dv.
\]

Therefore

\[
 F(u)=\int_0^u\frac{\sinh v}{v}\,dv-\sinh u,
\]

whose derivative gives `(WPR.5)`.  If `u!=0`, `(WPR.4)` contains the strictly positive quadratic
term, so `I_W(u)>0`.  QED.

## 3. Fusion law: response, current, and work

Put

\[
 C_W(u)=-F(u).
\]

### Theorem 3.1 — exact three-organ accumulation

For every real `u`,

\[
 \boxed{
 C_W(u)=\int_0^u I_W(v)\,dv.}
 \tag{WPR.7}
\]

For `a=|u|`, the polar work is exactly

\[
 \boxed{
 P(u)=\frac{\log2}{8}\,W_{I_W}(-a,a),}
 \tag{WPR.8}
\]

where

\[
 W_{I_W}(-a,a)=2a\int_{-a}^{a}I_W(v)\,dv.
\]

Thus the source objects form one forced ladder:

\[
 \boxed{
 \text{even response }I_W
 \xrightarrow{\int_0^u}
 \text{odd Wold current }C_W
 \xrightarrow{(\log2/2)u}
 \text{even polar work }P.}
 \tag{WPR.9}
\]

### Proof

Equation `(WPR.3)` and `F(0)=0` give `(WPR.7)`.  For `a>=0`, evenness of `I_W` yields

\[
 W_{I_W}(-a,a)
 =2a\int_{-a}^{a}I_W
 =4a\int_0^aI_W
 =-4aF(a).
\]

Using evenness of `P` and `(WPR.2)`,

\[
 P(u)=P(a)=-\frac{\log2}{2}aF(a)
 =\frac{\log2}{8}W_{I_W}(-a,a).
\]

This is `(WPR.8)`.  QED.

## 4. Quartic properness is forced, not added

### Corollary 4.1

For every real `u`,

\[
 \boxed{
 P(u)\ge\frac{\log2}{18}u^4,}
 \tag{WPR.10}
\]

and

\[
 \boxed{P(u)=0\iff u=0.}
 \tag{WPR.11}
\]

For every fixed `u`,

\[
 \boxed{
 \sup_{\lambda\ge1}P(\lambda u)<\infty
 \iff u=0.}
 \tag{WPR.12}
\]

### Proof

For `a=|u|`, `(WPR.6)` gives

\[
 \int_0^aI_W(v)\,dv\ge\int_0^a\frac{v^2}{3}\,dv=\frac{a^3}{9}.
\]

Equations `(WPR.2)` and `(WPR.7)` now yield

\[
 P(u)=\frac{\log2}{2}a\int_0^aI_W(v)\,dv
 \ge\frac{\log2}{18}a^4.
\]

This proves `(WPR.10)` and both equivalences.  QED.

The existing formal quartic theorem is therefore the first-mode shadow of global reflected
formation properness, not an isolated estimate.

## 5. Joint reconstruction

### Theorem 5.1 — work retains the full source profile

For every `u!=0`,

\[
 \boxed{
 F(u)=-\frac{2P(u)}{(\log2)u},
 \qquad
 C_W(u)=\frac{2P(u)}{(\log2)u}.}
 \tag{WPR.13}
\]

Moreover,

\[
 \boxed{
 I_W(u)=\frac{2}{\log2}
 \left(\frac{P'(u)}{u}-\frac{P(u)}{u^2}\right).}
 \tag{WPR.14}
\]

The removable values at zero are recovered by continuity.  Consequently any differentiable
observer preserving `P` on a punctured neighborhood preserves the complete Wold profile, every odd
jet, and the positive response density.  Polar work is coefficient-faithful, not merely a zero
detector.

### Proof

Equation `(WPR.13)` is algebraic rearrangement of `(WPR.2)`.  Write

\[
 P(u)=\frac{\log2}{2}uC_W(u).
\]

Differentiate and use `C_W'=I_W`:

\[
 P'(u)=\frac{\log2}{2}(C_W(u)+uI_W(u)).
\]

Subtract `P(u)/u` and divide by `u` to get `(WPR.14)`.  QED.

## 6. Exact jet transmutation

The response begins quadratically,

\[
 I_W(u)=\frac{u^2}{3}+O(u^4).
\]

Integration and polarization force

\[
 C_W(u)=\frac{u^3}{9}+O(u^5),
 \qquad
 P(u)=\frac{\log2}{18}u^4+O(u^6).
 \tag{WPR.15}
\]

This supplies a mechanism for the frontier's `quadratic Fisher -> cubic current -> quartic work`
ladder.  The separately formalized adaptive-information/Wold bridge identifies the cubic current
with inverse-gauged adaptive KL chirality prime by prime.  ULF-PRCM-3 now shows why multiplying that
current by reflected aperture produces the quartic properness law with its exact coefficient.

## 7. Fourth-organ prediction

The reconstruction theorem predicts:

> any proposed positive/completed observer that preserves literal polar work as a differentiable
> function of source grade automatically preserves the whole Wold current and its even response;
> a compression that erases the cubic orientation must either alter polar work or lose
> differentiability/admission at the center.

This prediction is not assumed in the Wold, adaptive-information, or polar-work organs.  It follows
from their new fusion identity `(WPR.8)` and can be tested on every proposed completion handoff.

In particular, equality of two differentiable polar-work realizations is far stronger than equality
of their zero loci: it forces equality of all source-profile coefficients through `(WPR.13)`.

## 8. RH scope

For a divisor copy with centered grade

\[
 u=2\operatorname{Re}\rho-1,
\]

the existing corpus identifies `u=0` with the critical line and proves bounded polar work along
every expanding source-scale orbit is RH-equivalent.  ULF-PRCM-3 does not supply that boundedness.
It changes the missing premise:

1. source work is now a complete reflected response accumulation, not an ad hoc positive scalar;
2. any valid boundedness producer must control the positive density `I_W`, or an exactly
   reconstructing work realization;
3. a lossy observer must account for its work deficit, by ULF-PRCM-1.

The remaining arithmetic theorem is a pre-zero conservation/budget law for complete work plus
deficit.  Positivity, functional-equation symmetry, or Fisher compactness alone do not provide it.

## 9. Hostile conjecture loops

1. **Cubic Wold and quartic polar laws are independent route accidents.**  False by `(WPR.7)`--
   `(WPR.9)`.
2. **Polar work sees only the critical zero.**  False by joint reconstruction `(WPR.13)`--
   `(WPR.14)`.
3. **The quartic lower bound needs a separate coercivity argument.**  False: it is the integrated
   quadratic response term.
4. **Common recovery can retain work while erasing current.**  False when it preserves the
   differentiable work function; reconstruction recovers current and response.
5. **This proves the source work bound.**  False.  Properness is proved; boundedness producer remains
   open and RH-bearing.

## 10. Parent mathematics and corpus status

Termwise differentiation of entire series, the hyperbolic sine integral, and nonnegative power
series are classical.  The source profile and polar work were already formalized separately in
`RHTower/SourceHorizontalWoldPrimeClockProfile.lean`.  Corpus search found no derivative response
density, PRCM identity, or reconstruction theorem.

No external novelty claim is needed.  New mathematical leverage is the exact source-level fusion:
one response law now generates and reconstructs three previously separate frontier organs.

### Lean formalization

`RHTower/SourceHorizontalWoldProfileResponsePolarization.lean` certifies the literal all-order
response series, removable `cosh - sinh/u` formula, positivity and exact zero locus, current
primitive, symmetric reflected-work fusion, quartic properness interface, full-ray unboundedness,
profile/current reconstruction, differentiated response reconstruction, and exact
quadratic/cubic/quartic transmutation series.  Module is imported by both
`HTGeometry/UniversalLawField.lean` and theorem-area umbrella `RHTower.lean`.

Direct Lean check and targeted module build pass.  All 34 new public declarations were audited and
use only standard axioms `[propext, Classical.choice, Quot.sound]`.  Formal lint reports no issue
for this module; remaining unreachable-module reports belong to unrelated concurrent work.

## 11. Gates

- [x] entire positive response density
- [x] exact profile primitive
- [x] exact reflected-work fusion identity
- [x] quartic properness from response
- [x] joint work/profile/response reconstruction
- [x] quadratic/cubic/quartic jet transmutation
- [x] fourth-organ preservation/loss prediction
- [x] hostile corpus audit
- [x] Lean formalization
- [ ] pre-zero complete-work budget

## Log

- 2026-08-12 — source profile differentiated after PRCM frontier mapping; exact three-organ fusion
  and reconstruction theorem proved on paper.
- 2026-08-28 — formalized WPR.4--WPR.15 unconditionally in
  `RHTower/SourceHorizontalWoldProfileResponsePolarization.lean`; direct check, targeted build,
  axiom audit, umbrella wiring, and lint gate completed; promoted to Stage 3.
