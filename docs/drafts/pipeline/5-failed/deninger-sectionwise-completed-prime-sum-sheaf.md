# Sectionwise completed prime sum on the full Deninger topology

- **ID:** `deninger-sectionwise-completed-prime-sum-sheaf`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Verdict:** `RETIRED AS AN ORDINARY SHEAF CONSTRUCTION`

## Failed conjecture

For prime-packet coefficient sheaves \(\mathscr A_p\), define on every
open \(V\) of Deninger's coarse suspension
\[
 \mathscr B_{\mathrm{naive}}(V)
 =
 \left\{
 (s_p)_p:
 s_p\in\mathscr A_p(V\cap X_p),\
 \sum_p\alpha_p\|s_p\|_{1,p}<\infty,\
 \sum_p\beta_p\|s_p\|_{2,p}^2<\infty
 \right\}.                                                        \tag{1}
\]
The conjecture was that `(1)` is automatically a complete locally
convex sheaf.

## Counterexample

Global summability is not local.  On a countable disjoint union of
points, cover by the singleton opens and take the section \(1\) on
every singleton.  Every local section has finite \(\ell^1\) and
\(\ell^2\) norm, and the family is compatible, but its glued family is
not in either global weighted space when the total weight diverges.
Thus `(1)` fails the sheaf gluing axiom.

The same obstruction applies to an arbitrary full topology whenever an
open admits an infinite cover that separates an unsummable family of
prime supports.  Sheafification repairs locality by admitting locally
summable sections, but then global weighted summability is lost.

## Strongest positive survivor

Let
\[
 a:X_{\mathrm{Den}}\longrightarrow\operatorname{Spec}\mathbb Z
\]
be the arithmetic projection and first take the derived direct image of
each already-constructed packet coefficient.  On the cofinite Zariski
base every nonempty open is quasi-compact, every open cover has a finite
subcover, and every inclusion of nonempty opens removes only finitely
many closed primes.  Consequently weighted local summability does glue
globally there, and restriction is split by finite-coordinate extension
by zero.

The correct all-prime object is therefore
\[
 \widehat{\underset{P\subset\{\text{primes}\},\,|P|<\infty}
 {\operatorname{ind\,lim}}}
 \ \bigoplus_{p\in P}
 i_{p,*}R(a_p)_*\mathscr A_p(-1)                                  \tag{2}
\]
in complete locally convex sheaves on
\(\operatorname{Spec}\mathbb Z\), not the sectionwise prescription
`(1)` on arbitrary Deninger opens.

Finite packet sheaves and their residues remain genuine sheaves on
Deninger's actual coarse space.  Only the nonlocal all-prime
summability completion is applied after arithmetic derived direct
image.  This preserves
\[
 R\Gamma(X_{\mathrm{Den}},-)
 =
 R\Gamma(\operatorname{Spec}\mathbb Z,Ra_*(-))
\]
whenever a full-space realization exists, while avoiding an invalid
sheaf axiom.

## No-go closure

- **Killing mechanism:** an infinite compatible family may be locally
  summable on every member of an infinite cover but not globally
  summable.
- **Sharp boundary:** the construction works on quasi-compact
  cofinite arithmetic opens because finite subcovers convert local
  bounds into a global bound.
- **Positive replacement:** completed finite-packet direct images
  `(2)`; proved in `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`.
- **No hidden loss:** mean-zero modes inside each compact prime packet
  remain in \(R(a_p)_*\mathscr A_p\).

No quotient stack, CCM object, zeta zero, or RH premise is involved.
