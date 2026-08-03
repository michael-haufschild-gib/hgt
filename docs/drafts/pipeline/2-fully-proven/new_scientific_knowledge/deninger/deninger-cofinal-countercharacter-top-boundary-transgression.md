# Deninger cofinal countercharacter top-boundary transgression

- **ID:** `deninger-cofinal-countercharacter-top-boundary-transgression`
- **Route:** L — Deninger/Hodge/cohomological realization
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-03
- **Exact advance:** the relative raw-to-countertransported Deninger class has a literal
  finite-stage source representative.  It is the difference between two cofinal naturality
  defects of the Tate interval forward map.  Critical reflection polarizes that representative
  to the Deninger mate curvature times the nonzero Tate top boundary, and the top-coordinate
  reader lands it coefficient-faithfully in the existing completed Calderón--Witt incidence
  carrier.

## 1. Frontier

The previous Route-L theorem identified the centered-flow countercharacter with the inverse of
the Deninger half-density gain.  Absolute countertransport therefore makes the framed transport
flat for every spectral parameter.  The actual Gamma class survives only relatively:

\[
 R_s(n)=1-\chi_s(n),\qquad
 R_{s^\#}(n)-R_s(n)=K_n(s),
 \tag{1}
\]

where

\[
 \chi_s(n)=\exp((2\operatorname{Re}s-1)\log n),\qquad
 s^\#=1-\overline s,
 \tag{2}
\]

and

\[
 K_n(s)=\chi_s(n)-\chi_s(n)^{-1}.
 \tag{3}
\]

Equation `(1)` was a scalar relative curvature.  The missing infrastructure was a concrete
preclosure source class retaining it before completion and before diagonal sewing.

## 2. Literal preclosure construction

Let

\[
 V_m=\mathbb R^{\{0,\ldots,m\}},
 \]

let \(S_m:V_m\to V_m\) be the nilpotent forward Tate arrow, and let
\(I_m:V_m\to V_{m+1}\) append a zero top coordinate.  The existing Tate interval theorem gives

\[
 S_{m+1}I_m-I_mS_m=\beta_m,                         \tag{4}
\]

where \(\beta_m\) is the rank-one top-boundary map.  If \(e_m\) is the old top basis vector,

\[
 \beta_m e_m=e_{m+1}\ne0.                            \tag{5}
\]

For a scalar gain \(g\), define the naturality defect of the scaled forward family by

\[
 D_g(m;v)=gS_{m+1}I_m v-I_m(gS_m v).                 \tag{6}
\]

Linearity of \(I_m\), together with `(4)`, gives the exact source formula

\[
 D_g(m;v)=g\,\beta_m v.                              \tag{7}
\]

At fixed power clock \(n\), the raw Deninger family has gain \(\chi_s(n)\), while canonical
centered-flow countertransport has total gain one.  Define their **relative cofinal defect** in
flat-minus-raw orientation by

\[
 \mathfrak B_s(n,m;v)=D_1(m;v)-D_{\chi_s(n)}(m;v).
 \tag{8}
\]

Substitution in `(7)` yields

\[
 \mathfrak B_s(n,m;v)
   =(1-\chi_s(n))\beta_m v
   =R_s(n)\beta_m v.                                 \tag{9}
\]

Thus the scalar relative curvature is not being renamed.  It is the coefficient of the actual
cofinal naturality obstruction already forced by the local Tate--Kummer--Wold--Gamma source.

## 3. Reflection transgression and coefficient faithfulness

Apply `(9)` at \(s^\#\) and \(s\).  Equation `(1)` gives

\[
 \mathfrak B_{s^\#}(n,m;v)-\mathfrak B_s(n,m;v)
   =K_n(s)\beta_m v.                                  \tag{10}
\]

Let \(\varepsilon_m:V_{m+1}\to\mathbb R\) read the new top coordinate.  By `(5)`,

\[
 \varepsilon_m(\beta_m e_m)=1.                       \tag{11}
\]

Consequently

\[
 \varepsilon_m\!\left(
   \mathfrak B_{s^\#}(n,m;e_m)-\mathfrak B_s(n,m;e_m)
 \right)=K_n(s).                                      \tag{12}
\]

For every \(n\ge2\), the already proved exact zero set of the mate curvature gives

\[
 \mathfrak B_{s^\#}(n,m;e_m)-\mathfrak B_s(n,m;e_m)=0
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\tfrac12.                        \tag{13}
\]

The cofinal class is therefore retained and coefficient-faithful.  Ordinary finite nilpotence
does not kill it; nilpotence arises by discarding precisely the next top boundary.

At the forced composite clock \(n=6=2\cdot3\), for an actual Xi divisor copy \(r\), the existing
Gamma comparison reads

\[
 b_\Gamma(r)=c_{23}K_6(\rho_r),\qquad c_{23}>0.       \tag{14}
\]

Combining `(12)` and `(14)` proves

\[
 b_\Gamma(r)=c_{23}\,\varepsilon_m\!\left(
   \mathfrak B_{\rho_r^\#}(6,m;e_m)
    -\mathfrak B_{\rho_r}(6,m;e_m)
 \right).                                             \tag{15}
\]

Hence the literal Gamma/Calderón--Witt coefficient is the normalized top-boundary coordinate of
the preclosure relative transgression.

## 4. Completed Calderón--Witt landing

For one divisor copy \(r\), place the coefficient in `(12)` in the corresponding Xi basis line:

\[
 x_{r,m}=K_6(\rho_r)e_r\in \ell^2(\mathrm{XiDivisorCopy}).  \tag{16}
\]

This is a finite-support vector, hence lies unconditionally in the completed Xi carrier.  Apply
the already constructed isometric completed comparison for any distinct source primes \(p,q\):

\[
 \iota_{p,q}:\ell^2(\mathrm{XiDivisorCopy})
   \overset{\cong}{\longrightarrow}
   \widehat{\mathrm{Inc}}_{p,q}^{\rm CW}.             \tag{17}
\]

The normalized incidence coordinate of \(\iota_{p,q}(x_{r,m})\) at \(r\) is exactly
\(K_6(\rho_r)\).  Its decoded algebraic source value is

\[
 K_6(\rho_r)\,w_{p,q},                                \tag{18}
\]

where \(w_{p,q}\ne0\) is the actual cross-prime Milnor-incidence witness.  Therefore

\[
 K_6(\rho_r)w_{p,q}=0
 \Longleftrightarrow K_6(\rho_r)=0
 \Longleftrightarrow b_\Gamma(r)=0
 \Longleftrightarrow \operatorname{Re}\rho_r=\tfrac12. \tag{19}
\]

This completes the previously missing **finite-fibre coefficient-faithful landing**.  It does
not identify `(16)` with the global source Green primitive; that comparison remains a separate
source theorem and is not smuggled into the construction.

## 5. Hostile audit

1. **Not a generic mapping-cone theorem.**  Mapping cones and cofinal boundary maps are parent
   homological algebra.  New content is the exact cross-identification of the HGT Tate-clock
   naturality obstruction, centered-flow countercharacter, Deninger mate curvature, forced
   composite clock six, and actual Gamma/Calderón--Witt coefficient.
2. **No RH premise.**  Every identity holds for arbitrary \(s\in\mathbb C\).  Xi is used only to
   specialize the already constructed divisor support and actual Gamma coefficient.
3. **No completion erasure.**  Equations `(11)`, `(12)`, and `(18)` exhibit explicit left readers.
   The completed landing is isometric and the incidence witness is nonzero.
4. **No cyclicity shortcut.**  A twisted or paracyclic quotient may absorb the raw modular gain,
   but `(10)` lives in the relative flat-minus-raw defect before that quotient.
5. **No universal Stokes annihilation.**  By `(13)`, the polarized class is nonzero for every
   off-critical parameter.  Any source law claimed to annihilate it merely from finite interval
   exactness, square-boundary exactness, cyclicity, or countertransport is false.
6. **No global Green identification by naming.**  The finite-support vector `(16)` is called a
   relative-Bockstein Xi vector, not the completed Green primitive.  Proving that the actual
   source Green primitive supplies or annihilates this coefficient is still the hard theorem.

Verdict: **SURVIVES PRELIMINARY ATTACK** as a concrete Route-L preclosure construction and exact
annihilation wall.  External priority remains unverified.

## 6. Literature boundary

Relative cyclic homology, modular crossed modules, twisted cyclic homology, finite-rank shift
defects, mapping telescopes, and derived-limit Bocksteins are parent mathematics.  The targeted
search found those mechanisms separately, including modular-crossed cyclic objects and modular
automorphism twists, but did not locate the arithmetic conjunction in `(10)`--`(18)`.  This is a
collision audit, not a priority claim.

## 7. Exact remaining core

The construction removes ambiguity about the source object and makes the remaining obstruction
strictly stronger:

> `[OPEN CORE — ORDINARY_INTEGER_GREEN_STOKES_ANNIHILATION]` Construct an ordinary-integer,
> source-derived comparison from the completed/cofinal Xi Green primitive to the relative Tate
> top-boundary class `(10)`, compatible with the Gamma/co-Poisson Hodge boundary and the
> Calderón--Witt incidence reader, and prove its Stokes boundary vanishes.  The proof may not
> assume vanishing of `K_6`, Gamma/Hardy kernel membership, countercharacter triviality, static
> capacity, positivity equivalent to RH, or RH itself.

Because `(12)` and `(15)` are coefficient-faithful, this is now visibly the RH-bearing arithmetic
annihilation theorem.  Generic relative homology, completion, or cyclic machinery cannot prove it.
