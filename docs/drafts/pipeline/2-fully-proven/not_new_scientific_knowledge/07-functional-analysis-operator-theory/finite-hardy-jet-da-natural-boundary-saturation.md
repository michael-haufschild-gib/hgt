# Finite Hardy-jet DA natural-boundary saturation

- **ID:** `finite-hardy-jet-da-natural-boundary-saturation`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) -- `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence landscape; Hardy spaces; natural boundaries
- **Statement:** For every finite depth `r>=0`, there is a differentially algebraic holomorphic
  function `F` on the unit disk such that `F,F',...,F^(r)` all belong to `H^infinity`, while the
  unit circle is a natural boundary of `F`.

## Goal

The bounded-jet continuation bridge says that a DA solution whose jet is bounded through the order
of a minimal ADE cannot have a natural boundary.  The open frontier was whether boundedness of the
function alone might suffice.

It does not.  More strongly, no fixed finite Hardy-jet depth suffices.  Repeated primitives of the
quasimodular Eisenstein series `E_2` give explicit counterexamples at every prescribed depth.

## The source function

Put

`E_2(q)=1-24 sum_(n>=1) sigma_1(n) q^n`, `|q|<1`,                 (1)

where `sigma_1(n)=sum_(d|n)d`, and let

`delta=q d/dq`.

Ramanujan's differential system for `E_2,E_4,E_6`, after eliminating `E_4` and `E_6`, gives the
Chazy equation

`2 delta^3 E_2-2 E_2 delta^2 E_2+3(delta E_2)^2=0`.             (2)

Hence `E_2` is differentially algebraic over `C(q)`.

The unit circle is a natural boundary of the `q`-function `E_2`.  Indeed, let `a/c` be any reduced
rational number and choose

`gamma=(a b; c d) in SL_2(Z)`.

For `tau` in the upper half-plane, the quasimodular transformation law is

`E_2(gamma tau)=(c tau+d)^2 E_2(tau)-(6 i c/pi)(c tau+d)`.       (3)

As `Im tau->infinity`, one has `E_2(tau)->1`, while

`gamma tau->a/c`.

The quadratic term in (3) dominates the anomalous linear term, so

`|E_2(gamma tau)|->infinity`.                                   (4)

Under `q=exp(2 pi i tau)`, this approaches the root of unity `exp(2 pi i a/c)`.  Thus every root
of unity is a singular boundary point of (1).  Roots of unity are dense in the unit circle, so no
open boundary arc admits analytic continuation.

## The explicit family

For every integer `m>=3`, define

`F_m(q)=-24 sum_(n>=1) sigma_1(n) n!/(n+m)! q^(n+m)`.            (5)

This series is the `m`-fold primitive of `E_2-1` with all integration constants zero.  Termwise
differentiation gives

`F_m^(m)=E_2-1`.                                                 (6)

## Differential algebraicity `[PROVED HERE]`

Substitute `E_2=F_m^(m)+1` into (2).  Since

`delta y=q y'`,

`delta^2 y=q y'+q^2 y''`,

`delta^3 y=q y'+3q^2 y''+q^3 y'''`,                             (7)

the result is a nonzero algebraic differential equation over `C(q)` for `F_m`, of order at most
`m+3`.  Its highest derivative occurs in the nonzero term `2q^3 F_m^(m+3)`.  Therefore every
`F_m` is DA over `C(q)`.

No closure-under-indefinite-integration theorem is being assumed: equation (2) is transported
directly through the identity (6).

## Arbitrarily long bounded jets `[PROVED HERE]`

For `0<=j<=m`, differentiating (5) gives

`F_m^(j)(q)`

` =-24 sum_(n>=1) sigma_1(n) n!/(n+m-j)! q^(n+m-j)`.             (8)

If `j<=m-3`, set `s=m-j>=3`.  On the closed unit disk, the absolute coefficient sum is bounded by

`24 sum_(n>=1) sigma_1(n)/n^s`

` =24 zeta(s) zeta(s-1)<infinity`.                              (9)

Thus (8) converges absolutely and uniformly on `|q|<=1`.  In particular,

`F_m,F_m',...,F_m^(m-3) in H^infinity(D)`.                      (10)

Given an arbitrary prescribed depth `r>=0`, choose `m=r+3`.  Then the complete finite jet

`F_m,F_m',...,F_m^(r)`

is bounded on the disk.

## The natural boundary survives integration `[PROVED HERE]`

Suppose `F_m` continued analytically through a nonempty open arc of the unit circle.  Differentiating
the continuation `m` times would continue `F_m^(m)=E_2-1` through the same arc.  This contradicts the
dense root-of-unity singularities established from (3)--(4).  Hence the unit circle is a natural
boundary of every `F_m`.

Combining this with (7)--(10) proves the theorem. `QED`

## Law extracted

**Finite Hardy-jet natural-boundary saturation law.**  For every fixed finite observation depth,
the simultaneous data

1. holomorphy on the disk;
2. boundedness of the function and all observed derivatives;
3. maximal boundary noncontinuability;

remain compatible with a finite algebraic differential equation.

Natural-boundary behavior becomes an HT certificate only when paired with jet control whose depth tracks
the order of the alleged ADE.  There is no universal finite Hardy-jet cutoff.

## Exact route consequence

The theorem excludes implementations that try to infer HT, or an RH selector, from a transformed disk
carrier using only a fixed finite list of Hardy bounds together with a natural boundary.  In particular:

1. a Hardy/Nyman--Beurling implementation cannot replace its exact norm-closure and arithmetic generator
   by `H^infinity` membership plus boundary noncontinuability;
2. a de Branges or spectral implementation cannot replace its global positivity/kernel data by any fixed
   bounded derivative passport plus a natural boundary;
3. transform-domain arguments cannot treat a natural boundary as evidence of infinite differential
   complexity unless their derivative control is adaptive to the candidate ADE order.

The full classical routes are not refuted.  Their exact norm, positivity, spectral-measure, and arithmetic
data are absent from this counterexample.  The theorem rules out only the stated finite-Hardy-jet
substitutions.

## Attacks and boundaries

1. **Why three integrations first suffice.**  The Dirichlet series identity in (9) converges exactly for
   `s>2`; `m=3` already gives a bounded function.  Larger `m` bank additional bounded derivatives.
2. **No claim about the minimal ADE order.**  Equation (7) gives an annihilator of order at most `m+3`.
   The theorem needs only DA, not minimality.
3. **The function is bounded but not extendible.**  Absolute convergence on the closed disk gives boundary
   values; it does not give holomorphic continuation through an arc.  The `m`-th derivative remembers every
   modular cusp.
4. **This does not contradict the bounded order-`n` jet bridge.**  The constructed bounded jet stops well
   below the displayed ADE order.  The theorem proves that a depth fixed independently of ADE order cannot
   work.
5. **Disk statement only.**  No entire-function or finite-order assertion is made.

## Parent theory and novelty verdict

The ingredients are classical:

- Ramanujan's differential equations and the Chazy equation for `E_2`;
- the quasimodular transformation law of `E_2` and its singularities at rational cusps;
- the divisor-sum Dirichlet series `sum sigma_1(n)n^(-s)=zeta(s)zeta(s-1)`;
- preservation of a natural boundary under taking a finite primitive, by differentiation of any putative
  continuation.

Searches for bounded DA natural-boundary functions, iterated `E_2` primitives, Eisenstein Eichler integrals,
and finite bounded-jet natural-boundary examples did not locate this exact combined statement.  Nearby
Eichler-integral literature studies modular transformations, period polynomials, quantum modular boundary
values, and arithmetic formulas rather than the DA-versus-HT diagnostic formulated here.

Nevertheless the parent-theory gate fails.  Once `E_2` is selected, the proof is an immediate finite
integration and coefficient-summability argument.  The result closes a useful frontier and supplies a sharp
counterexample family, but it is too direct a synthesis of classical modular-form facts to count as new
scientific knowledge.  Its correct status is `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

Primary adjacent sources checked:

1. Ramanujan differential-system treatments, including the geometric account in Movasati,
   *Quasi-modular forms attached to elliptic curves I*, `arXiv:1110.3664`.
2. Standard quasimodular transformation references; the formula (3) is the defining anomaly of `E_2`.
3. Bringmann--Ono--Wagner, *Eichler integrals of Eisenstein series as q-brackets of weighted t-hook
   functions on partitions*, `arXiv:2009.07236`, as nearby modern Eichler-integral literature.

## Lean status

No complete Lean claim is made.  Stage 3 would require one theorem containing the analytic `E_2` series,
Ramanujan--Chazy identity, modular cusp transformation, divisor-sum summability, termwise derivatives,
Hardy boundedness, and natural-boundary argument.  The current tree has no such analytic modular-form stack.
Partial sequence or differentiation lemmas would not formalize this theorem.

## Gates

- [x] 0 -> 1: bounded-function frontier and finite-jet strengthening isolated
- [x] 1 -> 2: explicit unconditional construction and complete paper proof
- [x] parent-theory audit: bridge / not new scientific knowledge
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready note only if useful as part of a broader HT boundary paper

## Log

- 2026-06-24 -- Opened as the question whether `f in H^infinity` alone can coexist with DA and a
  natural boundary; finite-value quasi-Painleve branch points were proposed as a possible mechanism.
- 2026-07-11 -- Closed unconditionally by repeated primitives of `E_2`.  Strengthened from a single bounded
  DA counterexample to arbitrarily long bounded finite jets, retained the natural boundary by differentiation,
  and classified the result as a classical-parent bridge.
