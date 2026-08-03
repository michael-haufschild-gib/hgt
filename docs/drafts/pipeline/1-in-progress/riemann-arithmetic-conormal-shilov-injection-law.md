# Arithmetic conormal Shilov-socle law

- **ID:** `riemann-arithmetic-conormal-shilov-socle-law`
- **Stage:** `1-in-progress`
- **Type:** UNIVERSAL SUPPORT THEOREM + FROZEN ARITHMETIC SOURCE LAW
- **Status:** `[UNIVERSAL CONSUMER PAPER-PROVED] [SOURCE LAW OPEN] [NOT RH]`
  `[NO DIVISOR-SELECTED METRIC] [NOVELTY UNVERIFIED]`
- **Lean:** none until the source comparison is constructed on paper
- **Parents:**
  - `../4-publication-ready/riemann-boundary-completeness-law/main.tex`;
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `singular-infinite-source-pointed-common-test-factorization.md`;
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../2-fully-proven/new_scientific_knowledge/other/primitive-fibre-modular-renormalization-law.md`.

## Result

The missing assertion is not that every modular character is unitary, and it is not the
pointwise statement that every horizontal divisor defect vanishes.  It is one source-level
support law.

Let

\[
 G=\mathbb Q_{>0}^{\times}=\bigoplus_{p\ {m prime}}\mathbb Z,
 \qquad
 A=C^*(G)=C(\widehat G),
 \tag{1}
\]

and write $u_g\in A$ for the canonical unitary attached to $g\in G$.  Let
\(\mathcal N_\Xi^{\rm src}\) be the algebraic principal-conormal cohomology of the completed
Euler--Gamma/co-Poisson source, with its centered rational-dilation action.  This module is
defined before choosing or enumerating a zero.  The existing continuation and noncensoring
theorems imply that a divisor point \(\rho\) of multiplicity \(m_\rho\) contributes a nonzero
primary jet packet on which, for every $g\in G$,

\[
 \bigl(g-g^{\rho-1/2}\bigr)^{m_\rho}=0.
 \tag{2}
\]

More sharply, the top local class $(s-\rho)^{m_\rho-1}$ is nonzero and satisfies the exact
eigenrelation

\[
 g\,(s-\rho)^{m_\rho-1}
   =g^{\rho-1/2}(s-\rho)^{m_\rho-1}.
 \tag{2a}
\]

Indeed, locally the action is multiplication by
$g^{s-1/2}=g^{\rho-1/2}\exp((s-\rho)\log g)$, and every positive power of
$(s-\rho)$ beyond degree $m_\rho-1$ vanishes.  Thus multiplicity produces a generalized
primary packet but always leaves one exact character line: its socle.  The exponent in
`(2)`--`(2a)` is the centered conormal character, not an assumed spectral normalization.

The arithmetic coefficient source supplies the Wold--Toeplitz extension

\[
 0\longrightarrow \mathfrak J_\Gamma
 \longrightarrow \mathfrak T_\Gamma
 \longrightarrow A\longrightarrow0.
 \tag{3}
\]

Its regular anomaly is the exact polarized Gamma determinant cocycle.  Its singular anomaly is
the exact BV/co-Poisson first-trace conormal with coefficient $1-q^{-1}$.  A plain boundary
$A$-module kills both anomalies, so the comparison must be formed in a source-normal relative
Rees totalization of `(3)` before taking boundary cohomology.

> **[FROZEN SOURCE LAW -- ARITHMETIC CONORMAL SHILOV-SOCLE CONSERVATIVITY]**
>
> The actual Wold--Gamma determinant and BV/co-Poisson first-trace classes define, without
> divisor specialization, a canonical centered-$G$-equivariant chain comparison from the
> completed arithmetic conormal complex to a singular source-normal relative Rees totalization
> of `(3)`.  Its boundary cohomology \(\mathcal H_{\rm Sh}^{\rm src}\) is a unital
> $A=C^*(G)$-module, and the induced map
>
> \[
> \boxed{
> \jmath_{\rm src}:\mathcal N_\Xi^{\rm src}
>       \longrightarrow
>       \mathcal H_{\rm Sh}^{\rm src}}
> \tag{ASSC}
> \]
>
> satisfies
>
> \[
> \boxed{
> \ker\jmath_{\rm src}\cap
> \operatorname {Soc}_{G}(\mathcal N_\Xi^{\rm src})=0.}
> \tag{10}
> \]
>
> Here \(\operatorname {Soc}_{G}(N)\) is the sum of the one-dimensional
> \(\mathbb C[G]\)-submodules of $N$.

`(ASSC)` is the requested independent arithmetic source law.  It contains no \(\rho\), no zero
location, no Weil sign, no divisor-indexed norm, and no assertion that arbitrary modular
characters are unitary.  Its inputs are the integral prime-valuation source, the actual Wold
ideal, the Gamma determinant anomaly, the BV first-trace anomaly, and the distinguished
co-Poisson conormal section.  Divisor points enter only after `(ASSC)`, by taking the support of
the already constructed source module.

The map is not required to be injective.  Its kernel may be large, dense in weaker topologies,
or maximally vertical away from the algebraic character socle.  The law forbids one loss only:
erasure of an exact source character line.  This is the weakest conservation statement that can
still detect horizontal displacement.

## Universal theorem: Shilov support from socle conservativity

**Theorem.**  Let $G$ be a discrete abelian group, $A=C^*(G)$, $N$ a
\(\mathbb C[G]\)-module, and $M$ a unital $A$-module.  Suppose

\[
 j:N\longrightarrow M,
 \qquad
 \ker j\cap\operatorname {Soc}_G(N)=0
 \tag{4}
\]

is a \(\mathbb C[G]\)-module map.  If $0\ne v\in N$ and, for a character
\(\lambda:G\to\mathbb C^\times\),

\[
 gv=\lambda(g)v
 \quad\text{for every }g\in G
 \tag{5}
\]

then

\[
                         |\lambda(g)|=1
 \quad\text{for every }g\in G.
 \tag{6}
\]

**Proof.**  Fix $g$.  If \(|\lambda(g)|\ne1\), then the function

\[
                  u_g-\lambda(g)\in C(\widehat G)
\]

has no zero because \(|u_g(\chi)|=1\) for every \(\chi\in\widehat G\).  Hence it is invertible
in $A$.  Equivariance and `(5)` give

\[
 (u_g-\lambda(g))j(v)=0.
\]

Invertibility forces $j(v)=0$.  The character line \(\mathbb Cv\) lies in
\(\operatorname {Soc}_G(N)\), so `(4)` forces $v=0$, a contradiction.  Thus
\(|\lambda(g)|=1\).  Since $g$ was arbitrary, `(6)` follows. \(\square\)

This theorem covers multiple zeros because every primary jet packet has the nonzero exact
eigenline `(2a)`.  Lower jets may be erased.  No simplicity premise and no faithfulness away from
the socle are used.

## Riemann consequence

Assume `(ASSC)`.  Take the nonzero top conormal class `(2a)` at a nontrivial Xi divisor point
\(\rho\).  Apply the universal theorem to

\[
                         \lambda_\rho(g)=g^{\rho-1/2}.
 \tag{7}
\]

For one rational prime $p$,

\[
 1=|\lambda_\rho(p)|=p^{\Re\rho-1/2},
\]

and therefore \(\Re\rho=1/2\).  The source-derived horizontal parameter and the faithful
Gamma/co-Poisson defect already satisfy

\[
 a_\rho=2(\Re\rho-1/2),
 \qquad
 D_\rho=0\iff a_\rho=0.
 \tag{8}
\]

Consequently

\[
 \boxed{\forall\rho,\ D_\rho=0},
 \tag{9}
\]

and the Riemann hypothesis follows by the existing horizontal-vanishing frontier theorem.

The implication is short because the corpus has already constructed and proved faithful every
reporter in `(8)`.  All new mathematical burden is `(ASSC)`.

## Why this is sharper than prime-Schwartz temperedness

Prime-Schwartz temperedness says directly that every conormal jet has polynomial growth on every
bilateral valuation lattice.  In the natural analytic quotient that statement is already
equivalent to RH.  `(ASSC)` moves one level upstream:

1. no growth condition is imposed on any divisor character;
2. the source module is required to enter a boundary category whose character spectrum is
   independently fixed by the arithmetic group $G$;
3. unitary support is then a theorem of the target category, not a premise on the source fibres;
4. the comparison is constrained by the two actual anomaly readings, so an arbitrary map into a
   convenient $A$-module is forbidden;
5. no global embedding is demanded: only exact character lines must survive.

Thus the missing producer is **socle-conservative anomaly descent to the arithmetic Shilov
boundary**.
Temperedness, two-way contractivity, common-test positivity, and horizontal vanishing are its
different shadows.

## Corpus-wide shadow laws

`(ASSC)` explains the current positive and negative results in one statement.

1. **Wold--Poisson ancestry.**  Quotienting the Wold ideal gives the independently fixed group
   boundary $C^*(G)$.  This is where unitary prime characters live.
2. **Gamma/BV unity.**  The regular determinant and singular first trace are two readings of the
   same relative class; retaining only one does not define the comparison.
3. **Hedenmalm dense radicals.**  Haar scalarization of $C^*(G)$ erases point fibres.  Hence a
   scalar $L^2$ completion cannot realize `(ASSC)`.  Dense radicals elsewhere are permitted.
4. **Maximal vertical completion.**  Product-coordinate closed relations forget every output,
   including the socle.  `(ASSC)` requires a finer topology only on the exact character lines;
   it does not demand globally informative transport.
5. **Finite-Rees no-go.**  Off-line reflected valuation sectors have exponential bilateral
   growth, so no finite-order graded sewing can induce `(ASSC)`.
6. **Gamma whitening divergence.**  Fisher whitening completes occupancy, not the primitive
   conormal.  The unnormalized anomaly must be retained before the source-normal blow-up.
7. **Sonin/Calkin and four-unit Ward consumers.**  These become valid scalar consequences after
   Shilov landing; they cannot construct the socle-conservative landing map.
8. **Krein common-test obstruction.**  Primewise reflected interval cells are indefinite.  The
   Rees comparison must cancel the negative sector globally before positive boundary
   scalarization.
9. **Hypertranscendental persistence.**  Adjoining all scalar valuation layers preserves the
   differential matroid.  `(ASSC)` changes support category rather than seeking a finite
   differential-algebraic relation.
10. **No blanket unitarity.**  Algebraic characters of $G$ with nonunit modulus remain valid.
    They are excluded only from exact character lines retained by the arithmetic
    $C^*$-boundary.

## Hostile audit

### 1. Is `(ASSC)` merely RH renamed?

An arbitrary socle-separating map chosen after inspecting the Xi divisor would be exactly that.  It is
prohibited.  The law is scientifically independent only if the chain comparison is constructed
from `(3)` and its two fixed anomaly readings before passing to divisor support.  The comparison
must commute with prime enlargement, source reflection, Wold renewal, and change of a
noncensoring BV window.  Those requirements are falsifiable at finite source stages.

In the actual Xi source, existence of some map with the conclusion of `(ASSC)` is expected to be
RH-equivalent.  The frontier advance is not a weaker logical reformulation; it is identification
of the minimal source construction whose independent proof would force RH.  No claim of an RH
proof is made until that construction and socle conservativity are proved.

### 2. Why not use the plain $A$-module boundary?

Every representation factoring through $A$ kills $Q$, every Wold projection $E_p$, the
Gamma determinant defect, and the BV first-trace density.  A plain boundary map has therefore
forgotten the source evidence it is supposed to transport.  The relative Rees totalization in
`(ASSC)` is mandatory, not decoration.

### 3. Why not infer socle conservativity from algebraic exactness?

The coefficient Wold complex is already split exact.  Algebraic contraction carries no Xi
information.  Socle conservativity can arise only after coupling that contraction to the
completed co-Poisson constraint and proving non-erasure of its exact character lines in the
singular source-normal topology.

### 4. Why not infer it from positivity or bounded CP continuation?

The corpus proves ordinary bounded CP continuation has the wrong divisor order, and the local
reflected interval kernel has a negative two-point determinant.  Any valid CP object must be a
division-free Rees correspondence on unnormalized numerator/mass data; positivity may appear
only after global anomaly cancellation.

### 5. Countermodel test

A generalized-prime source with an off-line character may reproduce functional equation,
reflection, local Gamma factors, finite Wold identities, and algebraic conormal covariance.  It
cannot satisfy `(ASSC)`: the universal theorem would make its nonunitary socle line zero.
Thus the law uses more than the known local package and survives the Beurling firewall.

## Exact open core

Construct one chain-level object, not another reporter:

\[
 \boxed{
 \text{source Wold--Toeplitz extension}
 \xrightarrow{\ \text{Gamma determinant + BV first trace}\ }
 \text{relative source-normal Rees totalization}
 \xleftarrow{\ \jmath_{\rm src}\ }
 \text{completed co-Poisson conormal complex}}
 \tag{11}
\]

and prove:

1. the two anomaly formulas are the regular and singular boundary values of one chain class;
2. the comparison exists before divisor specialization and is independent of prime exhaustion;
3. its boundary cohomology carries the unital $C^*(G)$-action;
4. its kernel misses the algebraic $G$-character socle;
5. for each multiplicity packet it retains the top exact character line, without a
   divisor-selected norm.

Clause 4 is the load-bearing theorem.  Clauses 1--3 prevent it from being a renamed
temperedness assumption; clause 5 prevents a simple-zero truncation.  Full injectivity is not a
gate: hostile review shows it is stronger than the Riemann consequence requires and needlessly
collides with the corpus's dense-radical and maximal-vertical no-go results.

## Gates

- [x] source law stated without divisor variables
- [x] exact-socle Shilov-support theorem proved on paper
- [x] deduction `(ASSC) -> forall rho, D_rho=0 -> RH` proved on paper
- [x] bounded, plain-module, scalar-Hilbert, finite-Rees, and divisor-GNS shortcuts excluded
- [x] overpowered full-injectivity candidate retired
- [ ] construct relative Rees totalization from actual source complexes
- [ ] identify Gamma determinant and BV first trace as one chain class
- [ ] construct canonical comparison `j_src`
- [ ] prove conormal-socle conservativity
- [ ] prove presentation and prime-exhaustion independence
- [ ] run independent hostile mathematical review
- [ ] formalize only after the complete source proof exists
- [ ] RH
