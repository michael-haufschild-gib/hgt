# Hellinger--Beta/Calderón--Witt relative residue obstruction

- **ID:** `hellinger-beta-calderon-witt-relative-residue-obstruction`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean) + FALSIFIED FIXED-WITNESS VECTOR REPAIR
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `hellinger-beta-copoisson-resonance-transmutation.md`;
  - `../deninger/deninger-calderon-witt-singular-gamma-transgression.md`;
  - `../../../4-publication-ready/riemann-oriented-source-admission/main.tex`.
- **RH used:** no
- **Computation used:** no
- **Lean:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittHellingerBetaRelativeResidueTransgression`

## Frontier

The scalar Hellinger correction of the critical co-Poisson Mellin vector has
nonzero reflected residues

\[
 r_n=
 \frac{\eta(-1-2n)}{-1-2n}
 \frac{\Gamma(3/2)}{(2n)!\,\Gamma(3/2-2n)}\ne0,
 \qquad n\ge0,
 \tag{1}
\]

at the half-lattice \(s_n=3/2+2n\).  The open vector-coface conjecture asked
whether these residues become boundaries before scalar Haar orientation.
That question must distinguish two notions which the scalar statement hides:

1. membership in the ambient Calderón--Witt incidence space;
2. membership in the actual Gamma/Hardy admitted incidence sector.

Only the second notion controls the relative Hodge boundary and the completed
graph domain.

Fix distinct primes \(p,q\).  Let \(w_{p,q}\) be the canonical nonzero
cross-prime Milnor-incidence witness and let

\[
       \mathcal R_{p,q,n}:=r_n w_{p,q}.
\tag{2}
\]

This is the only fixed-witness lift compatible with the normalized source
coordinate: that coordinate sends \(w_{p,q}\) to \(1\), so it must send
\(\mathcal R_{p,q,n}\) to \(r_n\).

## Exact theorem

`[PAPER-PROVED] [HELLINGER_BETA_CALDERON_WITT_RELATIVE_RESIDUE_OBSTRUCTION]`

For every \(n\ge0\), every pair of distinct primes \(p,q\), and every real
modular displacement \(a\):

1. \(\mathcal R_{p,q,n}\) is a nonzero actual Calderón--Witt Milnor
   incidence;
2. its normalized source-native incidence coordinate is exactly \(r_n\);
3. \(\mathcal R_{p,q,n}\) belongs to the concrete Gamma/Hardy admitted Hodge
   sector \(S_a\) if and only if \(a=0\);
4. regarding \(\mathcal R_{p,q,n}\) as an exterior cocycle, its canonical
   relative Gamma boundary class vanishes if and only if \(a=0\);
5. at any common depth, its actual reflection-odd boundary coordinate is
   \[
   r_n\,XiGammaOdd_a((p,e),(q,e)),
   \tag{3}
   \]
   and is nonzero whenever \(a\ne0\).

Consequently the fixed-cross-prime form of
`[VECTOR_HELLINGER_COFACE_RESIDUE_BOUNDARY]` is false.  The half-lattice
residue does land in ambient incidence, but it does not land in the admitted
relative boundary at an off-critical modular displacement.

## Proof

The scalar transmutation theorem proves \(r_n\ne0\).  The completed-incidence
comparison proves \(w_{p,q}\ne0\).  Scalar multiplication by a nonzero field
element is injective, hence `(2)` is nonzero.  Linearity of the normalized
incidence coordinate and its normalization on \(w_{p,q}\) give

\[
 \operatorname{coord}_{p,q}(\mathcal R_{p,q,n})
 =r_n\operatorname{coord}_{p,q}(w_{p,q})=r_n.
\tag{4}
\]

The admitted sector \(S_a\) is a complex submodule.  For every nonzero scalar
\(c\) and every incidence \(x\),

\[
                cx\in S_a\quad\Longleftrightarrow\quad x\in S_a.
\tag{5}
\]

The reverse implication is submodule closure.  For the forward implication,
multiply \(cx\) by \(c^{-1}\) inside the submodule.  Applying `(5)` to
\(c=r_n\) and \(x=w_{p,q}\), then using the exact cross-prime admission law,
gives

\[
 \mathcal R_{p,q,n}\in S_a
 \Longleftrightarrow w_{p,q}\in S_a
 \Longleftrightarrow a=0.
\tag{6}
\]

The exterior cup of the underlying vector of every Milnor incidence is zero,
so \(\mathcal R_{p,q,n}\) is an exterior cocycle.  The global Milnor Green
retraction fixes incidences.  Relative-contraction exactness therefore gives

\[
 [\mathcal R_{p,q,n}]_{S_a}=0
 \Longleftrightarrow
 \mathcal R_{p,q,n}\in S_a
 \Longleftrightarrow a=0,
\tag{7}
\]

which proves item 4.

Finally the actual Gamma/Hardy boundary is linear and its canonical
cross-prime coordinate reads the reflection-odd coefficient exactly.  Thus
it sends `(2)` to `(3)`.  At equal depth and distinct primes the two physical
half-heights differ.  The singular Gamma law says the second factor in `(3)`
vanishes exactly when \(a=0\); together with \(r_n\ne0\), this proves item 5.

## No-go closure

- **Exact killing mechanism:** the current vector-valued Calderón--Witt
  transport retains the packet suspension center but is diagonal in the
  Gamma-head/Hardy-tail polarization: both evaluated channels recover the
  same unsplit incidence vector.  Multiplying a fixed incidence by a nonzero
  Hellinger residue cannot change admitted-sector membership.
- **Strongest positive survivor:** the half-lattice residue family is a
  faithful source-native relative obstruction.  Each residue is an actual,
  nonzero, source-readable incidence whose relative class detects modular
  displacement exactly.
- **New insight:** successful vector repair cannot live on any fixed
  cross-prime incidence line.  Existing complete finite-cell diagonal
  rigidity strengthens this: it cannot live in any finite canonical
  prime-power-cell span.  It must be a genuinely cofinal, cell-mixing chain
  with convergence in the closed defect graph norm before any coordinate or
  Haar scalarization.
- **Status:** dependency-closed paper proof and unconditional Lean
  formalization complete. Direct Lean and targeted module build pass; axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Replacement conjecture

`[CONJECTURE] [COFINAL_HELLINGER_RESIDUE_GRAPH_BOUNDARY]`

> The Beta coface recurrence and the prime-power source current jointly
> define an infinite, source-horizon-graded incidence chain whose finite
> truncations retain all cell labels, whose reflection-odd boundaries form a
> graph-Cauchy telescoping family, and whose graph limit represents the
> completed Xi Green primitive.  The limit belongs to the admitted kernel
> without requiring any fixed residue incidence to be admitted separately.

This conjecture changes the primitive: target is not an ambient incidence
vector or closed subset, but a graph-convergent chain at infinity carrying
both source-horizon grade and head/tail polarization.  It is falsified if the
Beta/eta residue coefficients cannot satisfy the boundary telescoping law or
if the graph norm of every such labelled chain diverges.

## Rediscovery and novelty audit

- Local corpus search found the analytic residue theorem, fixed-witness
  admission classification, relative contraction law, completed incidence
  coordinate, and finite-cell rigidity separately.  It found no theorem
  identifying the Hellinger residue lift with the relative Gamma boundary
  class.
- Burnol's co-Poisson/Sonine work supplies reflected Mellin constraints and
  evaluator spaces, but not Calderón--Witt incidence or this relative
  residue class.
- Deninger-style cohomological literature motivates a source cohomology but
  does not contain this explicit Hellinger-residue/cross-prime-incidence
  calculation.
- Targeted primary-source searches found no exact statement.  Priority and
  broader novelty remain unverified.

Primary sources checked:

- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007),
  525--602, DOI `10.5802/aif.2268`.
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros
  of the Riemann zeta function*, JTNB 16 (2004), 65--94,
  DOI `10.5802/jtnb.434`.
- C. Deninger, *A dynamical systems analogue of Lichtenbaum's conjectures on
  special values of Hasse--Weil zeta functions*, arXiv:`math/0605724`.

## Gates

- [x] fixed-witness vector statement frozen and hostile-tested
- [x] exact paper theorem and proof
- [x] positive survivor extracted
- [x] local corpus audit
- [x] preliminary primary-literature audit
- [x] exact Lean formalization
- [ ] graph-boundary replacement conjecture attacked

## Log

- 2026-08-02 — fixed-witness vector repair falsified; relative residue
  obstruction and cofinal graph-boundary survivor extracted.
