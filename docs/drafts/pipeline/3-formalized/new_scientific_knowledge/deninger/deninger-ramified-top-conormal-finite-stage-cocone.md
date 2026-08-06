# Ramified top-conormal cocone on actual rational-Witt stages

- **ID:** `deninger-ramified-top-conormal-finite-stage-cocone`
- **Stage:** 3-formalized
- **Type:** BRIDGE INFRASTRUCTURE / EXACT SOURCE-SECTOR CONSTRUCTION
- **Label:** `DAC_RAMIFIED_TOP_CONORMAL_FINITE_STAGE_COCONE`
- **Parents:**
  `deninger-ramified-top-conormal-ambidexterity`,
  `deninger-calderon-witt-algebraic-source`
- **Status:** dependency-closed paper proof; Lean pending

## 1. Category mismatch exposed by hostile audit

The local ramified algebra

\[
 \mathbb C[y]/(y^k)\longrightarrow\mathbb C[x]/(x^{kn}),
 \qquad y\longmapsto x^n,
\]

does not itself occur in the existing finite rational-Witt packet system.  At prime `p`, an
actual finite source stage is

\[
 Q_s=(\mathbb Z/s\mathbb Z)^\times/\langle p\rangle,
\tag{1}
\]

and refinement `s|t` is a surjection `g_(s,t):Q_t -> Q_s`, corrected by the proved cyclotomic
gauge.  These stages contain only units.  In particular they have no ramified zero fibre, no
nilpotent local parameter, and no intrinsic final residue class.

Therefore the local theorem does **not** by itself construct the actual rational-Witt source
transport.  The minimal honest bridge is to retain the actual stage label and adjoin the forced
ramified conormal block as a separate source grade.

## 2. Actual finite-stage conormal thickening

Fix ramification degree `n>=1`.  Give the finite function spaces their counting-measure Hilbert
metrics and put

\[
 H_s=\ell^2(Q_s),
 \qquad
 \widetilde H_{s,n}=\ell^2(Q_s\times\{0,\ldots,n-1\}).
\tag{2}
\]

Define top-conormal embedding and residue

\[
 \begin{aligned}
 C_{s,n}:H_s&\longrightarrow\widetilde H_{s,n},
 &(C_{s,n}F)(q,r)&=
 \begin{cases}F(q),&r=n-1,\\0,&r\ne n-1,
 \end{cases}\\
 R_{s,n}:\widetilde H_{s,n}&\longrightarrow H_s,
 &(R_{s,n}G)(q)&=G(q,n-1).
 \end{aligned}
\tag{3}
\]

The preceding local theorem gives

\[
 C_{s,n}^\dagger=R_{s,n},\qquad
 R_{s,n}C_{s,n}=\operatorname{id},
\tag{4}
\]

and, after multiplication of both maps by `sqrt(n)`, the composite is `n id`.

## 3. Gauge-corrected refinement

For `s|t`, extend the actual gauge transition without altering ramified grade:

\[
 \widetilde g_{s,t}:Q_t\times\{0,\ldots,n-1\}longrightarrow
 Q_s\times\{0,\ldots,n-1\},
 \qquad
 \widetilde g_{s,t}(q,r)=(g_{s,t}(q),r).
\tag{5}
\]

Let `P_(s,t)` and `Ptilde_(s,t)` be pullback along `g_(s,t)` and
`gtilde_(s,t)`.  Existing arithmetic source theory proves

\[
 g_{r,s}g_{s,t}=g_{r,t}.
\]

Consequently

\[
 \widetilde P_{s,t}C_{s,n}=C_{t,n}P_{s,t},
 \qquad
 R_{t,n}\widetilde P_{s,t}=P_{s,t}R_{s,n},
\tag{6}
\]

and

\[
 \widetilde P_{s,t}\widetilde P_{r,s}=widetilde P_{r,t}.
\tag{7}
\]

Every `g_(s,t)` is surjective, so every extended pullback is injective.  Thus the thickened
finite stages form a strict directed source system rather than unrelated finite blocks.

### Proof

All identities are coordinatewise.  For `(q,r)` in the target stage,

\[
 (\widetilde P_{s,t}C_{s,n}F)(q,r)
 =\mathbf 1_{r=n-1}F(g_{s,t}(q))
 =(C_{t,n}P_{s,t}F)(q,r),
\]

which proves the first identity in `(6)`.  Evaluating at `r=n-1` proves the second.  Equation
`(7)` follows from the existing strict gauge-transition composition.  If two thickened functions
have equal pullbacks, choose a preimage of each `q in Q_s` by surjectivity of `g_(s,t)` while
retaining the same grade `r`; every coordinate was equal, proving injectivity.

## 4. Concrete admitted sector

Define

\[
 \mathcal S_{s,n}=
 \{G\in\widetilde H_{s,n}:G(q,r)=0\text{ whenever }r\ne n-1\}.
\tag{8}
\]

Then

\[
 \mathcal S_{s,n}=\operatorname{ran}C_{s,n},
\tag{9}
\]

`R_(s,n)` is injective on `S_(s,n)`, and every extended gauge pullback sends
`S_(s,n)` into `S_(t,n)`.

### Proof

Every `C_(s,n)F` has the support condition.  Conversely, for `G` satisfying `(8)`, take
`F=R_(s,n)G`; equality `C_(s,n)F=G` holds in the final grade by definition and in every other
grade by `(8)`.  If two admitted vectors have the same residue, represent both by `(9)` and use
`R C=id`.  Preservation follows from `(5)`, which leaves the grade unchanged.

## 5. Landing in the actual algebraic Calderon--Witt source

Let

\[
 j_s:\mathbb C^{Q_s}\longrightarrow P_p^{\rm alg}
\tag{10}
\]

be the already-proved injective finite-stage map into the directed algebraic rational-Witt packet.
Define

\[
 L_{s,n}=j_sR_{s,n}:\widetilde H_{s,n}\longrightarrow P_p^{\rm alg}.
\tag{11}
\]

Then:

\[
 L_{s,n}C_{s,n}=j_s,
\tag{12}
\]

`L_(s,n)` is injective on `S_(s,n)`, and the maps form a strict cocone,

\[
 L_{t,n}\widetilde P_{s,t}=L_{s,n}.
\tag{13}
\]

### Proof

Equation `(12)` is `R C=id`.  Injectivity combines injectivity of `j_s` with residue
injectivity on admitted sector.  For `(13)`, use the second identity in `(6)` followed by the
already-proved finite-stage cocone identity `j_t P_(s,t)=j_s`.

Thus the forced ramified conormal sector now lands coefficient-faithfully in the literal
algebraic source packet used by the Calderon--Witt cup.

## 6. What is and is not new

### Already known

- finite group-function pullback along a surjection is injective;
- tensoring a finite system with a fixed finite coordinate block;
- coordinate support/range identities;
- existing strict rational-Witt gauge cocone;
- local top-conormal dagger theorem.

### Candidate-new Route-L bridge

The candidate-new content is the exact synthesis forced by the category mismatch:

1. actual rational-Witt quotient labels are retained rather than replaced by a toy ramified
   algebra;
2. unique coherent top-conormal grade is adjoined before Hilbertization;
3. actual gauge-corrected refinement commutes with both conormal embedding and residue;
4. admitted sector is explicit, refinement-stable, and lands injectively in literal algebraic
   Calderon--Witt source.

This is infrastructure, not the RH theorem.

## 7. Remaining falsifier and hard frontier

The construction is the **minimal conormal thickening** of existing stages.  It does not prove
that Deninger's genuine framed rational-Witt coefficient intrinsically contains this extra grade.
A hostile model may satisfy every old unit-stage identity while refusing extension across the
nonunit Cartier boundary.

Exact remaining producer obligation is:

> Construct the top-conormal grade from the genuine finite-syntomic/framed coefficient itself,
> identify its cocone landing `(11)` with the actual Gamma/co-Poisson Xi Cartier top-conormal
> transport, and prove nonannihilation on every completed Xi top jet.

Freely tensoring the completed Xi carrier with `Fin n`, defining the grade from the desired Gamma
coefficient, or assuming source-inverse/analytic-dagger equality does not discharge this obligation.

## 8. Lean obligations

1. actual stage and ramified-stage Hilbert spaces;
2. gauge and extended gauge pullbacks;
3. strict composition and injectivity;
4. embedding/residue refinement squares;
5. admitted-sector range classification and residue injectivity;
6. coefficient-faithful cocone landing into actual algebraic packet;
7. umbrella, targeted build, axiom audit, lint.

## Log

- 2026-08-03 — hostile audit separated unit-group rational-Witt stages from ramified local
  algebra; constructed minimal strict top-conormal thickening and actual algebraic-source cocone.

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
