# Source-change reports are one exact path cocycle, not new particle indices

- **ID:** `source-defect-path-cocycle-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / REPORTER-INDEX NO-GO / NOT NEW MATHEMATICS
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NO PHYSICS PROVED]`
- **Parent:** `projective-source-visibility-parity-law.md`
- **Live conjecture:** `../../1-in-progress/composition-curvature-universal-law.md`
- **Retired shortcut:** `../../5-failed/source-reporter-counts-are-particle-indices.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SourceDefectPathCocycle.lean`

## Question

The minimal projective binary source has four classical labels
\[
\{1,A,B,AB\},
\]
two source-defect reporters, and a two-dimensional irreducible projective sector. Their raw
cardinalities suggest \(4\times2\times2\), superficially resembling a Pati--Salam family:
four colours including the lepton, a weak doublet, and a Weyl-spinor doublet.

Are these three independent indices?

No. The reporter and square-label counts were being confused with independent state
multiplicities.

## Exact path-cocycle law

Let \(K\) be a field, \(V\) a \(K\)-vector space, and \(A,B:V\to V\) linear. Define
\[
D_A=1-A.
\tag{SD.1}
\]

### Theorem 1

`[PROVED HERE]`

\[
\boxed{D_{AB}=D_A+A D_B.}
\tag{SD.2}
\]

Also \(D_1=0\).

### Proof

For every \(v\in V\),
\[
D_Av+A D_Bv=(v-Av)+A(v-Bv)=v-ABv=D_{AB}v.
\]
The identity formula is immediate. \(\square\)

Equation `(SD.2)` is the standard \(1\)-cocycle equation. More precisely, \(A\mapsto1-A\) is an
exact operator-valued cocycle: the negative of the coboundary of the identity operator under left
composition.

## Cocycle failure is exactly path curvature

For a comparison triangle \(A,B,C\), define
\[
\mathcal K_D(A,B;C)=D_A+AD_B-D_C.
\tag{SD.2a}
\]

### Theorem 2

`[PROVED HERE]`

\[
\boxed{\mathcal K_D(A,B;C)=C-AB.}
\tag{SD.2b}
\]

If path closure is projective,
\[
AB=\zeta C,
\tag{SD.2c}
\]
then
\[
\boxed{\mathcal K_D(A,B;C)=(1-\zeta)C.}
\tag{SD.2d}
\]

### Proof

Substitute `(SD.2)` into `(SD.2a)`:
\[
\mathcal K_D=D_{AB}-D_C=(1-AB)-(1-C)=C-AB.
\]
Equation `(SD.2d)` follows from `(SD.2c)`. \(\square\)

Thus exact change reports and comparison holonomy are not separate constructions. The first
fails by exactly the second. In the projective case, quantum phase is the central residual of that
failure. This is still elementary parent algebra, not a derivation of physical quantumness.

## Every path defect telescopes

For an ordered word \(w=A_1A_2\cdots A_n\), repeated use of `(SD.2)` gives
\[
D_w=
D_{A_1}+A_1D_{A_2}
+A_1A_2D_{A_3}
+\cdots+
A_1\cdots A_{n-1}D_{A_n}.
\tag{SD.3}
\]

### Theorem 3

`[PROVED HERE]`

Equation `(SD.3)` holds for every finite word of linear source changes.

### Proof

Induct on word length. The empty word is `(SD.1)` for the identity. The successor step is exactly
`(SD.2)`. \(\square\)

Thus adding longer path labels does not create independent reporter sectors. It creates transported
combinations of generator defects.

## Exact square-report factorization

Define the paired generator report
\[
\Delta_{A,B}(v)=(D_Av,D_Bv)
\tag{SD.4}
\]
and full square-label report
\[
\Sigma_{A,B}(v)=
\bigl((D_1v,D_Av),(D_Bv,D_{AB}v)\bigr).
\tag{SD.5}
\]

Define
\[
L_A(x,y)=\bigl((0,x),(y,x+Ay)\bigr).
\tag{SD.6}
\]

### Theorem 4

`[PROVED HERE]`

\[
\boxed{\Sigma_{A,B}=L_A\Delta_{A,B}.}
\tag{SD.7}
\]

The map \(L_A\) is injective. Consequently,
\[
\boxed{
\Sigma_{A,B}\text{ is injective}
\iff
\Delta_{A,B}\text{ is injective}.
}
\tag{SD.8}
\]

### Proof

Equation `(SD.7)` is \(D_1=0\) and `(SD.2)` written in product coordinates. The second and third
coordinates of \(L_A(x,y)\) are \(x\) and \(y\), so \(L_A\) is injective. Factorization then proves
`(SD.8)`. \(\square\)

If \(AB=\zeta BA\) with \(\zeta\ne1\), the existing projective-source visibility theorem makes
\(\Delta_{A,B}\) injective. The full four-label report is therefore injective too—but only because
it factors through the already-injective two-generator report.

## The \(4\times2\times2\) shortcut is occupied and false

The physical count is not novel even before the algebraic failure. Pati--Salam theory already
unifies leptons with quarks as four colours under
\(SU(4)\times SU(2)_L\times SU(2)_R\). One family occupies
\((2,1,4)\oplus(1,2,4)\); this is the familiar sixteen-state pattern. See
[Chamseddine--Connes--van Suijlekom](https://arxiv.org/abs/1304.8050) and
[Pati](https://arxiv.org/abs/1706.09531).

Spin(10) already places one generation in a single irreducible Weyl-spinor \(16\), and its
Pati--Salam subgroup is \(Spin(6)\times Spin(4)\). Pure-spinor pairs provide a modern geometric
construction of that subgroup; see [Krasnov](https://arxiv.org/abs/2209.05088).

Therefore a \(4\times2\times2\) count, without a source-only representation law, would be old
Pati--Salam/Spin(10) representation theory plus numerology.

## Strongest positive survivor

The failure changes the research target:

> **Change reports are exact. Physical force cannot be an index counting those reports. Genuine
> content must begin where source changes fail to compose strictly.**

This is not yet a physical theorem. It is an exact filter on candidate theories:

```text
source labels and defect reporters
  -> exact path cocycle
  -> no new particle multiplicity;

failure of strict/projective composition
  -> possible nontrivial 2-cocycle or curvature;

failure to glue public causal anchors
  -> possible gravitational curvature;

failure of all finite reporter closures
  -> possible Hypertranscendental higher history.
```

The first line is proved. The later identifications remain conjectural.

## Parent audit

The cocycle equation itself is standard. For a representation \(\pi\), a \(1\)-cocycle satisfies
\(b(gh)=b(g)+\pi(g)b(h)\); coboundaries are \(b(g)=\pi(g)v-v\). See, for example,
[Bekka](https://arxiv.org/abs/1612.08944). Equations `(SD.1)`--`(SD.3)` are the operator-valued
exact specialization.

No novelty is claimed for the algebra. Candidate novelty can only begin with a source-generated
positive higher completion that forces a nontrivial composition obstruction and then uniquely
selects its physical projections.

## Lean status

Unconditional declarations:

- `sourceChangeDefect_id`;
- `sourceChangeDefect_comp`;
- `sourceDefectTriangleCurvature_eq_pathDefect`;
- `sourceDefectTriangleCurvature_projective`;
- `sourceChangeDefect_word`;
- `sourceSquareDefectReport_factorization`;
- `sourceSquareDefectReport_injective_iff`; and
- `sourceSquareDefectReport_injective_of_projective`.

No physical premise occurs in their statements.

## Hostile-review audit

- **Independent-index claim:** fails. Exact factorization `(SD.7)` kills it.
- **Identity-channel claim:** fails. \(D_1=0\).
- **Composite-channel claim:** fails. \(D_{AB}=D_A+AD_B\).
- **Pati--Salam novelty:** fails. The target count and representation pattern are established.
- **New mathematics:** fails at this level. This is a standard exact cocycle.
- **Physics derivation:** fails/open. No force, particle, spacetime, or dynamics is selected.
- **Positive survivor:** pass. Nontrivial physics must be sought in composition obstruction or
  higher curvature, not reporter cardinality.
