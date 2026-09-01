# Range-relative Pluecker determinant-line formation law

- **ID:** `ULF-RDPD-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Evans/Gram/Pluecker no-go, determinant-line duality, and exterior-power
  functoriality exposed by corpus audit
- **Statement:** Every injective finite-rank formation map canonically factors its top exterior map
  through a one-dimensional determinant line of its actual range; the ambient Pluecker vector is the
  image of that line's nonzero generator, even when the ambient exterior target has dimension
  greater than one.
- **Status:** `[PROVED HERE] [UNCONDITIONAL] [NOT RH] [LEAN CERTIFIED]`

## 1. Big-picture higher law

Scalar routes do not see the formation object itself. They see gauges of a moving line.

For a finite-rank formation map (F:V\to W), the relevant carrier is not the generally
high-dimensional space (\bigwedge^d W). It is the range-relative line

\[
  \mathcal D_F:=\bigwedge^d(\operatorname{im}F),
  \qquad d=\dim V,
\]

together with its canonical inclusion into (\bigwedge^d W). A frame, determinant, Gram energy,
phase, or route scalar is a local gauge or quotient of this line. The line survives changes of
presentation; a scalar does not. In particular, positivity records a norm squared on
(\mathcal D_F) and therefore quotients its phase/orientation.

This changes the proposed universal mechanism. Selection should not be sought as another scalar
reporter. It should be sought as a source-forced statement about transport and holonomy of the
range determinant line through formation and completion.

## 2. Corpus audit before theorem

- `RHTower.CCMEvansDeterminantLine` correctly proves that
  (\bigwedge^d\mathbb C^{d+3}) has dimension (\binom{d+3}{d}>1), so the whole ambient exterior
  target is not a line and has no canonical scalarization.
- The same module proves that Gram determinant is unchanged when one source vector is negated while
  the Pluecker vector changes sign. Thus Gram positivity forgets orientation.
- `HTGeometry.ComplexGramPlucker` proves that the Gram determinant is the squared Pluecker norm and
  that the Pluecker vector is nonzero exactly for an injective presentation.
- `HTGeometry.DeterminantLine` proves that the top exterior power of a finite free module is
  one-dimensional.
- `HTGeometry.ExteriorPowerDirectLimit` proves that exterior power preserves injectivity over a
  field.
- `RHTower.ArithmeticXiStokesCentralRankPort` already identifies a literal Xi cyclic residue with
  determinant central holonomy minus identity and proves its vanishing is exactly critical-line
  support. It explicitly labels this a classifier, not global vanishing.
- `RHTower.DeningerExponentGammaSixShellTransportRigidity` proves the two-sheet exceptional
  reflection coefficient is a gauge coboundary; reflection covariance alone has no invariant
  horizontal holonomy. Its surviving invariant uses mixed reflection--Wold transport.
- `HTGeometry.ConstitutiveRecoveryCocycleHolonomy` classifies finite recovery gauges by cycle
  holonomy. Finite local transport algebra does not generate global vanishing.
- Corpus search found no theorem constructing the determinant line of the actual range and
  factoring the ambient Pluecker map through it.

The ambient dimension obstruction is valid. The further sentence “the Pluecker vector is not a
section of a determinant line” is too strong: it confuses the ambient exterior target with the
top exterior power of the image subspace.

## 3. Coordinate-free construction

Let (K) be a field, let (V) be a finite-dimensional (K)-vector space of dimension (d), let
(W) be a (K)-vector space, and let (F:V\to W) be injective. Write

\[
  R_F=\operatorname{im}F,
  \qquad
  q_F:V\to R_F,
  \qquad
  j_F:R_F\hookrightarrow W,
\]

where (q_F(x)=F(x)) with codomain restricted to the range. Then (F=j_F\circ q_F), (q_F) is
an isomorphism, and (j_F) is injective. Define

\[
  \mathcal D_F=\bigwedge^d R_F,
  \qquad
  Q_F=\bigwedge^d q_F,
  \qquad
  J_F=\bigwedge^d j_F.
\]

## 4. Main theorem

**Theorem 4.1 (range-relative determinant-line factorization).** With the data above:

1. (\dim_K R_F=d) and (\dim_K\mathcal D_F=1).
2. (Q_F:\det(V)=\bigwedge^dV\to\mathcal D_F) is an isomorphism.
3. (J_F:\mathcal D_F\to\bigwedge^dW) is injective.
4. The top exterior formation map has the exact factorization

   \[
     \bigwedge^dF=J_F\circ Q_F. \tag{RDF}
   \]

Hence (\operatorname{im}(\bigwedge^dF)=J_F(\mathcal D_F)) is a canonical line in
(\bigwedge^dW), independent of any basis of (V).

**Proof.** Injectivity of (F) makes (q_F) injective; its definition makes it surjective. Thus
(q_F) is an isomorphism and (\dim R_F=\dim V=d). The exterior dimension formula gives

\[
  \dim\mathcal D_F=\binom{\dim R_F}{d}=\binom dd=1.
\]

Exterior power is functorial and sends an isomorphism to an isomorphism, so (Q_F) is an
isomorphism. Over a field, exterior power preserves injective linear maps; hence (J_F) is
injective. Finally (F=j_F\circ q_F), and functoriality gives (RDF). The image of an isomorphism
followed by (J_F) is exactly (J_F(\mathcal D_F)), which is one-dimensional and defined solely
from (F). ∎

## 5. Frame form and gauge covariance

Let (v=(v_1,\ldots,v_d)) be a linearly independent family in (W), and let (F_v:K^d\to W)
be its synthesis map. Its range determinant line is (\mathcal D_v=\mathcal D_{F_v}). If
(\widetilde v_i\in R_{F_v}) denotes the same vector with range membership, define

\[
  \omega_v=\widetilde v_1\wedge\cdots\wedge\widetilde v_d\in\mathcal D_v.
\]

**Corollary 5.1 (Pluecker reconstruction).** The vector (\omega_v) is nonzero, spans
(\mathcal D_v), and

\[
  J_{F_v}(\omega_v)=v_1\wedge\cdots\wedge v_d.
\]

Thus the ordinary ambient Pluecker vector is exactly the included range-line generator.

**Proof.** The source basis wedge is nonzero and (Q_{F_v}) is an isomorphism, so its image
(\omega_v) is nonzero. Since (\mathcal D_v) has dimension one, (\omega_v) spans it. Equation
(RDF) evaluated on the source basis wedge gives the displayed identity. ∎

**Corollary 5.2 (gauge transition character).** If (A:V\to V) is an automorphism, then
(R_{F\circ A}=R_F), and under this literal equality of range lines the canonical top formation
maps differ by the determinant character:

\[
  Q_{F\circ A}=Q_F\circ\bigwedge^dA,
  \qquad
  \bigwedge^dA=(\det A)\,\mathrm{id}_{\det(V)}.
\]

**Proof.** Surjectivity of (A) gives (\operatorname{im}(F\circ A)=\operatorname{im}F).
Functoriality gives the first identity. The standard top-exterior determinant theorem gives the
second. ∎

Consequently frames are local gauges and determinant is their transition character. The line is
coordinate-free; a scalar coordinate requires a trivialization.

## 6. Positivity is a phase quotient

For complex coordinate targets, `ComplexGramPlucker` gives

\[
  \det(F_v^*F_v)=\|J_{F_v}(\omega_v)\|^2.
\]

Replacing one frame vector by its negative multiplies (\omega_v) and its ambient image by
(-1), but leaves this squared norm unchanged. More generally, multiplication by a unit complex
phase is invisible to the norm squared. Gram positivity therefore observes the Hermitian metric on
the range determinant line modulo phase; it is not the determinant-line carrier itself.

## 7. Exact RH closure interface

This theorem does not prove RH. It replaces a false carrier-level obstruction with a precise open
law. Existing determinant-holonomy modules already prove that the relevant scalar defect is a
critical-line classifier; rebuilding that classifier on the corrected carrier would not add
selection.

Corpus already proves a source-forced horizontal charge whose global vanishing is equivalent to RH.
To close RH using the present geometry, one must construct from literal pre-divisor arithmetic:

1. a cofinal formation system (F_I) whose range determinant lines (\mathcal D_{F_I}) carry all
   route presentations as local trivializations;
2. canonical transition maps induced by source refinement and functional-equation formation;
3. an equality identifying their scalar holonomy character with the existing source-forced
   horizontal charge; and
4. an unconditional source-completion theorem forcing that holonomy to be trivial.

Then trivial holonomy forces horizontal charge zero, and the existing theorem
`xiSourceForcedHorizontalVanishing_iff_riemannHypothesis` closes RH. Step 4 is the new selection
obligation. It must be proved from literal source execution; choosing a trivialization or assuming
flatness would merely insert RH. Because every globally framed finite line has coboundary transition
data, the needed obstruction cannot be ordinary finite gauge holonomy. It must occur in cofinal or
singular gluing, rank-changing relative determinant transport, or failure of a global nonvanishing
section, and then be killed by a source theorem.

## 8. Scope and non-circularity

- Theorem 4.1 and Corollaries 5.1--5.2 are unconditional finite-dimensional linear algebra.
- No Xi zero, RH-equivalent bound, positivity assumption, compactness, recurrence, or selected
  trivialization occurs in the proof.
- Ambient non-linearity remains true; only the inference from ambient non-linearity to absence of a
  canonical range line is rejected.
- This law supplies a universal carrier and exact factorization, not yet the arithmetic holonomy
  theorem that would narrow Xi occurrence.

## 9. Lean plan

Module `GaloisForLFunctions.HTGeometry.RangeDeterminantFormation` formalizes the range determinant
carrier, one-dimensionality under injectivity, canonical source--range equivalence, injective
ambient inclusion, exact exterior-formation factorization, canonical range generator, exact
Pluecker reconstruction, generator spanning, and equality between the embedded carrier and ambient
Pluecker line. It also proves that a source gauge change acts through its determinant character.
Direct compile and targeted module build pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-09-01 — corpus audit completed; range-relative correction identified; dependency-closed paper
  proof completed.
- 2026-09-01 — Lean module completed, wired into `HTGeometry`, direct check and targeted module build
  passed, axiom audit closed.
- 2026-09-01 — determinant-holonomy hostile audit completed; finite-line selection use retired;
  cofinal/singular rank-changing gluing isolated as next admissible location of obstruction.
