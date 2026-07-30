# Hedenmalm--Weil chiral aperture law

- **ID:** hedenmalm-weil-chiral-aperture
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** full Xi/HGT/HTGeometry/HilbertMetric corpus synthesis
- **Statement:** Critical-line reflection is a fundamental symmetry that anticommutes with signed
  transverse displacement; its orbitwise chiral doublets carry the complete off-critical
  obstruction, while their maximal transverse eigenvalue is the common spectral aperture.

## Goal

Replace collections of RH equivalences and route-specific no-gos by one structural theorem whose
projections explain them.  On the multiplicity-exact Xi divisor Hilbert space let

\[
  (Jv)(q)=v(Jq),\qquad
  (Av)(q)=\Im(\lambda_q)v(q),\qquad
  Q(v)=\operatorname{Re}\langle Jv,v\rangle ,
\]

where \(\lambda_q=(\rho_q-\tfrac12)/i\).  Prove unconditionally:

1. \(J^2=1\), \(J\) is isometric, and \(JA=-AJ\);
2. \(v=v_++v_-\), \(v_\pm=(v\pm Jv)/2\), with
   \(Q(v)=\|v_+\|^2-\|v_-\|^2\);
3. every free reflection orbit is a two-dimensional chiral/Witt block; critical-line fixed
   orbits are positive blocks;
4. \(A\) has orbit eigenvalues \(\pm|\Re\rho-\tfrac12|\), and
   \(\|A\|\) is the projective/Hurwitz/Poisson aperture;
5. \(A^2\) commutes with \(J\), precisely formalizing orientation loss under squaring;
6. the canonical Hurwitz orientation vector lies in the negative sector and is reconstructed by
   prime--Gamma Cauchy source packets.

RH is therefore absence of the transverse chiral operator, not an unexplained positivity slogan.

## Why this is a universal reinterpretation

- Hedenmalm's differential pair is symmetric for the canonical completed Weil form; positivity
  asks whether its source-generated states avoid the negative chiral sector.
- Hurwitz monodromy supplies a canonical trace-class negative-sector vector, not decorative phase
  notation.
- Prime--Gamma Cauchy packets reconstruct that vector, so the negative sector is source-visible.
- Poisson exponential type is the norm/support radius of transverse displacement.
- The \(8\pi\) Ward index counts free chiral blocks but contains no eigenvalue bound.
- Julia squaring and other even scalarizations replace \(A\) by \(A^2\), retaining support while
  erasing which reflection leg carries the sign.
- finite windows and jets are compact projections and may miss negative mass escaping to height;
  aperture is the operator-level invariant that survives.
- hypertranscendental differential independence changes analytic coordinates but cannot alter
  the common divisor operators \(J\) and \(A\).

## Approach

1. Prove abstract reflection/transverse algebra and orbit blocks on the existing divisor
   \(\ell^2\) carrier.
2. Identify the negative fiber vector as a Cauchy-source closure vector and compute its exact Weil
   square.
3. identify transverse spectral radius with the existing projective aperture.
4. Transport the canonical Hurwitz orientation reconstruction into this chiral language.
5. Audit exact novelty against Krein-space, Weil-criterion, de Branges, complex-spectral, and
   Hedenmalm literature.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, corpus shadows identified
- [ ] 1 → 2 fully-proven: paper proof dependency-closed
- [ ] 2 → 3 formalized: exact theorem module, foreground Lean pass, axiom/lint audit
- [ ] 3 → 4 publication-ready: standalone manuscript, claim trace, literature audit, hostile review

## Hostile tests

- [ ] Is the chiral anticommutation more than standard Krein linear algebra once specialized to Xi?
- [ ] Does the theorem yield a genuinely new source-side research program rather than another RH
      equivalence?
- [ ] Is the Hedenmalm pair connection exact, including domains and multiplicities?
- [ ] Is every paper claim proved independently of RH and simplicity unless explicitly conditional?
- [ ] Does prime--Gamma reconstruction establish source visibility without assuming the desired sign?
- [ ] Can the aperture/operator-norm identification be stated without hiding a nonattainment issue?
- [ ] Would a general-journal referee view the synthesis as a theorem with corollaries, not a
      renaming of zero displacement?

## Log

- 2026-07-30 — Created after full-corpus synthesis exposed critical-line reflection, Weil
  indefiniteness, Hurwitz negative-sector reconstruction, and spectral aperture as shadows of one
  chiral symmetry.
