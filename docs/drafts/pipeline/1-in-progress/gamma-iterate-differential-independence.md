# Differential independence of the positive Gamma-iterate tower

- **ID:** `gamma-iterate-differential-independence`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[CONJECTURE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The countable family

  \[
    \Gamma(z),\Gamma^{\circ2}(z),\Gamma^{\circ3}(z),\ldots
  \]

  is differentially algebraically independent over `ℂ`.

## Goal

Prove that composition depth supplies not merely new algebraic coordinates, but a new differential
transcendence coordinate at every level.  The identity iterate is deliberately excluded: `z' = 1`
makes the depth-zero coordinate differentially algebraic over the constant field.

## Current evidence

- Every positive iterate is individually hypertranscendental in Lean.
- The complete tower including `z` is algebraically independent in Lean.
- The point, value, and first derivative of every positive iterate form one countably infinite
  algebraically independent family in Lean.
- The first derivative-weight-homogeneous second-jet curvature and the first
  translation-invariant third-jet Schwarzian obstruction both have nonzero exact Gamma residues in
  Lean, at successive harmonic orders one and two.
- Harmonic degree alone is not injective: the complete dominant harmonic envelope
  `-C exp(a x)/x` obeys a common third-order differential equation.  The exact Gamma germ crosses
  that entire envelope at the subordinate pure-factorial scale with a nonzero `ζ(2)` residue in
  Lean.
- The factorial pole microscope lowers every positive depth simultaneously:

  \[
    \Gamma^{\circ(j+1)}\!\left(-n+\frac{(-1)^{n+1}}{n!}x\right)
      \longrightarrow \Gamma^{\circ j}(-1/x).
  \]

- For a joint differential relation, the highest derivative-weight slice therefore descends one
  composition level.  Derivative grading removes the inhomogeneous Riccati equation and closes the
  complete first-jet theorem.  The first surviving homogeneous obstruction is the second-jet
  projective curvature `y y''-2(y')²`.

## Resolved second- and third-jet obstructions `[PROVEN IN LEAN]`

Write `s_n=(-1)^(n+1)/n!` and

\[
  g_n(x)=\Gamma(-n+s_nx)
        =-\frac{1}{x}\,
          \frac{\Gamma(1+s_nx)}{\prod_{m=1}^n(1-s_nx/m)}.
\]

The reciprocal limit is differentially algebraic, so leading-order descent is not injective beyond
first jets.  The exact germ is a deformation whose coefficients contain the harmonic hierarchy
`H_n, H_n^(2), ...`.  The first deformation is an output translation of size `s_n H_n`.

`GammaFactorialSecondJetHarmonicResidue.lean` proves

\[
 \frac{g_n''-2g_n^3}{s_nH_n}\to\frac6{x^2},\qquad
 \frac{g_ng_n''-2(g_n')^2}{s_nH_n}\to\frac2{x^3}.
\]

The second limit crosses the first derivative-weight-homogeneous reciprocal kernel.  Its proof
includes the scaled-trigamma estimate

\[
 \frac{s_n^2\psi'(-n+s_nx)-x^{-2}}{s_nH_n}\to0.
\]

Direct compilation, the individual target, and axiom audits pass; no full build or numerical
computation was used.

The next relation is genuinely more rigid.  The translation-invariant Schwarzian numerator

\[
  \mathcal S_3(g)=2g'g'''-3(g'')^2
\]

vanishes both on the reciprocal boundary and on its first harmonic output translation.  Thus the
linear harmonic microscope cannot cross it.  `GammaFactorialThirdJetHarmonicResidue.lean` proves
the first surviving coefficient instead:

\[
  \frac{\mathcal S_3(g_n)}{(s_nH_n)^2}\longrightarrow-\frac6{x^4}.
\]

The proof derives exact order-two differentiated-digamma shift formulae and proves that the scaled
trigamma and second polygamma have zero quadratic-harmonic correction.  The surviving term is the
quadratic response of the digamma coordinate.  This establishes a strict obstruction hierarchy:
projective curvature is crossed at harmonic order one, while Schwarzian curvature is crossed at
harmonic order two.

## Resolved failure of harmonic injectivity `[PROVEN IN LEAN]`

The hierarchy cannot continue using maximal harmonic degree alone.  The full dominant harmonic
model is the exponential-reciprocal envelope

\[
  y_{C,a}(x)=-C\frac{e^{ax}}x.
\]

Writing `q=y'/y`, every member has `q'=x⁻²` and `q''=-2x⁻³`; hence the denominator-free
third-order discriminant

\[
 \mathcal E_3(y)=
 (y^2y'''-3yy'y''+2(y')^3)^2-4(yy''-(y')^2)^3
\]

vanishes on the entire envelope.  This is a genuine kernel element for every dominant harmonic
coefficient, not a missing estimate.

`GammaFactorialExponentialEnvelopeEscape.lean` proves that the exact Gamma germ leaves this
hypersurface at the lower pure-factorial scale:

\[
  \frac{\mathcal E_3(g_n)(x)}{s_n^2}
    \longrightarrow -\frac{4\pi^2}{x^{10}}.
\]

Equivalently, for the logarithmic derivative, `(q_n''²-4q_n'³)/s_n² → -4π²/x⁴`.  The coefficient
is `-24ζ(2)`.  Thus the correct pole-germ structure is at least bifiltered: unbounded harmonic
degree is followed by bounded zeta data.  This both falsifies the naïve one-filtration argument and
supplies the first nonzero subordinate residue.

## Open core: all-order intrinsic pole-germ residue

The projective curvature, the translation-invariant Schwarzian, and the first common equation of
the full exponential-reciprocal envelope are now crossed.  These do not yet imply injectivity on
the complete reciprocal differential ideal.  The residue map must retain the full lexicographic
signature: factorial order, harmonic degree, and the bounded generalized-harmonic/zeta layer.

The proof-grade missing theorem is:

> For every nonzero derivative-weight-homogeneous differential polynomial that vanishes on
> `-1/x`, the first nonzero coefficient of its exact Gamma pole-germ expansion is nonzero after
> lexicographic filtration by factorial order, harmonic degree, and bounded generalized-harmonic
> data.

Together with the already formalized nonvanishing of the factorial initial form, this would make
depth descent injective and close induction on composition depth.

## Attacks and falsifiers

1. Characterize the differential ideal of the exponential-reciprocal envelope and its successive
   subordinate kernels.  The first common third-order discriminant is crossed by `ζ(2)`; determine
   whether the next kernel is crossed by a triangular sequence of higher zeta values.
2. Derive the Gamma pole-germ residues symbolically from the exact product formula.  No numerical
   experiment is evidence for this card.
3. Prove that the residue map is injective on the associated graded kernel.  A nonzero homogeneous
   differential polynomial annihilating every exact residue layer retires this route.
4. Check parent theory on differential ideals of reciprocal/projective jets and singular
   perturbations.  A published general theorem implying the statement retires novelty, not truth.
5. Do not replace this core with separate hypertranscendence, finite algebraic independence, or a
   conditional wrapper: none proves joint differential independence.

## Significance gate

If true, this produces a countably infinite differential transcendence basis from one classical
hypertranscendental function by self-composition and identifies simple-pole deformation depth as
the mechanism.  The claim is potentially field-defining, but it is not promoted until the residue
injectivity theorem is complete and an independent priority audit finds no antecedent.

## Gates

- [x] 0 → 1 in-progress: precise positive-depth statement, exact leading obstruction, attack, and
  falsifier isolated
- [ ] 1 → 2 fully-proven: pole-germ residue injectivity and induction complete on paper
- [ ] 2 → 3 formalized: unconditional joint theorem in Lean, targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready: specialist priority review and standalone paper complete

## Log

- 2026-07-15 — opened after formalization of algebraic independence of the complete Gamma-iterate
  tower.  The algebraic descent is injective; the differential route is isolated to the
  reciprocal-boundary associated-graded kernel.
- 2026-07-15 — derivative grading was proved injective at first-jet order, closing the countable
  first-jet theorem.  Formalized the scaled-trigamma correction and the nonzero moving residue of
  the first homogeneous second-jet projective curvature.  The open core begins with the
  translation-invariant third-jet Schwarzian layer.
- 2026-07-15 — crossed the translation-invariant third-jet Schwarzian layer in Lean.  Its linear
  harmonic response cancels, but its quadratic harmonic residue is the nonzero rational profile
  `-6/x⁴`.  The open core is now the all-order reciprocal-ideal residue map, not either of the first
  two projective generators.
- 2026-07-15 — proved that maximal harmonic degree is not injective: it collapses onto the
  differential-algebraic envelope `-C exp(a x)/x`.  Formalized the first subordinate escape; its
  denominator-free third-jet discriminant has pure-factorial residue `-4π²/x¹⁰`.  The open core is
  now a multi-filtration theorem incorporating generalized-harmonic/zeta coefficients.
