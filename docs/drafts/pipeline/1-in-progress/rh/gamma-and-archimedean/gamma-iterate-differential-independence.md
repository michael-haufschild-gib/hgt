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
- The exact pole-jet decomposition is now proved in Lean for every finite polygamma order, so the
  remaining gap is residue-map injectivity rather than missing higher-derivative analytic formulae.
- The bounded layer is now evaluated in Lean at every order: odd polygamma orders have the
  nonzero residue `2m!ζ(m+1)`, while positive even orders cancel exactly and pass to a finer
  finite-tail normalization.
- The finer normalization is now evaluated in Lean at every positive even order: multiplication
  by `(n+1)^m` exposes the universal nonzero residue `-(m-1)!`.  Thus every individual positive
  polygamma coordinate is detected by the parity-tail ladder.
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

## Exact all-order source law `[PROVEN IN LEAN]`

For every `m,n∈ℕ`, `GammaFactorialAllOrderPoleJet.lean` proves the exact identity

\[
 \psi^{(m)}(-n+z)=\psi^{(m)}(1+z)
 +\frac{(-1)^{m+1}m!}{z^{m+1}}
 +m!\sum_{j=1}^n(j-z)^{-(m+1)}.
\]

After `z=s_nx`, this separates the reciprocal principal jet from a correction of exact factorial
order `m+1`.  The local and generalized-harmonic limits reinforce in odd polygamma order and cancel
in even order.  Hence the parity-dependent harmonic-zeta-tail ladder is now a theorem schema in
Lean, not an extrapolation from the first three jets.

`GammaFactorialAllOrderZetaLayer.lean` evaluates that bounded correction uniformly:

\[
 \frac{s_n^{m+1}\psi^{(m)}(-n+s_nx)-(-1)^{m+1}m!/x^{m+1}}
      {s_n^{m+1}}
 \longrightarrow
 \bigl(1+(-1)^{m+1}\bigr)m!\zeta(m+1).
\]

Thus every odd `m` is detected by the nonzero residue `2m!ζ(m+1)`.  Every positive even `m`
cancels at this layer.  `GammaFactorialAllOrderFiniteTail.lean` proves the next coefficient:

\[
 (n+1)^m
 \frac{s_n^{m+1}\psi^{(m)}(-n+s_nx)+m!/x^{m+1}}{s_n^{m+1}}
 \longrightarrow -(m-1)!.
\]

The limit is nonzero, rational, and independent of `x`.  Hence every individual positive
polygamma coordinate is now detected: odd orders by even-zeta residues and even orders by the
finite Euler-product tail.  The active core is no longer coordinate-level analytic detection but
simultaneous algebraic cancellation among finitely many jet coordinates.

## Direct outer-composition no-go and inverse-branch replacement

The lexicographic residue attack detects each individual polygamma coordinate, but it asks for a
new cancellation theorem at every differential order.  Worse, it cannot be implemented by taking
an ordinary Laurent series of an outer Gamma composition: after the pole microscope the inner
Gamma tends to infinity as `-1/X`, so the outer Gamma has no Laurent germ at `X=0`.  This retires
direct coefficientwise outer-Gamma substitution as the all-order mechanism.

The strong positive replacement is the complete family of normalized inverse branches.  Write

\[
  \Gamma(-n+s_nX)=-\frac{U_n(X)}X,\qquad
  A_n(X)=\frac{X}{U_n(X)},\qquad B_n=A_n^{\langle-1\rangle}.
\]

Then

\[
  \Gamma(-n+s_nB_n(T))=-\frac1T,
  \qquad B_n(T)=T\,U_n(B_n(T)).
\]

The full nonlinear coefficient family of `B_n`, as germs in the pole index, is algebraically
independent over `ℂ`: the already-free coefficients of `U_n` pass through multiplicative inversion
and then compositional inversion, and both universal coefficient transformations are involutions.
This replaces an infinite hierarchy of residue crossings by one invertible coordinate object.

For composition descent, put `w=-1/T` and `z=-n+s_nB_n(T)`.  The derivative transforms exactly as

\[
  D_z=\frac1{s_n B_n'(T)}D_T.
\]

At finite jet order, the generic time-change map is birational.  If `D_z=aD_w`, introduce the
independent `D_w`-jets of `a`.  Then

\[
  D_z^r w=(aD_w)^r w,
  \qquad D_z^rF_j(w)=(aD_w)^rF_j(w).
\]

The first family is triangular in the jets of `a`, with leading coefficients powers of `a`; after
those are recovered, the second family is triangular in the lower-tower jets, again with leading
coefficients powers of `a`.  Localizing at `a` gives a rational inverse.  Thus a generic inverse
branch restores exactly the one differential coordinate lost when `Gamma(z)` becomes the new base
variable `w`.

The remaining proof-grade bridge is no longer an unknown residue injectivity statement.  It is the
finite-jet specialization theorem saying that the algebraically independent coefficient germs of
`B_n` realize this generic time-change birational map disjointly from an arbitrary finite lower
Gamma-jet frame.  The pole/lower-frame scalar-extension part is formalized; the recursive
time-change triangularity and its integration with the existing derivative-weight initial-form
descent remain.

## Attacks and falsifiers

1. Formalize generic time-change jet birationality at arbitrary finite depth and jet order by an
   explicit rational inverse after localizing at the first time-change coordinate.
2. Specialize the generic time-change variables to the normalized inverse-Gamma branch and use
   pole/lower-frame disjointness to retain injectivity.
3. Compose this with the existing derivative-weight/factorial initial-form descent.  A kernel in
   this composite map retires the inverse-branch route and must yield an explicit positive
   differential invariant.
4. Audit iteration theory, differential algebra, and inverse-special-function literature.  A
   published theorem implying the statement retires novelty, not truth.
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
- 2026-07-15 — replaced the order-by-order pole-jet calculations with one exact Lean theorem for
  every polygamma order.  The remaining all-order core is algebraic injectivity of the resulting
  parity-sensitive harmonic-zeta-tail signature.
- 2026-07-15 — evaluated the bounded all-order layer in Lean.  Odd polygamma orders carry nonzero
  even-zeta residues; positive even orders cancel and expose the finer finite Euler-product tail.
- 2026-07-15 — resolved the finite-tail scale in Lean.  At every positive even order `m`, the
  normalized correction tends the universal nonzero coefficient `-(m-1)!`.  Coordinate-level
  detection is complete; the remaining core is injectivity on differential-polynomial products.
- 2026-07-15 — retired direct Laurent substitution through the outer Gamma: after the pole
  microscope its input tends to infinity and no outer Laurent germ exists.  Replaced the
  order-by-order residue core by normalized inverse-pole branches.  Their complete nonlinear
  coefficient family is paper-proved free via multiplicative and compositional coefficient
  involutions.  The active all-order core is the birational generic time-change jet map and its
  specialization disjointly from the lower Gamma-jet frame.
