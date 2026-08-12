# Hedenmalm--theta Möbius pole-unit transverse curvature

- **ID:** P-G41
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-current-frontier-map.md` · Route P source-Julia saturation open core
- **Statement:** After the universal P-G38 boost kernel is divided out, the finite squarefree Möbius Hardy Gram has zero value and slope defect at the Euler pole; its exact quadratic transverse defect is the derivative of the regular squarefree current.

## Goal

Find the first source-pure Euler datum that is not constant on the common P-G40/Route-R horizontal
boost orbit.  A successful discriminator must be intrinsic to the literal squarefree Möbius source,
not an imposed polar metric, and must eventually force zero rapidity rather than merely measure it.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: exact jet is Lean theorem `squarefreeMobiusPoleUnitMidpointDefect_iteratedDeriv_two`; strict-sign dependency remains open
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Definitions

Write

\[
 Z(s)=\frac{\zeta(s)}{\zeta(2s)},\qquad
 F(s)=\frac{(s-1)\zeta(s)}{\zeta(2s)},\qquad
 B(s)=-\frac{F'(s)}{F(s)}.
\]

Here `(s-1)ζ(s)` means the analytic residue unit at `s=1`, so `F` and `B` are analytic near
`1`, and `F(1)=1/ζ(2)≠0`.  For source apertures `u,v>-1/2`, set

\[
 x=1+2u,\quad z=1+2v,\quad y=\frac{x+z}{2}=1+u+v.
\]

For `ε>0`, the squared normalized finite Gram is

\[
 K_\varepsilon(u,v)^2
   =\frac{Z(1+y\varepsilon)^2}
          {Z(1+x\varepsilon)Z(1+z\varepsilon)}
   =\frac{xz}{y^2}
      \frac{F(1+y\varepsilon)^2}
           {F(1+x\varepsilon)F(1+z\varepsilon)}.
\]

The first factor is exactly the universal P-G38 kernel
`K₀²=xz/y²=sech²(η(u)-η(v))`.  Define the division-free arithmetic defect

\[
 D_{x,z}(\varepsilon)
 =F(1+y\varepsilon)^2-F(1+x\varepsilon)F(1+z\varepsilon).
\]

## P-G41 exact transverse-jet theorem

For every complex `x,z`,

\[
 D_{x,z}(0)=D'_{x,z}(0)=0,
\]

and

\[
 D''_{x,z}(0)
 =\frac{(x-z)^2}{2}
   \bigl(F'(1)^2-F(1)F''(1)\bigr)
 =\frac{(x-z)^2}{2}F(1)^2B'(1).
\tag{P-G41}
\]

Equivalently, if

\[
 Q_{x,z}(\varepsilon)=
 \frac{F(1+y\varepsilon)^2}
      {F(1+x\varepsilon)F(1+z\varepsilon)},
\]

then `Q(0)=1`, `Q'(0)=0`, and

\[
 Q''_{x,z}(0)=\frac{(x-z)^2}{2}B'(1).
\]

### Proof of the algebraic jet identity `[PROVED HERE]`

Let `f_j=F^{(j)}(1)`.  The two derivatives of `ε↦F(1+aε)` at zero are `af₁` and
`a²f₂`.  Product rule gives

\[
 D'(0)=f_0f_1(2y-x-z)=0
\]

because `2y=x+z`, while

\[
\begin{aligned}
 D''(0)
 &=2y^2(f_1^2+f_0f_2)
   -(x^2+z^2)f_0f_2-2xzf_1^2\\
 &=\frac{(x-z)^2}{2}(f_1^2-f_0f_2).
\end{aligned}
\]

Since `B=-F'/F` and `f₀≠0`, quotient differentiation gives
`B'(1)=(f₁²-f₀f₂)/f₀²`.  This proves P-G41.  Applying the same calculation to
`log Q`, then using `Q(0)=1` and `Q'(0)=0`, proves the normalized version.

## Euler--pole decomposition and sign gate

The public regular current has the exact decomposition

\[
 B(s)=-\operatorname{logDeriv}((s-1)\zeta(s))
      -2\,\operatorname{infinitePrimeFlux}(2s),
\]

so

\[
 B'(1)=-(\log((s-1)\zeta(s)))''\big|_{s=1}
        -4\,\operatorname{infinitePrimeFlux}'(2).
\tag{*}
\]

The Euler term is strictly positive because the derivative of
`infinitePrimeFlux(s)=Σ Λ(n)n^{-s}` is the negative strict prime-power log moment.  A July 2026
external theorem proves strict log-concavity of `(s-1)ζ(s)` on the real interval `s>1`, which would
make both terms in `(*)` positive.  Its published proof below `s=4` uses numerical zero bounds, so
it is evidence, not an admissible dependency for this route's no-computation Lean closure.

An internal nonnumerical replacement is available in outline.  The Stieltjes series and convex
left-rectangle bound for `f(t)=log(t)/t` give

\[
 \gamma_1>
 \log2+\frac{\log3}{3}+\frac{\log5}{10}-\frac{(\log5)^2}{2}>-\frac18.
\]

Together with the already formalized `γ>1/2`, this implies
`2γ₁+γ²>0`, hence strict pole-unit log-concavity at `1`.  Missing dependency: formalize the
Stieltjes-series identity and connect it to the second derivative of the analytic residue unit.

## Hostile audit / anti-theatre

- The midpoint Hessian identity for a generic analytic function is elementary and is not itself a
  novelty claim.
- Corpus-new weld: the *literal finite squarefree Möbius Hardy Gram* factors into P-G38's universal
  boost kernel and this pole-unit quotient.  Arithmetic is invisible at orders zero and one and
  first appears as the transverse second jet `B'(1)`.
- Lean closes literal-source status at finite scale: theorem
  `inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp_sq_eq_finiteUnitHardyGramSq` identifies
  the square of the actual normalized source inner product with the three-point squarefree Gram
  before the pole-unit factorization is applied.
- This differs from existing `GammaSewnApertureFisherSeam` and
  `GammaSewnFourRateSchurFisherCurvature`: those are prime-local Gamma-sewn aperture curvatures;
  P-G41 is the global pole-normalized squarefree source correction to P's Hardy Gram.
- P-G41 with `B'(1)>0` says arithmetic initially contracts rapidity separation relative to the
  universal boost orbit.  It measures and orients the broken orbit but does **not** force `x=z`.
  Calling it an RH producer would be theatre.
- Required next conjecture: derive a source-pure completed transport inequality with the opposite
  endpoint sign or a monotone conservation law.  Combined with strict P-G41 curvature, that could
  squeeze the relative rapidity to zero.  If no such transport exists, P-G41 survives as a sharp
  detector/no-go boundary, not a saturation proof.

## Door passport

- **Source purity:** `F` is forced by the exact squarefree Möbius Dirichlet series; no external
  metric or target coefficient is introduced.
- **Non-circularity:** definition and jet identity use only the Euler half-plane and removable pole
  unit, not zero locations or RH.
- **Hard obstruction addressed:** P-G40 shows all zeroth-order normalized geometry lies on one
  common boost orbit.  P-G41 locates the first coefficient that can break that orbit.
- **Open gate:** unconditional noncomputational sign proof in Lean; then a genuine saturation
  mechanism, not merely a discriminator.

## Log

- 2026-08-12 — created directly in `1-in-progress`; affine/reflection selector killed by existing
  common-center/coboundary no-go, generic local-curvature variants collided with existing
  Gamma-sewn Fisher modules, global pole-unit transverse jet survived hostile audit.
- 2026-08-12 — exact finite literal-source weld, pole-unit factorization, zero/slope cancellation,
  quadratic jet, and pole/Euler current decomposition formalized in
  `HedenmalmThetaMobiusPoleUnitTransverseCurvature.lean`; sign gate deliberately remains open.
