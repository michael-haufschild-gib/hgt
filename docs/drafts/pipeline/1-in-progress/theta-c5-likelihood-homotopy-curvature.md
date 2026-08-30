# Theta C5 likelihood-homotopy curvature

- **ID:** CLG-TTF-C5-likelihood-homotopy-curvature
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** fixed-action C5 likelihood lift and amplitude-stable curvature-topology audit

## Exact claim

Fix the physical structural tail

```text
0 < t <= u,
6 <= thetaCuspSingleAtomReflectionScale 1 u,
0 <= lambda <= 1.
```

Let every completed action/displacement/centre jet be the affine interpolation between its exact
first-atom value and its exact full-theta value, and let `M(lambda)` be the literal C5 completed
compensation formula evaluated on those seven interpolated jets.

```text
[CONJECTURE]  M'''(lambda) > 0  and  M''(0) >= 0.
```

Together these imply `M''(lambda)>=0`. The separate atom-tangent conjecture
`M'(0)>=-M(0)/5`, combined with formal `M(0)>0`, would then prove `M(1)>0` and discharge the
literal full-theta structural-tail compensation gate.

## Internal frontier

- `[CORPUS]` Exact first-atom compensation is positive.
- `[CORPUS]` Likelihood action and first three displacement jets are negative; all three centre-flow
  jets are positive.
- `[CORPUS]` Action--jet hierarchy and mixed trapezoid coupling constrain the adverse channels.
- `[CORPUS]` Pointwise signs and current pairwise cone are insufficient: saturated second-channel
  direction is strictly adverse.
- `[CORPUS]` Full compensation equals false adaptive-reserved endpoint plus an exact positive
  third-channel residual.
- `[CORPUS]` Higher-tail likelihood is an exact Laplace transform of a positive atomic spectral
  measure; dominant second-atom `exp(-3A)` identities already exist.

## External frontier

Chouikha proves complete monotonicity for classical theta quotients and their logarithmic
derivatives (arXiv:1409.1498). Yang--Tian prove variation-diminishing monotonicity rules for ratios
of Laplace transforms (arXiv:1803.02513). Standard theta log-convexity controls isolated source
derivatives. None supplies the nonlinear seven-jet C5/Bose compensation curvature above.

## Hostile status

- Monotone improvement `M'(lambda)>=0` is `[FALSIFIED]`.
- Coarse sign/pairwise-cone proof of atom-tangent reserve is `[FALSIFIED]`.
- Adaptive-reserved positivity is `[FALSIFIED]` by its negative fifth seam germ.
- Raw far-tail subtraction is numerically invalid; amplitude-factored dominant coefficient is
  positive but is diagnostic only and cannot enter a proof.
- Exact seam algebra isolates the new source invariant
  `F2 * F5 - 2 * F3 * F4`, equivalently `(F4 / F2^2)' > 0`.
- Pointwise fourth/sixth Cauchy is `[FALSIFIED]`: the physical score defect
  `p4*p6-p5^2` is negative in the tail. Pointwise `p5 <= 3*A*p4` also fails away from the
  minimal spectral edge.
- The sufficient split `3*A*F2 < -F3` and `-F5 < 6*A*F4` survived a 4,096-point,
  80-digit scan on `6<=A<=1000`; this is diagnostic only.
- The complete `n=2` atom-plus-ray ordinary reserve for `F5+6*A*F4` has an exact rational
  numerator whose expansion in `A-6` has only positive coefficients. At `A=6`, computed
  `n>=3` ordinary opposition is `2.01e-10` of that reserve.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Open core

Fourth cooling and the seam invariant are closed.  For the literal affine seven-jet homotopy, prove
or kill the exact lower-transport inequality

```text
W''' * H + 3 * W'' * H' + 3 * W' * H'' < 0
```

throughout `0 <= lambda <= 1`, where `W` is the literal Bose coefficient and `H` is the lower
velocity transport.  This condition is equivalent to `M'''(lambda) > 0`; no highest displacement or
second mixed-centre channel remains in it.  The independent initial condition `M''(0) >= 0` also
remains before the convex likelihood lift can close.

## Log

- 2026-08-29 — Claim frozen after internal corpus and primary-literature audit; algebraic hostile
  attack opened.
- 2026-08-29 — Exact seam factorization found. Generic pointwise proof killed. Dominant-atom/ray
  cooling route opened and computation archived in
  `2-fully-proven/computations/2026-08-29-c5-homotopy-seam-cooling/`.
- 2026-08-29 — Closed lower cooling theorem `3*A*F2 < -F3` formalized in
  `ThetaCuspFixedActionC5LikelihoodLiftReduction`; targeted module build and axiom audit pass.
- 2026-08-30 — `[LEAN-PROVED]` Fourth cooling closed in
  `ThetaCuspLikelihoodFourthFifthLogCooling`.  The two cooling laws now give the exact strict seam
  invariant `F2*F5 - 2*F3*F4 > 0`; quotient-rule formalization proves positive derivative and
  tail-ray strict monotonicity of `F4/F2^2` in
  `ThetaCuspLikelihoodHomotopySeamRatioOrientation`.  Current `[OPEN CORE]` is no longer seam
  orientation: it is positivity of `M'''(lambda)` away from the seam together with `M''(0) >= 0`.
  Current-literature audit found Planat--Solé's second-level theta-kernel concavity
  (arXiv:2608.19160), but the corpus formal no-go shows that property does not imply C5; no located
  primary result supplies this nonlinear seven-jet homotopy curvature.
- 2026-08-30 — `[LEAN-PROVED ROUTE KILL]` Literal affine homotopy, both endpoints, and its first
  three derivative profiles were formalized in
  `ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction`.  Exact product-rule cancellation
  proves
  `M''' = -(W'''*H + 3*W''*H' + 3*W'*H'')`.  Consequently the entire velocity--slope numerator,
  including third displacement and second mixed-centre likelihood channels, is absent from
  `M'''`; changing those highest channels leaves third curvature definitionally unchanged.  This
  kills every curvature proof based on the previously favorable highest-channel reserve.  The
  positive survivor is the exact three-term lower-transport balance
  `W'''*H + 3*W''*H' + 3*W'*H'' < 0`, now the sole off-seam `M'''` source burden.  `M''(0) >= 0`
  remains separate.
- 2026-08-30 — `[LEAN-PROVED SIGNIFICANT PREMISE]` The seam invariant was integrated globally,
  without numerical bounds.  For `Fₖ` the source likelihood jets, the projective energy
  `E = 3*F₃^2 - 2*F₂*F₄` satisfies
  `E' = -2*(F₂*F₅ - 2*F₃*F₄) < 0` on every structural-tail ray, while exact cumulant decay gives
  `E -> 0`.  Therefore `E > 0`, equivalently `2*F₂*F₄ < 3*F₃^2`; analytically this is strict
  convexity of `1/sqrt(F₂)`.  Formalization is
  `ThetaCuspLikelihoodHomotopyCurvatureEnergy`.  This discharges the first global nonlinear shape
  premise behind `H''`; the remaining integral comparison from this projective curvature law to
  the full reflected lower-transport determinant is still open.
- 2026-08-30 — `[FROZEN CONJECTURE J]` Corpus search isolated the next projective derivative
  
  `J = F₃^2*F₄ + 2*F₂*F₄^2 - 2*F₂*F₃*F₅`.
  
  No matching invariant or exact reflected-integral consequence was found in the corpus or current
  primary literature.  Writing `h=F₂`, `α=-F₃`, `C=F₄`, `γ=-F₅`, the identity is
  `J = α^2*C + 2*h*C^2 - 2*h*α*γ`.  It is simultaneously the derivative numerator of
  `C^2/(α^2*h)` and the negative derivative numerator of `E/α`.  The exact RH chain being attacked
  is `J>0 -> reflected lower-transport determinant H''>0 -> M'''>0 -> convex likelihood lift ->
  direct-J -> rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH`.
- 2026-08-30 — `[PAPER ROUTE SURVIVES HOSTILE ALGEBRA]` Existing fourth/fifth cooling gives
  `γ < 6*A*C`.  Two structural four-cooling laws suffice:
  `4*A*h < α` and `4*A*α < C`.  They imply
  `J > α*C*(α-4*A*h) > 0`.  The first law follows from the square-gap support recurrence and the
  strict cumulant comparison `(5/2)*variance < thirdCumulant`.  For the second, introduce the
  missing ordinary third score `P₃(z)=z^3-3*z^2+z`; on the exact support `z=A*t>=18`,
  `4*z*P₃(z) <= 5*P₄(z)`.  Spectral integration gives
  `4*A*ordinary₃ <= (5/6)*ordinary₄`; exact Bell algebra gives `α<ordinary₃`, while the existing
  retention theorem gives `(19/20)*ordinary₄<C`.  Hence `4*A*α<C` with substantial structural
  slack, not a tuned endpoint certificate.
- 2026-08-30 — `[PAPER REFLECTED BRIDGE]` For a symmetric packet set
  `a=h(u-t), b=h(u+t), α=-h'(u-t), β=-h'(u+t), C=h''(u-t), D=h''(u+t)`.
  `J>0` makes `C^2/(α^2*h)` strictly increasing; `E>0` makes `1/sqrt(h)` strictly convex.  These
  two facts imply the sharp endpoint comparison
  `C*(b-t*β) <= D*(a+t*α)`.  Strict decrease of `E` then makes the derivative ratio
  
  `(α+β)/(2*(a+b)+t*(α-β))`
  
  strictly decreasing.  Two weighted monotone-l'Hospital integrations force
  `t -> s(t)/(t*x(t))` strictly decreasing, where
  `x=integral(h(u-r)+h(u+r))` and `s=integral(h(u-r)-h(u+r))`.  Its derivative numerator is exactly
  the negative of the remaining lower-transport determinant
  `K=(x+t*y)*s-t*x*m`.  Thus `K>0`, subject only to formalizing this audited calculus chain.
