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
- 2026-08-30 — `[LEAN-PROVED SIGNIFICANT PREMISE]` The full reflected bridge and both
  monotone-l'Hospital descents are now closed in
  `ThetaCuspLikelihoodHomotopyLowerTransport`.  A new four-cooling proof gives
  `4*A*F2 < -F3` and `4*A*(-F3) < F4`; hence the projective invariant
  `J = F3^2*F4 + 2*F2*F4^2 - 2*F2*F3*F5` is strictly positive.  Together with the previously
  formalized energy `E>0`, this proves the sharp reflected endpoint comparison, strict
  antitonicity of the second transport ratio, then strict antitonicity of the first transport
  ratio.  The capstone theorem
  `thetaCuspC5LikelihoodHomotopy_velocityCenterTwo_pos` proves unconditionally that
  `(thetaCuspC5LikelihoodHomotopyData u t).velocityCenterTwo > 0` whenever
  `0<t<=u` and `scale(u-t)>=6`.  This discharges the entire `H''>0` lower-transport curvature
  premise in the chain
  `H''>0 -> M'''>0 -> convex likelihood lift -> direct-J -> rank-four/Ptolemy -> CLG/TTF or Weil
  positivity -> RH`.  Remaining C5 burden is the exact three-term Bose-weighted assembly
  `W'''*H + 3*W''*H' + 3*W'*H'' < 0` and the independent initial condition `M''(0)>=0`; lower
  transport itself is no longer open.  Direct source check and named-module build pass; axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide lint sees no local
  forbidden declaration but remains red on unrelated concurrent un-wired modules.
- 2026-08-30 — `[LEAN-PROVED ROUTE KILL + POSITIVE SURVIVOR]` The naive unshifted alternating
  Bose cone is impossible in the negative convex lower-transport chamber: for `P(z)=z*H(z)`,
  `z>0`, `H<0`, `H''>0`, and `P'>0` force `H'>0` and hence `P''>0`, contradicting the proposed
  `P''<0`.  The replacement is an exact lowest-mode-shifted Bernstein cone.  Closed positive
  formulas for the first three centered Bose jets decompose the full three-term lower-transport
  balance into the strict base term `30*(t*da)*H''<0` plus four nonpositive polynomial faces.
  Thus four source inequalities imply the literal `M'''>0`, without a Bose-series expansion,
  truncation, or interchange argument.  In the theta-source specialization, the prior
  unconditional theorem `H''>0` discharges the only strict base sign; the surviving off-seam
  burden is exactly the four-face source cone, with `M''(0)>=0` still independent.  Formalization:
  `ThetaCuspLikelihoodHomotopyBoseBernsteinCone`.  Exact chain:
  `shifted four-face cone -> M'''>0 -> convex likelihood lift -> direct-J -> rank-four/Ptolemy ->
  CLG/TTF or Weil positivity -> RH`.  Direct source check and targeted module build pass; axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide lint sees
  no local forbidden declaration and remains red only on unrelated concurrently unwired modules.
- 2026-08-30 — `[CONJECTURE K]` For every `0<t<=u`, every `0<=l<=1`, and every structural-tail
  point `6<=thetaCuspSingleAtomReflectionScale 1 (u-t)`, the literal affine theta packet
  `d=thetaCuspC5LikelihoodHomotopyData u t` satisfies `d.BoseShiftedTransportCone l`; equivalently,
  all four lowest-mode-shifted derivatives `(D-d.dq)^j ((d.t*d.jetOne)*d.velocityCenter)`,
  `0<=j<=3`, are nonpositive.  This is frozen as the decisive next source claim.  Exact chain:
  `Conjecture K -> literal M'''>0 -> convex likelihood lift -> direct-J -> rank-four/Ptolemy ->
  CLG/TTF or Weil positivity -> RH`.  Hostile attack order is source endpoints, modular seam jets,
  then structural-tail propagation.  Any wrong-sign face kills the whole shifted-Bernstein survivor;
  no weaker subset is being substituted.
- 2026-08-30 — `[LEAN-PROVED ROUTE KILL + POSITIVE SURVIVOR]` The adaptive shift chosen to cancel
  affine velocity variation cannot establish Conjecture K or any all-nonpositive shifted cone.
  For an arbitrary shift `sigma`, exact cancellation `dv+sigma*v=0` reduces the second shifted face
  to `v*(H''-sigma^2*H)`.  At the literal source endpoint `l=0`, the already-proved first-atom signs
  give `v>0` and `H<0`, while the reflected lower-transport bridge gives `H''>0`; therefore this
  second face is strictly positive.  The source theorem rules out the unique cancelling shift for
  every `0<t<=u` with `scale(u-t)>=6`, not at sampled parameters.  Formalization:
  `ThetaCuspLikelihoodHomotopyAdaptiveBernsteinNoGo`.  This kills the entire adaptive
  velocity-cancellation variant of the shifted-Bernstein strategy.  Positive survivor is the exact
  source law `0 < v*(H''-sigma^2*H)` under cancellation.  The fixed physical lowest-mode Bose shift
  `sigma=-dq` does not cancel `dv` and remains the sole shifted-cone route under Conjecture K, with
  unchanged chain `K -> M'''>0 -> convex likelihood lift -> direct-J -> rank-four/Ptolemy ->
  CLG/TTF or Weil positivity -> RH`.
- 2026-08-30 — `[LEAN-PROVED SIGNIFICANT PREMISE]` Corpus audit of the completed endpoint exposed
  the native monotone ratio `-A'/A^2`, where `A=-(log Theta)''`.  Its derivative numerator is
  `2*(A')^2-A*A''`.  On the structural tail this numerator is now unconditionally positive.  For
  the first atom, clearing the sixth power of the Born--Witten coordinate `q>=9/2` leaves
  `16*q^6-144*q^4-504*q^3-288*q^2+108*q+162>0`.  Completion then preserves strict positivity
  without estimating the fourth likelihood jet: the negative third likelihood jet enlarges
  `(A')^2`, while positive second and fourth likelihood jets strictly shrink the adverse product
  whenever that product is positive; if completed `A''<=0`, the sign is immediate.  The native
  capstone `strictMonoOn_thetaCuspCompletedInverseCurvatureSlope_of_scale` proves strict increase
  of `-A'/A^2` on every ray starting at a positive scale-six point.  A current-literature audit
  found no statement of this reciprocal-curvature inequality; the closest August 2026 result,
  Planat--Sole's second-level concavity theorem, concerns log-concavity of the first Laguerre
  expression after the squared radial change and uses certified interval patches, not this
  completed log-curvature ratio or its exact tail proof.  Formalization:
  `ThetaCuspCompletedInverseCurvatureTransport`.  Exact chain attacked:
  `completed inverse-curvature transport + companion projective endpoint comparison ->
  velocityCenter(1)<0 -> Conjecture K zero face -> shifted Bose cone -> M'''>0 -> direct-J ->
  rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH`.  This discharges the first of the two
  monotone-ratio premises for the completed endpoint; the companion comparison, and the remaining
  three shifted faces, stay open.
- 2026-08-30 — `[FROZEN CONJECTURE K0]` The completed endpoint needed for Conjecture K's zero face is
  `c5CompletedVelocityCenterNumerator u t < 0` for `0<t<=u` and
  `6<=thetaCuspSingleAtomReflectionScale 1 (u-t)`.  In intrinsic curvature coordinates
  `A=-(log Theta)''`, its two-step monotone-l'Hospital numerator is controlled by the companion
  projective law that `A''/A` decreases.  This candidate is corpus-driven by the already-proved
  strict increase of `-A'/A^2` and the exact likelihood reflected-transport proof.  Hostile test:
  inverse-curvature convexity alone is insufficient (positive affine curvature gives endpoint
  determinant exactly zero), while decrease of `A''/A` excludes that obstruction and supplies both
  the endpoint bridge and strict projective-energy drift.  Exact chain attacked:
  `A''/A strict decrease -> completed endpoint negative -> Conjecture K zero face -> remaining three
  shifted faces -> M'''>0 -> convex likelihood lift -> direct-J -> rank-four/Ptolemy -> CLG/TTF or
  Weil positivity -> RH`.  First target is unconditional cofinal closure using the corpus's
  super-polynomial likelihood cooling; this removes the noncompact endpoint burden before the
  scale-six compact chamber.
- 2026-08-30 — `[LEAN-PROVED SIGNIFICANT PREMISE]` Conjecture K0 is proved cofinally.  For
  `A=-(log Theta)''`, the completed projective energy `A'*A''-A*A'''`, multiplied by the
  first-atom reflection scale, tends exactly to `5184`; hence `A''/A` is strictly decreasing on a
  positive cofinal ray.  Its companion potential `3*(A')^2-2*A*A''` is strictly increasing there.
  These two endpoint comparisons make the second reflected derivative ratio strictly decreasing;
  two exact monotone-l'Hospital descents then prove the closed theorem
  `exists_c5CompletedVelocityCenterNumerator_neg_farTail`: some `x₀>0` satisfies
  `c5CompletedVelocityCenterNumerator u t<0` for every `t>0` and `x₀<=u-t`.  No computation,
  interval certificate, premise, hypothesis, or added axiom enters the theorem.  Formalization:
  `ThetaCuspCompletedCurvatureProjectiveFarTail` and
  `ThetaCuspCompletedVelocityCenterFarTail`.  Exact chain advanced:
  `completed endpoint negative -> Conjecture K zero face -> remaining three shifted faces ->
  M'''>0 -> convex likelihood lift -> direct-J -> rank-four/Ptolemy -> CLG/TTF or Weil positivity
  -> RH`.  Remaining zero-face burden is compact; this theorem removes its entire noncompact
  endpoint region.  Direct checks and targeted final-module build pass.  Axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  Global lint finds no local forbidden declaration;
  it remains red only on unrelated pre-existing umbrella-reachability failures.
