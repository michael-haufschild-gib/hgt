# TG-C9.11b: the cubic survivor of coherent Ward cancellation

- **Stage:** 3-formalized
- **Route:** TG; unconditional RH goal remains unmet
- **Parent:** `../1-in-progress/tg-joint-prime-gamma-relative-lift.md`
- **Predecessor:** `tg-sonin-coherent-aperture-transgression.md`
- **Retired candidate:** `../5-failed/tg-balanced-ward-positive-completion.md`

## Exact new knowledge

Let 0<a≤b≤c, let every retained source scale satisfy r_i>1 and c≤r_i a,
and retain arbitrary complex coherent coefficients u_i. With the actual Sonin
projections Q and dilation sums D, define

Y = Σ_i u_i (Q_a-Q_b) D_i Q_b,
Z = Y(1-Q_c), W = Y Q_c,
K = Q_c Y†Y Q_c-Y†Y,
X = Z+Z†, C = [X,Q_a-Q_b],
B = K + C†C/2.

The following statements are now formalized for these actual source operators:

- C=Z†-Z and C†C=Z†Z+ZZ†; the correction is the canonical Ward Gram.
- B belongs to the concrete Sonin principal-relative ideal, is self-adjoint,
  and has **zero complete complex trace**.
- **Re Tr(B³)=-(3/2)||ZZ†W||²_HS.** Every source cross term remains.
- Re Tr(B³)=0 iff Z†W=0: exactly the retained/lost Gram decoupling locus.
- B is positive iff Z=0; -B is positive iff Z=0. Thus a nonzero lost
  transition makes B indefinite despite its zero scalar trace.

The operator identities and the positivity classifications need only aperture
nesting and the scale definitions. The crossing chamber is used to certify the
concrete relative ideal and the ordinary traces. No RH, Xi-zero, compatibility,
continuation, or budget assumption enters these statements.

## Dependency-closed paper proof

1. Exact source support gives Q_b Y=0 and Y Q_b=Y. Therefore Y²=0 and
   Q_c Y=0. Since Q_c is an orthogonal projection, Z²=WZ=WZ†=0.
2. Y=Z+W and W†W=Q_c Y†Y Q_c. Expanding the Gram gives
   K=-Z†Z-(Z†W+W†Z).
3. The certified coherent Ward boundary gives C=Z†-Z. Nilpotence Z²=0
   gives C†C=Z†Z+ZZ†. Thus
   M:=2B=P-A-2(V+V†), where P=ZZ†, A=Z†Z, V=Z†W.
4. P annihilates A,V,V† on both sides. Also V²=(V†)²=VA=AV†=0.
   Concrete relative-ideal membership validates every use of trace linearity
   and cyclicity; no junk-value trace manipulation is used.
5. Tr P=Tr A and Tr V=Tr V†=0, so Tr M=0. In the cubic expansion,
   Tr P³=Tr A³ and the odd off-diagonal words vanish. The three cyclic
   returning words each contribute Tr(A V V†), with total coefficient -12.
6. Cyclicity identifies Tr(A V V†) with Tr((PW)†(PW)). Taking real parts
   gives Re Tr M³=-12||PW||²_HS and hence the stated B identity.
7. PW=ZV. If PW=0, then V†V=W†PW=0, so V=0. The converse is immediate.
   Faithfulness of Hilbert--Schmidt energy proves the exact cubic zero locus.
8. The exact conjugations Z M Z†=-(ZZ†)² and Z† M Z=(Z†Z)² show that
   positivity of either sign of M forces Z=0. Conversely Z=0 makes M=0.
   The actual B is self-adjoint by its Gram formula.

## Formal sources

- `formal/GaloisForLFunctions/RHTower/SoninRelativeWardCubic.lean`:
  exact relative-ideal three-block cubic, scalar trace cancellation,
  returning-word rigidity, and both semidefinite classifications.
- `formal/GaloisForLFunctions/RHTower/SoninCoherentWardCubic.lean`:
  actual source support, normal form, canonical Ward Gram identification,
  relative ideal, self-adjointness, zero complex trace, exact cubic law,
  its vanishing locus, and both source positivity classifications.

Main source declarations:
`re_opTrace_soninCoherentBalancedWardCompletion_cube`,
`re_opTrace_soninCoherentBalancedWardCompletion_cube_eq_zero_iff`,
`soninCoherentBalancedWardCompletion_eq_curvature_add_WardGram`,
`soninCoherentBalancedWardCompletion_isPositive_iff`,
`neg_soninCoherentBalancedWardCompletion_isPositive_iff`.

## Verification

Both leaves pass their final foreground `lake --old env lean <module> -o <olean>`
checks at default heartbeats, without warnings. Both imports are wired; no umbrella
or full build was run. Their oleans are current. A separate `/tmp` API and
`#print axioms` audit passes all **21 public declarations**. Dependencies are only
`propext`, `Classical.choice`, and `Quot.sound`. No numerical experiment, added
axiom, hole, or raised heartbeat limit. Generated Lean indexes were refreshed.

Global `scripts/formal_tools.py lint` still fails on ten unrelated unwired modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
Neither new leaf has a lint error.

## Frontier and next mathematical question

This closes a finite matrix-complete cubic calculation, not TG's Hardy-index
transgression. The canonical positive Ward Gram cancels the scalar trace but
cannot make the actual completed operator positive except in the lossless case.
Its strongest survivor is the exact cubic return and its Gram-decoupling criterion.
A joint prime–Gamma construction must retain and control this returning channel;
a zero scalar trace is not a substitute.

Still open: the source-derived cofinal joint prime–Gamma completion, its actual
Hardy-index identification, and a source-derived sub-unit budget. No inference
that RH follows is made. A follow-up question is whether the literal Sonin source
has a further rigidity law Z†W=0 ⇒ Z=0, beginning with one scale. It is unproved:
the follow-up corpus query had partial semantic coverage and a timeout, and did
not provide such a producer. Do not assume dense range or infer absence from it.
