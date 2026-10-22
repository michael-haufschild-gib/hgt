# HB finite-local-angular threshold no-go

Status: formalized in Lean 4

## Result

No polynomial `P : Complex[X]`, of any finite degree, can cancel the exact chiral AIME mass-jet
coefficient on every positive real Hardy-line Xi fibre:

`-12 / (Q(t) + 2) + P(Q(t)) = 0`.

This kills the complete finite-order local angular threshold class, not a fixed-degree truncation.

## RH proof chain reduced

The eliminated chain was

`literal Einstein--Teukolsky source -> one finite-order local angular threshold operator P(Q) -> radiative ++ extinction -> fixed-clock covariance -> full cokernel extinction -> RH`.

Finite angular locality cannot supply its threshold extinction premise.  Any surviving HB chain must
instead derive a genuinely nonlocal angular resolvent, infinite-order angular response, or
fibre-adaptive law from the Einstein--Teukolsky source.

## Proof

On the positive real Hardy coordinate,

`Im Q(t) = t / 4`.

Therefore distinct positive Hardy zeros have distinct `Q` values, and `Q(t) + 2` is nonzero.  For a
hypothetical polynomial `P`, set

`R(X) = (X + 2) P(X) - 12`.

Choose `R.natDegree + 1` distinct positive real `XiC` zeros using the corpus Hardy packet theorem.
Cancellation makes their distinct `Q` images roots of `R`.  Polynomial root counting forces
`R = 0`; evaluation at `X = -2` gives `-12 = 0`, contradiction.

## Lean artifact

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEFiniteLocalAngularThresholdNoGo`
- Main no-go:
  `RHTower.not_d4HBFiniteLocalAngularThresholdXiComplete`
- Closed certificate:
  `RHTower.d4HBFiniteLocalAngularThresholdCancellationRouteKilled`
- Positive structural lemmas:
  `RHTower.d4ThetaTeukolskyAngularQ_ofReal_im` and
  `RHTower.d4ThetaTeukolskyAngularQ_ofReal_injective`

## Verification

- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingAIMEFiniteLocalAngularThresholdNoGo.lean`
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEFiniteLocalAngularThresholdNoGo`
  passed `12021/12021`.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint found no defect in this module and confirmed umbrella reachability.  Its nonzero exit
  was caused by pre-existing concurrently unwired Deninger, Hedenmalm, and lower-ramification
  modules outside this card.

## Novelty audit, 2026-08-31

Internal corpus searches found exact AIME reciprocal coefficient, Hardy packets, and polynomial
root-count infrastructure, but no theorem applying them to eliminate all finite-order local angular
threshold laws.

Primary literature reviewed:

- [Sberna et al., absorption-induced mode excitation](https://arxiv.org/abs/2112.11168) establishes
  AIME as a third-order secular mass-backreaction effect and studies its modal excitation.
- [Spiers--Pound--Moxon, second-order Teukolsky nonlinear source](https://arxiv.org/abs/2305.19332)
  derives the reduced second-order nonlinear source and its gauge/asymptotic framework.
- [Mitman et al., nonlinearities in black-hole ringdowns](https://arxiv.org/abs/2208.07380) and
  [Giesler et al., overtones and nonlinearities](https://arxiv.org/abs/2411.11269) establish
  nonlinear mode content in numerical ringdown data.

None states the all-degree polynomial-versus-reciprocal obstruction on the unconditional Hardy Xi
family.  Novelty claim is therefore limited to this exact route-class no-go and its Lean proof.

