# CCM Convolution–Tilt Odds Rigidity Universality Law

- **ID:** ccm-convolution-tilt-odds-rigidity-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of `CCMFirstClockExponentialTiltOdds` and `CCMInfiniteConvolutionPrimeFaceRigidity`
- **Statement:** On the literal irreducible-prime first-clock face, arbitrary scalar Gamma sewing followed by an infinite Dirichlet-convolution functional preserves critical counter/aligned odds exactly; when its prime derivative is nonnegative, the sewn face remains at least as counter-biased as every safe Mellin exponent `σ ≥ 1/2`.

## Goal

Prove the source-forced connector between prime-face convolution rigidity and separated
exponential-tilt monotonicity.  Unlike a conjunction, both inputs act on the same filtered
irreducible-prime source, and the conclusion compares the transformed source directly with its
safe Mellin tilts.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact `lake env lean` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Restrict the existing separated-tilt theorem to the prime-filtered first aperture.  Use the exact
prime evaluation formula for an arbitrary convolution series on the Gamma-sewn von Mangoldt
source to factor both aligned and counter masses by one common derivative scalar.  The common
factor gives exact odds preservation; multiplying the critical-versus-safe cross inequality by a
nonnegative derivative gives the no-escape comparison.

## Proof

`[PROVED HERE]` Let `D` be the prime derivative of the convolution series at the scalar Gamma
coordinate.  At every prime `p`, Dirichlet convolution has only divisor pairs `(1,p)` and `(p,1)`;
hence every convolution-series value is `D` times the original von Mangoldt prime coefficient.
After multiplication by the critical Mellin weight, summing separately against positive and
negative first-clock half-wave kernels gives

`aligned_sewn = D · aligned_critical` and
`counter_sewn = D · counter_critical`.

Cross multiplication immediately proves exact odds preservation, including zero chambers.
The separated exponential-tilt theorem restricted to the same prime support gives

`counter_critical · aligned_safe ≥ counter_safe · aligned_critical`

for `σ ≥ 1/2`.  Multiplication by `D ≥ 0` and the two factor identities yield the sewn
critical-versus-safe inequality.

## Novelty audit

- **Status:** `[LEAN PROVED — LITERATURE AUDITED]`
- Karlin–Rubin's classical monotone-likelihood-ratio work covers the separated exponential-tilt
  mechanism ([DOI 10.1214/aoms/1177728259](https://doi.org/10.1214/aoms/1177728259);
  [DOI 10.1080/01621459.1956.10501355](https://doi.org/10.1080/01621459.1956.10501355)).
- Standard arithmetic-function literature records Dirichlet convolution as Cauchy convolution on
  each prime-power tower; see Tóth,
  [*Quotients of arithmetical functions under the Dirichlet convolution*](https://nntdm.net/papers/nntdm-29/NNTDM-29-2-185-194.pdf).
- Brudnyi studies general arithmetic convolution equations and Dirichlet series
  ([arXiv:0712.3172](https://arxiv.org/abs/0712.3172)).
- Targeted searches found no theorem joining these mechanisms on the von-Mangoldt
  critical-Mellin irreducible-prime first-clock face, no exact common-derivative
  counter/aligned-odds invariance statement, and no resulting safe-exponent no-escape law.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CCMConvolutionTiltOddsRigidityUniversalityLaw`
- Main theorem:
  `RHTower.ccmGammaSewnConvolution_irreduciblePrimeTiltOddsRigidity`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/CCMConvolutionTiltOddsRigidityUniversalityLaw.lean`
  (exit 0, no output)
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Axiom audit and module build are deferred to required final audit; no intermediate
  `lake build` was run.

## Log

- 2026-07-23 — created in 1-in-progress after whole-corpus terminal-cluster scan exposed the shared irreducible-prime source.
- 2026-07-23 — exact Lean proof completed and post-proof literature audit found no exact prior law.
