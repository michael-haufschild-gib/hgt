# FCRJ theta--Abel finite-mode observability

- **ID:** fcrj-theta-abel-finite-mode-observability
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/critical-multiplicative-compensated-cancellation-rh.md
- **Statement:** Every coordinate of a finite packet of distinct theta--Abel exponential modes is uniformly observable from coherent aperture `L²` mass; one supercritical coordinate forces renormalized packet energy to beat every real power.

## Goal

Test surviving possibility from one-mode rate wall: finite cross-mode interference might cancel a
supercritical zero contribution inside raw theta-response energy.

## Gates

- [x] 0 → 1  in-progress: finite packet, exact factorization, and dual extraction strategy identified
- [x] 1 → 2  fully-proven: dependency-closed paper proof and Lean proof
- [x] 2 → 3 formalized: direct check, targeted build, and axiom audit pass; global lint blocked by unrelated unwired modules
- [ ] 3 → 4  publication-ready: standalone exposition and external novelty review

## Statement

For distinct complex nodes `lambda_k`, any nondegenerate interval `[a,b]`, and any coordinate `j`,
there exists `C_j>0` such that every coefficient vector `x` satisfies

```text
|x_j|^2 <= C_j integral_a^b |sum_k x_k exp(lambda_k u)|^2 du.       (1)
```

The theorem is proved for complete exponential-polynomial feature families, so confluent modes are
also covered. For a finite packet of distinct theta--Abel modes `z_i`, exact loop-71 factorization
gives

```text
sum_i a_i R_(z_i)(m,u)
 =sum_i [a_i(exp(c z_i)-1)(z_i+1)/z_i exp(z_i m)] exp(-z_i u).       (2)
```

Thus every selected mode coefficient is bounded by one fixed aperture constant times full coherent
packet energy. If selected coefficient is nonzero and `-1/2<Re z_j<0`, then for every real `p`,

```text
exp(m)/m^p * integral_0^A |sum_i a_i R_(z_i)(m,u)|^2 du -> infinity. (3)
```

For `z_j=rho_j-1`, this is exactly `Re rho_j>1/2`.

## Proof

Distinct exponential-polynomial features have a strictly positive interval Gram matrix. Invert its
moment map against coordinate vector `e_j`, producing compact dual extractor `g_j`. Exact pairing
recovers `x_j`; complex integral Cauchy--Schwarz gives `(1)`, uniformly over all coefficient phases.
Apply `(1)` to factorization `(2)`. Positive width makes `exp(cz_j)-1` nonzero in `Re z_j<0`, while
`z_j!=-1` makes Abel factor nonzero. Standard exponential-versus-power asymptotics then gives `(3)`.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelFiniteModeObservability.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Capstones:
  - `exists_exponentialPolynomialInterval_coordinate_observability`
  - `xiPhysicalThetaAbelFiniteModeResponse_eq_intervalCombination`
  - `exists_xiPhysicalThetaAbelFiniteMode_coordinate_observability`
  - `tendsto_exp_mul_xiPhysicalThetaAbelFiniteModeEnergy_div_rpow_atTop`

## No-go closure

- **Exact killing mechanism:** Finite coherent interference cannot hide any selected distinct mode:
  a fixed aperture dual recovers its coefficient with a uniform `L²` bound.
- **Strongest positive survivor:** Coordinate-by-coordinate observability `(1)` plus exact physical
  packet factorization `(2)` and supercritical divergence `(3)`.
- **New insight:** Loop-71 obstruction is not an artifact of diagonalizing too early. It survives
  arbitrary coherent cancellation inside every finite zero packet. Only an infinite, height-
  nonuniform tail can still cancel a supercritical finite coordinate.
- **Status:** Survivor paper- and Lean-proved. No assertion is made that actual infinite explicit-
  formula tail is uniformly negligible; that is now exact open core.

## Novelty audit

Finite exponential independence, positive Gram matrices, Ingham-type observability, and Turán power-
sum methods are classical. Primary-literature audit through 2026-08-27 also found modern Selberg-
integral and pair-correlation work, but no source locating this exact physical theta--Abel packet,
its restored multiplier, or coordinate-observability obstruction at FCRJ rate. Candidate-new claim
is restricted to route-specific synthesis `(1)--(3)` and exact infinite-tail boundary.

## Log

- 2026-08-27 — paper proof, Lean proof, umbrella wiring, axiom audit, corpus audit, and targeted primary-literature audit complete
