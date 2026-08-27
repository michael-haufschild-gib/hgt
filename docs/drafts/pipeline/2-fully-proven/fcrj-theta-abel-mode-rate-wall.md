# FCRJ theta--Abel spectral-mode rate wall

- **ID:** fcrj-theta-abel-mode-rate-wall
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/critical-multiplicative-compensated-cancellation-rh.md
- **Statement:** One exponential normalized-theta mode has an exact positive aperture-energy coefficient and a sharp three-regime transition at `Re z = -1/2`; every supercritical mode defeats every polynomial after FCRJ `exp(m)` renormalization.

## Goal

Determine whether loop-69 raw theta--Abel `L²` provider can be bounded by estimating explicit-formula
zero modes separately, and identify exact spectral rate forced by one mode.

## Gates

- [x] 0 → 1  in-progress: source-pure one-mode response and aperture energy identified
- [x] 1 → 2  fully-proven: dependency-closed paper proof and Lean proof
- [ ] 2 → 3  formalized: targeted build and axiom audit pass; global lint blocked by unrelated unwired modules
- [ ] 3 → 4  publication-ready: standalone exposition and external novelty review

## Statement

For `z in C`, define one normalized-theta exponential mode response

```text
R_z(m,u)=exp(z(m+c-u))-exp(z(m-u))
         +integral_(m-u)^(m+c-u) exp(zh) dh.
```

If `z != 0`, exact Abel transport gives

```text
R_z(m,u)=exp(z(m-u)) (exp(cz)-1) (z+1)/z.
```

For `Re z<0`, raw aperture energy factors exactly as

```text
J_z(A,c,m)=integral_0^A |R_z(m,u)|^2 du
          =exp(2 Re(z)m) K(A,c,z),

K(A,c,z)=|exp(cz)-1|^2 |(z+1)/z|^2
         *[exp(-2 Re(z)A)-1]/[-2 Re(z)].
```

If `A>0`, `c>0`, `Re z<0`, and `z!=-1`, then `K(A,c,z)>0`. Therefore:

```text
Re z < -1/2 : exp(m) J_z(A,c,m) -> 0,
Re z = -1/2 : exp(m) J_z(A,c,m) = K(A,c,z),
Re z > -1/2 : exp(m) J_z(A,c,m)/m^p -> infinity
              for every real p.
```

For a nontrivial zeta zero `rho`, `z=rho-1`; wall is exactly `Re rho=1/2`.

## Proof

Integrate complex exponential primitive `exp(zh)/z`. Factoring endpoint difference produces
window multiplier `exp(cz)-1`; Abel integral contributes restoration factor `(z+1)/z`. Squared
complex norm is `exp(2 Re(z)(m-u))` times constant mode factors. Exact integration over `[0,A]`
produces `K`. Positive width plus `Re z<0` makes window multiplier nonzero; `z!=-1` makes Abel
factor nonzero; remaining real quotient is positive. Standard exponential-versus-real-power
asymptotics gives three regimes.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelModeRateWall.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Capstones:
  - `xiPhysicalThetaAbelExponentialModeResponse_eq`
  - `intervalIntegral_norm_sq_xiPhysicalThetaAbelExponentialModeResponse_eq`
  - `xiPhysicalThetaAbelExponentialModePrefactor_pos`
  - `tendsto_exp_mul_xiPhysicalThetaAbelExponentialModeRawEnergy_zero`
  - `exp_mul_xiPhysicalThetaAbelExponentialModeRawEnergy_eq_prefactor`
  - `tendsto_exp_mul_xiPhysicalThetaAbelExponentialModeRawEnergy_div_rpow_atTop`

## No-go closure

- **Exact killing mechanism:** Any provider that replaces full zero sum by nonnegative diagonal
  mode energies or absolute mode masses must pay `J_z`. One zero with `Re rho>1/2` then makes
  required `exp(m) poly(m)^{-1}` budget diverge, so such provider already presupposes right-half RH.
- **Strongest positive survivor:** Exact positive coefficient and complete subcritical/critical/
  supercritical rate classification above.
- **New insight:** Ordinary PNT extinction and RH-scale FCRJ decay are separated by a literal
  spectral phase transition. Remaining viable provider must preserve coherent cross-mode
  cancellation in full theta response, or turn desired energy rate into zero exclusion; diagonal
  positivity cannot supply missing unconditional estimate.
- **Status:** Survivor paper- and Lean-proved. It does not lower-bound full response by one mode;
  cross terms remain possible, so no RH conclusion is claimed.

## Novelty audit

Corpus search found no prior exact clipped theta--Abel one-mode coefficient or three-regime FCRJ
rate classifier. Primary-literature audit through 2026-08-27 found classical explicit-formula,
Selberg-integral, and short-interval variance work, including Goldston--Montgomery equivalences,
later pair-correlation refinements, and Selberg-integral/log-derivative comparisons. No source
located this exact physical aperture operator, Abel-restoration multiplier, positive coefficient,
or route-specific termwise-provider obstruction. Candidate-new claim is restricted to this exact
synthesis and classification, not to classical fact that an off-line zero changes PNT-error rate.

## Log

- 2026-08-27 — paper proof, Lean proof, targeted build, umbrella wiring, axiom audit, corpus audit, and targeted primary-literature audit complete
