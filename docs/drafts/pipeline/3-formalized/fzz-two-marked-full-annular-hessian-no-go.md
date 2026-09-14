# Full two-marked FZZ annular Hessian

- **ID:** fzz-two-marked-full-annular-hessian
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarParityTwoMarkedSourceContact`; Halder--Jafferis, arXiv:2402.00932, §3.2.3
- **Statement:** Full compact opposite-winding mixed log response is exactly direct contact plus connected tilted radial fluctuation.

## Goal

Close missing absolute depth-one compact Hessian in FZZ-P source chain:
`neutral source → mixed Ward orientation → balanced-Gamma saturation → passivity → RH`.

## Gates

- [x] 0 → 1  in-progress: source-pure two-marked annular integral and exact attack
- [x] 1 → 2  fully-proven: closed-form integral and two-variable chain rule
- [x] 2 → 3  formalized: targeted build green; axiom audit standard only
- [ ] 3 → 4  publication-ready

## Result

With `a₀=-exp u`, contact `C`, level `k`, tilted mean
`μ(a)=exp(a)/(exp(a)-1)-1/a`, and variance
`V(a)=1/a²-exp(a)/(exp(a)-1)²`, Lean proves

`∂ε∂δ log Z_L(0,0) = C(L+μ(a₀)) + k²V(a₀)`.

Consequences: response is affine with nonzero negative slope `C`, surjective in `L`, and has one
and only one neutral geometry at each physical level.

## Scope

This discharges complete depth-one annular Hessian, not all-depth neutral torus sum. Corpus proves
torus neutrality activates every depth for nonzero coupling; that infinite completion remains open.

## Novelty audit (through 2026-08)

Corpus search found only relative response `C(k)L`, not absolute Hessian. Primary-literature search
found no matching contact--variance classification; arXiv:2402.00932 leaves torus one-point and
finite-cutoff boundary-term problems open. Claim is limited to this exact annular source model.

## Lean

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedFullAnnularHessianNoGo`
- Main theorem: `fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv`
- Classification: `existsUnique_fzzTwoMarkedAnnularFullMixedResponse_eq_zero`
- Route kill: `fzzTwoMarkedAnnularUniversalSignRouteKilled`
- Audit: targeted leaf build PASS; axioms `[propext, Classical.choice, Quot.sound]`; formal lint PASS
