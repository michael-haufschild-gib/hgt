# RN-P-7g: exact signed Sturm energy of the actual two-node span

- **Stage:** 3-formalized

Status: identities (1), (2) and (3), their integrability, the polarized
bilinear form, the port law and the actual projection orthogonality are
Lean-proved (`ThetaTwoNodeSignedSturmEnergy.lean`,
`ThetaTwoNodeProjectionSturmIdentity.lean`); see the Lean certificate.
Sign compensation remains open.

Fix `0≤x₁<x₂`, `h=x₂-x₁`, and use the actual theta source `k` and
`p=-(log k)'`. For `t≥0`, write `zᵢ=xᵢ+t`, `Fᵢ(t)=k(zᵢ)` and

    s(t)=(p(z₂)-p(z₁))/h,
    j(t)=(z₁p(z₂)-z₂p(z₁))/h,
    λ(t)=1/s(t),
    w(t)=2j(t)/s(t)+λ'(t).

For arbitrary real coefficients, put `f=c₁F₁+c₂F₂` and
`v=c₁z₁F₁+c₂z₂F₂`. Because `p(zᵢ)=s zᵢ-j`,

    f'=j f-s v,
    2fv = -(λ f²)' + w f².

The literal common-tail formula therefore gives the exact identity

    cᵀMc = f(0)²/s(0) + ∫₀∞ w(t) f(t)² dt,              (1)

where `Mᵢⱼ=H(xᵢ,xⱼ)`. Polarization gives the corresponding bilinear
identity on this same two-dimensional span.

## Analytic closure

The corpus proves `p'>0` and `p''>0` on `(0,∞)`, with smooth endpoint
extension. Thus `s>0`, `s'≥0`, `0<λ≤λ(0)`, and `λ'≤0`.
The positive decreasing function λ has a finite nonnegative limit.
FTC on finite intervals followed by monotone convergence proves
`∫₀∞ -λ'=λ(0)-lim λ<∞`.

Strict increase of `p(x)/x` gives `j≥0` for `z₁≥0`; since `p(z₁)≥0`,
`j/s=z₁-p(z₁)/s≤z₁`. Schwartz bounds give integrability of
`2(j/s)f²`. Boundedness of f and integrability of `-λ'` give
integrability of `λ'f²`. Finally `λ f²→0`, since λ is bounded and
f tends to zero. This justifies (1), including the exact boundary term,
without an assumed sign for w or an unproved decay estimate for p.

## Exact inverse-matrix consequence

Let `u=(k(x₁),k(x₂))`, `d=M⁻¹u`, `G=d₁F₁+d₂F₂`, and
`α=uᵀM⁻¹u>0`. The existing strict two-node determinant theorem makes
M invertible and positive definite. Then `G(0)=α` and `dᵀMd=α`, so

    α-s(0) = -(s(0)/α) ∫₀∞ w(t)G(t)² dt.                (2)

Thus the inverse-matrix feedback in the first RN-P-7e barrier is exactly
a signed scalar energy of the actual source representer. This is an
identity, not a positivity proof.

## Actual projection orthogonality

For `y>x₂`, let `c=M⁻¹(H(x₁,y),H(x₂,y))` and
`R(t)=k(y+t)-c₁F₁(t)-c₂F₂(t)`. Define E(t) as the positive extrapolation
defect of p at `y+t` from `z₁,z₂`. The affine law gives
`R'=jR-sX-k(y+t)E`, where X is the coordinate-source residual.
Polarizing the preceding calculation against an old-span function f gives

    Q(f,R)=λ(0)f(0)R(0)+∫ w fR-∫ λ f k(y+t)E.

For actual projection `Q(f,R)=0`. On the first port boundary `R(0)=0`,

    ∫ w G R = ∫ λ G k(y+t)E.                            (3)

The signed-energy compensation needed to combine (2),(3) with
`(α-s(0))B<k(y)E(0)` is still the hard open problem. The identity involving
R needs the same integral justification, retaining the forcing integral
as the difference of already integrable derivative/source terms.

Formalized continuation: `ThetaTwoNodeCenterFeedback.lean` proves that
`α(0,z)>s(0,z,0)` for every z>0, so the actual representer energy in (2)
is strictly negative throughout this family. The source-zero old-span
packet has exact positive signed energy `det(M) α`. Both signs occur on
the literal old-node span; see RN-P-7h for the exact square decomposition.

## Sign warning and next conjecture

At the center-anchored endpoint `x₁=0,t=0`, `j(0)=0` while
`s'(0)=(p'(x₂)-p'(0))/x₂>0`, so `w(0)<0`. Uniform positivity of this
density is false. The positive survivor is the exact signed decomposition
and the finite total negative variation of λ. No universal inequality on
arbitrary test functions can replace actual source-span/projection control.

Corpus search `theta secant Sturm weight` completed its configured stages
but refresh was incomplete and most compiler metadata was source-only or
pending. Returned source/candidate results supplied no matching identity.
Source dependencies are the actual common-tail formula, Schwartz source,
strict log-concavity, negative fourth log jet, and the new affine port law.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ThetaTwoNodeSignedSturmEnergy`, `GaloisForLFunctions.RHTower.ThetaTwoNodeCenterFeedback`, `GaloisForLFunctions.RHTower.ThetaTwoNodeProjectionSturmIdentity`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (clean under `lake env lean`, built as modules, axiom audit `[propext, Classical.choice, Quot.sound]` only):
`GaloisForLFunctions.RHTower.ThetaTwoNodeSignedSturmEnergy`, `GaloisForLFunctions.RHTower.ThetaTwoNodeCenterFeedback`
(corpus, audited) and the new `GaloisForLFunctions.RHTower.ThetaTwoNodeProjectionSturmIdentity`. All in namespace
`RHTower.ThetaSturm` (`ThetaCenterFeedback` for the continuation). Conventions: `k = thetaCuspFullSource`,
`p = thetaCuspLogDecaySlope`, `H = thetaTailFirstMomentKernel`, nodes `x < z` (card `x₁ < x₂`), `s = secant`,
`j = intercept`, `λ = reciprocal = 1/s`, `λ' = reciprocalJet`, `w = density`, `f = packet`, `v = coordinatePacket`.

| Claim | Lean declaration |
|-|-|
| Affine law `f' = j f − s v` | `packet_hasDerivAt` |
| `s > 0`, `s' > 0`, `λ' < 0`, `λ` antitone, finite limit, `∫ −λ' < ∞` | `secant_pos`, `secantJet_pos`, `reciprocalJet_neg`, `reciprocal_antitoneOn`, `reciprocal_limit_exists`, `reciprocalJet_integrable` |
| `j ≥ 0`, `j/s ≤ z₁` | `intercept_nonneg`, `intercept_div_le` |
| Integrability of `w f²` (any packet) | `density_square_integrable` |
| Common-tail formula `cᵀMc = ∫ 2 f v` | `energy_eq_integral` |
| Identity (1) | `energy_eq_boundary_add_signed_integral` |
| Polarized identity on the two-node span | `crossPairing_old_span` |
| Inverse-Gram representer: `M d = u`, `dᵀMd = α`, `α > 0`, `G(0) = α` | `representer_equations`, `representer_energy`, `feedback_pos` |
| Identity (2) | `feedback_sub_secant_eq_signed_energy` |
| Extrapolation defect `E > 0` for `y > x₂` | `extrapolationDefect`, `extrapolationDefect_pos` |
| Port law `R' = jR − sX − k(y+t)E` (three-node packets in general) | `portPacket_hasDerivAt`, `portResidual_hasDerivAt` |
| Integrability of the forcing `λ f k(y+·) E` (difference of integrable derivative/source terms) | `forcing_integrable`, `weighted_translate_product_integrable` |
| `Q(f,g) = λ(0)f(0)g(0) + ∫ w f g − d ∫ λ f k(y+·)E` (literal common-tail pairing) | `crossPairing`, `integral_pairing_eq_crossPairing`, `crossPairing_eq_boundary_add_signed_integral` |
| Projection coefficients `c = M⁻¹(H(x₁,y),H(x₂,y))`, `Q(f,R) = 0` on the old span | `portLeft`, `portRight`, `port_equations`, `crossPairing_portResidual_eq_zero` |
| `Q(f,R) = λ(0)f(0)R(0) + ∫ wfR − ∫ λ f k(y+·)E` with `Q(f,R) = 0` | `portResidual_signed_identity` |
| Identity (3): `R(0) = 0 ⇒ ∫ w G R = ∫ λ G k(y+·) E` | `representer_portResidual_signed_identity` |
| Continuation: `α(0,z) > s(0,z,0)`, negative representer energy, source-zero packet energy `det(M) α > 0` | `ThetaCenterFeedback.center_secant_lt_feedback`, `center_representer_signed_energy_neg`, `source_zero_packet_signed_energy_eq`, `source_zero_packet_signed_energy_pos` |
| Sign warning `w(0) < 0` at the center-anchored endpoint | `density_center_neg` |

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
