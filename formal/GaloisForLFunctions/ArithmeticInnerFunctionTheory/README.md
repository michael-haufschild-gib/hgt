# Arithmetic Inner-Function Theory (AIF)

Namespace `GaloisForLFunctions.ArithmeticInnerFunctionTheory`; umbrella
`ArithmeticInnerFunctionTheory.lean`. Every theorem is unconditional; a statement about RH is an
equivalence with RH, and no theorem has RH as a premise.

*First draft: targets marked (target) are the programme's planned pillars.*

## 1. Motivation

On `Re s > ½` the function `E(s) = (s − 1)ζ(s)/s` factors as an inner function times an outer function, and
its inner factor is the Blaschke product of the right zeros. RH says this inner factor is trivial. Every
route in the corpus reads this one object: Balazard–Saias–Yor reads its mass at `1`, `N(ρ) ≤ Πϱ` reads it
at a zero, the Krein–Langer index reads its degree, Schur parameters and the anchor reflection `r(a)` peel
it, Carleson separation is its regularity.

Every available tool stops for a proved reason: size, positivity preservation, sieve data, barriers, short
mollifiers, finite computation, tensor amplification, integrality, parabolic monotonicity, unitarity,
torus-uniform Euler positivity. Each route has a one-sided sign proved, and the opposite sign is RH. So what
is missing is not a sharper estimate of the first expression but a *second expression*.

AIF studies inner factors of arithmetic functions and the passive systems attached to them, in the language
of Hardy space, Krein systems and critical Hardy inequalities. These theories exist; what is new is arithmetic
forcing: which inputs can make an inner factor trivial, and at what zero slack.

## 2. Objects

| Object | Meaning |
|---|---|
| Inner field | `I(w) = P_w[log|ζ|] − log|E(w)|`, `w ∈ Re s > ½`: the Green potential of the right zeros |
| Inner mass | `I(1)`, the BSY integral |
| Green kernel, pseudo-hyperbolic ratio | `G(w,ρ) = log(1/ϱ(w,ρ))`, `ϱ(w,ρ) = |w−ρ|/|w+ρ̄−1|` |
| Budget | `P_w[|EM|²]` for a mollifier `M`, the upper side of the Szegő formula |
| Carleson measure of near-line zeros | `Σ_ρ b_ρ δ_ρ`, `b_ρ = Re ρ − ½`; shadow `[γ−b, γ+b]`; crowd `Σ_ρ b_ρ P_ρ(t)` |
| Passive layered medium | canonical flow `r, q` with `κ = artanh r` |
| Prime insertion | `T_p = (1 − 2cos(θ_p)σ_p + σ_p²)^{−1}` on amplitudes over `log ℕ` |
| Hecke–Hankel form | `Σ_{D|(M,M')} a(MM'/D²)` |
| Curve inner mass | `Σ_{|β|>1} log|β|`, the Mahler measure of the normalized `L`-polynomial |

## 3. Language

Budget instead of exact sign; hyperbolic geometry of zeros (depth, crowd, Carleson box, shadow); slack as a Szegő
product; prime weights dual to blind states; the Laguerre form as common observable.

## 4. Mechanisms

1. **A second expression.** The first expression of the inner mass is the zero sum, manifestly `≥ 0`. The second
   is the Szegő formula: `exp(2I) = inf_M ∫|EM|²dP₁`, whose every member is a manifest upper bound, and which is exact.
2. **Phase locking.** For a fixed summable amplitude, locked phases `(p^{ib})` and free torus phases give the same
   positivity (Kronecker). Locking can produce positivity only through correlation of amplitude with height.
3. **Passivity from initial data.** In the hyperbolic coordinate the anchor flow is `κ′ = q − sinh 2κ`: it comes
   down from infinity, so contact is local.

## 5. Traps (draft)

| Trap | Truth |
|---|---|
| A mollifier loses information about the zeros | Szegő: the infimum over mollifiers is exactly the inner mass |
| `N(ρ) ≤ Πϱ` is lossy | It is an equality over all other zeros (target) |
| Phase locking is a free extra positivity | For fixed summable amplitude it equals torus positivity (target) |
| Reflectors sit on `½log n` | Only to first order; multiple reflections force compensating reflectors (target) |

## 6. Questions

1. When is a frustrated form nonnegative at zero slack?
2. What replaces Allegretto–Piepenbrink?
3. Which cones of amplitudes are invariant under prime insertion with locked phases?
4. When is an echo train passive?
5. Why is `(β, s) = (1, 0)` critical?
6. Can an arithmetic inner factor be finite and nontrivial?

## 7. Tools to build

Exact certificates for frustrated forms; a priori estimates for Krein systems with soft atomic kicks, free of `1/μ`;
concentration-compactness for arithmetic quadratic forms; Carleson embedding at the critical scale with arithmetic
coefficients; inverse scattering with prime data. Test cases: the function-field chain, `{2,3}` spectra, one critical ratio.

## 8. Foundational pillars (target)

| Pillar | Statement |
|---|---|
| Poisson–Jensen identity | `I(w) = Σ_ρ m_ρ G(w,ρ)` at every centre; no singular inner factor |
| One-point RH | RH ⇔ `I(w₀) = 0` at one nonzero point `w₀` |
| Derivative law | `N(ρ) = Π_{a≠ρ} ϱ(ρ,a)^{m_a}` |
| Szegő formula | `exp(2I(1)) = inf_Q ∫|ζ|²|e^{Q}|² dP₁` |
| Curve chain | inner mass = Mahler measure; Castelnuovo ⇔ Carathéodory ⇔ trivial inner factor |
| Insertion cone | torus positivity ⇔ Hecke–Hankel positivity; locked = torus for summable amplitudes; log-concave tails excluded |
| Anchor flow | comes down from infinity; energy identity; Darboux pair |
| Certificate | causal factorization replaces the positive supersolution; slack = Schur product |

## 9. Place in the research

Receiver side of the sign block, with interfaces to MZF (derivative law, camera), CTF-BSY (inner mass), CHT and CSTW
(canonical system, datum), TH (prime insertion), FADF (frustration), AKL (index), GWZ (lattice Schur parameters), ACS (curves).
The production side (square-root precision) is not obviously part of the field; the corpus proves no bridge.

## 10. Criteria

A proof of the field's main statement must be false on every corpus fake (columns, golden, twins, shifted products, heated
kernels), parity-breaking, locally pure, at unbounded aperture; recover Weil's proof over `𝔽_q` including Castelnuovo; and see
incommensurability of `log p`, since periodic data admits finite impurity.

A contribution must be an exact identity, an equivalence, a classification, a sharp law, or a no-go with its strongest positive
survivor; it must be unconditional; and it must say which data it reads.
