# Critical theta Mellin blow-up remembers Euler chronology

- **ID:** theta-euler-harmonic-tangent-chronology
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); no-go for a cutoff-independent two-parameter boundary invariant
- **Routes:** theta source completion, CCM-FU, Suzuki finite-to-completed transport
- **Status:** [PROVED HERE ON PAPER] [REAL ATOM MELLIN FORMALIZED] [SCALING LIMITS LEAN OPEN] [NOT RH] [EXTERNAL PRIORITY NOT CLAIMED]
- **Dependencies:** [theta Euler critical boundary mass escape](../../../3-formalized/theta/theta-euler-critical-boundary-mass-escape.md), unconditional Mertens third theorem and the asymptotic `sum_(p≤x) log(p)/p ~ log x` (both in the corpus). The standard Dickman transform is prior art; the claim here is its exact comparison with the two literal theta-source exhaustions, not novelty of that transform.

## Problem and failed reframe

The completed source has critical Mellin charge `1/2`; each admissible finite Euler stage has charge zero. A proposed two-parameter boundary law might try to resolve this jump by setting the Mellin displacement to `z/log R`, with `R` the first omitted arithmetic scale, and then assert that the blow-up depends only on the completed source. The assertion is false. Integer cutoff and finite-prime cutoff have different analytic scaling limits although both exhaust the same literal theta source and their first omitted positive integer is of scale `R`.

## Exact source observable

For each positive integer `n`, write `phi_n(x)=thetaCuspSourceTerm x n`. For a set `A` with absolutely convergent source sum near the critical Mellin parameter, let `S_A(x)=sum_(n in A) phi_n(x)`. Put

    G(w)=Gamma(w/2+5/4) pi^(-w/2-1/4).

The literal atom calculation in the cited card gives, near `w=1/2`,

    M_A(w):=integral_R exp(w x) S_A(x) dx
           =(w-1/2) G(w) Z_A(w+1/2),
    Z_A(s)=sum_(n in A) n^(-s).                         (1)

For `I_N={1,...,N}` the sum is finite. For `E_P={n≥1: every prime divisor of n is ≤P}`, it converges absolutely when `Re s>0`, and `Z_E,P(s)=prod_(p≤P)(1-p^(-s))^(-1)`. Both source observations are absolutely defined for `w` in a neighborhood of `1/2`.

## The two scaling laws

As `N→infinity`, locally uniformly for complex `z`,

    M_I,N(1/2+z/log N) → F_I(z)=(1/2)(1-exp(-z)).     (2)

As `P→infinity`, locally uniformly for complex `z`,

    M_E,P(1/2+z/log P) → F_E(z)
      =(1/2) z exp(gamma) exp(J(z)),
    J(z)=integral_0^1 (exp(-z u)-1)/u du,              (3)

where the integrand at `u=0` is `-z` and `gamma` is Euler's constant. The second profile is the familiar Dickman Laplace profile, with normalization fixed here by the literal theta atom. Both limits vanish at `z=0` and tend to `1/2` along positive real `z→infinity`, but

    F_I'(0)=1/2,   F_E'(0)=exp(gamma)/2 > 1/2.        (4)

Thus a cutoff-independent analytic two-parameter profile does not exist even for these two canonical cofinal exhaustions. This does not contradict the common scalar escaped charge: the latter is the far-positive-`z` endpoint of two different profiles.

There is a stronger complex diagnostic. `F_E` has no zeros away from `0`, whereas `F_I` has simple zeros at `2 pi i k`, every nonzero integer `k`. By local uniform convergence and Rouche's theorem, the finite integer Dirichlet head `sum_(n≤N)n^(-s)` has one zero at `s=1+(2 pi i k+o(1))/log N` for each fixed nonzero `k`. Every finite-prime Euler product is zero-free in its convergence half-plane. These finite-head zeros are chronology artifacts, not Xi zeros.

The difference cannot be repaired by a finite signed *translation-invariant convolution* at the tangent-measure level. The integer harmonic tangent measure is Lebesgue measure on `[0,1]`. The finite-prime tangent measure is the Dickman density `rho(u)du` on `[0,infinity)`, whose Laplace transform is `exp(gamma+J(z))`; this follows from (3), the standard Dickman Laplace identity, and uniqueness/continuity for finite Laplace measures. At every nonzero `z=2 pi i k`, the former transform is zero and the latter is nonzero. If a finite complex measure `K` satisfied `rho(u)du=1_[0,1](u)du * K`, Fourier transformation would make the latter value zero, a contradiction. The positive survivor is a **meromorphic pole-lattice transfer quotient**, not a bounded convolution kernel. This only excludes translation-invariant tangent transfer; it does not exclude a nonstationary, prime-marked source operator.

## Proof

Set `alpha=z/log N` in (1). Uniformly for `z` in a fixed compact set, the difference between `sum_(n≤N)n^(-1-alpha)` and `integral_1^N t^(-1-alpha)dt` is `O(1)`: sum each unit-cell error by `integral |(t^(-1-alpha))'|`, whose total is uniformly bounded once `Re alpha≥-1/2`. Since `alpha integral_1^N t^(-1-alpha)dt=1-exp(-z)` and `G(1/2+alpha)→G(1/2)=1/2`, this proves (2), including `z=0` by analytic continuation.

For (3), put `Q_P(alpha)=prod_(p≤P)(1-p^(-1-alpha))^(-1)` and `alpha=z/log P`. Mertens gives `Q_P(0)/log P→exp(gamma)`. Expand the logarithm of `Q_P(alpha)/Q_P(0)`. Prime-power terms with exponent at least two converge uniformly to zero as `alpha→0`, by domination with `sum_p p^(-3/2)`. The remaining term is

    sum_(p≤P) [exp(-z log p/log P)-1]/p.

The probability-scale measures `(1/log P) sum_(p≤P)(log p)/p delta_(log p/log P)` converge weakly to Lebesgue measure on `[0,1]`, since their cumulative mass up to `u` tends to `u` by `sum_(p≤x)log p/p ~ log x`. Test with the continuous function `(exp(-zu)-1)/u`, uniformly on compact `z` sets. The result is `J(z)`, and exponentiation proves (3). Equation (4) follows by differentiation and the corpus inequality `gamma>1/2`. Rouche gives the zero statement. The no-convolution assertion uses only the convolution theorem for finite measures and the displayed nonzero Dickman transform; it assumes no sign for the putative transfer measure.

## Whole-route meaning and limit

This falsifies a universal RG-style boundary profile based only on pointwise completion plus the first omitted scale. Euler chronology is a coordinate retained by the critical blow-up. The prime-specific leading profile itself cannot orient Xi zeros: it is the classical, zero-free Dickman transform, derived from first-order prime distribution. Any RH-bearing two-parameter law must act on the signed arithmetic deviation from that profile and preserve prime–polar–Gamma cancellation. Merely formalizing (2)–(3) or using the scalar half-charge as a positivity certificate would be theatre.

Even the **entire analytic germ and all Taylor coefficients** of this leading prime profile are determined by `J`, hence by the first-order prime-log distribution. Taking more derivatives of the limit does not recover the discarded prime error. The missing datum is the *rate and orientation of convergence* to the tangent law, not a higher jet of the tangent law itself.

More sharply, a fixed spectral point `w≠1/2` has blow-up coordinate `z=(w-1/2)log P`, which leaves every compact set as `P→infinity`. Thus compact-local convergence in the blow-up variable cannot locate even one fixed off-line Xi zero. The necessary next estimate is a *growing-`z`*, source-faithful comparison, at the same scale where the zero-sensitive prime remainder ceases to be negligible. This is the hard gate; the Dickman law only identifies the RH-blind leading sector.

**Lean boundary:** `ThetaEulerAtomMellin.lean` now proves the exact radial, logarithmic, and literal-atom Mellin laws for real `w > -5/2`. Its targeted `lake --old build ...:olean` passed; the module is wired into `RHTower.lean` without an umbrella build. Equation (1) for general complex `w`, the two locally uniform scaling laws, and the resulting no-go remain to formalize. Existing Lean has every atom's zero critical charge, the completed half-charge, Mertens third theorem, the prime-window Lévy limit (in `PrimeBoundaryPoissonJumpField.lean`), and requisite harmonic/PNT infrastructure. The Dickman component is already in the Lean corpus; the distinctive unformalized comparison here is between literal integer and finite-prime theta exhaustions. No RH claim is made for this card.
