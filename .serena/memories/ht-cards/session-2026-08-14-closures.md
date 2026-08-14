# ht cards 1/3/5 — what this session closed, and the exact residue

## Card 1 `helson-universal-ht-arbitrary-divisor-orthogonality`

**CLOSED: the boundary-everywhere seam, unconditionally (Saksman–Webb NOT needed for it).**
`HTGeometry/HelsonCubeRootNonContinuation.lean`. Mechanism: the constant phase `χ ≡ ω`, `ω` a
primitive cube root of unity. Since `1, ω, ω̄` are the cube roots of `1`,
`(1-ωx)(1-ω̄x)(1-x) = 1-x³`, so multiplying the Euler products of `χ`, its conjugate and the trivial
phase gives `‖Z_ω(σ)‖²·ζ(σ) = ζ(3σ)` on the real axis `σ > 1` (the conjugate phase is the complex
conjugate there). Hence `‖Z_ω(σ)‖²` vanishes to order exactly **one** as `σ ↓ 1`
(`ζ(3) ≠ 0`, `(σ-1)ζ(σ) → 1`), while a function meromorphic at `1` has `‖F(σ)‖²` vanishing to an
**even** order. `2n ≠ 1` — done. Then: continuability transfers along finite modifications, so
every finite modification of that phase is noncontinuable, and those are dense.
Gives `dense_compl_continuableStratum`, `frontier_continuableStratum_eq_univ`,
`nowhereContinuous_continuationIndicator`, `no_continuous_factorization_continuationIndicator`.

**CLOSED: Pong's conclusion for `Z_χ` itself + the labelled isomorphism `Φ_(χ,ψ)`.**
- `HTGeometry/ArithmeticFunctionGeneralJacobian.lean` — the Shapiro–Sparer bridge WITHOUT the
  prime-support restriction. KEY: the Dirichlet algebra is a domain, so
  `algebraicIndependent_of_domain_jacobian` (corpus-owned, `JacobianDomainCriterion.lean`) needs only
  `det ≠ 0`, and that is decided at `n = 1`: evaluation at `1` is a ring hom `𝒜 →+* ℂ`
  (`arithmeticEvalOne`) and `(∂_q b)(1) = b q` with no support hypothesis. Chain up to
  `algebraicIndependent_fractionArithmetic_of_tailIndependent` (over `finitePrimeCoefficientField`).
- `HTGeometry/HelsonZetaShiftedJetIndependence.lean` — `helsonClockJet χ α c k` (coefficients
  `χ(n)n^{-α}(c log n)^k`), `differentialJet_helsonClockJet` (the corpus derivation is
  `f ↦ I • logWeight f`, so `c = I`), tail independence via the corpus shift–jet palette,
  `algebraicIndependent_of_finite_subfamilies` for the unbounded jet order, then
  `helsonShifts_differentialIndependent` and `helsonLabelledAlgEquiv`.

**OPEN**: `Haar(M) = 0` (Saksman–Webb/Seip) and Andersson Thm 5 (divisor surjectivity).
Note `Haar(M)=0` is no longer load-bearing for anything else on the card.
Note: `M` is invariant under the dense subgroup of finite modifications, so a 0–1 law gives
`μ(M) ∈ {0,1}`; excluding `1` is the whole content and needs the critical-line theory.

## Card 3 `irrational-power-canonical-products-…-gevrey-slope-rigidity`

`(4)`–`(6)` are now CLOSED at every genus. The genus chain
(`HTGeometry/BarnesKernelMellin`, `RHTower/BarnesMellinGenus{Representation,Expansion}`,
`RHTower/BarnesCanonicalProductExpansion`) was built by another session; KEY IDEA:
`D log E_g(-u) = (-1)^g u^{g+1}/(1+u)` and `mellin (barnesModel g) w = (-1)^g(-π/sin πw)` on
`-(g+1) < Re w < -g`, so the genus-`g` sum has the SAME integrand as genus zero, only the strip
moves. This session added the derivative-compatible half:
`RHTower/BarnesMellinGenusEulerDerivative.lean` — `barnesGenusEulerSum`,
`eulerIterate_barnesGenusEulerSum`, **`barnes_genus_poincare_expansion_euler`**; and
`barnes_expansion_powerCanonicalProduct_euler` in `BarnesCanonicalProductExpansion.lean`, which is
`(6)` for `x W_s'/W_s` itself.

**OPEN — the single remaining item**: the Sibuya–Ramis exact Newton-slope theorem.
Assessment of routes (all deep): (i) Gevrey spaces + Newton polygon of the linearized operator +
Malgrange index + nonlinear fixed point; (ii) resurgence — the `s`-Borel transform of the tail is
explicitly MEROMORPHIC on `ℂ` with simple poles at `-(2πn)^s e^{±iπs/2}`, so the tail is
`1/s`-summable; a "singularities lie in a finitely generated semigroup" argument runs into
four/six-exponentials territory. (iii) Maillet–Malgrange alone is NOT enough (it only bounds the
order from above by a rational).

## Card 5 `nonautonomous-rational-complete-tail-orbifold-classification`

Untouched this session. Residue: the Lie–Cartan/Casale classification of proper transitive rational
differential groupoids on a curve into `G1/G2/G3` (used only in §2). Another agent appears to be
building the triangle-group/monodromy-cover layer (`VonDyckTriangleGroup`,
`HurwitzTriangleCoverTower`, `OrbifoldMonodromyCover`, `MonodromyVoltage*` are parked unwired) —
do not duplicate that work.

## Working notes
- Do NOT blanket-`pkill` lean: other agents run `lake env lean` concurrently in this repo.
- The lint gate's "owned module unreachable from umbrella" errors are other agents' parked modules.
