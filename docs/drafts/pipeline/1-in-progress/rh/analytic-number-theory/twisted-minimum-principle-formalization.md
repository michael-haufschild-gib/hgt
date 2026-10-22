# Twisted minimum principle (TMP): paper proof and formalisation programme

**Status:** SUPERSEDED. TMP is proved in Lean by the dual route: `RHTower/TwistedArcMinimumPrincipleProof.twistedArcMinimumPrinciple_holds`
(standard axioms). The proof uses no positive finite certificate; its ingredients are the certificate's stream function
ψ = Σ a_i y K₁(k_i y) sin(k_i x), the half-domain stream minimum principle (`HTGeometry/ModularHalfDomainStreamMinimumPrinciple`), and a
corner second-derivative comparison. Consequences: `riemannHypothesis_iff_primeBlindPositive_unconditional` and
`WeilConeUniquenessUnconditional.eq_vonMangoldt_of_weilPositiveFull` (the Weil cone has at most one point). The
potential-theory programme below (M3–M6) is not needed; the primal κ̃* construction is kept only as paper mathematics.

## Statement
Some nonzero positive finite measure on the modular bottom arc annihilates every twisted moment
M_n(u) = ∫ g_u(x) cos(2π(n+2)x) dx, n ≥ 0. Hence `TwistedArcMinimumPrinciple`, and by
`riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple` [L], RH ⟺ PBAP.

## Proof skeleton
1. **Legendre bridge.**
   - 𝒟_x(Q_u^{−½}) = ℒ_u(Q_u^{−½}), with Q_u(x) = x² − 2ux + 1, 𝒟 = −∂_x x²∂_x and ℒ = ∂_u(1−u²)∂_u (algebraic identity).
   - So g_u = √y·ℒ_u²ψ_u and M_n(u) = 4√y·ℒ_u²[K₀(2πm√(1−u²))cos 2πmu], m = n+2. Use the corpus formula
     ∫P'sin = −4aK₀cos and differentiation under the integral.
2. **Potentials on F** (fundamental strip above the arc, cusp at ∞, glued corner P of angle 2π/3).
   - Ψ̃₁ = I₀(2πy)cos 2πu − D_g, with g the data of the I-mode and D_g its bounded extension.
   - K̃_P is the corner Martin kernel, normalised to 1 at the cusp.
   - β = ω(g) > 0 [L corpus].
   - Ṽ* = Ψ̃₁ + βK̃_P has no constant and no log term at the cusp.
3. **Clamped deflection.** κ̃* solves (cosh²κ̃'')'' = σ*, with σ* the flux of Ṽ*, clamped at ±S, in s = log tan(α/2).
4. **Blindness.**
   - 1D integration by parts and 2D Green on F with the excised corner.
   - The two regularisations differ by a functional of the 1-jet at P that vanishes on Ṽ = 1 and Ṽ = log y.
   - Mode orthogonality at the cusp then gives ∫M_n dκ* = 0.
5. **Positivity.**
   - The cumulative flux Φ equals the stream function χ* on the arc.
   - χ* solves the mixed problem (L*χ = 0, Neumann on the arc, 0 on u = 0 and u = ½, positive cusp and corner
     behaviour).
   - Hence χ* ≥ 0 by the mixed minimum principle (M5), so the shear M' = Φ ≥ 0 on [0, S).
   - `nonneg_of_coshSq_clampedBeam_of_cumulativeLoad` [L] then gives κ̃* ≥ 0.

## Lean modules
- M0 [L, done] `HTGeometry/ClampedBeamCumulativeLoad`: clamped 𝔐² positivity under a load with nonnegative cumulative
  moment, with singular ends allowed.
- M1 [L, done] `RHTower/TwistedArcLegendreBridge` (τ_c = ℒ²[Q_c^{−½}]); also `RHTower/TwistedArcLegendreForm`.
- M2 [L, done in weak form] `RHTower/TwistedArcStreamMoment.integral_twArcMoment_mul_legendreKernel`.
- M3a: corner sector modes in hyperbolic polar coordinates at P. The radial parts are (sinh R)^{−½}{P_n, Q_n}(coth R),
  n = 3k+1, and are elementary for n = 1 (coth R, R coth R − 1). Prove the ODE identities, then the sine-series
  expansion of a solution in the sector R < log 3.
- M3b: global existence (C1) of D_g and K̃_P. Candidate routes:
  - (a) 3D Perron for the periodic chain of unit balls: mean value property by rotation averaging, a local solver, and
    exterior-sphere barriers at every boundary point, including the edge circle;
  - (b) a variational weak solution with regularity proved by separation of variables in hyperbolic polar coordinates
    (sectors at P and i, disks inside, half-disks on the arc);
  - (c) Schwarz alternating between explicit pieces (corner sectors at P and i, and the cusp strip y > 1), with
    contraction from the minimum principle.
- M4: Green identity on F and corner 1-jet matching.
- M5 [L, principle done] `HTGeometry/ModularArcStreamMinimumPrinciple.nonneg_of_neumann_on_modularHalfArc`. This replaces
  the nodal two-domain lemma. Remaining: construct the stream function χ* of Ṽ* and verify the hypotheses (interior
  equation, Neumann on the arc, zero on the sides, cusp and corner signs).
- M6: assembly into `TwistedArcMinimumPrinciple`.
