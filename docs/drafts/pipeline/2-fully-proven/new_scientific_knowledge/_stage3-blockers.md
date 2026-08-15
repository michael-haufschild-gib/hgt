# The three classical inputs that gate the remaining cards

- **Type:** PLANNING NOTE (not a card)
- **Scope:** `ht/`, `constrained-prolate/`, `burnol/`

Two of the ten cards in these folders are at stage 3.  The other eight are gated on exactly three
imported classical theorems, none of which exists in mathlib in any form.  Each card's own new
mathematics is already formal; what is missing is the published input it cites.

| gate | cards | what has to be built |
|---|---|---|
| Dunster's uniform radial-PSWF Bessel expansion | the 6 `constrained-prolate` cards | uniform asymptotics of prolate spheroidal wave functions across a turning point |
| Lie--Cartan/Casale classification of proper transitive rational differential groupoids on a curve into `G1`,`G2`,`G3` | `ht/nonautonomous-rational-complete-tail-orbifold-classification` | transitive Lie pseudogroups and `D`-envelopes on a curve |
| Pong Thm 5.9, Andersson's arbitrary continuation divisors, Saksman--Webb/Seip almost-sure abscissa `1/2` | `ht/helson-universal-ht-arbitrary-divisor-orthogonality` | differential--difference independence of Dirichlet series; random Dirichlet series and the Bohr lift |

## Done: `burnol` and `ht/irrational-power-canonical-products`

`burnol-first-wall-cartier-residue-cancellation-law` and
`irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity` are at stage 3.
The second is the template for the others: its blocker was the **sharp half of Sibuya--Ramis**, and
it was closed not by formalizing that theorem but by observing that the card needed it for a single
implication about a single series whose coefficients are pinned on both sides, and proving that
implication directly.  Look for the same shortcut before starting a classical build.

## The prolate lane: what is already formal

The analytic machinery the prolate proofs use *around* Dunster's input is built, wired, axiom-clean:

    HTGeometry/GronwallVariableCoefficient.lean    Grönwall with a variable coefficient — the total
                                                   mass of the control in the exponent, which is
                                                   Olver's error-control function.  mathlib's
                                                   Grönwall is constant-coefficient; the corpus's
                                                   VolterraLinearIntegralEquation likewise.
    HTGeometry/LiouvilleGreenErrorBound.lean       Olver Ch. 6, oscillatory case
    HTGeometry/PerturbedOscillatorVolterra.lean    a genuine solution of `W'' + (u²+ψ)W = 0` obeys
                                                   the variation-of-constants equation, so the
                                                   bound holds from the ODE alone
    HTGeometry/OscillatoryIntegralVanishing.lean   nonstationary phase at explicit rate `1/c`,
                                                   arbitrary phase, and the `cos²` mean `1/2`

The last is literally the step named in
`constrained-prolate-radial-leakage-divisibility-spectrum.md` §1.

### A correction recorded on that card

The Lean bridge `nuLambdaDensity_tendsto_L1` asks for **a.e. pointwise** convergence of the finite
leakage density.  That hypothesis is **false** for this family — the density carries a factor
`cos²(c ξ(x) − π/4)` which, at fixed `x > 1`, oscillates in `[0,1]` and does not converge.  Only its
mean survives, and only after integration.  Do not try to prove it; the route is the genuine weak
one, and the `cos²` mean theorem above is its engine.

## Suggested order

1. **Prolate**, because one input unblocks six cards, and because the surrounding layer is done.
   The remaining piece is the Bessel-type *uniform* asymptotic at the turning point `x = 1`; the
   far-field oscillatory half is already proved.
2. **Nonautonomous**, whose consumers of the classification (`G1` transported tensor, `G2 -> G3`
   projectivization transport) are both formal already, so only the trichotomy is missing.
3. **Helson**, the largest of the three: three independent published inputs.

## Re-audit (after the radial-leakage card reached stage 3)

The table above is **wrong about the prolate lane**.  Dunster's uniform radial expansion is *not*
the gate: the corpus already contains a complete unconditional Dunster layer
(`ProlateCanonicalSeparationLimit.lean`: `tendsto_signedModeRadialData_s_zero`,
`tendsto_integral_Ioi_signedModeRadialDensity_unconditional`,
`tendsto_integral_Ioi_signedModeFirstRowRadialProduct_unconditional`, all axiom-clean).  What was
missing for `constrained-prolate-radial-leakage-divisibility-spectrum` was only the two-mode
combination, now built:

    HTGeometry/TwoModeSquareCombination.lean      Cauchy--Schwarz removal of a vanishing admixture,
                                                  in square and bilinear form
    RHTower/ProlateTwoModeRadialLeakage.lean      its instantiation on the canonical signed radial
                                                  modes, the constrained CCM coefficients, and the
                                                  two-mode radial dilation Gram matrix

That card is at stage 3.  Three cards are now at stage 3: `burnol`, `ht` card 3, and this one.

### The real gate for three of the five remaining prolate cards

`constrained-prolate-two-mode-ground-state`, `constrained-prolate-fixed-mode-spectral-ladder`, and
`constrained-prolate-fourier-parity-floor-separation` are gated on the **same two true-operator
inputs**, and on nothing else:

| input | statement | where it is needed |
|---|---|---|
| **(A) Fuchs asymptotics** | `1 − χ_n(λ)² ~ A_n λ^{2n+1} e^{−4πλ²}` for each fixed `n` | `(8)`–`(9)` of the ground-state card; every `Fuchs-model` gate in the ladder and parity cards |
| **(B) prolate-to-Hermite origin limit** | `e_n(0) → (2π)^{1/4} h_n(0)`, equivalently `ℓ_n(λ) → (2π)^{1/4}|h_n(0)|` | `(10)` of the ground-state card; `hl0`, `hl1` of `ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed` |

`RHTower/ConstraintCoordinateHermiteValues.lean` already proves that the four target constants are
one statement — `target_n = (2π)^{1/4}|h_n(0)|` — so **(B)** is a single limit, not four.
`RHTower/CCMHypothesisDischarge.lean` records that `hsum` and `hbessel` are discharged and `hgrow`
is *refuted* for the Fuchs amplitudes, so the ground-state transfer additionally needs its `hgrow`
route replaced (the trace route `exists_secular_tail_bound_of_trace` is the candidate).

Both **(A)** and **(B)** come from the same source: the scaling `x = t/√c`, `c = 2πλ²`, turns

```text
((1−x²)y')' − c²x²y = −χ y      into      u'' − t²u + (χ/c)u = (t²u'' + 2t u')/c ,
```

i.e. the harmonic oscillator with an `O(1/c)` perturbation.  So `χ_n(c)/c → 2n+1` and the scaled
eigenfunction converges to the Hermite function `h_n`.  **(B)** is the value of that limit at the
origin; **(A)** is the exponentially small tunneling correction on top of it.  Build the scaling
limit once and both follow.

### The other two prolate cards

- `constrained-prolate-full-radial-prime-charge-law` needs `(5)` (`G_λ(k,k)/d₁ ≤ C/k²`, reachable
  now from `radialProlateDensity_le_profileWeight` plus `arcsin(1/k) ≤ π/(2k)`), `(6)` (dominated
  convergence over `k`), and the cofinal off-diagonal sums `(7)`, `(8)`, `(8a)`.  The last three
  come from two parent cards that are themselves **still at stage 2**:
  `2-fully-proven/not_new_scientific_knowledge/ccm/ccm-exact-radial-nonstationary-sector-bound.md`
  and `.../ccm-exact-high-radial-first-row-bv-bound.md`.
- `constrained-prolate-arithmetic-dilation-operator-limit` has every matrix/operator/determinant
  layer formal, but the "discharge" theorems
  (`arithmeticDilation_projective_tendsto_discharged`,
  `arithmeticDilation_traceClass_traceNorm_limit_discharged`) still carry hypotheses `hoff`,
  `hdiag_le`, `hdiag_ev` about the actual radial Gram defect `E`.  Instantiating them needs the same
  quantitative row bound `|G_λ(j,k)| ≤ C d₁/(c j k |j−k|)` as the prime-charge card.

## Progress on input **(B)**: the four target constants are now *derived*, not quoted

`formal/GaloisForLFunctions/HTGeometry/HermiteOriginValues.lean` and
`formal/GaloisForLFunctions/RHTower/HermiteOriginConstraintTargets.lean` (both wired, axiom-clean)
identify the CCM constraint-coordinate targets with the actual orthonormal Hermite basis the corpus
already builds in `HermiteOrthogonality.lean`:

```text
derivative_hermitePoly_succ        p_{n+1}' = 2(n+1) p_n          (Appell law)
eval_zero_hermitePoly_add_two      p_{n+2}(0) = −((n+1)/π) p_n(0)
schwartzPair_hermiteSchwartz_self_eq   ⟨h_n, h_n⟩ = n!/(πⁿ√2)
norm_hermiteSchwartz_toLp_sq       ‖h_n‖² = n!/(πⁿ√2)
hermiteOriginValue n = p_n(0)/‖h_n‖
hermiteOriginValue_sq_{zero,two,four,six} = √2, √2/2, 3√2/8, 5√2/16
abs_hermiteOriginValue_{zero,two,four,six} = 2^{1/4}, 2^{−1/4}, √3·2^{−5/4}, √5·2^{−7/4}
```

The normalization is the corpus's own self-dual one, `h_n = p_n·e^{−πx²}`, and that is exactly the
normalization the problem produces: the prolate operator at aperture `λ` scales to the oscillator at
bandwidth `c = 2πλ²`, so the concentration length is `λ/√c = (2π)^{−1/2}`, an absolute constant, and
the limiting profile is literally `e^{−πx²}`.  Hence no `(2π)^{1/4}` bookkeeping factor is needed;
the four constants are `|ĥ_n(0)|`, and `hermiteOriginValue_sq_eq_targetSq_*` proves agreement with
the squared targets already recorded in `ConstraintCoordinateHermiteValues`.

**What is left of (B)** is only the convergence itself, `ℓ_j(λ) → |ĥ_{4j}(0)|`, i.e. the statement
that the actual signed prolate mode converges, after the `x = t/√c` rescaling, to the Hermite
function.  The three ingredients the corpus already owns for it:

- `SlepianSincCommutation.prolateSLAction_sincKernel` — the commuting-operator identity,
- `HermiteOscillatorEigen.prolateSLAction_hermiteFun` — the exact prolate action on a rescaled
  Hermite function, `−(2n+1)c·φ` plus a `c`-independent defect,
- `ConstrainedProlateSignedSpectrum` — the actual signed modes of `P_λ F P_λ`.

The missing link is the identification of the signed modes with prolate-ODE eigenfunctions
(operator commutation plus simplicity of the prolate spectrum) and the singular-perturbation limit.

### Input **(A)** is smaller than "Fuchs asymptotics"

The three cards do not consume the full Fuchs formula.  What their statements use is only

```text
d_0/d_1 → 0 ,   d_1/d_2 → 0 ,   d_2 − d_1 ∼ d_2 ,
```

i.e. **strict scale separation between consecutive `4j` concentration eigenvalues**, plus the
already-formal Bessel bound.  That is a separation statement of the same type as the radial
`tendsto_signedModeRadialData_s_zero` the corpus proves by clock-preserving tunneling plus Sonin
energy — look there before starting a WKB build.

## Progress on input **(C)**: the radial row bound

The parent card `not_new_scientific_knowledge/ccm/ccm-exact-radial-nonstationary-sector-bound.md`
listed three absent pieces.  All three are now built, wired, axiom-clean:

    HTGeometry/NonstationaryPhaseLowerBound.lean   the first-derivative test in the form
                                                   |∫ g cos(cξ)| ≤ (…)/(c·m) when |ξ'| ≥ m
    RHTower/RadialDilatedPhaseSeparation.lean      (2/3)(j−k) ≤ speed(j) − speed(k) and
                                                   j+k ≤ speed(j) + speed(k), for j,k ≥ 2, x ≥ 1,
                                                   uniformly in the turning parameter — no
                                                   differentiation in the index is used
    HTGeometry/GronwallScaledBound.lean            Grönwall with an arbitrary initial size
    RHTower/RadialPSWFAmplitudeVariation.lean      A(x) ≤ A(a)exp((1/c)∫‖ψ‖) and the O(V/c)
                                                   total variation of the interaction amplitudes

What remains for `(8)` is the **assembly**: insert the two-phase decomposition into the product,
integrate by parts once in each of the four phase branches with the separation `(6)` as the
nonstationarity constant, and sum.  After that, the arithmetic layer `(9)`–`(10)` is already formal
in `RadialGramOffDiagonalDecay.lean`, and the two consumers — the prime-charge card and the
arithmetic-dilation card — reduce to their remaining first-row sector.

### The `(8)` assembly is built

    HTGeometry/NonstationaryPhaseLowerBound.lean   first-derivative test, global and fully local
    HTGeometry/TwoPhaseOscillatoryProduct.lean     product-to-sum expansion + four-branch estimate
    RHTower/RadialTwoIndexOscillatoryBound.lean    the same for the exterior radial phases:
        |∫_a^b U_j U_k| ≤ (four budgets / ((2/3)(j−k))) / c   for 2 ≤ k < j, 1 ≤ a ≤ b, 0 ≤ s ≤ 1/2
    RHTower/RadialPSWFAmplitudeVariation.lean      real two-branch form of a real solution:
        (W x).re = radialAmpCos·cos(cx) + radialAmpSin·sin(cx), with derivatives and |·| ≤ 2‖a₊‖

All axiom-clean, all wired.  The remaining step for the actual Gram entries is the composition of
these amplitudes through the Liouville variable `ξ_s(rx)`, the `x^{−1/2}` geometric prefactor, the
`d_1` normalization, and the tail beyond a finite interval.

## Progress on the `nonautonomous` card: the Lie--Cartan rank bound

`HTGeometry/LieCartanFormalVectorFields.lean` (wired, axiom-clean) proves the algebraic core of the
classification the card imports:

    vfBracket f g = f g' − f' g
    hasOrder_vfBracket                  ord f ≠ ord g ⟹ ord [f,g] = ord f + ord g − 1
    hasOrder_le_two_of_finiteDimensional
        a finite-dimensional bracket-closed subspace containing a field of order 0 has
        every order ≤ 2, hence dimension ≤ 3

mathlib has no theory of Lie algebras of formal vector fields; this is built from scratch on
`PowerSeries` with an explicit `HasOrder` predicate, so no `ℕ∞` arithmetic is involved.  What
remains of the parent theorem is the conjugation to the normal forms `⟨∂⟩`, `⟨∂, z∂⟩`,
`⟨∂, z∂, z²∂⟩` and the groupoid-side translation into `(4)`–`(6)`.

## Progress on the `helson` card

The card is much further along than "three published inputs": Pong's conclusion for `Z_χ` itself and
the labelled isomorphism `Φ_(χ,ψ)` are already formal and unconditional, as are density, codensity,
`boundary(M) = Ω`, nowhere-continuity and the no-continuous-factorization theorem.  Two items were
open: `Haar(M) = 0` (Saksman--Webb/Seip) and Andersson's divisor surjectivity.

`HTGeometry/FiniteModificationZeroOne.lean` (wired, axiom-clean) reduces the first one:

    measurableSet_limsup_of_invariant     finite-modification invariance ⟹ tail event
    measure_eq_zero_or_one_of_invariant   ⟹ measure 0 or 1 under independent coordinates
    iIndep_coordSigma_infinitePi          coordinates of a product measure are independent

Since changing finitely many prime phases multiplies `Z_χ` by a finite Euler factor — meromorphic on
the plane — `M` is a tail event, so `Haar(M) ∈ {0,1}` and only `Haar(M) ≠ 1` remains.

### `(8)` is now numerical

    HTGeometry/OscBudgetSymbolBound.lean        oscBudget ≤ 2M/m + M'/m + MN/(3m²) under symbol
                                                decay, uniformly in the right endpoint
    RHTower/RadialSymbolTwoBranchBound.lean     SymbolTwoBranch bundles the regularity + decay;
        abs_integral_radial_twoBranch_symbol_le :
        |∫_a^b U_j U_k| ≤ 4(2M_jM_k/m + (M_j'M_k + M_jM_k')/m + M_jM_kN/(3m²))/c, m = (2/3)(j−k)

With `M_r = C√d₁/r` this is `O(d₁/(c j k (j−k)))` — the card's `(8)`.  The only remaining step for the
two consumer cards is producing the `SymbolTwoBranch` record for the actual PSWF solutions and the
phase-curvature bound; both are compositions of already-formal pieces.

### Lie--Cartan: the rank half is complete

    finrank_le_three, finrank_eq_three, exists_hasOrder_zero_one_two

A finite-dimensional transitive bracket-closed subspace of formal vector fields has dimension at most
three, and when it is three the realized orders are exactly `0, 1, 2`.  Remaining: the normal forms
and the groupoid-side translation.

### The `(8)` ingredient list is complete

    RadialTwoIndexOscillatoryBound   sub_one_le_xiEndpointPhase, le_dilatedRadialPhase
    RadialNormalFormPotentialDecay   |ψ(x)| ≤ 54/x² beyond the second dilation, uniformly in c
    XiAmplitudeDecay (pre-existing)  |A| ≤ 4/√x , |A'| ≤ 4/(x√x)
    RadialPSWFAmplitudeVariation     |P|,|Q| ≤ 2A(a)e^{V/c} ; |P'(Φ)Φ'| ≤ (κKL/c)/x²
    RadialSymbolTwoBranchBound       symbolTwoBranch_of_composition and the final estimate

so the two consumer cards now need only the bookkeeping instantiation naming `W`, `V`, `ψ`, `Φ` for
the concrete signed-mode data, plus the first-row sector (a separate parent card).
