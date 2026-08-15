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

## State after the Lie--Cartan and high-first-row session

### `ht/nonautonomous-rational-complete-tail-orbifold-classification` — PROMOTED to stage 3

`HTGeometry/LieCartanNormalForms.lean` (wired, axiom-clean) closes the last imported parent, the
**normal-form half** of the Lie--Cartan trichotomy, in the invariant form the card's `(4)`--`(6)`
actually assert: a transitive finite-dimensional bracket-closed algebra of formal vector fields
preserves a weight-one differential (rank one), an affine connection (rank ≤ two) or a projective
connection (rank three), and in every case a projective connection.

    vfTensorDefect / vfAffineDefect / vfProjDefect     the three infinitesimal actions
    vfAffineDefect_eq_deriv        δ_f μ = (f μ + f′)′            — the affine primitive
    deriv_projNumerator            ((f′)² − 2 f f″)′ = −2 f f‴    — the projective quotient
    coeff_three_eq_zero_of_bracket [e₁,e₂] ∈ K e₂ forces coeff 3 e₂ = 0, which is exactly what
                                   makes that quotient regular
    vfProjDefect_vfBracket         the cocycle identity
    eq_zero_of_vfRho_eq_zero       ρ(e₂) w = 0 ⟹ w = 0 for an order-two e₂
    exists_projConnection          the capstone
    lieCartan_normal_form_trichotomy

No formal change of variable is used: the conjugation to `⟨∂, z∂, z²∂⟩` is replaced throughout by
the invariant equation it exists to certify.

### `ccm-exact-high-radial-first-row-bv-bound` — the estimate machinery is formal

`RHTower/CCMHighRadialFirstRowBV.lean` (wired, axiom-clean): `BVWeight`, `bvWeight_of_symbol`,
`firstRowWeight_symbol_bounds`, `integral_abs_mul_dilatedRadialPhaseAccel_le`,
`abs_integral_highRadial_firstRow_le`, `abs_setIntegral_Ioi_highRadial_firstRow_le`,
`summable_highRadial_logMajorant`, `tsum_weighted_highRadial_le`,
`tendsto_tsum_log_shift_div_sq_tail`.

This is the card's `(4)`, `(5)`, `(6)`, `(10)`, `(13)` and the interface form of `(7)`.

### The exact remaining item for the two charge/dilation cards

`constrained-prolate-full-radial-prime-charge-law` needs `(7)`, `(8)`, `(8a)`:

| item | state |
|---|---|
| `(7)` off-diagonal `j,k ≥ 2` | formal — `ccm-exact-radial-nonstationary-sector-bound` is at stage 3 |
| `(8)` low first row `k ≤ λ²` | formal — `ccm-exact-finite-aperture-first-row-vanishing` is at stage 3 |
| `(8a)` high first row `k > λ²` | machinery formal; **one input missing** |

The missing input is a **half-power symbol bound for the Bessel-comparison amplitude of the first
factor on all of `[1,∞)`**, i.e.

```text
|A_c(x)| ≤ Q/√x ,      |A_c′(x)| ≤ Q′/(x√x)     for x ≥ 1,
```

where `A_c = √(ξ_c/ξ_c′)·(x²−1)^{-1/2}` is the *pole-uniform* amplitude, which is regular at the
turning point `x = 1` — unlike the Liouville--Green amplitude `xiAmplitude`, whose corpus bounds
`abs_xiAmplitude_le_four`, `abs_xiAmplitudeDeriv_le` hold only for `x ≥ 2`.  With that bound,
`firstRowWeight_symbol_bounds` and `bvWeight_of_symbol` give `(7)` and hence `(12)`, `(13)`.

The derivative of the Bessel factor is what carries the bandwidth: near the turning point use
`|J₀′(u)| ≤ u/2` so that `c²ξξ′ = (c²ξ²)′/2` integrates to `c²ξ(x)²`, bounded on the endpoint layer
`c²(x−1) ≤ 1`; away from it use `|J₀′(u)| ≤ C u^{-1/2}`, whose contribution
`c^{1/2}ξ′/√ξ ≍ c^{1/2}(x−1)^{-3/4}` is integrable.  That is the whole content of the card's
"analytic endpoint coordinate `η = ξ_c²`" remark, and it is the next brick.

### The three prolate spectral cards

`constrained-prolate-two-mode-ground-state`, `constrained-prolate-fixed-mode-spectral-ladder` and
`constrained-prolate-fourier-parity-floor-separation` share exactly two open inputs, and only these:

1. **prolate-to-Hermite limits** `ℓ_j(λ) = ∫ h_{4j,λ} → |ĥ_{4j}(0)|`, i.e. `hl0`, `hl1` in
   `ConstrainedProlateFullDistanceCCM.lean`.  The target constants `2^{1/4}` and `√3·2^{-5/4}` are
   already formal (`HermiteOriginConstraintTargets.lean`).
2. **Fuchs identification** `d_j(λ) = 1 − χ_{4j}(λ)² ≍ A_j λ^{8j+1} e^{-4πλ²}`, i.e. that the actual
   leakage eigenvalues are of the modelled `fuchsRate` shape.

A soft route to `(1)` does not exist: strong convergence `T_λ → F` only shows that the modes
approach the `+1` eigenspace of the Fourier transform, which is the whole span of
`h_0, h_4, h_8, …`; and a Gaussian trial vector only gives `d_0 = O(e^{-2πλ²})`, one exponential
short of the true `e^{-4πλ²}`, so the deficit-ratio argument `d_0/d_1 → 0` cannot be closed from it.
Both inputs therefore need the **commuting prolate differential operator**

```text
L_c u = ((1 − t²) u′)′ − c² t² u ,      c = 2πλ² ,
```

whose commutation with the finite Fourier transform is an exact double integration by parts (the
boundary terms vanish because `1 − t²` does), followed by its `c → ∞` degeneration to the harmonic
oscillator.  That layer — `L_c` commutes with `T_λ`, its spectrum is simple, and its eigenfunctions
converge to Hermite functions after the parabolic rescaling — is the next brick for these three
cards, and mathlib has none of it.

### Correction — the prolate commuting-operator layer is already corpus-owned

The note above ends by calling the commuting prolate differential operator "the next brick".  That
is wrong: mathlib has none of it, but **this corpus already has all of it**, and a duplicate module
written against that mistaken assumption was deleted.  What exists:

```text
HTGeometry/SturmSelfAdjoint.lean          integral_mul_sturm_symm — the Sturm operator crosses an
                                          integral when the weight vanishes at both endpoints
HTGeometry/ProlateKernelSymmetry.lean     prolateKernel, prolateSymbol, prolateSymbol_symm,
                                          prolateOperator_kernel, prolateOperator_kernel_symm
RHTower/ProlateCommutationKernel.lean     prolateAction_bandTransform_commutes, and
                                          prolateAction_bandEigen_eq_smul: an eigenfunction of the
                                          finite Fourier transform satisfies the prolate ODE
RHTower/SlepianBandCommutation.lean       slepian_commutation, slepian_commutation_eigen
RHTower/FuchsProlateScale.lean            prolateSLAction, hermiteSLAction, the exact scaling
                                          identity prolateSLAction_sqrtScale, and the full
                                          fuchsRate calculus
RHTower/HermiteOscillatorEigen.lean       hermiteSLAction_hermiteFun (exact oscillator eigenvalue
                                          −(2n+1)) and prolateSLAction_hermiteFun (the two-sided
                                          quasimode at bandwidth c)
RHTower/ProlateRadialODEBridge.lean       exists_global_even_radialProlate_of_signedMode
RHTower/ProlateHermiteRescale.lean        exists_even_prolateHermiteRescale_of_signedMode:
                                          every live signed mode has a smooth even global profile
                                          whose Hermite rescaling satisfies
                                            hermiteSLAction u + c·s·u = (ξ²u″ + 2ξu′)/c
                                          EXACTLY, with no convergence premise
```

So the ODE side is finished.  **The single missing brick is spectral:** turning the exact `O(1/c)`
oscillator defect into a statement about the eigenvalue and the eigenfunction, namely

```text
c · s_n(c) → 2n + 1        and        u_n(c) → hermiteFun n   (normalized) .
```

The natural formal route is the *quasimode principle* for the self-adjoint harmonic oscillator
`H = −d²/dξ² + ξ²` on `L²(ℝ)`, whose spectrum is exactly `{2n+1}` with the Hermite functions as
eigenvectors: for a unit vector `v` in the domain, `dist(μ, spec H) ≤ ‖(H − μ)v‖`.  Applied to the
corpus's exact identity this reads

```text
dist(c·s_n(c), {2m+1 : m ∈ ℕ}) ≤ ‖ξ²u″ + 2ξu′‖ / (c ‖u‖) ,
```

so the remaining analytic input is an **a priori `L²` bound on `ξ²u″ + 2ξu′` in terms of `‖u‖`**
for the rescaled prolate profile — not any asymptotic expansion.  Once the eigenvalue is pinned,
the same estimate pins the eigenvector, and `ℓ_j(λ) → |ĥ_{4j}(0)|` follows from
`ℓ_j = χ_{4j}·e_j(0)` together with `χ → 1`.  The Fuchs rate needs the same machinery carried to
second order.

### The oscillator-ladder pin — built

`HTGeometry/WholeLineWronskianSymmetry.lean` and `RHTower/ProlateOscillatorLadderPin.lean`
(both wired) supply the bridge identified above, and it turned out to be an **identity**, not an
estimate.

```text
integral_deriv_eq_zero_of_tendsto_zero   a derivative whose primitive tends to 0 at ±∞ integrates
                                         to 0 over the line
hasDerivAt_wronskian                     (u′v − uv′)′ = u″v − uv″
integral_secondDeriv_pairing_eq_zero     hence ∫(u″v − uv″) = 0 for a vanishing Wronskian
integral_secondDeriv_mul_comm            ∫ u″v = ∫ u v″

hasDerivAt_hermiteFun, hasDerivAt_deriv_hermiteFun
                                         the oscillator eigenfunctions are twice differentiable

hermitePairing_pin (n) :
    hermiteSLAction u + μ·u = D  pointwise, plus a vanishing Wronskian against φₙ
    ⟹ (μ − (2n+1)) · ⟨u, φₙ⟩ = ⟨D, φₙ⟩

abs_sub_oscillatorLadder_eq (n) :
    |μ − (2n+1)| = |⟨D, φₙ⟩| / |⟨u, φₙ⟩|
```

The `ξ²` potential cancels identically — it sits on both sides of the integration by parts — so no
operator theory, no spectral theorem and no quasimode inequality is involved.

Applied to the corpus's exact prolate identity
`hermiteSLAction u + (c·s)·u = (ξ²u″ + 2ξu′)/c` this reads

```text
|c·s(c) − (2n+1)| = |⟨ξ²u″ + 2ξu′, φₙ⟩| / (c · |⟨u, φₙ⟩|) ,
```

so the **entire remaining analytic content of the prolate-to-Hermite gate** is now a single a priori
bound: that the defect pairing `⟨ξ²u″ + 2ξu′, φₙ⟩` stays bounded relative to `⟨u, φₙ⟩` as the
bandwidth grows.  That is a statement about one fixed rescaled profile against one fixed Gaussian
weight — no expansion, no uniformity in the index — and it is the next brick.

### Correction and progress — the endpoint layer of the high first row

The note above said the corpus's amplitude bounds "hold only for `x ≥ 2`".  That is true of
`abs_xiAmplitude_le_four` as *stated*, but not of the underlying estimate: `xiAmplitude_le`
(`CCMFirstRowStationaryPhase`) already gives `A_s(x) ≤ √(√2)/√x` for every `x > 1`.  So the
amplitude half-power bound needed no new analysis, only a restatement.

Two modules now close the endpoint layer, both wired:

```text
RHTower/XiAmplitudeEndpointSymbol.lean
    abs_xiAmplitude_le_two_div_sqrt   |A_s(x)| ≤ 2/√x     for every x > 1
    abs_xiAmplitude_le_two            |A_s(x)| ≤ 2        for every x > 1
    abs_xiAmplitudeDeriv_le_near      |A_s′(x)| ≤ 6       for 1 < x ≤ 2
    abs_xiAmplitudeDeriv_le_six       |A_s′(x)| ≤ 6       for every x > 1

RHTower/BesselEndpointVariation.lean
    abs_besselJ0Deriv_le              |J₀′(v)| ≤ 2/π
    abs_besselJ0Deriv_le_mul_abs      |J₀′(v)| ≤ 2|v|/π   — flat at the turning point
    integral_abs_deriv_besselModulated_le
        ∫_a^b |(A·J₀(cΘ))′| ≤ Q′(b − a) + (Q c²/π)(Θ(b)² − Θ(a)²)
```

The derivative bound at the turning point is the corpus's `abs_phaseLogDefect_le_near` plus an
elementary rational estimate, extracted from an inline argument inside
`ProlateDunsterComparisonBridge`.  The Bessel bound is the integral representation together with
`|sin y| ≤ |y|`; its content is that `J₀(cξ)` is **flat** where `ξ` vanishes, so the differentiated
Bessel term is the exact derivative `(c²/π)(ξ²)′` rather than an `O(c)` oscillation.

With these, `(7)` of `ccm-exact-high-radial-first-row-bv-bound` has both of its symbol inputs on
all of `[1,∞)`, and what remains for the charge-law and dilation-limit cards is the bookkeeping
instantiation naming the concrete first-row factor — no further analytic input.

## The prolate-to-Hermite gate, after the defect transfer and the profile decay

Two further bricks (both wired, both axiom-clean) shrink this gate again.

### The defect pairing carries no derivative of the profile

`RHTower/ProlateDefectTransfer.lean`, with the first-order whole-line integration by parts
`integral_deriv_mul_eq_neg` added to `HTGeometry/WholeLineWronskianSymmetry.lean`:

```text
integral_prolateDefect_transfer            ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²φₙ″ + 2ξφₙ′⟩
integral_prolateDefect_transfer_explicit   ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²(ξ²−2n−1)φₙ + 2ξφₙ′⟩
prolateLadder_pin_hermiteSide
    (μ − (2n+1))·⟨u, φₙ⟩ = ⟨u, ξ²(ξ²−2n−1)φₙ + 2ξφₙ′⟩ / c
```

The earlier note called for an a priori bound on `⟨ξ²u″ + 2ξu′, φₙ⟩`.  That is the wrong target:
two integrations by parts — second order against `ξ²φₙ`, first order against `2ξφₙ` — move both
derivatives onto the Hermite factor.  The `4ξφₙ′` of the first and the `−2ξφₙ′` of the second leave
`2ξφₙ′`; the two `±2φₙ` cancel; and `φₙ″ = (ξ²−2n−1)φₙ` makes the survivor explicit.

### The profile decays like `1/|x|`, from the integral equation alone

`RHTower/ProlateProfileDecay.lean`:

```text
abs_sincSmooth_le_inv              |sinc_c(u)| ≤ 1/(π|u|)
abs_le_of_bandTransform_eigen      T̃_c Φ = χ²Φ  ⟹  |Φ(x)| ≤ (∫_{-1}^{1}|Φ|)/(|χ²| π (|x|−1))
```

The corpus's global profile is produced as a time–band eigenfunction, and the band integral runs
only over `[-1,1]`, so every `|x| > 1` sees a kernel of size at most `1/(π(|x|−1))`.  No asymptotic
analysis of the prolate differential equation is needed for the decay — the integral equation the
profile already satisfies gives it directly.  This is what licenses the two integrations by parts
against Gaussian weights: the Wronskian `u′·ξ²φₙ − u·(ξ²φₙ)′` and the product `u·2ξφₙ` both vanish
at `±∞`.

### What is left

```text
|c·s(c) − (2n+1)| = |⟨u, ξ²(ξ²−2n−1)φₙ + 2ξφₙ′⟩| / (c · |⟨u, φₙ⟩|)
```

with `u(ξ) = Φ(ξ/√c)`.  The remaining content is a **non-degeneracy comparison**: the pairing of the
rescaled profile against `φₙ` must not decay faster than `1/c` relative to its pairing against the
fixed weight `ξ²(ξ²−2n−1)φₙ + 2ξφₙ′`.  Both are pairings of one function against fixed
Gaussian-decaying weights; no expansion and no derivative estimate is involved.  The decay bound
above also supplies the integrability side conditions, since `1/|x|` against a Gaussian is
integrable.

### The derivative decays too — the side conditions are discharged

Added to `RHTower/ProlateProfileDecay.lean` (wired, axiom-clean):

```text
abs_deriv_sincSmooth_le              |sinc_c′(u)| ≤ (|c||u| + 1)/(π u²)
abs_deriv_le_of_bandTransform_eigen  |Φ′(x)| ≤ (|c|(|x|+1)+1)·(∫_{-1}^{1}|Φ|)/(|χ²| π (|x|−1)²)
```

Differentiating the band eigen-relation keeps the same mechanism: the differentiated sinc kernel is
still `O(1/|u|)`, because the `u cos(cu)` numerator is killed by the `u²` denominator.  So both `Φ`
and `Φ′` decay like `1/|x|`, and therefore so do `u` and `u′` after the rescaling `u(ξ) = Φ(ξ/√c)`.

That discharges every side condition of the defect transfer: the Wronskian
`u′·ξ²φₙ − u·(ξ²φₙ)′` and the product `u·2ξφₙ` each carry a Gaussian factor and vanish at `±∞`, and
`1/|x|` against a Gaussian is integrable.

### The single remaining statement

```text
|c·s(c) − (2n+1)| = |⟨u, ξ²(ξ²−2n−1)φₙ + 2ξφₙ′⟩| / (c · |⟨u, φₙ⟩|)
```

is now an identity with every step licensed.  What it does *not* yet give is which rung: pairing an
`L²`-normalized `u` against the orthonormal Hermite basis gives `Σ_m ⟨u,φ̂_m⟩² = 1`, so some `m`
carries mass and `dist(c·s(c), {2m+1}) = O(1/c)` for that `m`, but the index depends on how the
profile's mass is distributed and that distribution is exactly what a fixed-index asymptotic would
supply.  The honest residue is therefore:

> a lower bound on `|⟨u, φₙ⟩|` for the *matching* index `n`, uniform in the bandwidth.

That is a non-degeneracy statement about one function against one fixed Gaussian weight — no
derivative estimate, no ODE asymptotics, no expansion — and it is the last thing these three cards
need.
