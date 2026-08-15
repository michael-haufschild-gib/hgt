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
