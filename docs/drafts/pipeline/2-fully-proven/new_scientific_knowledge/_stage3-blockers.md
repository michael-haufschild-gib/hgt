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
