# Euler–FE transport theory

## Motivation and target

The Euler product controls positive prime data in a half-plane of absolute convergence.
The Riemann functional equation reflects the continued function across the critical line.
This programme seeks the missing interaction that forces an exceptional zero to recur at
unbounded heights. Its target is AAL, `Θ = Θ∞`, or a counterexample in the specified
Euler–FE class that settles the falsification branch.

For ζ, `Θ` is the supremum of zero real parts and `Θ∞` is the supremum remaining after
arbitrary bounded-height deletions. Failure of AAL leaves a finite top layer above the
tail. The corresponding prime error contains a finite oscillation `x^Θ T(log x)` with
a smaller remainder exponent. The question is why the exact arithmetic and reflection
cannot support that isolated oscillation.

## Objects and language

- **Reflection:** `s ↦ 1−s̄`, with the completed functional equation and pole terms retained.
- **Transport:** a rule producing zeros above every height from a given exceptional zero.
- **Depth:** `Re ρ−½`. **Replication at the same depth** retains this number exactly.
- **Rigid oscillation:** the finite exponential sum forced by an isolated top layer of ζ.
- **Two-scale coupling:** an identity linking the reflected oscillation and the positive
  Euler data at different scales, with both infinite tails retained.
- **Resonant tower:** the evaluations at powers of a base such as `exp(π/γ)`, detecting
  the mode of ordinate `γ`; the desired law couples `γ` to `(2k+1)γ`.
- **FE defect:** the uncompleted critical-line discrepancy `g` in the Hamburger strip
  identity, with size `D = ∫ ‖g‖`. Gamma-weighted integrability is a different condition.
- **Layer cost:** the infimum of `D` over nonclassical countable Beurling systems in that
  analytic class carrying a finite nonempty off-line layer; it is infinite if this class is empty.

## Foundations and the missing mechanism

The corpus already proves AAL equivalent to zero transport with every positive real-part
loss, and identifies the rigid finite-layer world when AAL fails. Bohr recurrence supplies
transport where uniform holomorphic recurrence is actually available. It does not extend
itself through the critical strip.

The proposed mechanism has four parts:

1. Express the finite top oscillation through the actual prime error and theta transform.
2. Track its reflection from exponent `Θ` to `1−Θ`, including the pole and archimedean terms.
3. Use Euler positivity between atoms to force coherent reproduction of this reflected
   oscillation by the infinite zero tail at every scale.
4. Convert that reproduction into zeros of depth `Θ−½` at unbounded heights.

Parts 2–4 require new arithmetic theorems. Reflection alone preserves absolute height.
An implication assuming the required reproduction or recurrence is not a construction
of the transport operator.

## Milestones

| Milestone | Required mathematical outcome |
|---|---|
| M1 | Resolve B122: complete rigidity for arbitrary integrable FE defect, or construct the nonclassical finite-defect class. |
| M2 | Determine `D_layer`; in particular prove its infinitude or construct a finite-defect finite-layer system. |
| M3 | Prove replication for one exceptional quartet of ζ at the same depth. |
| M4 | Prove `LinAt C` for an actual finite `C`, coupling the global and asymptotic depths. |
| M5 | Prove AAL, with the corpus's ZAL implication then giving RH. |

M1 and M2 classify other Euler systems. Even complete rigidity does not exclude a finite
layer of ζ. If M1 is true, perturbations within the integrable-defect class provide no
nonclassical models; transport must use exact identities of ζ. M3 is an endpoint target:
AAL permits arbitrarily small positive loss and does not by itself give same-depth copies.

## Tools to develop and open questions

| Tool | Question |
|---|---|
| FE-to-transport operator, B112 | Which exact combination of reflection and Euler factorization changes height? |
| Quantitative recurrence of the rigid oscillation | Which returns survive coupling to the complete prime and zero tails? |
| Resonant-tower identities | How do the modes at `γ` and `(2k+1)γ` constrain each other without a growing frozen head? |
| Conditional prime-discrepancy defect calculus | Can a conditionally convergent Euler discrepancy have integrable uncompleted defect? |
| Same-depth replication theorem | Why must one exceptional top force infinitely many tops at its exact real part? |

The critical-zero coupling must be derived from the actual continued Euler product.
Counting zeros, mean-square bounds, or phase recurrence alone do not identify the needed
joint arithmetic information.

## Shared analytic pillars

`ExactEventTheory` develops the finite-defect side of M1. It proves arbitrary-defect
rigidity under integer support or asymptotic integer alignment, and unique norm
factorization without alignment. Its Laplace boundary calculus gives continuous values
away from zero, a locally integrable `|y|⁻¹ᐟ²` bound, and decay at infinity.
Its variable-width tent identity separates atomic mass into a sinc-squared cosine pairing,
the pole term, and a decaying boundary error. Atomic recurrence now forces the real
boundary defect to vanish throughout `0 < |y| < 1`. The origin pairing must still turn
this into integer support and complete M1. These are shared inputs, not zero-replication
theorems. Full M1–M5 remain open here.

## Calibration and traps

Every proposed law must use the Euler product and FE jointly at two scales. It must
distinguish ζ from the heat family, `cosh` models, positive Beurling one-offs and Wolff
towers, and recover the established local-squares purity law at finite rank.

An exact zero cannot be replaced by a near-zero event. A return of finitely many prime
phases does not control a continued Euler tail. A positive pairing does not locate zeros
unless the arithmetic input preventing fake configurations is proved. Removing a finite
layer must preserve and verify all Euler, reflection and analytic conditions used.

## Position and contribution criteria

`ExactEventTheory` supplies exact-tail and defect-boundary mechanisms.
`ZeroConfigurationGeometry` supplies AAL, the strict linear dial and the rigid top layer.
`ArithmeticPositiveDuality` supplies Hamburger rigidity, positive measures and one-off
calibrations. `TailArithmeticOfThePrimeOrbit` supplies head–tail identities and returns.
`InfiniteRankWeilTheory`, `ArithmeticCastelnuovoSeveri` and `SurfaceOfSpecZ` supply the
tower and geometric receivers against which transport must be tested.

This programme owns new Euler–FE coupling and replication results in this directory;
its umbrella is `../EulerFETransportTheory.lean`. Shared results retain their original
home. A contribution must remove an actual infinite-problem obstruction or construct
a required operator, identity, classification or counterexample. Finite computations,
renamed equivalences and wrappers around unproved arithmetic inputs do not qualify.

Completion requires the stated tools and questions to be resolved with dependency-closed
Lean proofs, including the replication/AAL branch. A retired route must yield and audit
its strongest positive survivor. The foundational description alone does not develop
the missing mathematics.
