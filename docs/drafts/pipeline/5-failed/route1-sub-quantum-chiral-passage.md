# Route 1 — sub-quantum chiral loss through the Gaussian Euler–continuum passage

- **ID:** R1-SQCP
- **Stage:** 5-failed
- **Type:** FALSIFIED (CIRCULAR) + THEOREM (Lean) positive survivor
- **Source:** `docs/reports/route-proposals/route1.md`
- **Statement:** `κ₋(D) < 1` for every admissible strict-right rectangle `D`, where `κ₋` is the negative-chirality Hankel energy lost by `Φₓ/|Φₓ|` as `x → 0⁺`.
- **Fact log:** `../1-in-progress/route1-chiral-passage/facts.md`

## No-go closure

- **Exact killing mechanism:**
  1. *Holomorphic rigidity.* Take zero-free holomorphic approximants that converge on an open anchor inside the disc. If their boundary arguments are bounded in `L¹` modulo constants, the limit is zero-free on the whole disc. By Bourgain–Brezis–Mironescu, bounded `H^(1/2)(S¹;S¹)` phase energy gives that `L¹` bound. Every strict-right zero `ρ` lies in a disc `B(1+i Im ρ, r)`, `r<1/2`, which reaches the safe chart `Re s>1` where `Φₓ → ξ`. So step 2 of the route (bounded, weakly convergent passage) already forbids the zero. The chiral losses of anchored approximants always balance, `κ₋ = κ₊`, and step 4 (`κ₋ ≤ B_base`) is logically idle.
  2. *Explicit formula.* `logDeriv Φₓ - logDeriv ξ = ½ Σ_ρ Γ((ρ-s)/2)(πx)^((s-ρ)/2) + O(x)`. Each zero is felt only to its left, growing like `x^(-(β-σ)/2)`. Under RH the passage converges in `C¹` on compacts of `Re s>1/2`. Under ¬RH it diverges diffusely along every sequence and never bubbles. Step 2 is therefore equivalent to RH: it is the Gaussian-smoothed form of `ψ(X) = X + O(X^(1/2+ε))`.
  3. *Fixed-x arm (stop-test fallback).* `Tr T_(D,x) = wind(u_D)` for every `x`. The only Euler-side identity, Brezis–Nirenberg `E₊ - E₋ = deg`, renormalizes back to the chiral losses of (2).
- **Strongest positive survivor:** anchored phase-passage rigidity.
  - (i) Schwarz difference formula: `G z - G z₁ = (i/π)∫ K (Im G - m) dθ`.
  - (ii) Interior increments are bounded by the boundary-argument oscillation.
  - (iii) Anchored bubbling exclusion.
  - (iv) Bounded `L¹` boundary argument of the Gaussian potential `Lₓ + Aₓ` along one sequence `x_k → 0⁺`, on every circle `C(1+iγ, r)`, implies RH.
- **New insight:** holomorphic readers have no sub-quantum regime. Their integer is protected by rigidity and changes only through divergence, so a budget must bound a growth exponent (`(β-σ)/2`), never a quantum. Test A of the route proposal ("strictly below one quantum, uniform in height") is the wrong gate for holomorphic passages: any finite bound per disc suffices, and even that is RH. A bubble in an unanchored limit is a boundary double zero of the interior limit (a Koebe factor), never an interior event.
- **Status:** paper proof dependency-closed; the only citation is Bourgain–Brezis–Mironescu (IHES 2004) for the `H^(1/2)` → `L¹`-lift step. The Lean survivor is `GaloisForLFunctions.RHTower.AnchoredPhasePassageRigidity`:
  - `schwarz_difference_formula`
  - `norm_sub_le_of_boundary_im_oscillation`
  - `ne_zero_of_anchored_boundaryArgOscillation_bounded`
  - `riemannHypothesis_of_gaussianPassage_boundaryArgOscillation_bounded`

  Axioms: `propext`, `Classical.choice`, `Quot.sound`. Not formalized: the BBM bridge and the explicit-formula converse (RH ⇒ bounded passage).

## Log
- 2026-09-26 — route 1 attacked and killed (CIRCULAR); survivor formalized.
