# Phase D — Move to the (u)-plane: deliverables (formalized)

Descent object (prior infra): `Y(z) = ξ(1/2+z)` is even, so `Y(z)=X(z²)` with
`X(u)=xiDescent(u)=ξ(1/2+√u)` entire (Painlevé across the slit), and
`RH ⟺ xiDescent has no zero on the slit plane ℂ∖(−∞,0]`. The critical line is the slit;
the FE involution is quotiented away.

The three Phase-D deliverables are formalized in `formal/GaloisForLFunctions/RHTower/`
(`UPlaneReflection.lean`, `UPlaneTorsor.lean`, `UPlaneWinding.lean`), all axiom-clean,
`MainTheorems` green, lint passed.

## The structural fact: the descent halves the symmetry group

The `s`-plane Klein four-group `V₄ = {s, 1−s, s̄, 1−s̄}` collapses to `ℤ/2 = {w, w̄}` in the
`u`-plane: the FE reflection `s↦1−s` (i.e. `z↦−z`) is absorbed by `z↦z²`. What remains is
conjugation, made precise by

* `xiDescent_conj : xiDescent(w̄) = conj(xiDescent w)` — the u-plane reality (from
  `ξ(s̄)=conj ξ(s)` and `√(w̄)=conj √w` off the slit, extended by continuity across the dense
  slit plane).
* `xiDescent_orderAt_conj`, and its charge/winding avatars.

Consequence — the whole ladder is decided on **half** the slit plane
(`z↦z²` maps the `s`-plane right upper quadrant order-preservingly onto the `u`-plane
upper-half slit plane):

> `rhLadder_iff_xiDescent_upperHalf` :
> `RHLadder k ↔ ∀ w ∈ slitPlane, 0 ≤ Im w → xiDescent w = 0 → 2^k ∣ ord_w xiDescent`.

## Deliverable 1 — classification of allowed root torsors on slit domains

* **Zero-free / simply-connected** (prior `UPlaneLadder`): a coherent dyadic tower / analytic
  `2^k`-th root exists on a simply-connected slit region iff `xiDescent` is zero-free there.
* **Annulus (rank-one torsor)**: `xiDescent_deckClass_annulus_isolating` — around an isolated
  `u`-plane zero `w₀`, any two chart roots on the right/left slit-annulus charts have deck class
  `exp(2πi·ord_{w₀}/n)`; `xiDescent_deckClass_annulus_one_iff_dvd` — the class is trivial
  (global `n`-th root across the annulus) iff `n ∣ ord_{w₀}`. The annulus torsor is `ℤ/n`,
  classified by the enclosed order mod `n`.
* **Root existence on a slit domain**: `xiDescent_root_on_slit_iff_charge` — on a convex open
  slit-plane region with one nonvanishing point, a `2^k`-th root of `xiDescent` exists iff its
  deck charge `carrierCharge xiDescent k` is trivial at every enclosed zero. A single nonzero
  local charge (an off-slit zero of order not divisible by `2^k`) is the whole obstruction.
  (`xiDescent_zeros_finite_ball` supplies local finiteness.)
* **Charge form of the ladder**: `rhLadder_iff_xiDescent_carrierCharge_upperHalf` / `_slitPlane`
  — a single `μ_{2^k}`-valued observable on (half) the slit plane classifies each rung.

## Deliverable 2 — the seam-index (winding) formula

* `windingNumber_xiDescent_disc` : the winding of `xiDescent` around a circle equals the total
  order `Σ_{w∈t} ord_w` of the enclosed `u`-plane zeros.
* `loopCharge_xiDescent_disc` : its rung-`k` reduction is the enclosed deck charge
  `wCharge (2^k) (Σ ord_w)` — boundary winding equals the sum of enclosed deck charges.
* `windingNumber_xiDescent_zero` / `loopCharge_xiDescent_zero` : the single-zero case.
* **Seam blindness** (`loopCharge_xiDescent_disc_two_eq_zero`): for a circle centred on the real
  axis whose enclosed zeros are all off-real, the island is conjugation-symmetric, so its rung-`1`
  winding charge is `0` — reality forces even total order. Constraint-side twins:
  `seam_order_two_mul` (`Σord = 2·Σ_upper ord`), `seam_charge_two_eq_zero`,
  `xiDescent_seam_order_even`. This is exactly why a symmetric seam detector is blind to a compact
  conjugate-pair island (`P(u)=u²+1`, zeros `±i`, total order `2`): the aggregate sees only the
  parity of the total, not a single odd upper defect.

## Deliverable 3 — comparison: s-plane quadrant charge ↔ u-plane slit charge

* **Charge face**: `xiDescent_carrierCharge_center_sq` — `carrierCharge xiDescent k ((ρ−1/2)²) =
  carrierCharge xi k ρ` (same `μ_{2^k}` element); `xiDescent_carrierCharge_conj` — conjugation
  invariance.
* **Winding face**: `windingNumber_xiDescent_center_sq` — the `u`-plane winding around the
  descended image `(ρ−1/2)²` equals `ord_ρ ξ`; `windingNumber_xiDescent_eq_xi_of_center_sq` — the
  `s`-plane quadrant winding of `ξ` around `ρ` equals the `u`-plane slit winding of `xiDescent`
  around `(ρ−1/2)²`: the same integer.

## What this opens

The seam blindness result is sharp: it says the aggregate rung-`1` winding is a *parity* invariant
and therefore cannot alone force a single odd upper defect off the plane. The forward move is the
**quadrant-local / relative** invariant that survives the conjugate-pair collapse — a signed or
`ℤ/4`-refined charge on one half of the slit plane, whose vanishing is not automatic from reality.
The domain-halving (`rhLadder_iff_xiDescent_upperHalf`) already restricts the target to the upper
half; the next object is a half-plane charge finer than the mod-`2` aggregate.
