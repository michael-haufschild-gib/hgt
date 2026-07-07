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

## The half-plane charge: the finer invariant, constructed (`HalfPlaneCharge.lean`)

The forward object named above is built. Reality forces `Σ_S ord = 2·(Σ_upper ord)`
(`aggregate_eq_two_upperOrder`), so the aggregate index lies wholly in the mod-2 **discard**
(`SignatureParity.parity_blind_to_pairs`: the pair count `q` in `deckRed 2 (k+2q)` is invisible).
Keeping the discarded quotient gives the quadrant-local invariant:

  `upperOrder S ord = Σ_{w∈S, Im w>0} ord w`,  `halfCharge n S ord = wCharge n (upperOrder) ∈ ℤ/n`.

* **Refinement** `aggregate_charge_succ_eq_zero_iff_halfCharge`:
  `wCharge (2^{k+1}) (Σ_S ord) = 0 ↔ halfCharge (2^k) S ord = 0`. The aggregate at rung `k+1`
  recovers the half charge at rung `k`; the mod-2 aggregate (`k=0`) recovers only the trivial
  rung — the blindness — and the **mod-4 aggregate** (`k=1`) recovers the upper parity
  (`mod4_aggregate_eq_zero_iff_upper_even`).
* **Detection** `halfCharge_two_ne_zero_of_odd_upperOrder`: an odd upper-half order sum (a lone
  off-line odd defect) gives `halfCharge 2 ≠ 0`, while the aggregate reads `0`.
* **Not automatic from reality** `exists_conjSym_halfCharge_ne_zero`: the witness `S={i,−i}`,
  orders `1,1`, is conjugation-symmetric, fixed-point-free, with mod-2 aggregate `0`, half charge
  `1`, mod-4 aggregate `2 ≠ 0`. Reality forces the aggregate even but leaves the upper parity free.
* **RH forces it trivial** `rhLadder_imp_xiDescentHalfCharge_zero`: `RHLadder k` ⟹ the descended
  half charge vanishes on every slit configuration. So a nonzero `xiDescentHalfCharge` is a genuine
  off-line odd defect — the finer detector on which the quadrant-seam conservation programme is posed.

Next: a **conservation law** for `halfCharge` under admissible deformations (Phase E in the
`u`-plane), and the seam boundary term that a nonzero half charge must produce — the relative
half-seam class the naive mod-2 seam parity could not express.

## Phase E: half-charge conservation and the seam-deposit law (`HalfChargeConservation.lean`)

Allowing seam zeros (`Im w = 0`), reality partitions a conjugation-symmetric configuration as
`Σ_S ord = 2·upperOrder + seamOrder` (`aggregate_eq_two_upperOrder_add_seamOrder`) — conjugation
bijects the off-seam upper/lower halves and fixes the seam. The aggregate is the homotopy-invariant
boundary winding, so an admissible deformation (no zero crosses `∂B`) conserves it:

* **Deposit law** `halfCharge_seam_deposit` / `halfCharge_deposit_eq`:
  `2·upperOrder + seamOrder` is conserved, i.e. `Δ(seamOrder) = −2·Δ(upperOrder)`. The half charge
  changes only by depositing order on the seam.
* **Conserved when the seam is inert** `upperOrder_conserved_of_seam_inert`.
* **Relative half-seam class** `seamOrder_parity_conserved`: the deposit `2·Δq` is even, so the
  *mod-2 seam parity is conserved — blind to the transfer*. The emitted datum is the integer deposit
  `2·Δ(upperOrder)`, which the mod-2 parity cannot express (mod-4 sees it, matching the half-charge
  refinement).
* **Far-field drain** `xiDescent_ne_zero_of_uSqrt_re_gt` (`Re √u > 1/2 ⟹ Re s > 1 ⟹ ξ ≠ 0`),
  `xiDescentUpperOrder_eq_zero_of_no_upper_zero`: the half charge is `0` in the far field, so it cannot
  be pushed there.
* **The `{i,−i}` collision** `exists_halfCharge_seam_deposit_witness`: `{i,−i}` (half charge `1`, seam
  `0`) → `{0}` (half charge `0`, seam `2`), equal aggregate `2`. The half charge is carried onto the
  seam as order `2` — the local model `P_t(u)=(u−a)²+t²` made a theorem.

**The reduced open core.** A nonzero half charge must persist to the far field (impossible: there it
is `0`) or deposit an even seam order. So `RH_2` is now: can the true descended `ξ` realize a nonzero
`xiDescentHalfCharge` — is the relative half-seam deposit possible for this one function, or forbidden?
The whole burden is a single seam-boundary question about `xiDescent`.

## Deposit vs ξ's germ: the central-parity verdict (`HalfChargeSeamCompat.lean`)

The `u`-plane seam `{Im u = 0}` = far field (`u>0`, ξ≠0) ∪ center (`u=0`, `s=1/2`) ∪ **critical line**
(`u<0`, `s=1/2+i√|u|`). An off-line pair colliding onto the seam lands at `u<0` (as `β→1/2`,
`u₀=(β−1/2+iγ)²→−γ²<0`) — on the critical line, *not* the center.

* `analyticOrderAt_xiDescent_sq_of_ne_center`: off-center (`s≠1/2`) the descent is a local iso, so the
  seam multiplicity is exactly `ord_s ξ` — **no parity constraint**.
* `xiDescent_online_seam_order`: on-line ξ-zeros map to the negative-real seam (`Im=0, Re≤0`) with
  order `ord_ρ ξ`, which can be odd (all known on-line zeros are simple).
* `xi_central_order_eq_two_mul`: `ord_{1/2} ξ = 2·ord_0(xiDescent)` — central parity (Phase C) is the
  descent's halving, automatic for any descended order (`xi_central_order_even_via_descent`). A center
  deposit of order `n` is a central ξ-zero of order `2n`, Phase-C-consistent.
* `deposit_respects_central_parity`: under any admissible deformation the mod-2 seam parity is
  conserved — the deposit can never violate central parity.

**Verdict.** Central parity constrains only `u=0`, and there it is automatic; the deposit lands on the
critical line `u<0` where the seam carries arbitrary (even odd) order; the deposit is even and preserves
the seam parity. **Central parity does not obstruct the deposit — it survives; the `{i,−i}` deposit is
compatible with ξ's germ.** The obstruction, if any, is finer than parity: it must distinguish a genuine
on-line zero from a deposited pair-collision residue.
