# Elliptic function-field theorem: VALIDATED brick plan (serves ht cards 3, 4, 5)

GOAL: f meromorphic on ℂ, Λ-periodic (L : PeriodPair) ⟹ f ∈ ℂ(℘[L], ℘'[L]); then phase-field
presentation + multiplication protocol + tail (close card 3 elliptic column, card 4 protocol
residue). Deck fixed fields on the jet model DONE (mem:ht-cards/stage3-sweep-progress-2).

## CONFIRMED mathlib pillars
- `MeromorphicOn.circleAverage_log_norm` (Mathlib.Analysis.Complex.JensenFormula): Jensen for
  meromorphic f on closedBall c |R|:
  circleAverage (log ‖f·‖) c R = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c-u‖⁻¹)
    + divisor f CB c * log R + log ‖meromorphicTrailingCoeffAt f c‖.
- `ZLattice.covolume.tendsto_card_div_pow` (+',''): lattice-point counting asymptotics.
- `IsZLattice.isCompact_range_of_periodic` (used in mathlib's own relation_eq_zero Liouville).
- Corpus: `const_of_lattice_periodic_differentiable` (EllipticLiouvilleFacetCodimension) = B1 ✓.
- Corpus: `finite_setOf_meromorphicOrderAt_ne_zero` (divisor meets compacts finitely, in
  TripticChargeClassFunction).

## B2 order-balance: THE KEY TRICK (validated design)
Target: per-Λ-class divisor sum of an elliptic f is 0 (zeros-per-cell = poles-per-cell).
Radial-averaged Jensen kills the hard circle bound:
- LHS bound: ∫_R^{2R} circleAverage(log‖f‖) dr = (1/2π)∬_{annulus} log‖f z‖/|z| dA;
  |weight| ≤ 1/R; ∬_{annulus}|log‖f‖| ≤ #cells·∫_cell|log‖f‖| = O(R²)·O(1) (log‖f‖ ∈ L¹loc:
  from meromorphy — mathlib has circleIntegrable_log_norm-type lemmas inside JensenFormula's
  cone; L¹loc on cells from local: near a point of order m, log‖f‖ = m·log‖z−u‖ + log‖g‖ with
  g analytic nonvanishing). Total: O(R) — beats R³ trivially.
- RHS integrated: ∫_R^{2R} Σ_{u∈D_r} div(u)·log(r/‖u‖) dr; if per-cell sum S ≠ 0 the leading term
  grows ~ S·R³·(const) (two-sided via cell tiling + mathlib counting); contradiction ⟹ S = 0.
- Good-radii/edge effects: integrating over r smooths circle-through-divisor issues (Jensen holds
  for a.e. r; integrable in r).
Then: poles of ℘ − c per cell = 2 (explicit: mathlib pole structure of ℘ at lattice = double;
weierstrassPExcept analytic ⟹ order exactly −2) ⟹ zeros per cell = 2 ⟹ FIBER THEOREM:
℘ z₁ = ℘ z₂ ↔ z₂ ≡ ±z₁ (mod Λ) (evenness gives ⊇; count caps it; 2-torsion doubling: ℘′ odd +
periodic ⟹ ℘′ = 0 at half-periods). Corollaries: e_i distinct, ℘′ zeros exactly half-periods,
(℘,℘′) injective off 0, ℘′ z₁ = ±℘′ z₂ via ODE.

## B3 even/odd: f = f₊ + ℘′·g, f₊ := (f(z)+f(−z))/2, g := f₋/℘′ both even elliptic (℘′ odd).
## B4 even ⟹ ℂ(℘): divisor-product route: h := ∏ᵢ (℘ − ℘(aᵢ))^{mᵢ} over zero/pole classes ±aᵢ of
   f (choosing representatives; 2-torsion multiplicity halving via fiber thm); f/h elliptic no
   zeros/poles ⟹ entire+periodic+never-0 ⟹ constant (B1 on f/h and h/f). Need pole bookkeeping
   at 0-class: adjust by ℘-powers.
## B5 assembly + the field ℂ(℘,℘′) ⊆ meroField univ as differential intermediate field
   (℘″ = 6℘² − g₂/2 for derivation closure).
## B6 Fix(Λ-translations of meroField) = ℂ(℘,℘′) — germ-level composition automorphisms.
## B7 multiplication protocol [m]: f ↦ f(m·); sublattice ℘'s: PeriodPair (mω₁ mω₂)-style and
   (1/m)Λ; depthwise deck identity; nonautonomousTail instance; close cards 3+4.

## Module sequence (execute in order)
M1 `EllipticLogL1.lean`: local/annulus L¹ bounds for log‖f‖ of meromorphic f (periodic case:
   annulus integral O(area)).
M2 `EllipticDivisorBalance.lean`: radial-averaged Jensen ⟹ per-cell divisor sum 0.
M3 `WeierstrassFiber.lean`: ℘-degree-2, fiber theorem + corollaries.
M4 `EllipticEvenReduction.lean`: B3+B4. M5 `EllipticFunctionField.lean`: B5. M6-7: B6+B7 protocol.
