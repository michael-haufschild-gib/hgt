import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.SubFarkasBudgetCertificates
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.ChosenMomentInputs
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.FinalAssemblyData

/-!
# Sub-`16799/19200` detector row counts from Stage-1 selected inverse-marked moments

Combining the existing `(9/2 + 12 Δ, 2)` raw moment bundle `Moments` with the Stage-1 complete-factor
inverse-marked bound `∑ s ∈ selected, F.widths s < 269/500 - (69/125) F.r` on `69/100 ≤ F.r ≤ 19/26`
upgrades the adaptive detector row count inside `B = [17/50, 41/100] × [12/25, 1/2]` to
`Budget.rowCount_B` while retaining `Budget.rowCount` outside `B`:

* `count_from_raw_moments_sub16799`: proves `(F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
  U ^ (Budget.rowCountSub16799 δ x + Δ / 4 + 159 ε + εm + F.mesh + 7 ν)` at the adaptive cutoff
  `cutoffSub16799 δ q`. On `[19/26, 1)` the existing `(1 - r)/2` inverse-marked line meets
  `269/500 - (69/125) r` continuously at `r = 19/26`.
* `adaptive_source_count_from_raw_moments_sub16799` and
  `actual_nonfloor_class_from_raw_moments_sub16799`: propagate `MomentsSub16799` into the nonfloor
  central cube amplitude-class bound.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open GaloisForLFunctions.FamilyContinuationTheory

namespace HeckeDetectorRowCount

/-- Upgraded inverse count exponent `1 - δ r - 2 δ x (269/500 - 69 r / 125)` on `[69/100, 19/26]`. -/
def inverseExponent_B (δ x r : ℝ) : ℝ :=
  1 - δ * (269 * x / 250 + (1 - 138 * x / 125) * r)

/-- Upgraded short count exponent inside `B` at witness cutoff `t`. -/
def shortExponent_B (δ x t : ℝ) : ℝ :=
  inverseExponent_B δ x (Budget.crossing_B x t)

theorem crossing_B_bounds {x t : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (ht : 1 ≤ t) (ht' : t ≤ 3 / 2) :
    1 / 2 ≤ Budget.crossing_B x t ∧ Budget.crossing_B x t ≤ 11 / 10 ∧
      1 / 3 ≤ t - Budget.crossing_B x t ∧ t - Budget.crossing_B x t ≤ 3 / 4 := by
  have hd : 0 < Budget.rowD_B x := lt_of_lt_of_le (by norm_num) (Budget.rowD_B_pos hx')
  have hp : 0 ≤ 2 - 8 * x / 9 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0 ≤ 1 - 138 * x / 125 := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t - Budget.crossing_B x t =
      ((1 - 138 * x / 125) * t + 1421 * x / 2250) / Budget.rowD_B x := by
    unfold Budget.crossing_B
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hd.ne']
    unfold Budget.rowD_B
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_, (div_le_iff₀ hd).mpr ?_, ?_, ?_⟩
  · unfold Budget.rowD_B; linarith
  · unfold Budget.rowD_B; linarith
  · rw [he]; apply (le_div_iff₀ hd).mpr; unfold Budget.rowD_B; linarith
  · rw [he]; apply (div_le_iff₀ hd).mpr; unfold Budget.rowD_B; linarith

lemma plain_at_crossing_B (δ x t : ℝ) (hd : Budget.rowD_B x ≠ 0) :
    plainExponent δ x t (Budget.crossing_B x t) = shortExponent_B δ x t := by
  unfold plainExponent shortExponent_B inverseExponent_B Budget.crossing_B
  field_simp [hd]
  unfold Budget.rowD_B
  ring

theorem selected_short_bound_B {δ x t r : ℝ} (hδ : 0 ≤ δ) (_hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    (r ≤ Budget.crossing_B x t → plainExponent δ x t r ≤ shortExponent_B δ x t) ∧
      (Budget.crossing_B x t ≤ r → inverseExponent_B δ x r ≤ shortExponent_B δ x t) ∧
      (Budget.crossing_B x t ≤ 19 / 26 → 19 / 26 ≤ r →
        inverseExponent δ x r ≤ shortExponent_B δ x t) := by
  have hd : Budget.rowD_B x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (Budget.rowD_B_pos hx'))
  refine ⟨?_, ?_, ?_⟩
  · intro hr
    rw [← plain_at_crossing_B δ x t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 - 8 * x / 9 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    unfold shortExponent_B inverseExponent_B
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 - 138 * x / 125 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hcr hr
    have h1 : inverseExponent δ x r ≤ inverseExponent δ x (19 / 26) := by
      unfold inverseExponent
      have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 - x by linarith)
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
    have h2 : inverseExponent δ x (19 / 26) = inverseExponent_B δ x (19 / 26) := by
      unfold inverseExponent inverseExponent_B
      ring
    have h3 : inverseExponent_B δ x (19 / 26) ≤ shortExponent_B δ x t := by
      unfold shortExponent_B inverseExponent_B
      have hh := mul_le_mul_of_nonneg_left hcr (show 0 ≤ 1 - 138 * x / 125 by linarith)
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
    linarith

theorem balanced_cutoff_B_bounds {δ x : ℝ} (hB : Budget.inBoxB δ x) :
    1 ≤ Budget.balancedCutoff_B δ x ∧ Budget.balancedCutoff_B δ x ≤ 3 / 2 := by
  rcases hB with ⟨hδ0, hδ1, hx0, hx1⟩
  have hJ := Budget.rowJ_B_pos (δ := δ) (x := x) (by linarith) (by linarith) hx1
  have hN := Budget.rowN_B_bounds (by linarith) hx1
  unfold Budget.balancedCutoff_B
  constructor
  · exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by linarith) (by linarith [hN.1])) (by linarith))
  · have hdiff : 2 * (δ * Budget.rowN_B x) ≤ Budget.rowJ_B δ x := by
      unfold Budget.rowJ_B Budget.rowD_B Budget.rowP_B
      have hD : 2254 / 1125 ≤ 3 - 2242 * x / 1125 := by linarith
      have hP : 0 ≤ (2 - 8 * x / 9) * (1 - 138 * x / 125) := mul_nonneg (by linarith) (by linarith)
      have hN1 : δ * Budget.rowN_B x ≤ 41 / 100 := by
        nlinarith [mul_nonneg (show 0 ≤ δ by linarith) (sub_nonneg.mpr hN.2), hN.1]
      nlinarith [mul_nonneg (show 0 ≤ 5 / 6 - δ by linarith) (sub_nonneg.mpr hD),
        mul_nonneg (show 0 ≤ δ by linarith) hP]
    have hh : δ * Budget.rowN_B x / Budget.rowJ_B δ x ≤ 1 / 2 :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith

theorem balanced_count_identity_B {δ x : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (_hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    max (shortExponent_B δ x (Budget.balancedCutoff_B δ x))
        (longExponent δ (Budget.balancedCutoff_B δ x)) =
      Budget.rowCount_B δ x := by
  have hD0 : 0 < Budget.rowD_B x := lt_of_lt_of_le (by norm_num) (Budget.rowD_B_pos hx')
  have hJ := Budget.rowJ_B_pos (δ := δ) (x := x) hδ hδ' hx'
  have hJ0 : 0 < Budget.rowJ_B δ x := by linarith
  have hl : longExponent δ (Budget.balancedCutoff_B δ x) = Budget.rowCount_B δ x := by
    unfold longExponent Budget.balancedCutoff_B Budget.rowCount_B
    field_simp [hJ0.ne']
    ring
  have hs : shortExponent_B δ x (Budget.balancedCutoff_B δ x) = Budget.rowCount_B δ x := by
    unfold shortExponent_B inverseExponent_B Budget.crossing_B Budget.balancedCutoff_B
      Budget.rowCount_B
    field_simp [hD0.ne', hJ0.ne']
    unfold Budget.rowJ_B Budget.rowD_B Budget.rowP_B Budget.rowN_B
    ring
  rw [hl, hs, max_self]

theorem short_B_ge_base {δ x : ℝ} (hB : Budget.inBoxB δ x) :
    1 - δ ≤ shortExponent_B δ x (Budget.balancedCutoff_B δ x) := by
  rcases hB with ⟨hδ0, hδ1, hx0, hx1⟩
  have hD0 : 0 < Budget.rowD_B x := lt_of_lt_of_le (by norm_num) (Budget.rowD_B_pos hx1)
  have hJ := Budget.rowJ_B_pos (δ := δ) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < Budget.rowJ_B δ x := by linarith
  have hN := Budget.rowN_B_bounds (by linarith) hx1
  have hrc : 1 - δ ≤ Budget.rowCount_B δ x := by
    unfold Budget.rowCount_B
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith [hN.1]))
        hJ0.le)
  have hs : shortExponent_B δ x (Budget.balancedCutoff_B δ x) = Budget.rowCount_B δ x := by
    unfold shortExponent_B inverseExponent_B Budget.crossing_B Budget.balancedCutoff_B
      Budget.rowCount_B
    field_simp [hD0.ne', hJ0.ne']
    unfold Budget.rowJ_B Budget.rowD_B Budget.rowP_B Budget.rowN_B
    ring
  linarith

end HeckeDetectorRowCount

namespace HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem selected_inverse_requested_capacity (r ν : ℝ)
    (hr0 : 69 / 100 ≤ r) (_hr1 : r ≤ 19 / 26)
    (hν : 0 < ν) (hcap : ν < 269 / 500 - 69 * r / 125) :
    0 ≤ (269 / 500 - 69 * r / 125) - ν ∧
      (269 / 500 - 69 * r / 125) - ν ≤ 7 / 37 ∧
      (269 / 500 - 69 * r / 125) - ν < 269 / 500 - 69 * r / 125 := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem selected_inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (_hx : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hε : 0 ≤ ε) (_hmesh : 0 ≤ mesh) (hν : 0 ≤ ν) :
    1 - δ * r - 2 * (δ * x) * ((269 / 500 - 69 * r / 125) - ν) +
      2 * ε + δ * mesh + εm ≤
      inverseExponent_B δ x r + commonLoss ε εm mesh ν := by
  have hq : 2 * (δ * x) ≤ 1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 _hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent_B commonLoss
  have heq : 1 - δ * r - 2 * (δ * x) * ((269 / 500 - 69 * r / 125) - ν) =
      (1 - δ * (269 * x / 250 + (1 - 138 * x / 125) * r)) + 2 * (δ * x) * ν := by ring
  rw [heq]
  linarith

theorem plain_requested_capacity_B (Δ x t r m ε ν : ℝ)
    (hΔ : 0 ≤ Δ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) (ht : 1 ≤ t) (ht1 : t ≤ 3 / 2)
    (hr : r ≤ Budget.crossing_B x t) (hleft : t - r - ε ≤ m) (_hε : ε ≤ 1 / 1000)
    (hν : 0 ≤ ν) (hνcap : ν < (1 - 2 * m) / (9 / 2 + 12 * Δ)) :
    0 ≤ (1 - 2 * m) / (9 / 2 + 12 * Δ) - ν ∧
      (1 - 2 * m) / (9 / 2 + 12 * Δ) - ν ≤ 7 / 37 ∧
      2 * m + 6 * (3 / 4 + 2 * Δ) * ((1 - 2 * m) / (9 / 2 + 12 * Δ) - ν) ≤ 1 := by
  have hcross := crossing_B_bounds hx hx1 ht ht1
  have hm : 1 / 3 - ε ≤ m := by linarith [hcross.2.2.1]
  have hd : 0 < 9 / 2 + 12 * Δ := by linarith
  have hc : (1 - 2 * m) / (9 / 2 + 12 * Δ) ≤ 7 / 37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith, by linarith, ?_⟩
  have heq : 6 * (3 / 4 + 2 * Δ) = 9 / 2 + 12 * Δ := by ring
  rw [heq, mul_sub, mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end HeckeDetectorBranchBudget

namespace HeckeDetectorAdaptiveCutoff
open HeckeDetectorRowCount

def cutoffSub16799 (δ q : ℝ) : ℝ :=
  if δ ≤ 5 / 6 then
    let x := min (1 / 2) (max 0 (q / δ))
    if Budget.inBoxB δ x then Budget.balancedCutoff_B δ x else cutoff δ q
  else 3 / 2

theorem cutoffSub16799_bounds (δ q : ℝ) (hδ : 0 ≤ δ) :
    1 ≤ cutoffSub16799 δ q ∧ cutoffSub16799 δ q ≤ 3 / 2 := by
  unfold cutoffSub16799
  dsimp only
  split_ifs with hd hB
  · exact balanced_cutoff_B_bounds hB
  · exact cutoff_bounds δ q hδ
  · norm_num

theorem cutoffSub16799_eq_inBoxB (δ q : ℝ) (hδ : 0 < δ) (hd : δ ≤ 5 / 6)
    (hq : 0 ≤ q) (hq' : q ≤ δ / 2) (hB : Budget.inBoxB δ (q / δ)) :
    cutoffSub16799 δ q = Budget.balancedCutoff_B δ (q / δ) := by
  have hx : 0 ≤ q / δ := div_nonneg hq hδ.le
  have hx' : q / δ ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoffSub16799, if_pos hd, max_eq_right hx, min_eq_right hx', if_pos hB]

theorem cutoffSub16799_eq_outBoxB (δ q : ℝ) (hδ : 0 < δ) (hd : δ ≤ 5 / 6)
    (hq : 0 ≤ q) (hq' : q ≤ δ / 2) (hB : ¬ Budget.inBoxB δ (q / δ)) :
    cutoffSub16799 δ q = cutoff δ q := by
  have hx : 0 ≤ q / δ := div_nonneg hq hδ.le
  have hx' : q / δ ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoffSub16799, if_pos hd, max_eq_right hx, min_eq_right hx', if_neg hB]

theorem cutoffSub16799_eq_high (δ q : ℝ) (hδ : 5 / 6 < δ) : cutoffSub16799 δ q = 3 / 2 := by
  simp only [cutoffSub16799, if_neg (not_le_of_gt hδ)]

end HeckeDetectorAdaptiveCutoff

namespace HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorPlainFiberCount HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles HeckeDetectorCoefficientTransfer

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The standard `Moments` bundle augmented with the Stage-1 complete-factor inverse-marked bound
`∑ s ∈ selected, F.widths s < 269/500 - (69/125) F.r` on `69/100 ≤ F.r ≤ 19/26`. -/
structure MomentsSub16799 (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  base : Moments F Δ c κ C height εm
  inverse_marked_selected : 69 / 100 ≤ F.r → F.r ≤ 19 / 26 →
    ∀ selected : Finset Slot, selected ⊆ F.slots →
    (∑ s ∈ selected, F.widths s) < 269 / 500 - (69 / 125) * F.r →
    ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U ^ F.r) s t * F.physicalProduct selected u‖ ^ 2 ≤ C * U ^ (1 + εm)

theorem Fiber.selected_inverse_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : MomentsSub16799 F Δ c κ C height εm)
    (hU : 1 < U) (ha : 1 / 2 ≤ a) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height)
    (hr0 : 69 / 100 ≤ F.r) (hr1 : F.r ≤ 19 / 26)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 7 / 37) (hcap : z < 269 / 500 - (69 / 125) * F.r) :
    (F.rows.card : ℝ) ≤
      (12 * (1 + height) * C) * U ^ (1 - (2 * a - 1) * F.r - 2 * F.q * z +
        2 * ε + (2 * a - 1) * F.mesh + εm) := by
  let r := F.r
  have hδ : 0 ≤ 2 * a - 1 := by linarith
  obtain ⟨selected, hsub, _hpos, hlen, hspike⟩ :=
    HeckeDetectorPhysicalSelection.select_physical_product M H F.rows F.nonempty F.slots
      (fun u => u.val) F.profile F.upper F.widths F.bin F.external U (2 * a - 1) F.mesh F.binWidth z
      hU hδ F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
      hz (hz'.trans F.supply) F.fixed_bin
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes F.rows F.family U a ε tstar T allowance i hU
    (by linarith) (fun u => (F.witness u).toWitness) F.label F.left F.right
    F.fixed_label F.fixed_left F.fixed_right
  have hcap' : (∑ s ∈ selected, F.widths s) < 269 / 500 - (69 / 125) * F.r :=
    lt_of_le_of_lt hlen hcap
  have hUp : 0 < U := zero_lt_one.trans hU
  have hDp : 0 < U ^ r := Real.rpow_pos_of_pos hUp _
  have hE : 0 ≤ C * U ^ (1 + εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy F.rows F.family U a ε tstar T allowance i
    (by linarith) (fun u => (F.witness u).toWitness) F.label F.inverseProfile (U ^ r)
    (1 / 4) (9 / 4) (C * U ^ (1 + εm)) (fun u => F.physicalProduct selected u)
    hDp (by norm_num) (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hh hf
    (moments.inverse_marked_selected hr0 hr1 selected hsub hcap')
  have he' : ∑ u ∈ F.rows,
      ‖polynomial (F.family u F.label) true F.inverseProfile (U ^ r)
        (F.witness u).zero.re (F.witness u).frequency * F.physicalProduct selected u‖ ^ 2 ≤
      (12 * (1 + height) * C) * U ^ (1 + εm) := by
    (convert he using 1; first | rfl | ring)
  exact HeckeDetectorRowCount.inverse_count F.rows (fun u => F.family u F.label)
    F.inverseProfile (U ^ r) (fun u => (F.witness u).zero.re) (fun u => (F.witness u).frequency)
    (fun u => F.physicalProduct selected u) U (2 * a - 1) r F.q z (2 * ε)
    ((2 * a - 1) * F.mesh) εm (12 * (1 + height) * C) hUp
    (fun u hu => (hsp u hu).2.2.1) hspike he'

end HeckeDetectorRawFiber

namespace HeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount HeckeDetectorBatch

private lemma balancedRowCount_eq_rowCount {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx : x ≤ 1 / 2) :
    Endpoint.balancedRowCount δ (1 / 2 - x) = Budget.rowCount δ x := by
  have hJ := Budget.rowJ_pos (δ := δ) (x := x) hδ0 hδ hx
  have hJ0 : 0 < Budget.rowJ δ x := by linarith
  have hden : Endpoint.balanceDenominator δ (1 / 2 - x) = Budget.rowJ δ x := by
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
      Budget.rowJ Budget.rowD Budget.rowP
    ring
  unfold Endpoint.balancedRowCount Endpoint.balancedCutoff Budget.rowCount
  rw [hden]
  unfold Endpoint.primeWeight Budget.rowP
  field_simp [hJ0.ne']
  ring

private theorem count_bound_of_inBoxB_branches
    (N C U δ x Δ t r m loss ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hB : Budget.inBoxB δ x)
    (ht_eq : t = Budget.balancedCutoff_B δ x)
    (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ 1 / 8) (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : N ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + loss))
    (hP0 : N ≤ C * U ^ (1 - 2 * δ * m + loss))
    (hI_high : 19 / 26 ≤ r → r < 1 → ν < (1 - r) / 2 →
      N ≤ C * U ^ (inverseExponent δ x r + loss))
    (hI_sel : 69 / 100 ≤ r → r ≤ 19 / 26 → ν < 269 / 500 - 69 * r / 125 →
      N ≤ C * U ^ (inverseExponent_B δ x r + loss))
    (hP : r ≤ Budget.crossing_B x t → m < 1 / 2 → ν < (1 - 2 * m) / (9 / 2 + 12 * Δ) →
      N ≤ C * U ^ (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (9 / 2 + 12 * Δ) + loss)) :
    N ≤ C * U ^ (Budget.rowCount_B δ x + loss + Δ / 4 + 5 * γ + 6 * ν) := by
  have hδ : 0 ≤ δ := by linarith [hB.1]
  have hδcap : δ ≤ 5 / 6 := by linarith [hB.2.1]
  have hδ1 : δ ≤ 1 := by linarith [hB.2.1]
  have hx : 0 ≤ x := by linarith [hB.2.2.1]
  have hx' : x ≤ 1 / 2 := hB.2.2.2
  have ht_bds : 1 ≤ t ∧ t ≤ 3 / 2 := ht_eq ▸ balanced_cutoff_B_bounds hB
  have hcr_box : 139 / 200 ≤ Budget.crossing_B x t ∧ Budget.crossing_B x t ≤ 364 / 500 :=
    ht_eq ▸ Budget.crossing_B_mem_box hB
  have hid_bal : max (shortExponent_B δ x t) (longExponent δ t) = Budget.rowCount_B δ x :=
    ht_eq ▸ balanced_count_identity_B hδ hδcap hx hx'
  have hshort_le : shortExponent_B δ x t ≤ Budget.rowCount_B δ x :=
    hid_bal ▸ le_max_left _ _
  have hlong_le : longExponent δ t ≤ Budget.rowCount_B δ x :=
    hid_bal ▸ le_max_right _ _
  have hbase_le : 1 - δ ≤ Budget.rowCount_B δ x :=
    (ht_eq ▸ short_B_ge_base hB).trans hshort_le
  have hchoose := selected_short_bound_B (t := t) (r := r) hδ hx hx'
  have hcross := crossing_B_bounds hx hx' ht_bds.1 ht_bds.2
  have promote (p : ℝ) (hb : N ≤ C * U ^ p)
      (hpq : p ≤ Budget.rowCount_B δ x + loss + Δ / 4 + 5 * γ + 6 * ν) :
      N ≤ C * U ^ (Budget.rowCount_B δ x + loss + Δ / 4 + 5 * γ + 6 * ν) :=
    hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpq) hC)
  by_cases hr1 : 1 ≤ r
  · rw [max_eq_right (show 1 ≤ (1 + 5 * r) / 6 by linarith)] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδcap hγ hright
    have hcγ : (5 / 6 - δ) * γ ≤ γ := by nlinarith [mul_nonneg hδ hγ]
    linarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  rw [max_eq_left (show (1 + 5 * r) / 6 ≤ 1 by linarith)] at hI0
  by_cases hrc : Budget.crossing_B x t ≤ r
  · by_cases hr19 : 19 / 26 ≤ r
    · by_cases hcap : (1 - r) / 2 ≤ ν
      · apply promote _ hI0
        have hz := inverse_zero_capacity hδ hcap
        have hv : 2 * δ * ν ≤ 6 * ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδcap) hν]
        linarith
      · apply promote _ (hI_high hr19 hr1' (lt_of_not_ge hcap))
        have hs := hchoose.2.2 (by linarith [hcr_box.2]) hr19
        linarith
    · have hr19' : r ≤ 19 / 26 := (lt_of_not_ge hr19).le
      have hr69 : 69 / 100 ≤ r := by linarith [hcr_box.1]
      by_cases hcap : 269 / 500 - 69 * r / 125 ≤ ν
      · apply promote _ hI0
        have hq2 : 2 * (δ * x) ≤ 1 := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hx')]
        have h1 : 1 - δ * r ≤ inverseExponent_B δ x r + 2 * (δ * x) * ν := by
          unfold inverseExponent_B
          have : 2 * (δ * x) * (269 / 500 - 69 * r / 125) ≤ 2 * (δ * x) * ν :=
            mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) (mul_nonneg hδ hx))
          linarith
        have hs := hchoose.2.1 hrc
        have hv : 2 * (δ * x) * ν ≤ 6 * ν := by nlinarith
        linarith
      · apply promote _ (hI_sel hr69 hr19' (lt_of_not_ge hcap))
        have hs := hchoose.2.1 hrc
        linarith
  · have hrc' : r ≤ Budget.crossing_B x t := (lt_of_not_ge hrc).le
    by_cases hm : 1 / 2 ≤ m
    · apply promote _ hP0
      have hm' := mul_le_mul_of_nonneg_left hm hδ
      linarith
    · have hm' : m < 1 / 2 := lt_of_not_ge hm
      by_cases hcap : (1 - 2 * m) / (9 / 2 + 12 * Δ) ≤ ν
      · apply promote _ hP0
        have hk0 : 0 < 3 / 4 + 2 * Δ := by linarith
        have hk1 : 3 / 4 + 2 * Δ ≤ 1 := by linarith
        have hz := plain_zero_capacity hδ hk0 hk1 hν
          (show (1 - 2 * m) / (6 * (3 / 4 + 2 * Δ)) ≤ ν by convert hcap using 1; ring)
        have hv : 6 * δ * ν ≤ 6 * ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδcap) hν]
        linarith
      · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
        have hmm : 1 / 3 - γ ≤ m := by linarith [hcross.2.2.1]
        have hp := plain_capacity_comparison hδ hδ1 hx hx' hΔ hΔ' hmm hm'.le hγ hleft
        have hs := hchoose.1 hrc'
        linarith

theorem count_from_raw_moments_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      0 ≤ q → q ≤ (2 * a - 1) / 2 →
      ∀ {Label Slot : Type*}
        (F : Fiber M H Label Slot U a ε (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q)
          T allowance i),
      F.q = q →
      MomentsSub16799 F Δ c κ C height εm →
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
        U ^ (Budget.rowCountSub16799 (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 4 + 159 * ε + εm + F.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ ν C height q i hU ha hδcap hε hεsmall hΔ hΔ' hν hC hh hf hq0 hqδ
    Label Slot F hFq moments
  have hδ : 0 < 2 * a - 1 := by linarith
  have ha' : 1 / 2 ≤ a := by linarith
  have hδ1 : 2 * a - 1 ≤ 1 := by linarith
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hq0 hδ.le
  have hx' : q / (2 * a - 1) ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hqx : (2 * a - 1) * (q / (2 * a - 1)) = F.q := by rw [hFq]; field_simp
  have ht_bounds := HeckeDetectorAdaptiveCutoff.cutoffSub16799_bounds (2 * a - 1) q hδ.le
  have hgeom := F.lengths hU
  have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
  have hUp : 0 < U := zero_lt_one.trans hU
  obtain ⟨hconst, hconstP, hconstI, hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q' : ℝ) (hC' : C' ≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q') :
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ * U ^ q' :=
    hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε
    (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff
    moments.base.inverse_raw
  have hI0 : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (max 1 ((1 + 5 * F.r) / 6) - (2 * a - 1) * F.r + commonLoss ε εm F.mesh ν) :=
    promote _ _ _ hconstI0 hi0
      (no_slot_inverse_loss F.r (2 * a - 1) ε εm F.mesh ν hε F.mesh_nonneg hν.le)
  have hp0 := F.plain_unmarked_count moments.base hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (1 - 2 * (2 * a - 1) * F.m + commonLoss ε εm F.mesh ν) :=
    promote _ _ _ hconstP hp0
      (no_slot_plain_loss F.m (2 * a - 1) ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le)
  have hI : 23 / 37 ≤ F.r → F.r < 1 → ν < (1 - F.r) / 2 →
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
        U ^ (inverseExponent (2 * a - 1) (q / (2 * a - 1)) F.r + commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz, hz', hcap1, hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments.base hU ha' hC hh hf ((1 - F.r) / 2 - ν)
      hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r (2 * a - 1) (q / (2 * a - 1)) ε εm F.mesh ν
      hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  by_cases hB : Budget.inBoxB (2 * a - 1) (q / (2 * a - 1))
  · simp only [Budget.rowCountSub16799, if_pos hB]
    have ht_eq := HeckeDetectorAdaptiveCutoff.cutoffSub16799_eq_inBoxB (2 * a - 1) q
      hδ hδcap hq0 hqδ hB
    have hI_sel : 69 / 100 ≤ F.r → F.r ≤ 19 / 26 → ν < 269 / 500 - 69 * F.r / 125 →
        (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
          U ^ (inverseExponent_B (2 * a - 1) (q / (2 * a - 1)) F.r + commonLoss ε εm F.mesh ν) := by
      intro hr0' hr1' hv
      obtain ⟨hz, hz', hcap_sel⟩ := selected_inverse_requested_capacity F.r ν hr0' hr1' hν hv
      have hb := F.selected_inverse_marked_count moments hU ha' hC hh hf hr0' hr1'
        ((269 / 500 - 69 * F.r / 125) - ν) hz hz' (by linarith [hcap_sel])
      apply promote _ _ _ hconstI hb
      have hl := selected_inverse_marked_loss F.r (2 * a - 1) (q / (2 * a - 1)) ε εm F.mesh ν
        hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rwa [hqx] at hl
    have hP_B : F.r ≤ Budget.crossing_B (q / (2 * a - 1))
          (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) →
        F.m < 1 / 2 → ν < (1 - 2 * F.m) / (9 / 2 + 12 * Δ) →
        (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
          U ^ (1 - 2 * (2 * a - 1) * F.m -
            2 * ((2 * a - 1) * (q / (2 * a - 1))) * (1 - 2 * F.m) / (9 / 2 + 12 * Δ) +
            commonLoss ε εm F.mesh ν) := by
      intro hr hm hv
      obtain ⟨hz, hz', hcap_pln⟩ := plain_requested_capacity_B Δ (q / (2 * a - 1))
        (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) F.r F.m ε ν
        hΔ hx hx' ht_bounds.1 ht_bounds.2 hr hgeom.1 hεsmall hν.le hv
      have hb := F.plain_marked_count moments.base hU ha' hΔ hC hh hf
        ((1 - 2 * F.m) / (9 / 2 + 12 * Δ) - ν) hz hz' hcap_pln
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m (2 * a - 1) (q / (2 * a - 1)) Δ ε εm F.mesh ν
        hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      simpa only [hqx] using hl
    have hc' := count_bound_of_inBoxB_branches (F.rows.card : ℝ) (fiberConstant C height K₀)
      U (2 * a - 1) (q / (2 * a - 1)) Δ
      (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) F.r F.m
      (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hB ht_eq hΔ hΔ' hν.le hε
      hgeom.1 hgeom.2.1 hI0 hP0 (fun hr19 hr1 hv => hI (by linarith) hr1 hv) hI_sel hP_B
    convert hc' using 1; congr 2
    unfold commonLoss
    ring
  · simp only [Budget.rowCountSub16799, if_neg hB]
    have ht_eq := HeckeDetectorAdaptiveCutoff.cutoffSub16799_eq_outBoxB (2 * a - 1) q
      hδ hδcap hq0 hqδ hB
    have ht_bal := HeckeDetectorAdaptiveCutoff.cutoff_eq_balanced (2 * a - 1) q hδ hδcap hq0 hqδ
    have hP : F.r ≤ crossing (q / (2 * a - 1))
          (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) →
        F.m < 1 / 2 → ν < (1 - 2 * F.m) / (9 / 2 + 12 * Δ) →
        (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
          U ^ (1 - 2 * (2 * a - 1) * F.m -
            2 * ((2 * a - 1) * (q / (2 * a - 1))) * (1 - 2 * F.m) / (9 / 2 + 12 * Δ) +
            commonLoss ε εm F.mesh ν) := by
      intro hr hm hv
      obtain ⟨hz, hz', hcap⟩ := plain_requested_capacity Δ (q / (2 * a - 1))
        (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) F.r F.m ε ν
        hΔ hx hx' ht_bounds.1 ht_bounds.2 hr hgeom.1 (by linarith) hν.le hv
      have hb := F.plain_marked_count moments.base hU ha' hΔ hC hh hf
        ((1 - 2 * F.m) / (9 / 2 + 12 * Δ) - ν) hz hz' hcap
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m (2 * a - 1) (q / (2 * a - 1)) Δ ε εm F.mesh ν
        hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      simpa only [hqx] using hl
    have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀)
      U (2 * a - 1) (q / (2 * a - 1)) Δ
      (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q) F.r F.m
      (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hΔ hΔ'
      ht_bounds.1 ht_bounds.2 hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
    have hid_out : max (shortExponent (2 * a - 1) (q / (2 * a - 1))
          (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q))
        (longExponent (2 * a - 1)
          (HeckeDetectorAdaptiveCutoff.cutoffSub16799 (2 * a - 1) q)) =
        Budget.rowCount (2 * a - 1) (q / (2 * a - 1)) := by
      rw [ht_eq, ht_bal, balanced_count_identity hδ.le hδcap hx hx']
      exact balancedRowCount_eq_rowCount hδ.le hδcap hx'
    convert hc' using 1; congr 2
    rw [hid_out]
    unfold commonLoss
    ring

end HeckeDetectorCountFromMoments

namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff HeckeDetectorFiberPartition
open ProbePhysical ProbeMellinBoundary ProbeRaySlots

local notation "O" => Eisenstein.O

/-- Adaptive row-count exponent with `Budget.rowCountSub16799` on balanced bins `δ ≤ 5/6`. -/
def adaptiveRowExponentSub16799 (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ ≤ 5 / 6 then Budget.rowCountSub16799 δ (q / δ) + Δ / 4 + 159 * ε + εm + slotMesh + 7 * ν
  else 1 - δ + 78 * ε + εm

theorem balanced_adaptive_count_from_raw_moments_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoffSub16799 (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots U ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (Budget.rowCountSub16799 (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    HeckeDetectorCountFromMoments.count_from_raw_moments_sub16799
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf Label Slot _ B
    hne hq hmom
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _ => Budget.rowCountSub16799 (2 * a - 1) (q / (2 * a - 1)) +
      Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hnef
      exact hcount a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf
        hqb.1 hqb.2 (B.fiber bin j J K hnef)
        (HeckeDetectorFixedAmplitudeCount.fiber_mean_eq B q hq bin j J K hnef)
        (hmom bin j J K hnef))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hb

theorem high_adaptive_count_from_raw_moments_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1 < U → 5 / 6 < 2 * a - 1 → a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoffSub16799 (2 * a - 1) q) T allowance i),
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (1 - (2 * a - 1) + 78 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    HeckeDetectorHighBatchCount.high_batch_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoffSub16799_eq_high (2 * a - 1) q ha]
  intro Label Slot _ B hmom
  exact hcount a ε T allowance Δ C height i hU ha.le ha' hε hε' hC hh hf B
    (fun bin j J K hne => (hmom bin j J K hne).base)

section WithModulus
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Moment bounds for every retained source batch under `cutoffSub16799` and `MomentsSub16799`. -/
def SourceMomentsAtSub16799 {N : ℕ} (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N → ℝ) (W : Fin N → ℝ → ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀ q : ℝ, ∀ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z ^ d) a ε (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
    B.rows ⊆ rows → B.data = sourceMomentData M H hH S hS η →
    B.reverse = sourceMomentReverse M H → B.slots = Finset.univ →
    B.widths = (fun j => ell j / d) → B.profile = W → B.upper = (fun _ => b) →
    B.external = (fun _ => z) → B.mesh = slotMesh → B.binWidth = binWidth →
    (∀ u ∈ B.rows, ∀ j, B.family u j = sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
      MomentsSub16799 (B.fiber bin j J K hne) Δ c κ C height εm

theorem actual_source_amplitude_batches_sub16799 (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hdtop : dmax ≤ 37 / 42) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hheightCost : 0 ≤ heightCost) (hmargin : 0 < margin) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    ∀ (U : ℝ) (rows : Finset FreeRow), rows.Nonempty → rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) U →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
    ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
    ∀ (N : ℕ) (ell : Fin N → ℝ), (∀ j, 0 < ell j) → (∀ j, ell j ≤ dmin * mesh) →
      (∑ j, ell j) = 1 / 6 →
    ∀ (W : Fin N → ℝ → ℂ) (upper : Fin N → ℝ) (z : Fin N → ℂ),
    let Q := physical M H (fun u : FreeRow => u.val) W upper (fun j => ell j / d) z (Z ^ d)
    ∀ bin : BinLabel (Finset.univ : Finset (Fin N)) ((2 * a - 1) / 2) binWidth,
    let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) binWidth hb
      (fun j => ell j / d) Q bin
    rows'.Nonempty →
    let q := classMean Finset.univ ((2 * a - 1) / 2) binWidth (fun j => ell j / d) bin
    ∃ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z ^ d) a ε (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
      B.rows = rows' ∧ B.data = sourceMomentData M H hH S hS.prime η ∧
      B.reverse = sourceMomentReverse M H ∧ B.slots = Finset.univ ∧
      B.widths = (fun j => ell j / d) ∧ B.profile = W ∧ B.upper = upper ∧ B.external = z ∧
      B.mesh = mesh ∧ B.binWidth = binWidth ∧
      (∀ u ∈ rows', ∀ j, B.family u j =
        sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀ u ∈ B.rows, rowMean B.slots (Z ^ d) ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val)
          B.profile B.upper B.widths B.external (Z ^ d)) u = q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows _hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum
    W upper z
  dsimp only
  intro bin hne'
  let Q := physical M H (fun u : FreeRow => u.val) W upper (fun j => ell j / d) z (Z ^ d)
  let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) binWidth hb
    (fun j => ell j / d) Q bin
  let q := classMean Finset.univ ((2 * a - 1) / 2) binWidth (fun j => ell j / d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hcut := cutoffSub16799_bounds (2 * a - 1) q (by linarith)
  obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hZ, hMesh, hBin, hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu => hcal u (hsub hu)) (fun u hu => hrow u (hsub hu)) a i hi ha ha'
      (fun u hu => hnext u (hsub hu)) (fun u hu => hcurrent u (hsub hu))
      (cutoffSub16799 (2 * a - 1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hZ, hMesh, hBin, hFam, ?_⟩
  intro u hu
  have hu' : u ∈ rows' := hBr ▸ hu
  rw [hSlots, hWidths, hW, hUpper, hZ, hBin]
  exact rowMean_eq rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) binWidth hb
    (fun j => ell j / d) Q bin u hu'

end WithModulus
end ProbeHighRowFamily

namespace ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff HeckeDetectorFiberPartition
open ProbeHighRowFamily ProbePhysical ProbeMellinBoundary ProbeRaySlots Parameters

local notation "O" => Eisenstein.O

structure CountParametersSub16799 (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0 < cB
  cB_one : cB ≤ 1
  kB_pos : 0 < kB
  cH_pos : 0 < cH
  cH_one : cH ≤ 1
  kH_pos : 0 < kH
  balanced : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoffSub16799 (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots U ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (Budget.rowCountSub16799 (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν)
  high : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1 < U → 5 / 6 < 2 * a - 1 → a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoffSub16799 (2 * a - 1) q) T allowance i),
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (1 - (2 * a - 1) + 78 * ε + εm)

theorem exists_count_parameters_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    Nonempty (CountParametersSub16799 M H εm) := by
  obtain ⟨cB, kB, KB, hcB, hcB1, hkB, hKB, hbalanced⟩ :=
    balanced_adaptive_count_from_raw_moments_sub16799 M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH, kH, KH, hcH, hcH1, hkH, hKH, hhigh⟩ :=
    high_adaptive_count_from_raw_moments_sub16799 M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB, kB, cH, kH, hcB, hcB1, hkB, hcH, hcH1, hkH, ⟨KB, hKB, hbalanced⟩, ⟨KH, hKH, hhigh⟩⟩⟩

theorem source_count_parameters_sub16799 {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (CountParametersSub16799 F.modulus ⊤ D.t) :=
  exists_count_parameters_sub16799 F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x => (F.bounded x).2) D.t D.t_pos

lemma momentsSub16799_mono_constant {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ c κ C D height εm : ℝ} (hU : 0 ≤ U) (h : MomentsSub16799 F Δ c κ C height εm)
    (hCD : C ≤ D) :
    MomentsSub16799 F Δ c κ D height εm where
  base := moments_mono_constant hU h.base hCD
  inverse_marked_selected hr0 hr1 selected hsel hcap n hn s hs t ht :=
    (h.inverse_marked_selected hr0 hr1 selected hsel hcap n hn s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))

/-- Uniform raw moment estimates for all retained source rows under `MomentsSub16799`. -/
def SourceMomentBoundSub16799 {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParametersSub16799 F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1 / 200 : ℝ) ≤ d → d ≤ 7 / 8 → 51 / 100 < a → a ≤ 1 →
    (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - D.t)) →
    ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ height →
    SourceMomentsAtSub16799 F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
      (fun _ y => (F.w y : ℂ)) Z d a D.ε τ (7 / 8) 2 D.t D.t i z Δ
      (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBoundSub16799.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParametersSub16799 F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0 ≤ Z) (h : SourceMomentBoundSub16799 F counts η Z τ C height) (hC : C ≤ C') :
    SourceMomentBoundSub16799 F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hBr hBd hRev hSlots hW hP hU hE hM hB hF
    bin j J K hne
  exact momentsSub16799_mono_constant (Real.rpow_nonneg hZ _)
    (h rows d a hd hd' ha ha' hrows i z hz hzh q B hBr hBd hRev hSlots hW hP hU hE hM hB hF
      bin j J K hne) hC

theorem balanced_source_count_from_raw_moments_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : CountParametersSub16799 M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ ν C q : ℝ) (i : ℕ), i ≤ n → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → a ≤ 1 →
        0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type} (B : Batch M H Label Slot (Z ^ d) a ε
        (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z ^ d) ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z ^ d))
          u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ counts.cB counts.kB
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (Budget.rowCountSub16799 (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨K₀, hK₀, hcount⟩ := counts.balanced
  obtain ⟨K, hK, hpref⟩ := source_count_prefactor_eventually (Label := Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin, hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) dmin hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Δ ν
    (C * Z ^ momentCost) (Z ^ heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : CountParametersSub16799 M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ C q : ℝ) (i : ℕ), i ≤ n → 5 / 6 < 2 * a - 1 → a ≤ 1 →
        0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C →
      ∀ {Slot : Type} (B : Batch M H Label Slot (Z ^ d) a ε
        (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ counts.cH counts.kH
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (1 - (2 * a - 1) + 78 * ε + εm) := by
  obtain ⟨K₀, hK₀, hcount⟩ := counts.high
  obtain ⟨K, hK, hpref⟩ := source_count_prefactor_eventually (Label := Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin, hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) dmin hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Δ
    (C * Z ^ momentCost) (Z ^ heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem adaptive_source_count_from_raw_moments_sub16799
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : CountParametersSub16799 M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ ν C q : ℝ) (i : ℕ), i ≤ n → 51 / 100 < a → a ≤ 1 →
        0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type} (B : Batch M H Label Slot (Z ^ d) a ε
        (cutoffSub16799 (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z ^ d) ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z ^ d))
          u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        MomentsSub16799 (B.fiber bin j J K hne) Δ
          (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
          (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (adaptiveRowExponentSub16799 (2 * a - 1) q Δ ε εm B.mesh ν) := by
  obtain ⟨KB, hKB, hbalanced⟩ := balanced_source_count_from_raw_moments_sub16799
    M H Label N n dmin dmax τ logCost heightCost momentCost binWidth εm hdmin hdmax hτ hl hh hb
    counts
  obtain ⟨KH, hKH, hhigh⟩ := high_source_count_from_raw_moments_sub16799
    M H Label N n dmin dmax τ logCost heightCost momentCost binWidth εm hdmin hdmax hτ hl hh hb
    counts
  refine ⟨max KB KH, lt_of_lt_of_le hKB (le_max_left _ _), ?_⟩
  filter_upwards [hbalanced, hhigh, eventually_ge_atTop (1 : ℝ)] with Z hb' hh' _hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2 * a - 1 ≤ 5 / 6
  · simp only [if_pos hδ] at hmom
    have hc := hb' d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponentSub16799, if_pos hδ]
    exact hc.trans (by gcongr; exact le_max_left _ _)
  · simp only [if_neg hδ] at hmom
    have hc := hh' d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponentSub16799, if_neg hδ]
    exact hc.trans (by gcongr; exact le_max_right _ _)

section NonfloorClass
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Fixed sub-`16799/19200` count parameters give the upgraded nonfloor amplitude-class estimate. -/
theorem actual_nonfloor_class_from_raw_moments_sub16799
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * τ < dmin * cost) (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hWB : ∀ j t, ‖W j t‖ ≤ A) (hellsum : ∑ j, ell j = 1 / 6)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (_hεm : 0 < εm) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8) (hν : 0 < ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (counts : CountParametersSub16799 M H εm) :
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ (v a C0 : ℝ), 0 ≤ v → 51 / 100 < a → a ≤ 1 → 0 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal :=
        fun j => pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀ t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
      let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
      SourceMomentsAtSub16799 M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
        (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
        (C0 * Z ^ momentCost) (Z ^ heightCost) εm →
      let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
        (fun j => ell j / d) (fun _ => z) (Z ^ d)
      ∀ bin : BinLabel (Finset.univ : Finset (Fin N)) ((2 * a - 1) / 2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) mesh hmesh
        (fun j => ell j / d) Q bin
      let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2 * a - 1) / 2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (logCost + heightCost + momentCost +
            d * adaptiveRowExponentSub16799 (2 * a - 1) q Δ ε εm R ν +
            v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss - 2 / 75 + q / 6 + mesh / 6) := by
  have hdmax0 : 0 < dmax := hdmin.trans_le hdRange
  obtain ⟨K, hK, hcount⟩ :=
    adaptive_source_count_from_raw_moments_sub16799 M H
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh εm
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C, hC, hphysical⟩ :=
    actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh
      (1 / 100) margin loss he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost
      hmesh (by norm_num) hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello
      hellhi W hWs hW hWB hellsum
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches_sub16799 M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η, hcount, hbatches, eventually_gt_atTop (1 : ℝ)] with Z hphysical
    hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
  let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
    (fun j => ell j / d) (fun _ => z) (Z ^ d)
  let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) mesh hmesh
    (fun j => ell j / d) Q bin
  let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) (2 * Z ^ v + 1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1, (hrows u hu).2.1, by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0 < ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW', hUpper, hExternal, hMesh, hBin, hFam, hMean⟩ :=
    hbatch d hd hd' (2 * Z ^ v + 1) rows hrowne hband (fun u hu => (hrows u hu).2.2.1)
      (fun u hu => (hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi hellsum W (fun _ => b) (fun _ => z) bin hne
  have hBsub : B.rows ⊆ rows := hBr ▸ hsub
  have hBfam : ∀ u ∈ B.rows, ∀ j,
      B.family u j = sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j :=
    fun u hu j => hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots]; simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr, hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z ^ d) (2 * a - 1) mesh hmesh
    (fun j => ell j / d) Q bin (by linarith) (fun j _ => div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum Finset.univ ell d hellsum]; positivity) hne
  refine ⟨hqb.1, hqb.2, ?_⟩
  have hp := hphysical d hd hd' v a q (K * C0 * Z ^ (logCost + heightCost + momentCost))
    (adaptiveRowExponentSub16799 (2 * a - 1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu => hrows u (hsub hu)) (fun u hu => hnorm u (hsub hu)) hcard i hi
    (fun u hu => hnext u (hsub hu)) t ht
    (fun u hu => source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost + heightCost + momentCost +
      d * adaptiveRowExponentSub16799 (2 * a - 1) q Δ ε εm R ν +
      v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss - 2 / 75 + q / 6 + mesh / 6 =
      (logCost + heightCost + momentCost) + (d * adaptiveRowExponentSub16799 (2 * a - 1) q Δ ε εm R ν +
      v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss - 2 / 75 + q / 6 + mesh / 6) by ring,
    Real.rpow_add hZp (logCost + heightCost + momentCost)]
  ring

end NonfloorClass
end ProbeFinalAssembly

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
