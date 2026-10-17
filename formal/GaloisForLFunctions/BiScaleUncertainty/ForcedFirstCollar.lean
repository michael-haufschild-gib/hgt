import GaloisForLFunctions.BiScaleUncertainty.SignedCosetProductCoupling
import GaloisForLFunctions.BiScaleUncertainty.CollarEndpointTailMass

/-!
# Forced two-sided allocation at the first logarithmic node

Below the left edge of the node-three collar, exact mass conservation forces
the entire physical share onto node two. A fixed positive interval of offsets
places both branches in this region, uniformly in every cutoff at least three.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def firstCollarIsolationRadius : ℝ :=
  Real.log 3 - Real.log 2 - logarithmicCollarRadius

def firstCollarGapLeft : ℝ := firstCollarIsolationRadius / 3
def firstCollarGapRight : ℝ := 2 * firstCollarIsolationRadius / 3

theorem firstCollarIsolationRadius_pos : 0 < firstCollarIsolationRadius := by
  have h : Real.log ((2 : ℝ) ^ 3) < Real.log ((3 : ℝ) ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  unfold firstCollarIsolationRadius logarithmicCollarRadius
  linarith

theorem firstCollarIsolationRadius_lt_radius :
    firstCollarIsolationRadius < logarithmicCollarRadius := by
  have h : Real.log (3 : ℝ) < Real.log ((2 : ℝ) ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  norm_num at h
  unfold firstCollarIsolationRadius logarithmicCollarRadius
  linarith

theorem firstCollarGap_geometry :
    0 < firstCollarGapLeft ∧ firstCollarGapLeft < firstCollarGapRight ∧
      firstCollarGapRight < firstCollarIsolationRadius ∧
        firstCollarGapRight < logarithmicCollarRadius := by
  have hp := firstCollarIsolationRadius_pos
  have hu := firstCollarIsolationRadius_lt_radius
  unfold firstCollarGapLeft firstCollarGapRight
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem firstCollarGapInterval_subset :
    Ioc firstCollarGapLeft firstCollarGapRight ⊆ Ioo 0 logarithmicCollarRadius := by
  intro y hy
  exact ⟨firstCollarGap_geometry.1.trans hy.1,
    hy.2.trans_lt firstCollarGap_geometry.2.2.2⟩

theorem firstCollarNode_locations (σ : Bool) {y : ℝ}
    (hy : y ∈ Ioc firstCollarGapLeft firstCollarGapRight) :
    logarithmicCollarRadius < logarithmicCollarNode 0 + collarSignedOffset σ y ∧
      logarithmicCollarNode 0 + collarSignedOffset σ y <
        Real.log 3 - logarithmicCollarRadius := by
  have hy0 := (firstCollarGapInterval_subset hy).1
  have hyδ := (firstCollarGapInterval_subset hy).2
  have hye := hy.2.trans_lt firstCollarGap_geometry.2.2.1
  have he := firstCollarIsolationRadius_pos
  have hnode : logarithmicCollarNode 0 = Real.log 2 := by
    norm_num [logarithmicCollarNode]
  rw [hnode]
  unfold firstCollarIsolationRadius logarithmicCollarRadius at *
  cases σ <;> simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith

namespace PhysicalCollarPartition
variable {n : ℕ}

/-- All physical mass below the next collar's left edge belongs to node two. -/
theorem share_first_eq_one (ρ : PhysicalCollarPartition n) (hn : 1 ≤ n) {x : ℝ}
    (hx : logarithmicCollarRadius < x) (hu : x < Real.log 3 - logarithmicCollarRadius) :
    ρ.share 0 x = 1 := by
  have hcut : Real.log 3 ≤ logarithmicCollarEndpoint n := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 3 ≤ n + 2 by omega)
  have hmem : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) := by
    exact ⟨hx, by linarith [logarithmicCollarRadius_pos]⟩
  have hp := ρ.partition x
  rw [indicator_of_mem hmem] at hp
  have hs : (∑ k ∈ Finset.range (n + 1), ρ.share k x) = ρ.share 0 x := by
    apply Finset.sum_eq_single 0
    · intro k _ hk
      apply ρ.supported
      intro h
      have hnode : Real.log 3 ≤ logarithmicCollarNode k := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast (show 3 ≤ k + 2 by omega)
      have hleft : logarithmicCollarNode k - logarithmicCollarRadius < x := h.1.1
      linarith
    · intro h
      exact False.elim (h (by simp))
  rw [hs] at hp
  exact hp

theorem weight_first_eq_archWeight (ρ : PhysicalCollarPartition n) (hn : 1 ≤ n)
    (σ : Bool) {y : ℝ} (hy : y ∈ Ioc firstCollarGapLeft firstCollarGapRight) :
    ρ.weight σ 0 y = archLevySinhWeight (logarithmicCollarNode 0 + collarSignedOffset σ y) := by
  have hx := firstCollarNode_locations σ hy
  rw [weight, density, ρ.share_first_eq_one hn hx.1 hx.2, one_mul]

theorem one_le_weight_first (ρ : PhysicalCollarPartition n) (hn : 1 ≤ n)
    (σ : Bool) {y : ℝ} (hy : y ∈ Ioc firstCollarGapLeft firstCollarGapRight) :
    1 ≤ ρ.weight σ 0 y := by
  let x := logarithmicCollarNode 0 + collarSignedOffset σ y
  have hx := firstCollarNode_locations σ hy
  have hlog : Real.log 3 < 2 * Real.log 2 := by
    have h := firstCollarIsolationRadius_lt_radius
    unfold firstCollarIsolationRadius logarithmicCollarRadius at h
    linarith
  have hupper : x ≤ 2 * Real.log 2 := by
    have hu : x < Real.log 3 - logarithmicCollarRadius := hx.2
    linarith [logarithmicCollarRadius_pos]
  have he : (1 / 2 : ℝ) ≤ Real.exp (-x / 2) := by
    calc
      _ = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hw := (archWeight_half_exponential_remainder hx.1.le).1
  rw [ρ.weight_first_eq_archWeight hn σ hy]
  change 1 ≤ archLevySinhWeight x
  change 0 ≤ archLevySinhWeight x - 2 * Real.exp (-x / 2) at hw
  linarith

/-- Each indexed weight is bounded by its whole-sign aggregate norm. -/
theorem weight_le_signBlockNorm (ρ : PhysicalCollarPartition n) (σ : Bool) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (y : ℝ) :
    ρ.weight σ k y ≤ ρ.signBlockNorm σ y := by
  have hnode : k ∈ logarithmicCosetNodes n (logNodeOddPart k) :=
    Finset.mem_filter.mpr ⟨hk, rfl⟩
  have hcoset : logNodeOddPart k ∈ logarithmicOddCosets n :=
    Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have hl : ρ.weight σ k y ≤
      Real.sqrt (∑ j ∈ logarithmicCosetNodes n (logNodeOddPart k), ρ.weight σ j y ^ 2) :=
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg (ρ.weight σ j y)) hnode)
  refine hl.trans ?_
  exact Finset.single_le_sum (fun p _ => Real.sqrt_nonneg
    (∑ j ∈ logarithmicCosetNodes n p, ρ.weight σ j y ^ 2)) hcoset

theorem one_le_signBlockNorm_on_first_interval (ρ : PhysicalCollarPartition n)
    (hn : 1 ≤ n) (σ : Bool) {y : ℝ}
    (hy : y ∈ Ioc firstCollarGapLeft firstCollarGapRight) :
    1 ≤ ρ.signBlockNorm σ y :=
  (ρ.one_le_weight_first hn σ hy).trans (ρ.weight_le_signBlockNorm σ 0 (by simp) y)

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
