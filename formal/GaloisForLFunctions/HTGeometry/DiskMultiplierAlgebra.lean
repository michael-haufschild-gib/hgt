import GaloisForLFunctions.HTGeometry.DiskMultiplierLineBoundary

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Constant bounded analytic disk multiplier. -/
def DiskMultiplier.const (c : ℂ) : DiskMultiplier where
  fn := fun _ => c
  diff := differentiableOn_const c
  bd := ‖c‖
  bd_nonneg := norm_nonneg c
  bd_le := fun _ _ => le_rfl

/-- Sum in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.add (φ ψ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => φ.fn z + ψ.fn z
  diff := φ.diff.add ψ.diff
  bd := φ.bd + ψ.bd
  bd_nonneg := add_nonneg φ.bd_nonneg ψ.bd_nonneg
  bd_le := fun z hz => (norm_add_le _ _).trans (add_le_add (φ.bd_le z hz) (ψ.bd_le z hz))

/-- Additive inverse in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.neg (φ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => -φ.fn z
  diff := φ.diff.neg
  bd := φ.bd
  bd_nonneg := φ.bd_nonneg
  bd_le := fun z hz => by simpa using φ.bd_le z hz

/-- Difference in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.sub (φ ψ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => φ.fn z - ψ.fn z
  diff := φ.diff.sub ψ.diff
  bd := φ.bd + ψ.bd
  bd_nonneg := add_nonneg φ.bd_nonneg ψ.bd_nonneg
  bd_le := fun z hz => (norm_sub_le _ _).trans (add_le_add (φ.bd_le z hz) (ψ.bd_le z hz))

/-- Scalar multiple in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.scale (c : ℂ) (φ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => c * φ.fn z
  diff := (differentiableOn_const c).mul φ.diff
  bd := ‖c‖ * φ.bd
  bd_nonneg := mul_nonneg (norm_nonneg c) φ.bd_nonneg
  bd_le := fun z hz => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (φ.bd_le z hz) (norm_nonneg c)

/-- Reciprocal multiplier when the analytic function has a uniform positive lower bound. -/
def DiskMultiplier.invOfLowerBound (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖) : DiskMultiplier where
  fn := fun z => (φ.fn z)⁻¹
  diff := φ.diff.fun_inv fun z hz => norm_pos_iff.mp (hδ.trans_le (hlow z hz))
  bd := δ⁻¹
  bd_nonneg := (inv_pos.mpr hδ).le
  bd_le := fun z hz => by
    rw [norm_inv]
    exact (inv_le_inv₀ hδ (norm_pos_iff.mpr
      (norm_pos_iff.mp (hδ.trans_le (hlow z hz))))).2 (hlow z hz)

@[simp] theorem DiskMultiplier.const_fn (c : ℂ) (z : ℂ) :
    (DiskMultiplier.const c).fn z = c := rfl

@[simp] theorem DiskMultiplier.add_fn (φ ψ : DiskMultiplier) (z : ℂ) :
    (φ.add ψ).fn z = φ.fn z + ψ.fn z := rfl

@[simp] theorem DiskMultiplier.neg_fn (φ : DiskMultiplier) (z : ℂ) :
    φ.neg.fn z = -φ.fn z := rfl

@[simp] theorem DiskMultiplier.sub_fn (φ ψ : DiskMultiplier) (z : ℂ) :
    (φ.sub ψ).fn z = φ.fn z - ψ.fn z := rfl

@[simp] theorem DiskMultiplier.scale_fn (c : ℂ) (φ : DiskMultiplier) (z : ℂ) :
    (φ.scale c).fn z = c * φ.fn z := rfl

@[simp] theorem DiskMultiplier.invOfLowerBound_fn
    (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖) (z : ℂ) :
    (φ.invOfLowerBound δ hδ hlow).fn z = (φ.fn z)⁻¹ := rfl

theorem DiskMultiplier.mul_invOfLowerBound_fn
    (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (φ.mul (φ.invOfLowerBound δ hδ hlow)).fn z = 1 := by
  change φ.fn z * (φ.fn z)⁻¹ = 1
  exact mul_inv_cancel₀ (norm_pos_iff.mp (hδ.trans_le (hlow z hz)))

end

end GaloisForLFunctions.HTGeometry
