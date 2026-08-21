import GaloisForLFunctions.HTGeometry.PoincareHopf.MollifierIndependence
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The Brouwer degree

For a `C²` map `f` on `ℝⁿ`, a bounded open set `Ω`, and a point `y` not in the image of the
boundary of `Ω`, the degree of `f` on `Ω` at `y` is

  `deg (f, Ω, y) = ∫_Ω φ (f x - y) · det (Df x) dx`

for any smooth weight `φ` of total mass one supported in a ball small enough that `‖f - y‖` exceeds
twice its radius on `∂Ω`.  Independence of the weight is the mollifier independence theorem, so the
definition may fix any admissible radius; the workhorse statement below says the degree agrees with
the integral against every admissible weight.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {y : Fin n → ℝ} {ρ : ℝ}

/-- A canonical smooth weight of total mass one supported in the ball of radius `ρ`. -/
noncomputable def bumpWeight (ρ : ℝ) : (Fin n → ℝ) → ℝ :=
  if h : 0 < ρ then
    (⟨ρ / 2, ρ, half_pos h, by linarith⟩ : ContDiffBump (0 : Fin n → ℝ)).normed volume
  else 0

theorem bumpWeight_contDiff (hρ : 0 < ρ) : ContDiff ℝ 1 (bumpWeight (n := n) ρ) := by
  rw [bumpWeight, dif_pos hρ]
  exact ContDiffBump.contDiff_normed (n := 1) _

theorem bumpWeight_eq_zero (hρ : 0 < ρ) (w : Fin n → ℝ) (hw : ρ ≤ ‖w‖) :
    bumpWeight ρ w = 0 := by
  rw [bumpWeight, dif_pos hρ]
  have hsupp := ContDiffBump.support_normed_eq
    (⟨ρ / 2, ρ, half_pos hρ, by linarith⟩ : ContDiffBump (0 : Fin n → ℝ)) (μ := volume)
  by_contra hne
  have hmem : w ∈ Function.support
      ((⟨ρ / 2, ρ, half_pos hρ, by linarith⟩ : ContDiffBump (0 : Fin n → ℝ)).normed volume) := hne
  rw [hsupp, Metric.mem_ball, dist_zero_right] at hmem
  exact absurd hmem (not_lt.mpr hw)

theorem bumpWeight_integral (hρ : 0 < ρ) : ∫ w, bumpWeight (n := n) ρ w = 1 := by
  rw [bumpWeight, dif_pos hρ]
  exact ContDiffBump.integral_normed _

/-- `ρ` separates `y` from the image of the boundary of `Ω`, with room for a convolution. -/
def AdmissibleRadius (f : (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)) (y : Fin n → ℝ)
    (ρ : ℝ) : Prop := 0 < ρ ∧ ∀ x ∈ frontier Ω, ρ + ρ < ‖f x - y‖

open scoped Classical in
/-- **The Brouwer degree** of `f` on `Ω` at `y`. -/
noncomputable def degree (f : (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (y : Fin n → ℝ) : ℝ :=
  if h : ∃ ρ, AdmissibleRadius f Ω y ρ then
    degIntegral (fun x => f x - y) Ω (bumpWeight (Classical.choose h))
  else 0

theorem admissibleRadius_max (h₁ : AdmissibleRadius f Ω y ρ) {ρ' : ℝ}
    (h₂ : AdmissibleRadius f Ω y ρ') : AdmissibleRadius f Ω y (max ρ ρ') := by
  refine ⟨lt_of_lt_of_le h₁.1 (le_max_left _ _), fun x hx => ?_⟩
  rcases max_cases ρ ρ' with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · exact h₁.2 x hx
  · exact h₂.2 x hx

/-- A point off the image of the boundary of a bounded set admits a separating radius. -/
theorem exists_admissibleRadius (hf : Continuous f) (hΩb : Bornology.IsBounded Ω)
    (hy : y ∉ f '' frontier Ω) : ∃ ρ, AdmissibleRadius f Ω y ρ := by
  rcases eq_empty_or_nonempty (frontier Ω) with hemp | hne
  · exact ⟨1, one_pos, fun x hx => absurd hx (by rw [hemp]; exact notMem_empty x)⟩
  · have hcomp : IsCompact (frontier Ω) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_frontier
        (hΩb.closure.subset (frontier_subset_closure))
    have hcont : ContinuousOn (fun x => ‖f x - y‖) (frontier Ω) :=
      ((hf.sub continuous_const).norm).continuousOn
    obtain ⟨x₀, hx₀, hmin⟩ := hcomp.exists_isMinOn hne hcont
    have hpos : 0 < ‖f x₀ - y‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro hcon
      exact hy ⟨x₀, hx₀, hcon⟩
    refine ⟨‖f x₀ - y‖ / 3, by linarith, fun x hx => ?_⟩
    have hle : ‖f x₀ - y‖ ≤ ‖f x - y‖ := hmin hx
    linarith

/-- **The degree is the integral against any admissible weight.** -/
theorem degree_eq_degIntegral
    (hf : ContDiff ℝ 2 f) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {φ : (Fin n → ℝ) → ℝ} (hρ : AdmissibleRadius f Ω y ρ)
    (hφ : ContDiff ℝ 1 φ) (hφsupp : ∀ w : Fin n → ℝ, ρ ≤ ‖w‖ → φ w = 0)
    (hφmass : ∫ w, φ w = 1) :
    degree f Ω y = degIntegral (fun x => f x - y) Ω φ := by
  have hex : ∃ ρ, AdmissibleRadius f Ω y ρ := ⟨ρ, hρ⟩
  have hchoose : AdmissibleRadius f Ω y (Classical.choose hex) := Classical.choose_spec hex
  set ρ₀ := Classical.choose hex with hρ₀
  set r := max ρ₀ ρ with hr
  have hadm : AdmissibleRadius f Ω y r := admissibleRadius_max hchoose hρ
  have hu : ContDiff ℝ 2 (fun x => f x - y) := hf.sub contDiff_const
  have hfront : ∀ x ∈ frontier Ω, r + r < ‖(fun x => f x - y) x‖ := hadm.2
  have hbsupp : ∀ w : Fin n → ℝ, r ≤ ‖w‖ → bumpWeight ρ₀ w = 0 := fun w hw =>
    bumpWeight_eq_zero hchoose.1 w (le_trans (le_max_left _ _) hw)
  have hφsupp' : ∀ w : Fin n → ℝ, r ≤ ‖w‖ → φ w = 0 := fun w hw =>
    hφsupp w (le_trans (le_max_right _ _) hw)
  rw [degree, dif_pos hex, ← hρ₀]
  exact degIntegral_eq_of_mass_one hu (bumpWeight_contDiff hchoose.1) hφ hbsupp hφsupp'
    (bumpWeight_integral hchoose.1) hφmass hΩ hΩb hfront

end GaloisForLFunctions.HTGeometry.PoincareHopf
