import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorWeightedIntegral
import GaloisForLFunctions.RHTower.MaassAxisUniqueContinuation

/-!
# Transport of the quarter equation through compact-parameter integration

The fixed integrable weight dominates every local derivative of the smooth family.
Consequently the actual quarter defect commutes with its integral.
-/

noncomputable section

open Complex Set Filter MeasureTheory
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

open MaassAxisContinuation

/-- Spatial directional derivative of a joint family. -/
def compactParameterDir (v : ℂ) (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  compactParameterPartial F p v

variable {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
  {γ : ℝ → ℂ} (hγ : Continuous γ) (hγK : ∀ t, γ t ∈ K)
  {w : ℝ → ℝ} (hw : Integrable w)

include hV in
private lemma partial_smooth {F : ℂ × ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (upper ×ˢ V)) :
    ContDiffOn ℝ ∞ (compactParameterPartial F) (upper ×ˢ V) :=
  (hF.fderiv_of_isOpen (isOpen_upper.prod hV) (m := ∞) (by simp)).clm_comp contDiffOn_const

include hV in
theorem contDiffOn_compactParameterDir {F : ℂ × ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (upper ×ˢ V)) (v : ℂ) :
    ContDiffOn ℝ ∞ (compactParameterDir v F) (upper ×ˢ V) :=
  (partial_smooth hV hF).clm_apply contDiffOn_const

include hV in
theorem compactParameterDir_eq_dirD {F : ℂ × ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (upper ×ˢ V)) {z c : ℂ}
    (hz : z ∈ upper) (hc : c ∈ V) (v : ℂ) :
    compactParameterDir v F (z, c) = dirD v (fun x => F (x, c)) z := by
  have hd : DifferentiableAt ℝ F (z, c) :=
    (hF.contDiffAt ((isOpen_upper.prod hV).mem_nhds ⟨hz, hc⟩)).differentiableAt (by simp)
  have hf : HasFDerivAt (fun x => F (x, c)) (compactParameterPartial F (z, c)) z :=
    hd.hasFDerivAt.comp z ((hasFDerivAt_id z).prodMk (hasFDerivAt_const c z))
  simp only [compactParameterDir, dirD, hf.fderiv]

include hV hK hKV hγ hγK hw in
/-- The actual directional derivative equals the integral of the joint partial. -/
theorem dirD_weighted_compact_parameter {F : ℂ × ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (upper ×ˢ V)) {z : ℂ} (hz : z ∈ upper) (v : ℂ) :
    dirD v (fun x => ∫ t : ℝ, w t • F (x, γ t)) z =
      ∫ t : ℝ, w t • compactParameterDir v F (z, γ t) := by
  have hd := hasFDerivAt_weighted_compact_parameter isOpen_upper hV hK hKV hγ hγK hw
    (hF.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)) hz
  have hi := weighted_parameter_integrable isOpen_upper hV hK hKV hγ hγK hw
    (partial_smooth hV hF).continuousOn hz
  unfold dirD
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  rfl

include hV hK hKV hγ hγK hw in
/-- No extra differentiability or domination assumption is needed at second order. -/
theorem dirD_dirD_weighted_compact_parameter {F : ℂ × ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (upper ×ˢ V)) {z : ℂ} (hz : z ∈ upper) (v u : ℂ) :
    dirD v (dirD u (fun x => ∫ t : ℝ, w t • F (x, γ t))) z =
      ∫ t : ℝ, w t • dirD v (dirD u (fun x => F (x, γ t))) z := by
  rw [dirD_congr (fun x hx =>
    dirD_weighted_compact_parameter hV hK hKV hγ hγK hw hF hx u) hz v]
  rw [dirD_weighted_compact_parameter hV hK hKV hγ hγK hw
    (contDiffOn_compactParameterDir hV hF u) hz v]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    congr 1
    rw [compactParameterDir_eq_dirD hV (contDiffOn_compactParameterDir hV hF u)
      hz (hKV (hγK t)) v]
    exact dirD_congr (fun x hx => compactParameterDir_eq_dirD hV hF hx (hKV (hγK t)) u) hz v

include hV hK hKV hγ hγK hw in
/-- The quarter differential operator commutes with weighted compact-parameter integration. -/
theorem quarterDefect_weighted_compact_parameter {F : ℂ × ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (upper ×ˢ V)) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (fun x => ∫ t : ℝ, w t • F (x, γ t)) z =
      ∫ t : ℝ, w t • quarterDefect (fun x => F (x, γ t)) z := by
  have hsecond (v : ℂ) : Integrable (fun t : ℝ =>
      w t • dirD v (dirD v (fun x => F (x, γ t))) z) := by
    have hh := weighted_parameter_integrable isOpen_upper hV hK hKV hγ hγK hw
      (contDiffOn_compactParameterDir hV (contDiffOn_compactParameterDir hV hF v) v).continuousOn hz
    apply hh.congr
    exact Eventually.of_forall fun t => by
      dsimp only
      congr 1
      rw [compactParameterDir_eq_dirD hV (contDiffOn_compactParameterDir hV hF v)
        hz (hKV (hγK t)) v]
      exact dirD_congr (fun x hx => compactParameterDir_eq_dirD hV hF hx (hKV (hγK t)) v) hz v
  have hzero := weighted_parameter_integrable isOpen_upper hV hK hKV hγ hγK hw hF.continuousOn hz
  have hsum : Integrable (fun t : ℝ => w t • dirD 1 (dirD 1 (fun x => F (x, γ t))) z +
      w t • dirD I (dirD I (fun x => F (x, γ t))) z) := (hsecond 1).add (hsecond I)
  have hweight : Integrable (fun t : ℝ => quarterWeight z • w t • F (z, γ t)) :=
    Integrable.smul (quarterWeight z) hzero
  unfold quarterDefect
  rw [dirD_dirD_weighted_compact_parameter hV hK hKV hγ hγK hw hF hz,
    dirD_dirD_weighted_compact_parameter hV hK hKV hγ hγK hw hF hz,
    ← integral_smul]
  rw [← integral_add (hsecond 1) (hsecond I), ← integral_add hsum hweight]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    simp only [smul_add]
    congr 1
    exact smul_comm (quarterWeight z) (w t) (F (z, γ t))

end RHTower.WeilHigherDenominator
