import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothLogarithmicCellRefinement
import GaloisForLFunctions.HTGeometry.BoundedVariationPrimitive
import GaloisForLFunctions.RHTower.LogFloorExpBridge

/-!
# Complete logarithmic step profiles

Sampling at the left endpoints of logarithmic cells is composition with a monotone
map. Thus sampling does not increase total variation, although the samples have
jumps. On cells above index `N`, the uniform sampling error is at most `Lip(f)/N`.
-/

noncomputable section
open MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry HTGeometry

/-- The index of the complete logarithmic cell, clamped below the initial index. -/
def logCellIndex (R : ℝ) (N : ℕ) (u : ℝ) : ℕ :=
  max ⌊Real.exp (u + Real.log N + R)⌋₊ N

/-- The left endpoint of the cell containing `u`, clamped at `-R`. -/
def logCellPoint (R : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  Real.log (logCellIndex R N u) - Real.log N - R

/-- A literal complete-cell step profile, including its jump discontinuities. -/
def logStep (f : ℝ → ℝ) (R : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  f (logCellPoint R N u)

theorem logCellIndex_ge (R : ℝ) (N : ℕ) (u : ℝ) : N ≤ logCellIndex R N u :=
  le_max_right _ _

theorem monotone_logCellIndex (R : ℝ) (N : ℕ) : Monotone (logCellIndex R N) := by
  intro u v huv
  exact max_le_max (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))) le_rfl

theorem monotone_logCellPoint (R : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Monotone (logCellPoint R N) := by
  intro u v huv
  have hpos : (0 : ℝ) < logCellIndex R N u := by
    exact_mod_cast (hN.trans (logCellIndex_ge R N u))
  exact sub_le_sub_right (sub_le_sub_right
    (Real.log_le_log hpos (by exact_mod_cast monotone_logCellIndex R N huv)) _) _

theorem logCellPoint_endpoint (R : ℝ) {N a : ℕ} (hN : 1 ≤ N) (ha : N ≤ a) :
    logCellPoint R N (logEndpoint R N a) = logEndpoint R N a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast hN.trans ha
  have he : logEndpoint R N a + Real.log N + R = Real.log a := by
    unfold logEndpoint
    ring
  unfold logCellPoint logCellIndex
  rw [he, Real.exp_log ha0, Nat.floor_natCast, max_eq_left ha]
  rfl

theorem logCellPoint_below (R : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : u ≤ -R) :
    logCellPoint R N u = -R := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he : Real.exp (u + Real.log N + R) ≤ (N : ℝ) := by
    calc _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hN0
  have hi : ⌊Real.exp (u + Real.log N + R)⌋₊ ≤ N := by
    simpa only [Nat.floor_natCast] using Nat.floor_le_floor he
  simp only [logCellPoint, logCellIndex, max_eq_right hi, sub_self, zero_sub]

/-- Cell width, rather than differentiability of the step profile, pays sampling error. -/
theorem logCellPoint_bounds (R : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : -R ≤ u) :
    logCellPoint R N u ≤ u ∧ u - logCellPoint R N u ≤ 1 / (N : ℝ) := by
  have hn : N ≤ ⌊Real.exp (u + Real.log N + R)⌋₊ :=
    (_root_.RHTower.log_le_iff_le_floor hN _).mp (by linarith)
  let a := ⌊Real.exp (u + Real.log N + R)⌋₊
  have ha : 1 ≤ a := hN.trans hn
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hlo := Real.log_le_log ha0 (Nat.floor_le (Real.exp_pos _).le)
  rw [Real.log_exp] at hlo
  have hhi := Real.log_lt_log (Real.exp_pos (u + Real.log N + R))
    (Nat.lt_floor_add_one (Real.exp (u + Real.log N + R)))
  rw [Real.log_exp] at hhi
  have hw := (logCellWidth_le_inv ha).trans
    (one_div_le_one_div_of_le (by exact_mod_cast hN : (0 : ℝ) < N)
      (by exact_mod_cast hn))
  simp only [logCellPoint, logCellIndex, max_eq_left hn]
  change Real.log (a : ℝ) - Real.log N - R ≤ u ∧
    u - (Real.log (a : ℝ) - Real.log N - R) ≤ 1 / (N : ℝ)
  constructor
  · linarith only [hlo]
  · dsimp only [logCellWidth] at hw
    linarith only [hhi, hw]

theorem abs_logStep_sub_le {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (R : ℝ) {N : ℕ} (hN : 1 ≤ N) (hs : ∀ u, u ≤ -R → f u = 0) (u : ℝ) :
    |logStep f R N u - f u| ≤ (K : ℝ) / N := by
  by_cases hu : u ≤ -R
  · rw [logStep, logCellPoint_below R hN hu, hs _ le_rfl, hs u hu, sub_self, abs_zero]
    positivity
  · have hb := logCellPoint_bounds R hN (le_of_not_ge hu)
    have hl := hf.norm_sub_le (logCellPoint R N u) u
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hb.1)] at hl
    calc _ ≤ (K : ℝ) * (u - logCellPoint R N u) := by
           simpa only [logStep, neg_sub] using hl
      _ ≤ (K : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hb.2 K.coe_nonneg
      _ = _ := by ring

/-- A monotone cell map cannot create variation. -/
theorem eVariationOn_logStep_le (f : ℝ → ℝ) (R : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    eVariationOn (logStep f R N) univ ≤ eVariationOn f univ := by
  exact eVariationOn.comp_le_of_monotoneOn f (logCellPoint R N)
    ((monotone_logCellPoint R hN).monotoneOn univ) (fun _ _ => mem_univ _)

theorem boundedVariationOn_logStep {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (R : ℝ) {N : ℕ} (hN : 1 ≤ N) : BoundedVariationOn (logStep f R N) univ :=
  ne_top_of_le_ne_top hf (eVariationOn_logStep_le f R hN)

/-- The error may jump, but its variation stays bounded independently of resolution. -/
theorem variation_logStep_sub_le {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (R : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (eVariationOn (fun u => logStep f R N u - f u) univ).toReal ≤
      2 * (eVariationOn f univ).toReal := by
  have hstep := boundedVariationOn_logStep hf R hN
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eVariationOn_sub_le_of_finite hstep hf)
  rw [ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] at h
  have hs := ENNReal.toReal_mono hf (eVariationOn_logStep_le f R hN)
  linarith only [h, hs]

/-- Both exterior rays remain zero, with no enlarged support window. -/
theorem logStep_eq_zero_outside {f : ℝ → ℝ} (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0)
    {u : ℝ} (hu : u ≤ -R ∨ Real.log B - R ≤ u) : logStep f R N u = 0 := by
  rcases hu with hu | hu
  · rw [logStep, logCellPoint_below R hN hu]
    exact hs _ (Or.inl le_rfl)
  · have hNB : N ≤ N * B := by simpa using Nat.mul_le_mul_left N hB
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have he : logEndpoint R N (N * B) = Real.log B - R := by
      simp only [logEndpoint, Nat.cast_mul, Real.log_mul hN0.ne' hB0.ne']
      ring
    have hp := logCellPoint_endpoint R hN hNB
    rw [he] at hp
    have hm := monotone_logCellPoint R hN hu
    rw [hp] at hm
    exact hs _ (Or.inr hm)

/-- The literal cell profile agrees with its prescribed coefficient on every cell. -/
theorem logStep_eq_sample {f : ℝ → ℝ} (R : ℝ) {N a : ℕ}
    (hN : 1 ≤ N) (ha : N ≤ a) {u : ℝ}
    (hu : u ∈ Ico (logEndpoint R N a) (logEndpoint R N (a + 1))) :
    logStep f R N u = logSamples f R N a := by
  have ha1 := hN.trans ha
  have hlo : a ≤ ⌊Real.exp (u + Real.log N + R)⌋₊ :=
    (_root_.RHTower.log_le_iff_le_floor ha1 _).mp (by
      dsimp only [logEndpoint] at hu
      linarith only [hu.1])
  have hhi : ¬a + 1 ≤ ⌊Real.exp (u + Real.log N + R)⌋₊ := by
    intro hh
    have hh' := (_root_.RHTower.log_le_iff_le_floor (by omega : 1 ≤ a + 1) _).mpr hh
    dsimp only [logEndpoint] at hu
    linarith only [hu.2, hh']
  have he : ⌊Real.exp (u + Real.log N + R)⌋₊ = a := by omega
  simp only [logStep, logCellPoint, logCellIndex, he, max_eq_left ha, logSamples]

theorem hasCompactSupport_logStep {f : ℝ → ℝ} (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    HasCompactSupport (logStep f R N) := by
  apply HasCompactSupport.intro (K := Icc (-R) (Real.log B - R)) isCompact_Icc
  intro u hu
  apply logStep_eq_zero_outside R hN hB hs
  by_cases hlow : u ≤ -R
  · exact Or.inl hlow
  · exact Or.inr (le_of_not_gt (fun hhigh => hu ⟨(le_of_not_ge hlow), hhigh.le⟩))

theorem measurable_logStep {f : ℝ → ℝ} (hf : Measurable f) (R : ℝ)
    {N : ℕ} (hN : 1 ≤ N) : Measurable (logStep f R N) :=
  hf.comp (monotone_logCellPoint R hN).measurable

#print axioms abs_logStep_sub_le
#print axioms variation_logStep_sub_le
#print axioms logStep_eq_sample

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
