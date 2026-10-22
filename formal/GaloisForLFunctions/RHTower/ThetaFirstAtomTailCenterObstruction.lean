import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairOrientationAntisymmetry
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact first-atom scale moment and center obstruction

The squared first atom has normalized `exp(2x)` moment `75/(44*pi)`.
Its full-line center energy is therefore strictly negative. Consequently its
first-moment tail kernel fails global positive semidefiniteness.

This obstruction concerns the exact first atom, not the complete even theta
source. It does not assert a negative direction confined to a positive tail.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.FirstAtomTailAudit

def density (x : ℝ) : ℝ := (thetaCuspSourceTerm x 1)^2
def energy : ℝ := ∫ x, density x
def scaleEnergy : ℝ := ∫ x, Real.exp (2*x)*density x
def centerEnergy : ℝ := ∫ x, 2*x*density x

theorem density_integrable : Integrable density := by
  have h := integrable_exp_mul_thetaCuspSourceTerm_pair (σ := (1/2:ℝ))
    (by norm_num) (n := 1) (m := 1) (by norm_num) (by norm_num) 0
  change Integrable (fun x => (thetaCuspSourceTerm x 1)^2)
  simpa [pow_two] using h

theorem scale_integrable : Integrable (fun x => Real.exp (2*x)*density x) := by
  have h := integrable_exp_mul_thetaCuspSourceTerm_pair (σ := (3/2:ℝ))
    (by norm_num) (n := 1) (m := 1) (by norm_num) (by norm_num) 0
  norm_num [density, pow_two] at h ⊢
  exact h

theorem center_integrable : Integrable (fun x => 2*x*density x) := by
  have h := (integrable_center_mul_exp_mul_thetaCuspSourceTerm_pair (σ := (1/2:ℝ))
    (by norm_num) (n := 1) (m := 1) (by norm_num) (by norm_num) 0).const_mul 2
  simpa [density, pow_two, mul_assoc] using h

theorem energy_eq : energy =
    Real.Gamma (5/2)/(2*(2*Real.pi)^(1/2:ℝ))*(11/4) := by
  have h := integral_exp_mul_thetaCuspSourceTerm_pair (σ := (1/2:ℝ))
    (by norm_num) (n := 1) (m := 1) (by norm_num) (by norm_num) 0
  norm_num [thetaCuspWignerRadialQ, ← pow_two] at h
  exact h

theorem energy_pos : 0<energy := by
  rw [energy_eq]
  have h := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<5/2)
  positivity

/-- Exact normalized scale moment of the squared first atom. -/
theorem scaleEnergy_eq : scaleEnergy = (75/(44*Real.pi))*energy := by
  have h := integral_exp_mul_thetaCuspSourceTerm_pair (σ := (3/2:ℝ))
    (by norm_num) (n := 1) (m := 1) (by norm_num) (by norm_num) 0
  norm_num [thetaCuspWignerRadialQ, ← pow_two] at h
  change scaleEnergy = _ at h
  rw [h, energy_eq]
  have hg : Real.Gamma (7/2) = (5/2)*Real.Gamma (5/2) := by
    rw [show (7/2:ℝ)=5/2+1 by norm_num, Real.Gamma_add_one (by norm_num : (5/2:ℝ)≠0)]
  have hp : (2*Real.pi)^(3/2:ℝ) = (2*Real.pi)^(1/2:ℝ)*(2*Real.pi) := by
    rw [show (3/2:ℝ)=1/2+1 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  rw [hg, hp]
  field_simp
  ring

/-- The full-line center energy is bounded by the exact scale-moment defect. -/
theorem centerEnergy_upper : centerEnergy ≤ (75/(44*Real.pi)-1)*energy := by
  have h := integral_mono center_integrable (scale_integrable.sub density_integrable)
    (fun x => show 2*x*density x ≤ Real.exp (2*x)*density x-density x by
      have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2*x))
        (sq_nonneg (thetaCuspSourceTerm x 1))
      dsimp [density] at *
      nlinarith)
  dsimp only [Pi.sub_apply] at h
  rw [integral_sub scale_integrable density_integrable] at h
  change centerEnergy ≤ scaleEnergy-energy at h
  rw [scaleEnergy_eq] at h
  nlinarith

/-- The exact first atom has a strictly negative full-line first center moment. -/
theorem centerEnergy_neg : centerEnergy < 0 := by
  have hp : 75/(44*Real.pi)<1 := by
    apply (div_lt_one (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have hn : (75/(44*Real.pi)-1)*energy<0 :=
    mul_neg_of_neg_of_pos (by linarith) energy_pos
  exact lt_of_le_of_lt centerEnergy_upper hn

/-- Exact first-atom diagonal in tail coordinates. -/
def tailDiagonal (x : ℝ) : ℝ := ∫ t in Ioi x, 2*t*density t

/-- The bare-atom diagonal tends to its negative full-line center energy. -/
theorem tailDiagonal_limit : Tendsto tailDiagonal atBot (𝓝 centerEnergy) := by
  have hcov : AECover volume atBot (fun r : ℝ => Ioi r) := aecover_Ioi tendsto_id
  exact hcov.integral_tendsto_of_countably_generated center_integrable

theorem tailDiagonal_eventually_neg : ∀ᶠ x in atBot, tailDiagonal x<0 :=
  tailDiagonal_limit.eventually (gt_mem_nhds centerEnergy_neg)

theorem exists_tailDiagonal_neg : ∃ x : ℝ, tailDiagonal x<0 :=
  tailDiagonal_eventually_neg.exists

/-- The first-moment tail kernel formed from the exact first atom alone. -/
def kernel (x y : ℝ) : ℝ :=
  ∫ s in Ioi 0, (x+y+2*s)*thetaCuspSourceTerm (x+s) 1*thetaCuspSourceTerm (y+s) 1

private theorem integral_Ioi_shift (g : ℝ → ℝ) (a : ℝ) :
    (∫ u in Ioi a, g u) = ∫ v in Ioi (0:ℝ), g (a+v) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_add_right_eq_self (fun u => Set.indicator (Ioi a) g u) a]
  congr 1
  funext v
  by_cases hv : 0<v
  · rw [Set.indicator_of_mem (by simp only [mem_Ioi]; linarith : v+a ∈ Ioi a),
      Set.indicator_of_mem (mem_Ioi.mpr hv), add_comm]
  · rw [Set.indicator_of_notMem (by simp only [mem_Ioi]; intro h; exact hv (by linarith)),
      Set.indicator_of_notMem (by simpa using hv)]

theorem kernel_diag (x : ℝ) : kernel x x = tailDiagonal x := by
  unfold kernel tailDiagonal
  rw [integral_Ioi_shift (fun t : ℝ => 2*t*density t) x]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  unfold density
  ring

/-- Global positive semidefiniteness fails even for the exact first-atom kernel.
This theorem alone asserts no negative direction confined to a positive tail. -/
theorem not_global_posSemidef :
    ¬ ∀ (n : ℕ) (x : Fin n → ℝ), (Matrix.of (fun i j => kernel (x i) (x j))).PosSemidef := by
  intro h
  obtain ⟨r, hr⟩ := exists_tailDiagonal_neg
  have hd := (h 1 (fun _ => r)).diag_nonneg (i := 0)
  change 0 ≤ kernel r r at hd
  rw [kernel_diag] at hd
  linarith

end RHTower.FirstAtomTailAudit
