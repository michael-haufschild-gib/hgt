import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightTaylorRemainder
import GaloisForLFunctions.BiScaleUncertainty.NyquistResidualMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Logarithmic cell geometry and unconditional Taylor-producer bounds -/

open Set Filter Topology

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeightCellWidth (k : ℕ) : ℝ :=
  nyquistResidualNode (k + 1) - nyquistResidualNode k

def nyquistWeightCellResidual (β : ℝ) (m k : ℕ) (x : ℝ) : ℝ :=
  nyquistWeightTaylorResidual β m (nyquistResidualNode k) x

def nyquistWeightCellMass (β : ℝ) (m k : ℕ) : ℝ :=
  nyquistWeightTaylorMass β m (nyquistResidualNode k) (nyquistResidualNode (k + 1))

theorem nyquistResidualNode_nonneg (k : ℕ) : 0 ≤ nyquistResidualNode k := by
  rw [← nyquistResidualNode_zero]
  exact strictMono_nyquistResidualNode.monotone (Nat.zero_le k)

theorem nyquistWeightCellWidth_eq (k : ℕ) :
    nyquistWeightCellWidth k = ChebyshevGauge.cellLength (k + 1) := by
  simp only [nyquistWeightCellWidth, nyquistResidualNode, ChebyshevGauge.cellLength,
    Nat.cast_add, Nat.cast_one]

theorem nyquistWeightCellWidth_pos (k : ℕ) : 0 < nyquistWeightCellWidth k :=
  sub_pos.mpr (strictMono_nyquistResidualNode (by omega : k < k + 1))

theorem nyquistWeightCellWidth_bounds (k : ℕ) :
    1 / ((k + 2 : ℕ) : ℝ) ≤ nyquistWeightCellWidth k ∧
      nyquistWeightCellWidth k ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
  rw [nyquistWeightCellWidth_eq]
  constructor
  · convert ChebyshevGauge.inv_succ_le_cellLength (by omega : 1 ≤ k + 1) using 1
    push_cast
    ring
  · exact ChebyshevGauge.cellLength_le (by omega : 1 ≤ k + 1)

theorem nyquistWeightCellWidth_scaled_bounds (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * nyquistWeightCellWidth k ∧
      ((k + 1 : ℕ) : ℝ) * nyquistWeightCellWidth k ≤ 1 := by
  have hl := mul_le_mul_of_nonneg_left (nyquistWeightCellWidth_bounds k).1
    (Nat.cast_nonneg (α := ℝ) (k + 1))
  have hu := mul_le_mul_of_nonneg_left (nyquistWeightCellWidth_bounds k).2
    (Nat.cast_nonneg (α := ℝ) (k + 1))
  constructor
  · simpa only [mul_one_div] using hl
  · simpa only [mul_one_div, div_self (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0)] using hu

theorem tendsto_nyquistWeightCellWidth_scaled :
    Tendsto (fun k => ((k + 1 : ℕ) : ℝ) * nyquistWeightCellWidth k) atTop (𝓝 1) := by
  have hl : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    convert (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1) using 1
    norm_num [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun k => (nyquistWeightCellWidth_scaled_bounds k).1)
    (fun k => (nyquistWeightCellWidth_scaled_bounds k).2)

theorem continuous_nyquistWeightCellResidual (β : ℝ) (m k : ℕ) :
    Continuous (nyquistWeightCellResidual β m k) :=
  continuous_nyquistWeightTaylorResidual β m (nyquistResidualNode k)

theorem nyquistWeightCellResidual_nonneg {β : ℝ} (hβ : 0 ≤ β) (m k : ℕ)
    {x : ℝ} (hx : nyquistResidualNode k ≤ x) : 0 ≤ nyquistWeightCellResidual β m k x :=
  nyquistWeightTaylorResidual_nonneg hβ (nyquistResidualNode_nonneg k) m hx

theorem nyquistWeightCellMass_nonneg {β : ℝ} (hβ : 0 ≤ β) (m k : ℕ) :
    0 ≤ nyquistWeightCellMass β m k :=
  nyquistWeightTaylorMass_nonneg hβ (nyquistResidualNode_nonneg k)
    (strictMono_nyquistResidualNode.monotone (by omega : k ≤ k + 1)) m

theorem nyquistWeightCellMass_bounds {β : ℝ} (hβ : 0 ≤ β) (m k : ℕ) :
    nyquistWeightJet β (m + 1) (nyquistResidualNode k) *
        nyquistWeightCellWidth k ^ (m + 2) / ((m + 2).factorial : ℝ) ≤
      nyquistWeightCellMass β m k ∧
    nyquistWeightCellMass β m k ≤
      nyquistWeightJet β (m + 1) (nyquistResidualNode (k + 1)) *
        nyquistWeightCellWidth k ^ (m + 2) / ((m + 2).factorial : ℝ) :=
  nyquistWeightTaylorMass_bounds hβ (nyquistResidualNode_nonneg k)
    (strictMono_nyquistResidualNode.monotone (by omega : k ≤ k + 1)) m

theorem nyquistWeight_endpoint_normalization (β c d : ℝ) {n : ℝ} (hn : 0 < n) (r : ℕ) :
    (c * d ^ r / (r.factorial : ℝ)) / n ^ (β - (r : ℝ)) =
      (c / n ^ β) * (n * d) ^ r / (r.factorial : ℝ) := by
  rw [Real.rpow_sub hn, Real.rpow_natCast]
  field_simp
  ring

theorem nyquistWeightJet_log (β : ℝ) (j : ℕ) {n : ℝ} (hn : 0 < n) :
    nyquistWeightJet β j (Real.log n) =
      β ^ j / 2 * (n ^ β + (-1 : ℝ) ^ j * n ^ (-β)) := by
  simp only [nyquistWeightJet, Real.rpow_def_of_pos hn, mul_comm]

theorem nyquistWeightJet_log_normalized (β : ℝ) (j : ℕ) {n : ℝ} (hn : 0 < n) :
    nyquistWeightJet β j (Real.log n) / n ^ β =
      β ^ j / 2 * (1 + (-1 : ℝ) ^ j * n ^ (-2 * β)) := by
  have he : n ^ (-2 * β) * n ^ β = n ^ (-β) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  rw [nyquistWeightJet_log β j hn]
  apply (div_eq_iff (Real.rpow_pos_of_pos hn β).ne').mpr
  rw [mul_assoc, add_mul, one_mul, mul_assoc, he]

theorem nyquistWeightCellMass_le_power {β : ℝ} (hβ : 0 ≤ β) (m k : ℕ) :
    nyquistWeightCellMass β m k ≤
      (2 : ℝ) ^ β * β ^ (m + 1) / ((m + 2).factorial : ℝ) *
        ((k + 1 : ℕ) : ℝ) ^ (β - ((m + 2 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hn' : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hj : nyquistWeightJet β (m + 1) (nyquistResidualNode (k + 1)) ≤
      β ^ (m + 1) * ((2 : ℝ) ^ β * ((k + 1 : ℕ) : ℝ) ^ β) := by
    have hb : ((k + 2 : ℕ) : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    calc
      _ ≤ β ^ (m + 1) * Real.exp (β * nyquistResidualNode (k + 1)) :=
        nyquistWeightJet_le_exp hβ (nyquistResidualNode_nonneg (k + 1)) _
      _ = β ^ (m + 1) * ((k + 2 : ℕ) : ℝ) ^ β := by
        rw [Real.rpow_def_of_pos hn']
        simp only [nyquistResidualNode]
        congr 2
        ring
      _ ≤ β ^ (m + 1) * (2 * ((k + 1 : ℕ) : ℝ)) ^ β :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn'.le hb hβ) (pow_nonneg hβ _)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
  calc
    _ ≤ nyquistWeightJet β (m + 1) (nyquistResidualNode (k + 1)) *
        nyquistWeightCellWidth k ^ (m + 2) / ((m + 2).factorial : ℝ) :=
      (nyquistWeightCellMass_bounds hβ m k).2
    _ ≤ (β ^ (m + 1) * ((2 : ℝ) ^ β * ((k + 1 : ℕ) : ℝ) ^ β)) *
        (1 / ((k + 1 : ℕ) : ℝ)) ^ (m + 2) / ((m + 2).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul hj
        (pow_le_pow_left₀ (nyquistWeightCellWidth_pos k).le (nyquistWeightCellWidth_bounds k).2 _)
        (pow_nonneg (nyquistWeightCellWidth_pos k).le _) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hn, Real.rpow_natCast]
      simp only [div_pow, one_pow]
      field_simp [hn.ne']

theorem nyquistWeightTaylor_zero_parameter (m : ℕ) (a x : ℝ) :
    nyquistWeightTaylor 0 m a x = 1 := by
  induction m with
  | zero => simp [nyquistWeightTaylor_zero, nyquistWeight]
  | succ m hm => rw [nyquistWeightTaylor_succ, hm]; simp [nyquistWeightJet]

theorem nyquistWeightCellResidual_zero_parameter (m k : ℕ) (x : ℝ) :
    nyquistWeightCellResidual 0 m k x = 0 := by
  simp [nyquistWeightCellResidual, nyquistWeightTaylorResidual,
    nyquistWeightTaylor_zero_parameter, nyquistWeight]

theorem nyquistWeightCellMass_zero_parameter (m k : ℕ) :
    nyquistWeightCellMass 0 m k = 0 := by
  simp [nyquistWeightCellMass, nyquistWeightTaylorMass, nyquistWeightTaylorResidual,
    nyquistWeightTaylor_zero_parameter, nyquistWeight]

end
end GaloisForLFunctions.BiScaleUncertainty
