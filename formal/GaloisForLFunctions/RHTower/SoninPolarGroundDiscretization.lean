import GaloisForLFunctions.RHTower.SoninPrimePolarChronologicalWork
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.PSeries

/-!
# Admission of the original polar ground discretization error

Each logarithmic integer cell retains its exact polar mass. The remaining
within-cell vector errors are pairwise orthogonal in physical L2 and have
summable squared norms. Thus the entire correction series is admitted
unconditionally. The final identity identifies each correction with the
original native polar-only operator plus its exact cell mass.

This does not bound the remaining signed prime–polar arithmetic covariance.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower


private def density (u : ℝ) : ℝ := (Real.exp u+1)/u

private theorem density_cont (b R : ℝ) (hb : 0 < b) : ContinuousOn density (Icc b R) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  have hu0 : u ≠ 0 := ne_of_gt (hb.trans_le hu.1)
  unfold density
  fun_prop

private theorem entry_norm_sq (a : ℝ) (ha : 0 ≤ a) (u : ℝ) :
    ‖soninGroundEntry a u‖^2 = 2*a*Real.exp (-u) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_soninGroundEntry_of_le a ha u u le_rfl]
  rfl

private theorem difference_norm_sq (a : ℝ) (ha : 0 ≤ a) (b u : ℝ) (hbu : b ≤ u) :
    ‖soninGroundEntry a u-soninGroundEntry a b‖^2 =
      2*a*(Real.exp (-b)-Real.exp (-u)) := by
  have hi : inner ℂ (soninGroundEntry a u) (soninGroundEntry a b) =
      ((2*a*Real.exp (-u):ℝ):ℂ) := by
    rw [← inner_conj_symm, inner_soninGroundEntry_of_le a ha b u hbu, Complex.conj_ofReal]
  rw [norm_sub_sq (𝕜 := ℂ), entry_norm_sq a ha, entry_norm_sq a ha, hi]
  change 2*a*Real.exp (-u)-2*(2*a*Real.exp (-u))+2*a*Real.exp (-b) = _
  ring

private theorem difference_inner_zero (a : ℝ) (ha : 0 ≤ a) (b u c v : ℝ)
    (hbu : b ≤ u) (huc : u ≤ c) (hcv : c ≤ v) :
    inner ℂ (soninGroundEntry a u-soninGroundEntry a b)
      (soninGroundEntry a v-soninGroundEntry a c) = 0 := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_soninGroundEntry_of_le a ha u v (huc.trans hcv),
    inner_soninGroundEntry_of_le a ha u c huc,
    inner_soninGroundEntry_of_le a ha b v ((hbu.trans huc).trans hcv),
    inner_soninGroundEntry_of_le a ha b c (hbu.trans huc)]
  ring

private theorem cell_integrable (a x : ℝ) (hx : 1 < x) :
    IntegrableOn (fun u => (density u:ℂ) •
      (soninGroundEntry a u-soninGroundEntry a (Real.log x)))
      (Icc (Real.log x) (Real.log (x+1))) :=
  ((Complex.continuous_ofReal.comp_continuousOn
    (density_cont _ _ (Real.log_pos hx))).smul
      ((continuous_soninGroundEntry a).sub continuous_const).continuousOn).integrableOn_Icc

/-- Exact within-cell error of the original polar ground source; cell n
is the full logarithmic interval from log(n+2) to log(n+3). -/
def soninPolarGroundCellError (a : ℝ) (n : ℕ) : SoninL2 :=
  ∫ u in Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ)),
    (((Real.exp u+1)/u:ℝ):ℂ) •
      (soninGroundEntry a u-soninGroundEntry a (Real.log (n+2:ℝ)))

private theorem error_integrable (a : ℝ) (n : ℕ) :
    IntegrableOn (fun u => (density u:ℂ) •
      (soninGroundEntry a u-soninGroundEntry a (Real.log (n+2:ℝ))))
      (Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ))) := by
  simpa only [show (n:ℝ)+2+1=n+3 by ring] using
    cell_integrable a (n+2:ℝ) (by linarith [Nat.cast_nonneg (α := ℝ) n])

private theorem inner_integral_left {μ : Measure ℝ} {f : ℝ → SoninL2}
    (hf : Integrable f μ) (y : SoninL2) :
    inner ℂ (∫ u, f u ∂μ) y = ∫ u, inner ℂ (f u) y ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  exact inner_conj_symm _ _

private theorem error_inner_of_lt (a : ℝ) (ha : 0 ≤ a) (n m : ℕ) (hnm : n < m) :
    inner ℂ (soninPolarGroundCellError a n) (soninPolarGroundCellError a m) = 0 := by
  have hn := error_integrable a n
  have hm := error_integrable a m
  dsimp only [density] at hn hm
  unfold soninPolarGroundCellError
  rw [inner_integral_left hn]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [← integral_inner hm]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  rw [inner_smul_left, inner_smul_right,
    difference_inner_zero a ha _ u _ v hu.1
      (hu.2.trans (Real.log_le_log (by positivity) (by exact_mod_cast (show n+3 ≤ m+2 by omega)))) hv.1,
    mul_zero, mul_zero]
  rfl

/-- Distinct literal polar-cell errors are exactly orthogonal in physical L2. -/
theorem inner_soninPolarGroundCellError_eq_zero (a : ℝ) (ha : 0 ≤ a)
    {n m : ℕ} (hnm : n ≠ m) :
    inner ℂ (soninPolarGroundCellError a n) (soninPolarGroundCellError a m) = 0 := by
  rcases lt_or_gt_of_ne hnm with h | h
  · exact error_inner_of_lt a ha n m h
  · rw [← inner_conj_symm, error_inner_of_lt a ha m n h, map_zero]

private theorem cell_difference_bound (a : ℝ) (ha : 0 ≤ a) (x u : ℝ) (hx : 2 ≤ x)
    (hu : u ∈ Icc (Real.log x) (Real.log (x+1))) :
    ‖soninGroundEntry a u-soninGroundEntry a (Real.log x)‖ ≤ Real.sqrt (2*a)/x := by
  have hx0 : 0 < x := by linarith
  have hl : (x+1)⁻¹ ≤ Real.exp (-u) := by
    have h := Real.exp_le_exp.mpr (neg_le_neg hu.2)
    simpa only [Real.exp_neg, Real.exp_log (by positivity : 0 < x+1)] using h
  have hrat : x⁻¹-(x+1)⁻¹ ≤ 1/(x*x) := by
    calc
      _ = 1/(x*(x+1)) := by field_simp; ring
      _ ≤ _ := one_div_le_one_div_of_le (mul_pos hx0 hx0) (by nlinarith)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hx0.le)).mp
  rw [difference_norm_sq a ha _ u hu.1, Real.exp_neg, Real.exp_log hx0,
    div_pow, Real.sq_sqrt (by positivity)]
  calc
    _ ≤ 2*a*(x⁻¹-(x+1)⁻¹) := mul_le_mul_of_nonneg_left (sub_le_sub_left hl _) (by positivity)
    _ ≤ 2*a*(1/(x*x)) := mul_le_mul_of_nonneg_left hrat (by positivity)
    _ = _ := by ring

private theorem cell_density_bound (x u : ℝ) (hx : 2 ≤ x)
    (hu : u ∈ Icc (Real.log x) (Real.log (x+1))) :
    0 ≤ density u ∧ density u ≤ (x+2)/Real.log 2 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlu : Real.log 2 ≤ u := (Real.log_le_log (by norm_num) hx).trans hu.1
  have hex : Real.exp u ≤ x+1 := by
    simpa only [Real.exp_log (by positivity : 0 < x+1)] using Real.exp_le_exp.mpr hu.2
  constructor
  · exact div_nonneg (by positivity) (hlog.le.trans hlu)
  · unfold density
    exact div_le_div₀ (by linarith) (by linarith) hlog hlu

private theorem cell_length_bound (x : ℝ) (hx : 2 ≤ x) :
    Real.log (x+1)-Real.log x ≤ 1/x := by
  have hx0 : 0 < x := by linarith
  rw [← Real.log_div (by positivity) hx0.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < x+1) hx0)
  convert h using 1
  field_simp
  ring

private theorem error_norm_bound (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖soninPolarGroundCellError a n‖ ≤
      (2*Real.sqrt (2*a)/Real.log 2)/(n+2:ℝ) := by
  let x : ℝ := n+2
  have hx : 2 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlen : Real.log x ≤ Real.log (x+1) := Real.log_le_log hx0 (by linarith)
  have hbound : ∀ᵐ u ∂volume.restrict (Icc (Real.log x) (Real.log (x+1))),
      ‖(density u:ℂ) • (soninGroundEntry a u-soninGroundEntry a (Real.log x))‖ ≤
        (x+2)/Real.log 2*(Real.sqrt (2*a)/x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cell_density_bound x u hx hu).1]
    exact mul_le_mul (cell_density_bound x u hx hu).2 (cell_difference_bound a ha x u hx hu)
      (norm_nonneg _) (by positivity)
  have h := norm_setIntegral_le_of_norm_le_const_ae
    (isCompact_Icc.measure_lt_top : volume (Icc (Real.log x) (Real.log (x+1))) < ⊤) hbound
  rw [Real.volume_real_Icc_of_le hlen] at h
  have he : soninPolarGroundCellError a n = ∫ u in Icc (Real.log x) (Real.log (x+1)),
      (density u:ℂ) • (soninGroundEntry a u-soninGroundEntry a (Real.log x)) := by
    unfold soninPolarGroundCellError
    dsimp only [x, density]
    rw [show (n:ℝ)+2+1=n+3 by ring]
  rw [he]
  change _ ≤ (2*Real.sqrt (2*a)/Real.log 2)/x
  calc
    _ ≤ ((x+2)/Real.log 2*(Real.sqrt (2*a)/x))*(Real.log (x+1)-Real.log x) := h
    _ ≤ ((x+2)/Real.log 2*(Real.sqrt (2*a)/x))*(1/x) :=
      mul_le_mul_of_nonneg_left (cell_length_bound x hx) (by positivity)
    _ = ((x+2)/x)/Real.log 2*(Real.sqrt (2*a)/x) := by ring
    _ ≤ 2/Real.log 2*(Real.sqrt (2*a)/x) := by
      gcongr
      exact (div_le_iff₀ hx0).mpr (by linarith)
    _ = _ := by ring


/-- Critical square summability of the entire literal polar discretization error. -/
theorem summable_norm_sq_soninPolarGroundCellError (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun n : ℕ => ‖soninPolarGroundCellError a n‖^2) := by
  have hb : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))
  have hi : Function.Injective (fun n : ℕ => n+2) := fun _ _ h => Nat.add_right_cancel h
  have hs : Summable (fun n : ℕ => 1/(n+2:ℝ)^2) := by
    have hs' := hb.comp_injective hi
    change Summable (fun n : ℕ => 1 / ((n+2 : ℕ) : ℝ)^2) at hs'
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hs'
  apply (hs.mul_left ((2*Real.sqrt (2*a)/Real.log 2)^2)).of_nonneg_of_le
    (fun n => sq_nonneg _) (fun n => ?_)
  calc
    _ ≤ ((2*Real.sqrt (2*a)/Real.log 2)/(n+2:ℝ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (error_norm_bound a ha n) 2
    _ = _ := by rw [div_pow]; ring

/-- Unconditional physical-L2 admission of the full within-cell polar error,
using exact orthogonality rather than an absolute coefficient sum. -/
theorem summable_soninPolarGroundCellError (a : ℝ) (ha : 0 ≤ a) :
    Summable (soninPolarGroundCellError a) := by
  let V : ℕ → Submodule ℂ SoninL2 := fun n => Submodule.span ℂ {soninPolarGroundCellError a n}
  have hV : OrthogonalFamily ℂ (fun n => V n) (fun n => (V n).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro n m hnm
    apply Submodule.isOrtho_span.mpr
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    exact inner_soninPolarGroundCellError_eq_zero a ha hnm
  let f : ∀ n, V n := fun n => ⟨soninPolarGroundCellError a n, Submodule.subset_span (by simp)⟩
  exact (hV.summable_iff_norm_sq_summable f).mpr
    (summable_norm_sq_soninPolarGroundCellError a ha)

/-- The exact cell mass of the original polar density after ground normalization. -/
def soninPolarGroundCellMass (n : ℕ) : ℝ :=
  ∫ u in Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ)), (Real.exp u+1)/u

/-- Exact reconstruction of every original polar ground cell from its
unchanged cell mass and the admitted within-cell error. -/
theorem sonin_polar_ground_cell_decomposition (a : ℝ) (n : ℕ) :
    (∫ u in Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ)),
      soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial a 0)) =
      (soninPolarGroundCellMass n:ℂ) • soninGroundEntry a (Real.log (n+2:ℝ)) +
        soninPolarGroundCellError a n := by
  have hd := density_cont (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ))
    (Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hc := Complex.continuous_ofReal.comp_continuousOn hd
  have hi := (hc.smul (continuous_soninGroundEntry a).continuousOn).integrableOn_Icc (μ := volume)
  have hj := (hc.smul (continuousOn_const : ContinuousOn
    (fun _ : ℝ => soninGroundEntry a (Real.log (n+2:ℝ)))
      (Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ))))).integrableOn_Icc (μ := volume)
  change IntegrableOn (fun u : ℝ => (((Real.exp u+1)/u : ℝ) : ℂ) • soninGroundEntry a u)
    (Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ))) volume at hi
  change IntegrableOn (fun u : ℝ => (((Real.exp u+1)/u : ℝ) : ℂ) •
    soninGroundEntry a (Real.log (n+2:ℝ)))
    (Icc (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ))) volume at hj
  simp_rw [soninGroundEntry_polar_density]
  unfold soninPolarGroundCellError soninPolarGroundCellMass
  simp only [smul_sub]
  rw [integral_sub hi hj, integral_smul_const, integral_complex_ofReal]
  abel


/-- The correction is the original native polar-only source plus its exact
cell mass, rather than a replacement source with fitted coefficients. -/
theorem soninPrimePolar_empty_cell_ground (a : ℝ) (n : ℕ) :
    soninPrimePolarSourceOperator ∅ (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ)) 1
      (Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])) (soninCutoffMonomial a 0) +
        (soninPolarGroundCellMass n:ℂ) • soninGroundEntry a (Real.log (n+2:ℝ)) =
      -soninPolarGroundCellError a n := by
  rw [soninPrimePolarSourceOperator_apply]
  simp only [Finset.sum_empty, one_mul, zero_sub]
  rw [sonin_polar_ground_cell_decomposition]
  abel

/-- Unconditional assembly of all original polar-cell corrections on the
physical ground vector. The remaining discrete arithmetic source is not admitted here. -/
theorem summable_soninPrimePolar_ground_cell_correction (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun n : ℕ =>
      soninPrimePolarSourceOperator ∅ (Real.log (n+2:ℝ)) (Real.log (n+3:ℝ)) 1
        (Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])) (soninCutoffMonomial a 0) +
          (soninPolarGroundCellMass n:ℂ) • soninGroundEntry a (Real.log (n+2:ℝ))) := by
  exact (summable_soninPolarGroundCellError a ha).neg.congr
    (fun n => (soninPrimePolar_empty_cell_ground a n).symm)

end RHTower
