import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsRetainAtomicRecurrence
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Finite-energy boundaries vanish in the unit gap

Lebesgue differentiation recovers the almost-everywhere boundary from normalized
tents. Atomic recurrence makes all sufficiently small tents vanish in the unit gap,
so the real canonical boundary vanishes there without any continuity assumption.
-/

open Complex MeasureTheory Filter Topology Set Metric
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

private def normalizedTent (h y x : ℝ) : ℝ := unitTent (y / h) (x / h) / h

private theorem integral_unitTent (n : ℝ) : (∫ x : ℝ, unitTent n x) = 1 := by
  have hz : (∫ x : ℝ, unitTent 0 x) = 1 := by
    have he := intervalIntegral_window_eq_integral_unitTent (fun _ : ℝ => (1 : ℝ))
    simp only [mul_one] at he
    rw [← he]
    exact fejer_triangle_integral_one
  calc
    _ = ∫ x : ℝ, unitTent n (n + x) := (integral_add_left_eq_self (unitTent n) n).symm
    _ = ∫ x : ℝ, unitTent 0 x := by
      congr 1
      funext x
      simp only [unitTent, add_sub_cancel_left, sub_zero]
    _ = 1 := hz

private theorem integral_normalizedTent {h : ℝ} (hh : 0 < h) (y : ℝ) :
    (∫ x : ℝ, normalizedTent h y x) = 1 := by
  have ht : (∫ x : ℝ, unitTent (y / h) (x / h)) = h := by
    simpa only [div_eq_mul_inv, mul_comm, inv_inv, abs_of_pos hh,
      smul_eq_mul, integral_unitTent, mul_one] using
      Measure.integral_comp_mul_left (unitTent (y / h)) h⁻¹
  simp only [normalizedTent, integral_div, ht, div_self hh.ne']

private theorem support_normalizedTent {h : ℝ} (hh : 0 < h) (y : ℝ) :
    Function.support (normalizedTent h y) ⊆ closedBall y h := by
  intro x hx
  have hn : defectTentTest h (y / h) x ≠ 0 := by
    intro hz
    have hz' : unitTent (y / h) (x / h) = 0 := Complex.ofReal_eq_zero.mp hz
    exact hx (by simp only [normalizedTent, hz', zero_div])
  have hb := support_defectTentTest hh (y / h) hn
  rw [Real.closedBall_eq_Icc]
  have hl : h * (y / h - 1) = y - h := by field_simp [hh.ne']
  have hr : h * (y / h + 1) = y + h := by field_simp [hh.ne']
  simpa only [hl, hr] using hb

private theorem abs_normalizedTent_le {h : ℝ} (hh : 0 < h) (y x : ℝ) :
    |normalizedTent h y x| ≤ 2 / volume.real (closedBall y h) := by
  have hv : volume.real (closedBall y h) = 2 * h := by
    rw [Real.closedBall_eq_Icc, Real.volume_real_Icc_of_le (by linarith only [hh])]
    ring
  rw [normalizedTent, abs_div, abs_of_nonneg (unitTent_nonneg _ _), abs_of_pos hh, hv]
  calc
    unitTent (y / h) (x / h) / h ≤ 1 / h :=
      div_le_div_of_nonneg_right (unitTent_le_one _ _) hh.le
    _ = 2 / (2 * h) := by field_simp

private theorem ae_tendsto_normalizedTent {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ y : ℝ, Tendsto (fun h : ℝ => ∫ x : ℝ, normalizedTent h y x * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hf] with y hy
  have ht := hy.comp (Besicovitch.tendsto_filterAt volume y)
  have hlim := tendsto_integral_smul_of_tendsto_average_norm_sub 2 ht
    (g := fun h : ℝ => normalizedTent h y)
    (Eventually.of_forall fun h => hf.integrableOn_isCompact (isCompact_closedBall y h))
    (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall
      fun h hh => (integral_normalizedTent hh y).symm))
    (eventually_nhdsWithin_of_forall fun h hh => support_normalizedTent hh y)
    (eventually_nhdsWithin_of_forall fun h hh x => abs_normalizedTent_le hh y x)
  simpa only [smul_eq_mul] using hlim

private theorem normalizedTent_pairing_eq_error (g : DefectL2) {h : ℝ}
    (hh : 0 < h) (y : ℝ) :
    (∫ x : ℝ, normalizedTent h y x * (defectBoundaryL2 g x).re) =
      finiteEnergyTentError g h (y / h) / h := by
  have hI : Integrable (fun x : ℝ => defectTentTest h (y / h) x * defectBoundaryL2 g x) :=
    (memLp_defectTentTest hh (y / h)).integrable_mul (Lp.memLp (defectBoundaryL2 g))
  have he : finiteEnergyTentError g h (y / h) =
      ∫ x : ℝ, unitTent (y / h) (x / h) * (defectBoundaryL2 g x).re := by
    calc
      _ = ∫ x : ℝ, (defectTentTest h (y / h) x * defectBoundaryL2 g x).re :=
        (integral_re hI).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => Complex.re_ofReal_mul _ _
  rw [he, ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp only [normalizedTent]; ring

/-- Normalized tents recover almost every real canonical boundary value. -/
theorem ae_tendsto_normalizedFiniteEnergyTentError (g : DefectL2) :
    ∀ᵐ y : ℝ, Tendsto (fun h : ℝ => finiteEnergyTentError g h (y / h) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (defectBoundaryL2 g y).re) := by
  have hf : LocallyIntegrable (fun y : ℝ => (defectBoundaryL2 g y).re) volume :=
    (Lp.memLp (defectBoundaryL2 g)).re.locallyIntegrable (by norm_num)
  filter_upwards [ae_tendsto_normalizedTent hf] with y hy
  exact hy.congr' (eventually_nhdsWithin_of_forall
    fun h hh => normalizedTent_pairing_eq_error g hh y)

/-- The real Hardy boundary of the actual Beurling defect vanishes almost everywhere
in the positive unit gap. -/
theorem beurling_finiteEnergyBoundary_re_eq_zero_on_unit_gap
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∀ᵐ y : ℝ, y ∈ Ioo (0 : ℝ) 1 → (defectBoundaryL2 (hg.toLp g) y).re = 0 := by
  filter_upwards [ae_tendsto_normalizedFiniteEnergyTentError (hg.toLp g)] with y hy
  intro hgap
  have hz := beurling_finiteEnergyTentError_eventually_zero_on_unit_gap
    B hBsum hgm hgb hg hθ hgap.1 hgap.2
  have ht : Tendsto (fun h : ℝ => h / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, eventually_nhdsWithin_of_forall
      fun h hh => half_pos (show (0 : ℝ) < h from hh)⟩
    have hc : Continuous (fun h : ℝ => h / 2) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hl := hy.comp ht
  have hzero : Tendsto (fun h : ℝ =>
      finiteEnergyTentError (hg.toLp g) (h / 2) (y / (h / 2)) / (h / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with h hh
    rw [hh, zero_div]
  exact tendsto_nhds_unique hl hzero

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.ae_tendsto_normalizedFiniteEnergyTentError
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_finiteEnergyBoundary_re_eq_zero_on_unit_gap
