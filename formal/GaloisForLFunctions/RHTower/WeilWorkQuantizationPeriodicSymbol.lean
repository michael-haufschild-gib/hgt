import GaloisForLFunctions.RHTower.WeilWorkQuantizationPositiveFactor
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The periodic symbol of the actual canonical phase

The supplied exponential coefficient moment gives an analytic Laurent sum on
an annulus. The actual phase identity makes this symbol unimodular on the unit
circle, and compactness supplies a smaller nonzero annulus. These statements
construct analytic data from a representation; they do not supply a
representation from Weil positivity.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open GaloisForLFunctions.HTGeometry

def quantizationPeriodicSymbol (p : ℤ → ℂ) (z : ℂ) : ℂ := ∑' k : ℤ, p k * z ^ k

theorem quantization_norm_zpow_le {Q : ℝ} (hQ : 0 < Q) {z : ℂ}
    (hz : Q⁻¹ < ‖z‖ ∧ ‖z‖ < Q) (k : ℤ) : ‖z ^ k‖ ≤ Q ^ k.natAbs := by
  have hz0 : 0 < ‖z‖ := (inv_pos.mpr hQ).trans hz.1
  have hi : ‖z‖⁻¹ ≤ Q := (inv_le_comm₀ hz0 hQ).mpr hz.1.le
  cases k with
  | ofNat n =>
    change ‖z ^ (n : ℤ)‖ ≤ Q ^ n
    rw [zpow_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg z) hz.2.le n
  | negSucc n =>
    simpa only [zpow_negSucc, norm_inv, norm_pow, ← inv_pow, Int.natAbs_negSucc] using
      pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z)) hi (n + 1)

theorem summable_quantizationPeriodicSymbol {Q : ℝ} (hQ : 0 < Q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Q ^ k.natAbs) {z : ℂ}
    (hz : z ∈ annulusAt 0 Q⁻¹ Q) : Summable fun k : ℤ => p k * z ^ k := by
  apply Summable.of_norm
  apply hp.of_nonneg_of_le (fun k => norm_nonneg _)
  intro k
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (quantization_norm_zpow_le hQ
    (by simpa only [annulusAt, mem_setOf_eq, sub_zero] using hz) k) (norm_nonneg _)

theorem analyticOnNhd_quantizationPeriodicSymbol {Q : ℝ} (hQ : 0 < Q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Q ^ k.natAbs) :
    AnalyticOnNhd ℂ (quantizationPeriodicSymbol p) (annulusAt 0 Q⁻¹ Q) := by
  have hdiff (k : ℤ) : DifferentiableOn ℂ (fun z : ℂ => p k * z ^ k) (annulusAt 0 Q⁻¹ Q) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      have hn : Q⁻¹ < ‖z‖ := by simpa only [sub_zero] using hz.1
      exact norm_pos_iff.mp ((inv_pos.mpr hQ).trans hn)
    exact ((differentiableAt_zpow.mpr (Or.inl hz0)).const_mul (p k)).differentiableWithinAt
  have hd := Complex.differentiableOn_tsum_of_summable_norm hp hdiff
    (isOpen_annulusAt 0 Q⁻¹ Q) (fun k z hz => ?_)
  · exact hd.analyticOnNhd (isOpen_annulusAt 0 Q⁻¹ Q)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (quantization_norm_zpow_le hQ
      (by simpa only [annulusAt, mem_setOf_eq, sub_zero] using hz) k) (norm_nonneg _)

theorem quantizationPeriodicSymbol_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q : ℕ} {p : ℤ → ℂ}
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I))
    {x : ℝ} (hx : 0 < x) :
    quantizationPeriodicSymbol p (cexp (((2 * Real.log q * x : ℝ) : ℂ) * I)) =
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) := by
  rw [hphase x hx]
  unfold quantizationPeriodicSymbol
  apply tsum_congr
  intro k
  rw [← Complex.exp_int_mul]
  congr 2
  push_cast
  ring

theorem norm_quantizationPeriodicSymbol_circle {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : ‖quantizationPeriodicSymbol p z‖ = 1 := by
  have hn : ‖z‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  let x : ℝ := (z.arg + 2 * Real.pi) / (2 * Real.log q)
  have hx : 0 < x := div_pos (by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]) (by positivity)
  have hangle : 2 * Real.log q * x = z.arg + 2 * Real.pi := by
    dsimp [x]
    field_simp
  have hexp : cexp (((2 * Real.log q * x : ℝ) : ℂ) * I) = z := by
    rw [hangle]
    have he : (((z.arg + 2 * Real.pi : ℝ) : ℂ) * I) =
        (z.arg : ℂ) * I + 2 * (Real.pi : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    simpa only [hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
  rw [← hexp, quantizationPeriodicSymbol_phase hW hphase hx]
  simp [Complex.norm_exp]

/-- A circle avoiding zero has a nonzero round annular neighborhood. -/
theorem quantization_exists_nonzero_annulus {P : ℂ → ℂ} {a b : ℝ}
    (ha : a < 1) (hb : 1 < b) (hP : ContinuousOn P (annulusAt 0 a b))
    (hne : ∀ z ∈ sphere (0 : ℂ) 1, P z ≠ 0) :
    ∃ r R : ℝ, 0 < r ∧ r < 1 ∧ 1 < R ∧
      annulusAt 0 r R ⊆ annulusAt 0 a b ∧ ∀ z ∈ annulusAt 0 r R, P z ≠ 0 := by
  let U := annulusAt 0 a b ∩ P ⁻¹' ({0} : Set ℂ)ᶜ
  have hU : IsOpen U := hP.isOpen_inter_preimage (isOpen_annulusAt 0 a b) isOpen_compl_singleton
  have hcircle : sphere (0 : ℂ) 1 ⊆ U := by
    intro z hz
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    refine ⟨?_, hne z hz⟩
    simpa only [annulusAt, mem_setOf_eq, sub_zero, hn] using And.intro ha hb
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hU hcircle
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hann : annulusAt 0 (1 - ε) (1 + ε) ⊆ U := by
    intro z hz
    have hz' : 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε := by simpa only [annulusAt, mem_setOf_eq, sub_zero] using hz
    have hn0 : 0 < ‖z‖ := by linarith
    let ζ : ℂ := z / (‖z‖ : ℂ)
    have hζ : ‖ζ‖ = 1 := by
      dsimp [ζ]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0, div_self hn0.ne']
    have hζcircle : ζ ∈ sphere (0 : ℂ) 1 := by
      simpa only [mem_sphere_iff_norm, sub_zero] using hζ
    have he : z - ζ = (((‖z‖ - 1 : ℝ) : ℂ)) * ζ := by
      dsimp [ζ]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hn0.ne']
    have hdist : dist z ζ = |‖z‖ - 1| := by
      rw [dist_eq_norm, he, norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply hsub
    apply mem_thickening_iff.mpr
    refine ⟨ζ, hζcircle, ?_⟩
    rw [hdist, abs_lt]
    constructor <;> linarith [hz'.1, hz'.2]
  exact ⟨1 - ε, 1 + ε, by linarith, by linarith, by linarith,
    fun _ hz => (hann hz).1, fun _ hz => (hann hz).2⟩

/-- The nonzero annulus belongs to the actual represented phase. -/
theorem exists_nonzero_annulus_quantizationPeriodicSymbol
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I)) :
    ∃ r R : ℝ, 0 < r ∧ r < 1 ∧ 1 < R ∧
      AnalyticOnNhd ℂ (quantizationPeriodicSymbol p) (annulusAt 0 r R) ∧
      ∀ z ∈ annulusAt 0 r R, quantizationPeriodicSymbol p z ≠ 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have han := analyticOnNhd_quantizationPeriodicSymbol hq0 hp
  have hcircle : ∀ z ∈ sphere (0 : ℂ) 1, quantizationPeriodicSymbol p z ≠ 0 := by
    intro z hz he
    have hn := norm_quantizationPeriodicSymbol_circle hW hq hphase hz
    norm_num [he] at hn
  obtain ⟨r, R, hr, hr1, hR, hsub, hne⟩ := quantization_exists_nonzero_annulus
    ((inv_lt_one₀ hq0).mpr hq1) hq1 han.continuousOn hcircle
  exact ⟨r, R, hr, hr1, hR, han.mono hsub, hne⟩

end RHTower.WeilSpectral
