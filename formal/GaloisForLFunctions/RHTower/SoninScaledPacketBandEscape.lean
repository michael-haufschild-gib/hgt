import GaloisForLFunctions.RHTower.SoninScaledPacketEnergyLower

/-!
# Uniform band escape for the rescaled packet family

The band energy is at most the band's length times the square of a bound of size `δ`, while the
total energy is of size `δ`; so the captured fraction is of size `t δ`.  Two thresholds make this
uniform over the whole family: once the product of half-width and carrier is large the mean is below
one and the reference-square tails are below a fixed fraction of the reference square's mass, and
once the product of band radius and half-width is small the band cannot capture half the energy.

Neither threshold mentions the annulus.  So a single pair of constants serves every annulus at once,
which is what a family whose number of annuli grows with the scale requires.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform

/-- Every tail majorant of the reference profile is bounded by its mass. -/
theorem soninRefTailSup_le_mass (u : ℝ) :
    soninRefTailSup u ≤ ∫ y : ℝ, ‖soninUnitBumpC y‖ :=
  soninRefTailSup_le (integral_nonneg fun _ => norm_nonneg _)
    fun v _ => norm_fourier_soninUnitBumpC_le v

/-- **The mean is a tail majorant.**  The four transform values in the mean bound all sit outside
the band of radius `δ|w|`. -/
theorem abs_soninScaledPacketMean_le_tailSup (m δ w : ℝ) (hδ : 0 < δ) :
    |soninScaledPacketMean m δ (2 * Real.pi * w)| * (∫ y : ℝ, soninUnitBumpData y) ≤
      2 * soninRefTailSup (δ * |w|) := by
  have hmass : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  have hbase := abs_soninScaledPacketMean_le m δ w hδ
  have hpos : ‖𝓕 soninUnitBumpC (δ * w)‖ ≤ soninRefTailSup (δ * |w|) := by
    refine norm_fourier_soninUnitBumpC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ]
  have hneg : ‖𝓕 soninUnitBumpC (δ * -w)‖ ≤ soninRefTailSup (δ * |w|) := by
    refine norm_fourier_soninUnitBumpC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ, abs_neg]
  have hnegneg : ‖𝓕 soninUnitBumpC (δ * -(-w))‖ ≤ soninRefTailSup (δ * |w|) := by
    refine norm_fourier_soninUnitBumpC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ, neg_neg]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ∫ y : ℝ, soninUnitBumpData y)] at hbase
  nlinarith [hbase, hpos, hneg, hnegneg, hmass, abs_nonneg
    (soninScaledPacketMean m δ (2 * Real.pi * w))]

/-- **Uniform band escape.**  Two constants, independent of the annulus, force every rescaled packet
of the family to keep more than half its energy outside the band: the carrier must be far enough
from the origin on the scale of the half-width, and the band must be short on that same scale.  The
band radius itself is otherwise unconstrained — only its product with the half-width matters. -/
theorem exists_uniform_soninScaledPacket_band_escape :
    ∃ u₀ ρ : ℝ, 0 < u₀ ∧ 0 < ρ ∧
      ∀ (m δ w t : ℝ) (hδ : 0 < δ), δ < m → 0 ≤ t → t < w →
        u₀ ≤ δ * |w| → t * δ ≤ ρ →
        ‖evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ 2 ≤
          2⁻¹ * ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 := by
  set J₀ : ℝ := ∫ y : ℝ, soninUnitBumpData y with hJ₀def
  set I : ℝ := ∫ y : ℝ, soninUnitBumpSq y with hIdef
  set J : ℝ := ∫ y : ℝ, ‖soninUnitBumpC y‖ with hJdef
  have hJ₀ : 0 < J₀ := integral_soninUnitBumpData_pos
  have hI : 0 < I := integral_soninUnitBumpSq_pos
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp
    (tendsto_soninRefTailSup_atTop.eventually
      (gt_mem_nhds (show (0 : ℝ) < J₀ / 2 by positivity)))
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp
    (tendsto_soninRefSqTailSup_atTop.eventually
      (gt_mem_nhds (show (0 : ℝ) < I / 20 by positivity)))
  refine ⟨max (max U₁ U₂) 1, I / (128 * (J ^ 2 + 1)),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), by positivity, ?_⟩
  intro m δ w t hδ hm ht htw hcarrier hshort
  set μ : ℝ := soninScaledPacketMean m δ (2 * Real.pi * w) with hμdef
  have hU₁le : U₁ ≤ δ * |w| :=
    le_trans (le_trans (le_max_left U₁ U₂) (le_max_left _ _)) hcarrier
  have hU₂le : U₂ ≤ δ * |w| :=
    le_trans (le_trans (le_max_right U₁ U₂) (le_max_left _ _)) hcarrier
  have hS : soninRefTailSup (δ * |w|) ≤ J₀ / 2 := (hU₁ _ hU₁le).le
  have hSq : soninRefSqTailSup (δ * |w|) ≤ I / 20 := (hU₂ _ hU₂le).le
  have hSqnn : 0 ≤ soninRefSqTailSup (δ * |w|) := soninRefSqTailSup_nonneg _
  -- the mean is below one
  have hmean : |μ| ≤ 1 := by
    have h := abs_soninScaledPacketMean_le_tailSup m δ w hδ
    nlinarith [h, hS, hJ₀]
  have hmeannn : 0 ≤ |μ| := abs_nonneg μ
  -- the energy floor
  have hfloor : δ * I / 2 ≤ ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 := by
    refine le_trans ?_ (norm_sq_soninScaledPacketEven_ge m δ w hδ hm)
    have h4 : 0 ≤ 4 * δ * soninRefSqTailSup (δ * |w|) :=
      mul_nonneg (mul_nonneg (by norm_num) hδ.le) hSqnn
    have hterm : |μ| * (4 * δ * soninRefSqTailSup (δ * |w|)) ≤
        4 * δ * soninRefSqTailSup (δ * |w|) := by nlinarith [hmean, h4]
    have hdS : δ * soninRefSqTailSup (δ * |w|) ≤ δ * (I / 20) :=
      mul_le_mul_of_nonneg_left hSq hδ.le
    linarith [hterm, hdS]
  -- the band bound
  have hS1 : soninRefTailSup (δ * (w - t)) ≤ J := soninRefTailSup_le_mass _
  have hS0 : soninRefTailSup 0 ≤ J := soninRefTailSup_le_mass _
  have hS1nn : 0 ≤ soninRefTailSup (δ * (w - t)) := soninRefTailSup_nonneg _
  have hS0nn : 0 ≤ soninRefTailSup 0 := soninRefTailSup_nonneg _
  set M : ℝ := 2 * δ * soninRefTailSup (δ * (w - t)) + |μ| * (2 * δ * soninRefTailSup 0) with hMdef
  have hMnn : 0 ≤ M := by
    have h1 : 0 ≤ 2 * δ * soninRefTailSup (δ * (w - t)) :=
      mul_nonneg (mul_nonneg (by norm_num) hδ.le) hS1nn
    have h2 : 0 ≤ |μ| * (2 * δ * soninRefTailSup 0) :=
      mul_nonneg hmeannn (mul_nonneg (mul_nonneg (by norm_num) hδ.le) hS0nn)
    rw [hMdef]
    linarith
  have hMle : M ≤ 4 * δ * J := by
    have h1 : 2 * δ * soninRefTailSup (δ * (w - t)) ≤ 2 * δ * J :=
      mul_le_mul_of_nonneg_left hS1 (by linarith : (0 : ℝ) ≤ 2 * δ)
    have hb : 2 * δ * soninRefTailSup 0 ≤ 2 * δ * J :=
      mul_le_mul_of_nonneg_left hS0 (by linarith : (0 : ℝ) ≤ 2 * δ)
    have hnn : 0 ≤ 2 * δ * soninRefTailSup 0 :=
      mul_nonneg (mul_nonneg (by norm_num) hδ.le) hS0nn
    have h2 : |μ| * (2 * δ * soninRefTailSup 0) ≤ 2 * δ * J := by
      nlinarith [hmean, hnn, hb]
    rw [hMdef]
    linarith
  have hband := norm_sq_evenFourierCutoff_soninScaledPacketEven_le_uniform m δ w t hδ ht htw
  have hsq : M ^ 2 ≤ (4 * δ * J) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hMnn hMle
  have hY : 0 ≤ t * δ := mul_nonneg ht hδ.le
  have hshort' : t * δ * (128 * (J ^ 2 + 1)) ≤ I :=
    (le_div_iff₀ (by positivity)).mp hshort
  have hX : 32 * (t * δ * J ^ 2) ≤ I / 4 := by nlinarith [hshort', hY]
  have hchain : 2 * t * M ^ 2 ≤ 32 * δ * (t * δ * J ^ 2) := by nlinarith [hsq, ht]
  have hkey : 2 * t * M ^ 2 ≤ δ * I / 4 := by nlinarith [hchain, hX, hδ]
  calc ‖evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ 2
      ≤ 2 * t * M ^ 2 := hband
    _ ≤ δ * I / 4 := hkey
    _ = 2⁻¹ * (δ * I / 2) := by ring
    _ ≤ 2⁻¹ * ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 := by linarith [hfloor]

end RHTower
