import GaloisForLFunctions.CompletedArithmeticForms.GeometricAtomApertureWeight
import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureSpectrum

/-!
# The complete geometric theta-chain aperture spectrum

Local finiteness and a summable geometric majorant preserve the exact
phase cancellation through the radial integral.
-/

set_option autoImplicit false

open Complex Finset MeasureTheory Set Filter
open _root_.HTGeometry RHTower
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The locally finite common-center sum of every phase on a geometric chain. -/
def geometricAperturePhaseSum (a h p s : ℝ) (z : ℂ) : ℝ :=
  ∑' k : ℕ, geometricApertureWeight a h p s k * (geometricDiagonal z k).re

theorem geometricAperturePhaseSum_eq_finite {a h p s : ℝ} (z : ℂ)
    (hh : 0 ≤ h) (N : ℕ) (hN : s ≤ (N : ℝ) * h) :
    geometricAperturePhaseSum a h p s z =
      ∑ k ∈ range (N + 1),
        geometricApertureWeight a h p s k * (geometricDiagonal z k).re := by
  apply tsum_eq_sum
  intro k hk
  have hNk : N ≤ k := by simp only [Finset.mem_range, not_lt] at hk; omega
  have hNkR : (N : ℝ) ≤ k := by exact_mod_cast hNk
  have hs : s ≤ (k : ℝ) * h := hN.trans (mul_le_mul_of_nonneg_right hNkR hh)
  rw [geometricApertureWeight_zero hs, zero_mul]

theorem geometricAperturePhaseSum_pos {z : ℂ} (hz : ‖z‖ = 1)
    {a h p s : ℝ} (ha : 0 < a) (hh : 0 < h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hs : 0 < s) : 0 < geometricAperturePhaseSum a h p s z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (s / h)
  have hNs : s ≤ (N : ℝ) * h := ((div_lt_iff₀ hh).mp hN).le
  rw [geometricAperturePhaseSum_eq_finite z hh.le N hNs]
  exact geometricAperture_phase_sum_pos hz ha hh.le hp hp1 hs N hNs

private theorem summable_chain_majorant {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * p ^ k) := by
  have hnorm : ‖p‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hp]
  have hn := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  simp only [pow_one] at hn
  have h0 := summable_geometric_of_norm_lt_one hnorm
  exact (hn.add h0).congr (fun k => by ring)

private theorem norm_chain_integrand_le {a h p s : ℝ} {z : ℂ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hp : 0 ≤ p) (hz : ‖z‖ = 1)
    (hs : 0 ≤ s) (b : ℝ) (k : ℕ) :
    ‖geometricApertureWeight a h p s k * (geometricDiagonal z k).re *
      thetaPairCenterTailSpectrum 1 1 s b‖ ≤
      (((k : ℝ) + 1) * p ^ k) *
        (thetaCuspCenterTailWeight a s * thetaPairCenterTailSpectrum 1 1 s b) := by
  have hF := (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs b).le
  have hw := thetaCuspCenterTailWeight_nonneg ha (le_max_left 0 (s - (k : ℝ) * h))
  have hwm := thetaCenterTailWeight_mono ha (le_max_left 0 (s - (k : ℝ) * h))
    (max_le hs (sub_le_self s (mul_nonneg (Nat.cast_nonneg k) hh)))
  have hU := (Complex.abs_re_le_norm (geometricDiagonal z k)).trans
    (geometricDiagonal_norm_le hz k)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hF]
  unfold geometricApertureWeight
  rw [abs_mul, abs_of_nonneg (pow_nonneg hp k), abs_of_nonneg hw]
  calc
    _ ≤ (p ^ k * thetaCuspCenterTailWeight a s) *
        ((k : ℝ) + 1) * thetaPairCenterTailSpectrum 1 1 s b := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hwm (pow_nonneg hp k)) hU
          (abs_nonneg _) (mul_nonneg (pow_nonneg hp k)
            (thetaCuspCenterTailWeight_nonneg ha hs))) hF
    _ = _ := by ring

private theorem chain_integrand_integrable {a h p : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hh : 0 ≤ h) (hp : 0 ≤ p) (hz : ‖z‖ = 1)
    (b : ℝ) (k : ℕ) :
    IntegrableOn (fun s : ℝ => geometricApertureWeight a h p s k *
      (geometricDiagonal z k).re * thetaPairCenterTailSpectrum 1 1 s b) (Ioi 0) := by
  have hweight : Continuous (fun s : ℝ => geometricApertureWeight a h p s k) := by
    unfold geometricApertureWeight thetaCuspCenterTailWeight
    fun_prop
  have hmeas := (hweight.stronglyMeasurable.mul_const (geometricDiagonal z k).re).mul
    (stronglyMeasurable_thetaPairCenterTailSpectrum 1 1 b)
  apply ((integrableOn_weight_mul_thetaPairCenterTailSpectrum
    (by decide : 0 < 1) (by decide : 0 < 1) ha0 ha b).const_mul
      (((k : ℝ) + 1) * p ^ k)).mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact norm_chain_integrand_le ha0 hh hp hz hs.le b k

private theorem chain_integral_norm_le {a h p : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hh : 0 ≤ h) (hp : 0 ≤ p) (hz : ‖z‖ = 1)
    (b : ℝ) (k : ℕ) :
    (∫ s in Ioi (0 : ℝ), ‖geometricApertureWeight a h p s k *
      (geometricDiagonal z k).re * thetaPairCenterTailSpectrum 1 1 s b‖) ≤
      (((k : ℝ) + 1) * p ^ k) * thetaPairApertureSpectrum 1 1 a b := by
  have hi := chain_integrand_integrable ha0 ha hh hp hz b k
  have hF := integrableOn_weight_mul_thetaPairCenterTailSpectrum
    (by decide : 0 < 1) (by decide : 0 < 1) ha0 ha b
  have hbound := integral_mono_ae hi.norm (hF.const_mul (((k : ℝ) + 1) * p ^ k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact norm_chain_integrand_le ha0 hh hp hz hs.le b k)
  simpa only [integral_const_mul, thetaPairApertureSpectrum] using hbound

private theorem chain_summable_integral_norm {a h p : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hz : ‖z‖ = 1) (b : ℝ) :
    Summable (fun k : ℕ => ∫ s in Ioi (0 : ℝ),
      ‖geometricApertureWeight a h p s k * (geometricDiagonal z k).re *
        thetaPairCenterTailSpectrum 1 1 s b‖) := by
  exact ((summable_chain_majorant hp hp1).mul_right
    (thetaPairApertureSpectrum 1 1 a b)).of_nonneg_of_le
      (fun k => integral_nonneg fun _ => norm_nonneg _)
      (chain_integral_norm_le ha0 ha hh hp hz b)

/-- The integrated chain is its absolutely convergent sum of total-exponent blocks. -/
theorem integral_geometricAperturePhaseSum_eq_tsum {a h p : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hz : ‖z‖ = 1) (b : ℝ) :
    (∫ s in Ioi (0 : ℝ), geometricAperturePhaseSum a h p s z *
      thetaPairCenterTailSpectrum 1 1 s b) =
      ∑' k : ℕ, ∫ s in Ioi (0 : ℝ), geometricApertureWeight a h p s k *
        (geometricDiagonal z k).re * thetaPairCenterTailSpectrum 1 1 s b := by
  have hi := chain_integrand_integrable ha0 ha hh hp hz b
  have hsum := chain_summable_integral_norm ha0 ha hh hp hp1 hz b
  have hseries : ∀ s : ℝ, geometricAperturePhaseSum a h p s z *
      thetaPairCenterTailSpectrum 1 1 s b =
      ∑' k : ℕ, geometricApertureWeight a h p s k * (geometricDiagonal z k).re *
        thetaPairCenterTailSpectrum 1 1 s b := by
    intro s
    exact (tsum_mul_right).symm
  simp_rw [hseries]
  apply MeasureTheory.integral_tsum
  · exact fun k => (hi k).aestronglyMeasurable
  · have he (k : ℕ) :
        (∫⁻ s in Ioi (0 : ℝ),
          ‖geometricApertureWeight a h p s k * (geometricDiagonal z k).re *
            thetaPairCenterTailSpectrum 1 1 s b‖ₑ) =
        ENNReal.ofReal (∫ s in Ioi (0 : ℝ),
          ‖geometricApertureWeight a h p s k * (geometricDiagonal z k).re *
            thetaPairCenterTailSpectrum 1 1 s b‖) :=
      (ofReal_integral_norm_eq_lintegral_enorm (hi k)).symm
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun _ => norm_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top.ne

theorem integrableOn_geometricAperturePhaseSum {a h p : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hz : ‖z‖ = 1) (b : ℝ) :
    IntegrableOn (fun s : ℝ => geometricAperturePhaseSum a h p s z *
      thetaPairCenterTailSpectrum 1 1 s b) (Ioi 0) := by
  let F : ℕ → ℝ → ℝ := fun k s => geometricApertureWeight a h p s k *
    (geometricDiagonal z k).re * thetaPairCenterTailSpectrum 1 1 s b
  have hi : ∀ k, Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) :=
    chain_integrand_integrable ha0 ha hh hp hz b
  have hsum := chain_summable_integral_norm ha0 ha hh hp hp1 hz b
  have htotal : Integrable (fun s => ∑' k, F k s) (volume.restrict (Ioi (0 : ℝ))) := by
    refine ⟨AEStronglyMeasurable.tsum fun k => (hi k).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc
      (∫⁻ s in Ioi (0 : ℝ), ‖∑' k, F k s‖ₑ) ≤
          ∫⁻ s in Ioi (0 : ℝ), ∑' k, ‖F k s‖ₑ :=
        lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
      _ = ∑' k, ∫⁻ s in Ioi (0 : ℝ), ‖F k s‖ₑ :=
        lintegral_tsum fun k => (hi k).aestronglyMeasurable.enorm
      _ = ∑' k, ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ‖F k s‖) := by
        apply tsum_congr
        intro k
        exact (ofReal_integral_norm_eq_lintegral_enorm (hi k)).symm
      _ = ENNReal.ofReal (∑' k, ∫ s in Ioi (0 : ℝ), ‖F k s‖) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun k => integral_nonneg fun _ => norm_nonneg _) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  apply htotal.congr
  filter_upwards with s
  exact tsum_mul_right

/-- Every phase of the complete geometric chain has strictly positive radial integral. -/
theorem integral_geometricAperturePhaseSum_pos {a h p : ℝ} {z : ℂ}
    (ha0 : 0 < a) (ha : a < 1 / 2) (hh : 0 < h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hz : ‖z‖ = 1) (b : ℝ) :
    0 < ∫ s in Ioi (0 : ℝ), geometricAperturePhaseSum a h p s z *
      thetaPairCenterTailSpectrum 1 1 s b := by
  have hi := integrableOn_geometricAperturePhaseSum ha0.le ha hh.le hp hp1 hz b
  have hpos (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      0 < geometricAperturePhaseSum a h p s z * thetaPairCenterTailSpectrum 1 1 s b :=
    mul_pos (geometricAperturePhaseSum_pos hz ha0 hh hp hp1 hs)
      (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs.le b)
  have hnn : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ geometricAperturePhaseSum a h p s z * thetaPairCenterTailSpectrum 1 1 s b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hpos s hs).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hi]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support
      (fun s => geometricAperturePhaseSum a h p s z * thetaPairCenterTailSpectrum 1 1 s b) ∩
        Ioi (0 : ℝ) := by
    intro s hs
    exact ⟨(hpos s hs.1).ne', hs.1⟩
  exact (by simp : 0 < volume (Ioo (0 : ℝ) 1)).trans_le (measure_mono hsub)

private theorem geometric_pair_aperture_eq {q : ℕ} (hq : 0 < q)
    (i j : ℕ) (a b : ℝ) :
    thetaPairApertureSpectrum (q ^ i) (q ^ j) a b =
      Real.cos (((i : ℝ) - j) * (b * Real.log q)) *
        (Real.exp (-Real.log q / 2)) ^ (i + j) *
          ∫ s in Ioi (0 : ℝ),
            thetaCuspCenterTailWeight a (max 0 (s - ((i + j : ℕ) : ℝ) * Real.log q)) *
              thetaPairCenterTailSpectrum 1 1 s b := by
  have hprod : Real.log (((q ^ i : ℕ) : ℝ) * ((q ^ j : ℕ) : ℝ)) =
      ((i + j : ℕ) : ℝ) * Real.log q := by
    rw [Nat.cast_pow, Nat.cast_pow, ← pow_add, Real.log_pow]
  have hscale : Real.exp (-(((i + j : ℕ) : ℝ) * Real.log q) / 2) =
      (Real.exp (-Real.log q / 2)) ^ (i + j) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hphase : b * (Real.log ((q ^ i : ℕ) : ℝ) - Real.log ((q ^ j : ℕ) : ℝ)) =
      ((i : ℝ) - j) * (b * Real.log q) := by
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
    ring
  rw [thetaPairApertureSpectrum_eq_shifted (pow_pos hq i) (pow_pos hq j),
    hprod, hscale, hphase]

private theorem shifted_first_aperture_bounds {a d : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hd : 0 ≤ d) (b : ℝ) :
    0 ≤ (∫ s in Ioi (0 : ℝ),
      thetaCuspCenterTailWeight a (max 0 (s - d)) * thetaPairCenterTailSpectrum 1 1 s b) ∧
    (∫ s in Ioi (0 : ℝ),
      thetaCuspCenterTailWeight a (max 0 (s - d)) * thetaPairCenterTailSpectrum 1 1 s b) ≤
      thetaPairApertureSpectrum 1 1 a b := by
  have hc : Continuous (fun s : ℝ => thetaCuspCenterTailWeight a (max 0 (s - d))) := by
    unfold thetaCuspCenterTailWeight
    fun_prop
  have hbase := integrableOn_weight_mul_thetaPairCenterTailSpectrum
    (by decide : 0 < 1) (by decide : 0 < 1) ha0 ha b
  have hnn (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      0 ≤ thetaCuspCenterTailWeight a (max 0 (s - d)) * thetaPairCenterTailSpectrum 1 1 s b :=
    mul_nonneg (thetaCuspCenterTailWeight_nonneg ha0 (le_max_left _ _))
      (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs.le b).le
  have hbound (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      thetaCuspCenterTailWeight a (max 0 (s - d)) * thetaPairCenterTailSpectrum 1 1 s b ≤
        thetaCuspCenterTailWeight a s * thetaPairCenterTailSpectrum 1 1 s b :=
    mul_le_mul_of_nonneg_right
      (thetaCenterTailWeight_mono ha0 (le_max_left _ _)
        (max_le hs.le (sub_le_self s hd)))
      (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs.le b).le
  have hi : IntegrableOn (fun s : ℝ => thetaCuspCenterTailWeight a (max 0 (s - d)) *
      thetaPairCenterTailSpectrum 1 1 s b) (Ioi 0) := by
    apply hbase.mono'
      (hc.stronglyMeasurable.mul (stronglyMeasurable_thetaPairCenterTailSpectrum 1 1 b)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change ‖thetaCuspCenterTailWeight a (max 0 (s - d)) * thetaPairCenterTailSpectrum 1 1 s b‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn s hs)]
    exact hbound s hs
  constructor
  · exact integral_nonneg_of_ae
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact hnn s hs)
  · exact setIntegral_mono_on hi hbase measurableSet_Ioi hbound

private theorem abs_geometric_pair_aperture_le {q : ℕ} (hq : 2 ≤ q)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (i j : ℕ) (b : ℝ) :
    |thetaPairApertureSpectrum (q ^ i) (q ^ j) a b| ≤
      (Real.exp (-Real.log q / 2)) ^ (i + j) * thetaPairApertureSpectrum 1 1 a b := by
  have hq0 : 0 < q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hd := mul_nonneg (Nat.cast_nonneg (i + j)) (Real.log_nonneg hqR)
  obtain ⟨hI0, hI⟩ := shifted_first_aperture_bounds ha0 ha hd b
  rw [geometric_pair_aperture_eq hq0, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (Real.exp_pos _).le _), abs_of_nonneg hI0]
  calc
    _ ≤ 1 * (Real.exp (-Real.log q / 2)) ^ (i + j) *
        (∫ s in Ioi (0 : ℝ),
          thetaCuspCenterTailWeight a (max 0 (s - ((i + j : ℕ) : ℝ) * Real.log q)) *
            thetaPairCenterTailSpectrum 1 1 s b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)) hI0
    _ ≤ _ := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- Absolute summability holds before any cancellation inside a total-exponent block. -/
theorem summable_geometricPairApertureBlock_abs {q : ℕ} (hq : 2 ≤ q)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    Summable (fun k : ℕ => ∑ i ∈ range (k + 1),
      |thetaPairApertureSpectrum (q ^ i) (q ^ (k - i)) a b|) := by
  have hq1 : 1 < q := by omega
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hp : 0 ≤ Real.exp (-Real.log (q : ℝ) / 2) := (Real.exp_pos _).le
  have hp1 : Real.exp (-Real.log (q : ℝ) / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith only [hlog])
  apply ((summable_chain_majorant hp hp1).mul_right
    (thetaPairApertureSpectrum 1 1 a b)).of_nonneg_of_le
  · intro k
    exact sum_nonneg fun _ _ => abs_nonneg _
  · intro k
    calc
      _ ≤ ∑ i ∈ range (k + 1),
          (Real.exp (-Real.log q / 2)) ^ k * thetaPairApertureSpectrum 1 1 a b := by
        apply sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        simpa only [Nat.add_sub_of_le hik] using
          abs_geometric_pair_aperture_le hq ha0 ha i (k - i) b
      _ = _ := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- One total-exponent block is exactly the corresponding ordinary-pair aperture sum. -/
theorem geometricPairApertureBlock_eq_integral {q : ℕ} (hq : 0 < q)
    (a b : ℝ) (k : ℕ) :
    (∑ i ∈ range (k + 1), thetaPairApertureSpectrum (q ^ i) (q ^ (k - i)) a b) =
      ∫ s in Ioi (0 : ℝ),
        geometricApertureWeight a (Real.log q) (Real.exp (-Real.log q / 2)) s k *
          (geometricDiagonal (Complex.exp (((b * Real.log q : ℝ) : ℂ) * I)) k).re *
            thetaPairCenterTailSpectrum 1 1 s b := by
  let J : ℝ := ∫ s in Ioi (0 : ℝ),
    thetaCuspCenterTailWeight a (max 0 (s - (k : ℝ) * Real.log q)) *
      thetaPairCenterTailSpectrum 1 1 s b
  calc
    _ = (∑ i ∈ range (k + 1), Real.cos ((2 * (i : ℝ) - k) * (b * Real.log q))) *
        (Real.exp (-Real.log q / 2)) ^ k * J := by
      rw [sum_mul, sum_mul]
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [geometric_pair_aperture_eq hq, Nat.add_sub_of_le hik, Nat.cast_sub hik]
      rw [show (i : ℝ) - ((k : ℝ) - i) = 2 * (i : ℝ) - k by ring]
    _ = _ := by
      rw [← geometricDiagonal_exp_re]
      dsimp only [J]
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp only [geometricApertureWeight]
      ring

/-- The aperture spectrum of every ordinary ordered pair on the complete geometric chain. -/
def geometricThetaApertureSpectrum (q : ℕ) (a b : ℝ) : ℝ :=
  ∑' k : ℕ, ∑ i ∈ range (k + 1),
    thetaPairApertureSpectrum (q ^ i) (q ^ (k - i)) a b

/-- Strict positivity of the complete ordinary-pair aperture spectrum on a geometric chain. -/
theorem geometricThetaApertureSpectrum_pos {q : ℕ} (hq : 2 ≤ q)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) :
    0 < geometricThetaApertureSpectrum q a b := by
  have hq0 : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  have hq1 : 1 < q := by omega
  have hh : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hp : 0 ≤ Real.exp (-Real.log (q : ℝ) / 2) := (Real.exp_pos _).le
  have hp1 : Real.exp (-Real.log (q : ℝ) / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith only [hh])
  have hz : ‖Complex.exp (((b * Real.log q : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  unfold geometricThetaApertureSpectrum
  simp_rw [geometricPairApertureBlock_eq_integral hq0]
  rw [← integral_geometricAperturePhaseSum_eq_tsum ha0.le ha hh.le hp hp1 hz]
  exact integral_geometricAperturePhaseSum_pos ha0 ha hh hp hp1 hz b

end GaloisForLFunctions.CompletedArithmeticForms
