import GaloisForLFunctions.RHTower.SteinhausSubgaussian

/-!
# The rate function is strictly positive off the origin

Splitting the profile integral at a small `δ` and using `log I₀(x) ≤ x` below it and
`log I₀(x) ≤ x²/2` above it gives `Λ_α(λ) ≤ λδ^{1−α} + λ²(1−α)²δ^{−2α}/2`, so `Λ_α(λ)/λ → 0`.
Hence `I_α(q) > 0` for every `q > 0`.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- The profile mass of an initial segment. -/
theorem integral_weightProfile_Icc {α : ℝ} (hα : α < 1) (δ : ℝ) :
    (∫ v in (0 : ℝ)..δ, weightProfile α v) = δ ^ (1 - α) := by
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have hbase : (∫ v in (0 : ℝ)..δ, v ^ (-α)) = δ ^ (1 - α) / (1 - α) := by
    rw [integral_rpow (Or.inl (by linarith))]
    have hexp : -α + 1 = 1 - α := by ring
    rw [hexp, Real.zero_rpow (by linarith)]
    ring
  have hsimp : (∫ v in (0 : ℝ)..δ, weightProfile α v)
      = (1 - α) * ∫ v in (0 : ℝ)..δ, v ^ (-α) := by
    simp only [weightProfile]
    exact intervalIntegral.integral_const_mul _ _
  rw [hsimp, hbase]
  field_simp

/-- **The split bound for the cumulant.** -/
theorem rvCumulant_le_split {α : ℝ} (h0 : 0 ≤ α) (hα : α < 1) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    rvCumulant α lam
      ≤ lam * δ ^ (1 - α) + lam ^ 2 / 2 * ((1 - α) ^ 2 * δ ^ (-(2 * α))) := by
  have hint := intervalIntegrable_rvCumulant_integrand hα lam
  have hsub1 : Set.uIcc (0 : ℝ) δ ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hδ0.le, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl hδ1
  have hsub2 : Set.uIcc δ (1 : ℝ) ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hδ1, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc hδ0.le le_rfl
  have hI1 : IntervalIntegrable (fun v : ℝ => steinhausLogLaplace (lam * weightProfile α v))
      volume 0 δ := hint.mono_set hsub1
  have hI2 : IntervalIntegrable (fun v : ℝ => steinhausLogLaplace (lam * weightProfile α v))
      volume δ 1 := hint.mono_set hsub2
  have hW1 : IntervalIntegrable (weightProfile α) volume 0 δ :=
    (intervalIntegrable_weightProfile hα).mono_set hsub1
  have hsplit : rvCumulant α lam
      = (∫ v in (0 : ℝ)..δ, steinhausLogLaplace (lam * weightProfile α v))
        + ∫ v in δ..1, steinhausLogLaplace (lam * weightProfile α v) := by
    rw [rvCumulant, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  -- the head, by the linear envelope
  have hhead : (∫ v in (0 : ℝ)..δ, steinhausLogLaplace (lam * weightProfile α v))
      ≤ lam * δ ^ (1 - α) := by
    have hle : ∀ v ∈ Set.Icc (0 : ℝ) δ,
        steinhausLogLaplace (lam * weightProfile α v) ≤ lam * weightProfile α v := by
      intro v hv
      have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα hv.1
      have hb := steinhausLogLaplace_le_abs (lam * weightProfile α v)
      rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ lam * weightProfile α v)] at hb
    have hmono := intervalIntegral.integral_mono_on hδ0.le hI1 (hW1.const_mul lam) hle
    rw [intervalIntegral.integral_const_mul, integral_weightProfile_Icc hα δ] at hmono
    exact hmono
  -- the tail, by the quadratic envelope
  have htail : (∫ v in δ..1, steinhausLogLaplace (lam * weightProfile α v))
      ≤ lam ^ 2 / 2 * ((1 - α) ^ 2 * δ ^ (-(2 * α))) := by
    have hle : ∀ v ∈ Set.Icc δ (1 : ℝ),
        steinhausLogLaplace (lam * weightProfile α v)
          ≤ lam ^ 2 / 2 * ((1 - α) ^ 2 * δ ^ (-(2 * α))) := by
      intro v hv
      have hv0 : 0 < v := lt_of_lt_of_le hδ0 hv.1
      have hb := steinhausLogLaplace_le_sq (lam * weightProfile α v)
      refine hb.trans ?_
      have hw : weightProfile α v = (1 - α) * v ^ (-α) := rfl
      have hvle : v ^ (-α) ≤ δ ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos hδ0 hv.1 (show -α ≤ 0 by linarith)
      have hδpow : δ ^ (-(2 * α)) = (δ ^ (-α)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast (δ ^ (-α)) 2, ← Real.rpow_mul hδ0.le]
        congr 1
        push_cast
        ring
      have hvnn : (0 : ℝ) ≤ v ^ (-α) := Real.rpow_nonneg hv0.le _
      have hδnn : (0 : ℝ) ≤ δ ^ (-α) := Real.rpow_nonneg hδ0.le _
      rw [hw, hδpow]
      have hsq : (v ^ (-α)) ^ 2 ≤ (δ ^ (-α)) ^ 2 := by nlinarith [hvle, hvnn, hδnn]
      have hcoef : (0 : ℝ) ≤ lam ^ 2 * (1 - α) ^ 2 / 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq hcoef]
    have hmono := intervalIntegral.integral_mono_on hδ1 hI2 intervalIntegrable_const hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hnn : (0 : ℝ) ≤ lam ^ 2 / 2 * ((1 - α) ^ 2 * δ ^ (-(2 * α))) := by
      have : (0 : ℝ) ≤ δ ^ (-(2 * α)) := Real.rpow_nonneg hδ0.le _
      positivity
    nlinarith [hmono, hnn, hδ1, hδ0]
  rw [hsplit]
  linarith [hhead, htail]

/-- **The rate function is strictly positive off the origin.** -/
theorem rvRate_pos {α : ℝ} (h0 : 0 ≤ α) (hα : α < 1) {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    0 < rvRate α q := by
  have hexp : (0 : ℝ) < 1 / (1 - α) := by
    have : (0 : ℝ) < 1 - α := by linarith
    positivity
  set δ : ℝ := (q / 2) ^ (1 / (1 - α)) with hδdef
  have hq2 : (0 : ℝ) < q / 2 := by linarith
  have hδ0 : 0 < δ := by rw [hδdef]; exact Real.rpow_pos_of_pos hq2 _
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    exact Real.rpow_le_one hq2.le (by linarith) hexp.le
  have hδpow : δ ^ (1 - α) = q / 2 := by
    rw [hδdef, ← Real.rpow_mul hq2.le]
    have hne : (1 : ℝ) - α ≠ 0 := by linarith
    have hone : 1 / (1 - α) * (1 - α) = 1 := by
      field_simp
    rw [hone, Real.rpow_one]
  set K : ℝ := (1 - α) ^ 2 * δ ^ (-(2 * α)) with hK
  have hK0 : 0 < K := by
    rw [hK]
    have h1 : (0 : ℝ) < 1 - α := by linarith
    have h2 : (0 : ℝ) < δ ^ (-(2 * α)) := Real.rpow_pos_of_pos hδ0 _
    positivity
  set lam : ℝ := min 1 (q / (2 * K)) with hlamdef
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    exact lt_min (by norm_num) (by positivity)
  have hlamK : lam * K / 2 ≤ q / 4 := by
    have hle : lam ≤ q / (2 * K) := min_le_right _ _
    have hstep : lam * K ≤ q / (2 * K) * K := mul_le_mul_of_nonneg_right hle hK0.le
    have hid : q / (2 * K) * K = q / 2 := by
      field_simp
    rw [hid] at hstep
    linarith
  have hbound := rvCumulant_le_split h0 hα hδ0 hδ1 hlam0.le
  rw [hδpow, ← hK] at hbound
  have hle := le_rvRate hα hq hlam0.le
  have hkey : 0 < lam * q - rvCumulant α lam := by
    have hid : lam * (q / 2) + lam ^ 2 / 2 * K = lam * (q / 2) + lam * (lam * K / 2) := by ring
    rw [hid] at hbound
    nlinarith [hbound, hlamK, hlam0, hq0]
  linarith [hle, hkey]

end

end HTGeometry
