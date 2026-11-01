import GaloisForLFunctions.LatticeSectionTheory.DefiniteCountsHaveOffLineZeros
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The self-dual point of the boost line has no real zeros

The majorant lattices of the split plane form a line `u ↦ ℤ ⊕ e^{2u}ℤ`. At every boost `|u| > 1`
the completed Epstein function has a real zero in `(½, 1)` (`exists_boost_offLine_zero`). At the
self-dual point `u = 0` — the Gaussian integers `ℤ ⊕ ℤ`, fixed by Poisson duality — it has none:

* **Self-dual decay** (`rectTheta_one_sq_sub_one_le`, `epsteinModif_one_of_lt_one`). With
  `θ(t)² = t⁻¹ θ(1/t)²` the modified count is `t⁻¹(θ(1/t)² − 1) ≤ 10 t⁻¹ e^{−π/t}` on `(0, 1)` and
  `θ(t)² − 1 ≤ 10 e^{−πt}` on `(1, ∞)`.
* **The Mellin integral is small** (`epsteinMellin_one_le`). `e^x ≥ x³/6` turns both pieces into
  `60 t/π³` and `60/(π³ t³)`, so `M_1(σ) ≤ 60/π³ < 3` for every `σ ∈ (0, 1)`.
* **No real zero** (`epsteinLambda_one_neg`). `Λ_1(σ) = M_1(σ) − 1/σ − 1/(1 − σ) ≤ 60/π³ − 4 < 0` on
  all of `(0, 1)`.

So the fakes of the definite surface are created by the boost: the self-dual lattice is negative on
the real segment of the strip, the lattices beyond boost `1` cross zero there.
-/

noncomputable section

open Real Complex MeasureTheory Set

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticOrientationGeometry

/-- `θ(u)² − 1 ≤ 10 e^{−πu}` for `u ≥ 1`. -/
theorem thetaSum_sq_sub_one_le {u : ℝ} (hu : 1 ≤ u) :
    thetaSum u ^ 2 - 1 ≤ 10 * Real.exp (-π * u) := by
  have h1 := thetaSum_sub_one_le hu
  have h0 := one_le_thetaSum (lt_of_lt_of_le one_pos hu)
  have he : Real.exp (-π * u) ≤ 1 / 8 := by
    have hπ : Real.exp (-π * u) ≤ Real.exp (-π) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
    have h8 : 8 ≤ Real.exp π := by
      have := Real.add_one_le_exp π
      have := Real.quadratic_le_exp_of_nonneg Real.pi_pos.le
      nlinarith [Real.pi_gt_three]
    have : Real.exp (-π) ≤ 1 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
    linarith
  have hE := Real.exp_pos (-π * u)
  nlinarith

/-- On `(0, 1)` the self-dual modified count is `t⁻¹(θ(1/t)² − 1)`. -/
theorem epsteinModif_one_of_lt_one {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    epsteinModif 1 one_pos t = t⁻¹ * (thetaSum t⁻¹ ^ 2 - 1) := by
  rw [epsteinModif_of_lt_one one_pos ht0 ht, rectTheta]
  have h := thetaSum_inv ht0
  rw [← Real.sqrt_eq_rpow] at h
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  rw [one_pow, one_mul, Real.rpow_neg_one, h]
  have hinv : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = t⁻¹ := by rw [← mul_inv, hs]
  linear_combination (thetaSum t⁻¹ ^ 2) * hinv

/-- Pointwise bound on `(0, 1]`: `t^{σ−1} F_1(t) ≤ 60 t/π³`. -/
theorem epsteinIntegrand_one_le_of_le_one {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ 1) : t ^ (σ - 1) * epsteinModif 1 one_pos t ≤ 60 / π ^ 3 * t := by
  rcases ht.lt_or_eq with ht | ht
  · rw [epsteinModif_one_of_lt_one ht0 ht]
    have hu : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht0, ht.le⟩
    have hb := thetaSum_sq_sub_one_le hu
    have hF0 : 0 ≤ t⁻¹ * (thetaSum t⁻¹ ^ 2 - 1) := by
      have := one_le_thetaSum (inv_pos.mpr ht0)
      exact mul_nonneg (inv_nonneg.mpr ht0.le) (by nlinarith)
    have hpow : t ^ (σ - 1) ≤ t⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge ht0 ht.le (by linarith)
    -- `e^{π/t} ≥ (π/t)³/6`
    have hexp : Real.exp (-π * t⁻¹) ≤ 6 * t ^ 3 / π ^ 3 := by
      have h3 := Real.pow_div_factorial_le_exp (x := π * t⁻¹) (by positivity) 3
      rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num] at h3
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)] at h3
      have hX : (π * t⁻¹) ^ 3 * t ^ 3 = π ^ 3 := by field_simp
      rw [show -π * t⁻¹ = -(π * t⁻¹) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _),
        div_mul_eq_mul_div, one_le_div (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h3 (pow_pos ht0 3).le]
    calc t ^ (σ - 1) * (t⁻¹ * (thetaSum t⁻¹ ^ 2 - 1))
        ≤ t⁻¹ * (t⁻¹ * (10 * Real.exp (-π * t⁻¹))) := by
          refine mul_le_mul hpow (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht0.le)) hF0
            (inv_nonneg.mpr ht0.le)
      _ ≤ t⁻¹ * (t⁻¹ * (10 * (6 * t ^ 3 / π ^ 3))) := by gcongr
      _ = 60 / π ^ 3 * t := by field_simp; norm_num
  · subst ht
    simp [epsteinModif, WeakFEPair.f_modif]
    positivity

/-- Pointwise bound on `(1, ∞)`: `t^{σ−1} F_1(t) ≤ 60/(π³ t³)`. -/
theorem epsteinIntegrand_one_le_of_one_lt {σ : ℝ} (hσ : σ < 1) {t : ℝ} (ht : 1 < t) :
    t ^ (σ - 1) * epsteinModif 1 one_pos t ≤ 60 / π ^ 3 * t ^ (-3 : ℝ) := by
  rw [epsteinModif_of_one_lt one_pos ht, rectTheta, one_pow, one_mul, ← sq]
  have ht0 : 0 < t := by linarith
  have hb := thetaSum_sq_sub_one_le ht.le
  have hF0 : 0 ≤ thetaSum t ^ 2 - 1 := by
    have := one_le_thetaSum ht0; nlinarith
  have hpow : t ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le (by linarith)
  have hexp : Real.exp (-π * t) ≤ 6 / (π ^ 3 * t ^ 3) := by
    have h3 := Real.pow_div_factorial_le_exp (x := π * t) (by positivity) 3
    rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num] at h3
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6), mul_pow] at h3
    rw [show -π * t = -(π * t) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _),
      div_mul_eq_mul_div, one_le_div (by positivity)]
    linarith
  have hm3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
    rw [Real.rpow_neg ht0.le]; norm_cast
  calc t ^ (σ - 1) * (thetaSum t ^ 2 - 1) ≤ 1 * (10 * Real.exp (-π * t)) :=
        mul_le_mul hpow hb hF0 zero_le_one
    _ ≤ 1 * (10 * (6 / (π ^ 3 * t ^ 3))) := by gcongr
    _ = 60 / π ^ 3 * t ^ (-3 : ℝ) := by rw [hm3]; field_simp; norm_num

/-- **The self-dual Mellin integral is small**: `M_1(σ) ≤ 60/π³` on `(0, 1)`. -/
theorem epsteinMellin_one_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    epsteinMellin 1 one_pos σ ≤ 60 / π ^ 3 := by
  have hint := integrableOn_epsteinMellin one_pos σ
  rw [epsteinMellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  -- the piece on `(0, 1]`
  have h1 : ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * epsteinModif 1 one_pos t ≤ 30 / π ^ 3 := by
    have hmaj : IntegrableOn (fun t : ℝ => 60 / π ^ 3 * t) (Ioc 0 1) :=
      (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    calc ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * epsteinModif 1 one_pos t
        ≤ ∫ t in Ioc (0 : ℝ) 1, 60 / π ^ 3 * t :=
          setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) hmaj measurableSet_Ioc
            fun t ht => epsteinIntegrand_one_le_of_le_one hσ0 ht.1 ht.2
      _ = 30 / π ^ 3 := by
          rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
            integral_id]
          ring
  -- the piece on `(1, ∞)`
  have h2 : ∫ t in Ioi (1 : ℝ), t ^ (σ - 1) * epsteinModif 1 one_pos t ≤ 30 / π ^ 3 := by
    have hmaj : IntegrableOn (fun t : ℝ => 60 / π ^ 3 * t ^ (-3 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    calc ∫ t in Ioi (1 : ℝ), t ^ (σ - 1) * epsteinModif 1 one_pos t
        ≤ ∫ t in Ioi (1 : ℝ), 60 / π ^ 3 * t ^ (-3 : ℝ) :=
          setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi zero_le_one)) hmaj measurableSet_Ioi
            fun t ht => epsteinIntegrand_one_le_of_one_lt hσ1 ht
      _ = 30 / π ^ 3 := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos, Real.one_rpow]
          ring
  calc _ ≤ 30 / π ^ 3 + 30 / π ^ 3 := add_le_add h1 h2
    _ = 60 / π ^ 3 := by ring

/-- **The self-dual point has no real zeros**: `Λ_1(σ) < 0` for every `σ ∈ (0, 1)`. -/
theorem epsteinLambda_one_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (epsteinLambda 1 one_pos σ).re < 0 := by
  rw [epsteinLambda_ofReal, Complex.ofReal_re]
  have hM := epsteinMellin_one_le hσ0 hσ1
  have hπ : 60 / π ^ 3 < 3 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
      Real.pi_gt_three.le 3]
  have hamhm : 4 ≤ 1 / σ + 1 / 1 / (1 - σ) := by
    have h1σ : 0 < 1 - σ := by linarith
    rw [div_one, div_add_div _ _ hσ0.ne' h1σ.ne', le_div_iff₀ (mul_pos hσ0 h1σ)]
    nlinarith [sq_nonneg (2 * σ - 1)]
  linarith

/-- In particular the completed Epstein function of the Gaussian integers does not vanish on
`(0, 1)`. -/
theorem epsteinLambda_one_ne_zero {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    epsteinLambda 1 one_pos σ ≠ 0 := fun h => by
  have := epsteinLambda_one_neg hσ0 hσ1
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

end GaloisForLFunctions.LatticeSectionTheory
