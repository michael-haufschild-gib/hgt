import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryNorm
import GaloisForLFunctions.RHTower.WeilWorkDeficitProductKernelMellin
import GaloisForLFunctions.RHTower.EisensteinLineHeightOneMean
import GaloisForLFunctions.RHTower.EisensteinLineSourceSlices
import GaloisForLFunctions.RHTower.EisensteinLineSourceMeanSquare
import GaloisForLFunctions.RHTower.EisensteinCuspTailImaginaryOrderBound
import GaloisForLFunctions.RHTower.ZetaDerivNearOneLineBound
import GaloisForLFunctions.RHTower.ZetaNearOneLineBound
import GaloisForLFunctions.RHTower.SeamVerticalDecay
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.ArchimedeanHorizontalModel

/-!
# The effective boundary bound from the Mayer carrier

The Maass–Selberg norm of the completed Eisenstein field at height one is quadratic in `Λ(1+2it)`, up to the derivative
`Λ′(1+2it)`. Its first Whittaker mode has the exact size `e^{−πt}` up to a power of `t`. So the norm identity alone gives

`|ζ(1+2it)| ≥ c / (t³ log²(2t))`    (`exists_norm_riemannZeta_boundary_lower`).

No Euler-product inequality enters. The Whittaker mass is bounded below by testing against `y^{1+it}`: the Mellin
transform of `K_{it}` at that point is `(2π)^{−2−it} 2^{it} Γ(1+it)`, of modulus `≍ √t e^{−πt/2}`, while the ranges `y ≤ 1`
and `y ≥ t` contribute `O(log t · e^{−πt/2})` and `O(e^{−5t})`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryNorm

/-- The first Whittaker profile at height `y`. -/
def firstMode (t y : ℝ) : ℝ := ‖modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I)‖

theorem firstMode_nonneg (t y : ℝ) : 0 ≤ firstMode t y := norm_nonneg _

theorem continuousOn_firstMode (t : ℝ) : ContinuousOn (firstMode t) (Ioi 0) :=
  (continuousOn_modifiedBesselKOrder_scaled (by positivity : 0 < 2 * Real.pi) _).norm

/-! ## The Mellin test -/

/-- The test of the first mode against `y^{1+it}`. -/
def modeMellin (t : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ ((2 + (t : ℂ) * I) - 1) *
    modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I)

private theorem mellin_chamber (t : ℝ) : |((t : ℂ) * I).re| < (2 + (t : ℂ) * I).re := by
  simp

theorem integrableOn_modeMellin (t : ℝ) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ ((2 + (t : ℂ) * I) - 1) *
      modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I)) (Ioi 0) :=
  WeilWorkDeficitMellin.scaled_integrable (mellin_chamber t) (by positivity)

/-- **The exact size of the test.** `‖M‖² = (2π)⁻⁴ πt / sinh(πt)`. -/
theorem norm_modeMellin_sq {t : ℝ} (ht : t ≠ 0) :
    ‖modeMellin t‖ ^ 2 = (2 * Real.pi)⁻¹ ^ 4 * (Real.pi * t / Real.sinh (Real.pi * t)) := by
  have hm := WeilWorkDeficitMellin.scaled_mellin (mellin_chamber t)
    (show 0 < 2 * Real.pi by positivity)
  have h1 : (2 + (t : ℂ) * I + (t : ℂ) * I) / 2 = 1 + (t : ℂ) * I := by ring
  have h2 : (2 + (t : ℂ) * I - (t : ℂ) * I) / 2 = 1 := by ring
  have h3 : (2 + (t : ℂ) * I) - 2 = (t : ℂ) * I := by ring
  rw [h1, h2, h3, Complex.Gamma_one, mul_one] at hm
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hn1 : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I))‖ = (2 * Real.pi)⁻¹ ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    have hre : (-(2 + (t : ℂ) * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg hpi.le, inv_pow]
    norm_num
  have hn2 : ‖(2 : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 2 by norm_num) ((t : ℂ) * I)
    simpa using h
  have hG := norm_Gamma_one_add_mul_I_sq ht
  change ‖∫ y in Ioi (0 : ℝ), (y : ℂ) ^ ((2 + (t : ℂ) * I) - 1) *
    modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I)‖ ^ 2 = _
  rw [hm, norm_mul, norm_mul, hn1, hn2, one_mul, mul_pow, hG]
  ring

/-- `‖M‖² ≥ (2π)⁻⁴ 2πt e^{−πt}`. -/
theorem norm_modeMellin_sq_ge {t : ℝ} (ht : 0 < t) :
    (2 * Real.pi)⁻¹ ^ 4 * (2 * Real.pi * t * Real.exp (-(Real.pi * t))) ≤ ‖modeMellin t‖ ^ 2 := by
  rw [norm_modeMellin_sq ht.ne']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (by positivity)
  rw [le_div_iff₀ hs, Real.sinh_eq]
  have he : Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hp : 0 < Real.pi * t := by positivity
  have he2 : 0 < Real.exp (-(Real.pi * t)) := Real.exp_pos _
  have hk : Real.exp (-(Real.pi * t)) * (Real.exp (Real.pi * t) - Real.exp (-(Real.pi * t))) ≤ 1 := by
    have := mul_pos he2 he2
    nlinarith only [he, this]
  calc
    _ = Real.pi * t * (Real.exp (-(Real.pi * t)) *
        (Real.exp (Real.pi * t) - Real.exp (-(Real.pi * t)))) := by ring
    _ ≤ Real.pi * t * 1 := mul_le_mul_of_nonneg_left hk hp.le
    _ = _ := mul_one _

/-! ## The first mode off the main range -/

/-- Small arguments lose only the logarithm of the argument. -/
theorem norm_bessel_small {x τ : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) (hτ : 1 ≤ τ) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      Real.exp 1 * (Real.log (Real.pi * τ / x) + 1) * Real.exp (-(Real.pi * τ) / 2) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hτ0 : 0 < τ := by linarith only [hτ]
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = Real.pi / 2 - 1 / τ := ⟨_, rfl⟩
  have h1τ : 1 / τ ≤ 1 := by rw [div_le_one hτ0]; exact hτ
  have h1τ0 : 0 < 1 / τ := by positivity
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith only [h1τ, hπ3]
  have hθ : θ < Real.pi / 2 := by rw [hθdef]; linarith only [h1τ0]
  have hcosθ : Real.cos θ = Real.sin (1 / τ) := by rw [hθdef, Real.cos_pi_div_two_sub]
  have hsin : 2 / Real.pi * (1 / τ) ≤ Real.sin (1 / τ) :=
    Real.mul_le_sin h1τ0.le (by linarith only [h1τ, hπ3])
  have hbase := GaloisForLFunctions.RHTower.norm_modifiedBesselKOrder_I_mul_le_shifted hx0 τ hθ0 hθ
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = 2 * x / (Real.pi * τ) := ⟨_, rfl⟩
  have hy₀0 : 0 < y₀ := by rw [hy₀]; positivity
  have hy₀2 : y₀ ≤ 2 := by
    rw [hy₀, div_le_iff₀ (by positivity)]
    nlinarith only [hτ, hπ3, hx]
  have hxcos : y₀ ≤ x * Real.cos θ := by
    rw [hcosθ, hy₀]
    calc
      2 * x / (Real.pi * τ) = x * (2 / Real.pi * (1 / τ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsin hx0.le
  have hxcos0 : 0 < x * Real.cos θ := lt_of_lt_of_le hy₀0 hxcos
  have hint_le : (∫ t in Ioi (0 : ℝ), Real.exp (-(x * Real.cos θ) * Real.cosh t)) ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-y₀ * Real.cosh t) := by
    refine setIntegral_mono_on (GaloisForLFunctions.RHTower.integrableOn_exp_neg_mul_cosh_Ioi hxcos0)
      (GaloisForLFunctions.RHTower.integrableOn_exp_neg_mul_cosh_Ioi hy₀0) measurableSet_Ioi
      (fun t _ => ?_)
    apply Real.exp_le_exp.mpr
    have := Real.cosh_pos t
    nlinarith only [this, hxcos]
  have htail := GaloisForLFunctions.RHTower.integral_exp_neg_mul_cosh_le hy₀0 hy₀2
  have hlog : 2 / y₀ = Real.pi * τ / x := by
    rw [hy₀]
    field_simp
  rw [hlog] at htail
  have hexpθ : Real.exp (-τ * θ) = Real.exp 1 * Real.exp (-(Real.pi * τ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hθdef]
    field_simp
    ring
  calc
    _ ≤ Real.exp (-τ * θ) * ∫ t in Ioi (0 : ℝ), Real.exp (-(x * Real.cos θ) * Real.cosh t) := hbase
    _ ≤ Real.exp (-τ * θ) * (Real.log (Real.pi * τ / x) + 1) :=
      mul_le_mul_of_nonneg_left (hint_le.trans htail) (Real.exp_pos _).le
    _ = _ := by
      rw [hexpθ]
      ring

/-- Below height one the first mode is `O(log t · e^{−πt/2})`, against the weight `y`. -/
theorem mul_firstMode_le_of_le_one {t y : ℝ} (ht : 1 ≤ t) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    y * firstMode t y ≤ Real.exp 1 * (Real.log (Real.pi * t) + 2) * Real.exp (-(Real.pi * t) / 2) := by
  have hπ3 := Real.pi_gt_three
  have hπt : 1 ≤ Real.pi * t := by nlinarith only [hπ3, ht]
  have hlog := Real.log_nonneg hπt
  have hE : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi * t) / 2) := by positivity
  rcases le_or_gt 1 (2 * Real.pi * y) with hx | hx
  · have hb := GaloisForLFunctions.RHTower.norm_modifiedBesselKOrder_I_mul_le hx ht
    have hm : y * firstMode t y ≤ 1 * firstMode t y :=
      mul_le_mul_of_nonneg_right hy1 (firstMode_nonneg t y)
    rw [one_mul] at hm
    refine hm.trans (hb.trans ?_)
    nlinarith only [hE, mul_nonneg hE (show (0 : ℝ) ≤ 1 by norm_num)]
  · have hx0 : 0 < 2 * Real.pi * y := by positivity
    have hb := norm_bessel_small hx0 hx.le ht
    have hsplit : Real.log (Real.pi * t / (2 * Real.pi * y)) =
        Real.log (Real.pi * t) - Real.log (2 * Real.pi * y) := by
      rw [Real.log_div (by positivity) hx0.ne']
    obtain ⟨x, hxdef⟩ : ∃ x, x = 2 * Real.pi * y := ⟨_, rfl⟩
    rw [← hxdef] at hx hx0 hb hsplit
    have hxlog : -(x * Real.log x) ≤ 1 := by
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
      rw [Real.log_inv] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hx0.le
      have h3 : x * (x⁻¹ - 1) = 1 - x := by field_simp
      rw [h3] at h2
      nlinarith only [h2, hx0]
    have hyx : y * (-Real.log x) ≤ 1 := by
      have he : y * (-Real.log x) = (-(x * Real.log x)) / (2 * Real.pi) := by
        rw [hxdef]
        field_simp
      rw [he, div_le_one (by positivity)]
      linarith only [hxlog, hπ3]
    have hlin : y * (Real.log (Real.pi * t) + 1) ≤ 1 * (Real.log (Real.pi * t) + 1) :=
      mul_le_mul_of_nonneg_right hy1 (by linarith only [hlog])
    have hprod : y * (Real.log (Real.pi * t / x) + 1) ≤ Real.log (Real.pi * t) + 2 := by
      rw [hsplit]
      nlinarith only [hlin, hyx]
    calc
      _ ≤ y * (Real.exp 1 * (Real.log (Real.pi * t / x) + 1) * Real.exp (-(Real.pi * t) / 2)) :=
        mul_le_mul_of_nonneg_left hb hy0.le
      _ = Real.exp 1 * Real.exp (-(Real.pi * t) / 2) * (y * (Real.log (Real.pi * t / x) + 1)) := by ring
      _ ≤ Real.exp 1 * Real.exp (-(Real.pi * t) / 2) * (Real.log (Real.pi * t) + 2) :=
        mul_le_mul_of_nonneg_left hprod hE
      _ = _ := by ring

/-- Above height one the weighted first mode decays at rate five. -/
theorem mul_firstMode_le_exp {t y : ℝ} (hy : 1 ≤ y) :
    y * firstMode t y ≤ Real.exp 1 * Real.exp (-5 * y) := by
  have hπ3 := Real.pi_gt_three
  have hx : 1 ≤ 2 * Real.pi * y := by nlinarith only [hπ3, hy]
  have hb := norm_modifiedBesselKOrder_I_mul_le_exp hx t
  have hy0 : 0 < y := by linarith only [hy]
  have hyexp : y ≤ Real.exp y := by linarith only [Real.add_one_le_exp y]
  calc
    _ ≤ Real.exp y * (Real.exp 1 * Real.exp (-(2 * Real.pi * y))) :=
      mul_le_mul hyexp hb (firstMode_nonneg t y) (Real.exp_pos _).le
    _ = Real.exp 1 * Real.exp (y + -(2 * Real.pi * y)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      nlinarith only [hπ3, hy0]

/-- The test splits at heights `1` and `t`; only the middle range can carry its size. -/
theorem norm_modeMellin_le {t : ℝ} (ht : 1 ≤ t) :
    ‖modeMellin t‖ ≤
      Real.exp 1 * (Real.log (Real.pi * t) + 2) * Real.exp (-(Real.pi * t) / 2) +
        (∫ y in Ioc 1 t, y * firstMode t y) + Real.exp 1 * Real.exp (-5 * t) := by
  have hint := integrableOn_modeMellin t
  have hsub1 : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hsub2 : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hsub3 : Ioc 1 t ⊆ Ioi (1 : ℝ) := Ioc_subset_Ioi_self
  have hsub4 : Ioi t ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ht
  have hsplit1 := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
    measurableSet_Ioi (hint.mono_set hsub1) (hint.mono_set hsub2)
  have hsplit2 := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (1 : ℝ)) (b := t))
    measurableSet_Ioi ((hint.mono_set hsub2).mono_set hsub3) ((hint.mono_set hsub2).mono_set hsub4)
  rw [Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)] at hsplit1
  rw [Ioc_union_Ioi_eq_Ioi ht] at hsplit2
  have hnorm (y : ℝ) (hy : 0 < y) : ‖(y : ℂ) ^ ((2 + (t : ℂ) * I) - 1) *
      modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I)‖ = y * firstMode t y := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((2 + (t : ℂ) * I) - 1).re = 1 := by simp; norm_num
    rw [hre, Real.rpow_one]
    rfl
  unfold modeMellin
  rw [hsplit1, hsplit2, ← add_assoc]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (f := fun y : ℝ => (y : ℂ) ^ ((2 + (t : ℂ) * I) - 1) *
        modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I))
      (C := Real.exp 1 * (Real.log (Real.pi * t) + 2) * Real.exp (-(Real.pi * t) / 2))
      measure_Ioc_lt_top (fun y hy => by
        rw [hnorm y hy.1]
        exact mul_firstMode_le_of_le_one ht hy.1 hy.2)
    rw [Real.volume_real_Ioc_of_le (zero_le_one' ℝ)] at hb
    simpa using hb
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    exact hnorm y (by linarith only [hy.1])
  · have hi : IntegrableOn (fun y : ℝ => Real.exp 1 * Real.exp (-5 * y)) (Ioi t) :=
      (integrableOn_exp_mul_Ioi (by norm_num) t).const_mul _
    have hb := norm_integral_le_of_norm_le hi (f := fun y : ℝ => (y : ℂ) ^ ((2 + (t : ℂ) * I) - 1) *
        modifiedBesselKOrder (2 * Real.pi * y) ((t : ℂ) * I))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => by
        have hy1 : 1 ≤ y := ht.trans (le_of_lt hy)
        rw [hnorm y (by linarith only [hy1])]
        exact mul_firstMode_le_exp hy1))
    refine hb.trans ?_
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) t]
    have he : 0 < Real.exp 1 * Real.exp (-5 * t) := by positivity
    have : Real.exp 1 * (-Real.exp (-5 * t) / -5) = Real.exp 1 * Real.exp (-5 * t) / 5 := by ring
    rw [this]
    linarith only [he]

/-! ## From the test to the `L²` mass -/

/-- **Cauchy–Schwarz against `y^{3/2}`.** If the weighted first mode has mass at least `m` on `[1, t]`, its `L²` mass
is at least `4m²/t⁴`. -/
theorem integral_firstMode_sq_ge {t m : ℝ} (ht : 1 ≤ t) (hm0 : 0 ≤ m)
    (hm : m ≤ ∫ y in Ioc 1 t, y * firstMode t y) :
    4 * m ^ 2 / t ^ 4 ≤ ∫ y in Ioc 1 t, firstMode t y ^ 2 / y := by
  have ht0 : 0 < t := by linarith only [ht]
  have hcont : ContinuousOn (firstMode t) (Icc 1 t) :=
    (continuousOn_firstMode t).mono fun y hy => by
      have := hy.1
      exact show 0 < y by linarith only [this]
  have hi1 : IntegrableOn (fun y => y * firstMode t y) (Ioc 1 t) :=
    ((continuousOn_id.mul hcont).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun y => firstMode t y ^ 2 / y) (Ioc 1 t) := by
    refine ((hcont.pow 2).div continuousOn_id fun y hy => ?_).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
    have := hy.1
    exact (show 0 < y by linarith only [this]).ne'
  have hi3 : IntegrableOn (fun y : ℝ => y ^ 3) (Ioc 1 t) :=
    ((continuous_pow 3).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨l, hl⟩ : ∃ l, l = 4 * m / t ^ 4 := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  have hpt : (∫ y in Ioc 1 t, (2 * l * (y * firstMode t y) - l ^ 2 * y ^ 3)) ≤
      ∫ y in Ioc 1 t, firstMode t y ^ 2 / y := by
    refine setIntegral_mono_on ((hi1.const_mul _).sub (hi3.const_mul _)) hi2 measurableSet_Ioc
      fun y hy => ?_
    have hy0 : 0 < y := by linarith only [hy.1]
    have he : firstMode t y ^ 2 / y - (2 * l * (y * firstMode t y) - l ^ 2 * y ^ 3) =
        (firstMode t y - l * y ^ 2) ^ 2 / y := by
      field_simp
      ring
    have hn : 0 ≤ (firstMode t y - l * y ^ 2) ^ 2 / y := by positivity
    linarith only [he, hn]
  have hcube : (∫ y in Ioc 1 t, y ^ 3) ≤ t ^ 4 / 4 := by
    have h := integral_pow (a := (1 : ℝ)) (b := t) 3
    rw [intervalIntegral.integral_of_le ht] at h
    rw [h]
    norm_num
  rw [integral_sub (hi1.const_mul _) (hi3.const_mul _), integral_const_mul, integral_const_mul] at hpt
  refine le_trans ?_ hpt
  have hne : t ^ 4 ≠ 0 := by positivity
  have hval : 4 * m ^ 2 / t ^ 4 = 2 * l * m - l ^ 2 * (t ^ 4 / 4) := by
    rw [hl]
    field_simp
    ring
  rw [hval]
  have h1 := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * l by positivity)
  have h2 := mul_le_mul_of_nonneg_left hcube (show 0 ≤ l ^ 2 by positivity)
  linarith only [h1, h2]

/-! ## The Maass–Selberg norm controls the first mode -/

private theorem integrableOn_fd_norm_sq (u : ℂ) :
    IntegrableOn (fun z => ‖truncatedLineModel u 1 z‖ ^ 2) fd := by
  refine Measure.integrableOn_of_bounded volume_fd_ne_top
    ((measurable_truncatedLineModel u 1).norm.pow_const 2).aestronglyMeasurable
    (M := truncBound' u 1 ^ 2) ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Eventually.of_forall fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncatedLineModel_le_truncBound' u le_rfl hz) 2

/-- **The first Whittaker mode is paid by the Maass–Selberg norm.** -/
theorem eight_integral_firstMode_sq_le {t : ℝ} (ht : 0 < t) (ht1 : 1 ≤ t) :
    8 * (∫ y in Ioc 1 t, firstMode t y ^ 2 / y) ≤ (msLineValue t 1).re := by
  rw [← integral_norm_sq_truncatedLineModel_line ht le_rfl]
  let S : Set (ℝ × ℝ) := unitIcc ×ˢ Ioc 1 t
  let F : ℝ × ℝ → ℝ := fun p => ‖eisensteinLineTailPart t p.2 p.1‖ ^ 2
  have hSm : MeasurableSet S := measurableSet_Icc.prod measurableSet_Ioc
  have hpos : ∀ p ∈ S, 0 < p.2 := fun p hp => by
    have := hp.2.1
    exact show 0 < p.2 by linarith only [this]
  have hZ : {z : ℍ | (z.re, z.im) ∈ S} ⊆ fd := by
    intro z hz
    have hc : (z.re, z.im) ∈ cuspRect 1 := ⟨hz.1, hz.2.1⟩
    exact ((coord_mem_cuspRect_iff le_rfl z).mp hc).1
  have hsub := setIntegral_mono_set (integrableOn_fd_norm_sq ((t : ℂ) * I))
    (Eventually.of_forall fun z => by positivity) (HasSubset.Subset.eventuallyLE hZ)
  refine le_trans ?_ hsub
  have hval : (∫ z in {z : ℍ | (z.re, z.im) ∈ S}, ‖truncatedLineModel ((t : ℂ) * I) 1 z‖ ^ 2) =
      ∫ z in {z : ℍ | (z.re, z.im) ∈ S}, F (z.re, z.im) := by
    refine setIntegral_congr_fun (measurable_coordMap hSm) fun z hz => ?_
    have h1 : (1 : ℝ) < z.im := (show (z.re, z.im) ∈ S from hz).2.1
    have he : truncatedLineModel ((t : ℂ) * I) 1 z = eisensteinLineTailPart t z.im z.re := by
      unfold truncatedLineModel
      rw [if_pos h1]
      change d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * I) z.im +
        eisensteinLineTailPart t z.im z.re -
        d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * I) z.im = _
      ring
    simp only [F]
    rw [he]
  rw [hval, setIntegral_coord_eq_real hSm hpos F]
  -- Fubini on the compact rectangle.
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => F p / p.2 ^ 2) (unitIcc ×ˢ Icc 1 t) := by
    have hsubset : unitIcc ×ˢ Icc 1 t ⊆ {p : ℝ × ℝ | 1 / 2 < p.2} := fun p hp => by
      have := hp.2.1
      exact show 1 / 2 < p.2 by linarith only [this]
    refine ContinuousOn.div (((continuousOn_eisensteinLineTailPart_pair t).mono hsubset).norm.pow 2)
      (continuous_snd.continuousOn.pow 2) fun p hp => ?_
    have := hp.2.1
    exact pow_ne_zero 2 (show p.2 ≠ 0 by linarith only [this])
  have hcompact : IsCompact (unitIcc ×ˢ Icc (1 : ℝ) t) := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (fun p : ℝ × ℝ => F p / p.2 ^ 2) (unitIcc ×ˢ Ioc 1 t) := by
    exact (hcontF.integrableOn_compact hcompact).mono_set (prod_mono_right Ioc_subset_Icc_self)
  have hprod : Integrable (fun p : ℝ × ℝ => F p / p.2 ^ 2)
      ((volume.restrict unitIcc).prod (volume.restrict (Ioc 1 t))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint
  rw [setIntegral_prod_unitIcc hint, ← integral_const_mul]
  have hinner : IntegrableOn (fun y => ∫ x in unitIcc, F (x, y) / y ^ 2) (Ioc 1 t) :=
    hprod.integral_prod_right
  have hcont : ContinuousOn (firstMode t) (Icc 1 t) :=
    (continuousOn_firstMode t).mono fun y hy => by
      have := hy.1
      exact show 0 < y by linarith only [this]
  have hleft : IntegrableOn (fun y => 8 * (firstMode t y ^ 2 / y)) (Ioc 1 t) := by
    refine (((hcont.pow 2).div continuousOn_id fun y hy => ?_).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self).const_mul 8
    have := hy.1
    exact (show 0 < y by linarith only [this]).ne'
  refine setIntegral_mono_on hleft hinner measurableSet_Ioc fun y hy => ?_
  have hy1 : 1 < y := hy.1
  have hy0 : 0 < y := by linarith only [hy1]
  have hyh : 1 / 2 ≤ y := by linarith only [hy1]
  have hcontx : Continuous fun x : ℝ => ‖eisensteinLineTailPart t y x‖ ^ 2 :=
    (continuous_cuspTailPart_x t hyh).norm.pow 2
  have hper : Function.Periodic (fun x : ℝ => ‖eisensteinLineTailPart t y x‖ ^ 2) 1 := fun x => by
    simp only [eisensteinLineTailPart_periodic t y x]
  have hslice : (∫ x in unitIcc, F (x, y) / y ^ 2) =
      8 * (∑' N : ℕ, eisensteinLineModeSize t y N ^ 2) / y ^ 2 := by
    simp only [F]
    rw [integral_div]
    congr 1
    have hhalf : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
    rw [unitIcc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hhalf,
      intervalIntegral_half_eq_zero_one hper]
    exact intervalIntegral_normSq_eisensteinLineTailPart t hyh
  rw [hslice]
  have hmode : eisensteinLineModeSize t y 0 ^ 2 = y * firstMode t y ^ 2 := by
    unfold eisensteinLineModeSize firstMode
    have hc : ‖d4BMCompletedEisensteinWhittakerCoefficient ((t : ℂ) * I) ⟨0 + 1, by omega⟩‖ = 1 := by
      simp [d4BMCompletedEisensteinWhittakerCoefficient]
    rw [hc, one_mul, mul_pow, Real.sq_sqrt hy0.le]
    norm_num
  have hle := (summable_eisensteinLineModeSize_sq (t := t) hyh).le_tsum 0
    (fun N _ => sq_nonneg _)
  rw [hmode] at hle
  have hydiv : firstMode t y ^ 2 / y = y * firstMode t y ^ 2 / y ^ 2 := by
    field_simp
  rw [hydiv, mul_div_assoc']
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) (by positivity)

/-! ## The norm is quadratic in the boundary value -/

/-- **The upper side.** The Maass–Selberg value is at most `1400 e^{−πt} |ζ(1+2it)| log²(2t)`. -/
theorem msLineValue_re_le {t : ℝ} (ht : 100 ≤ t) :
    (msLineValue t 1).re ≤
      1400 * Real.exp (-(Real.pi * t)) * ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ *
        Real.log (2 * t) ^ 2 := by
  have ht0 : 0 < t := by linarith only [ht]
  have hs : (1 + 2 * ((t : ℂ) * I)) = ((1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = 1 + 2 * ((t : ℂ) * I) := ⟨_, rfl⟩
  have hsre : s.re = 1 := by rw [hsdef]; simp
  have hsim : s.im = 2 * t := by rw [hsdef]; simp
  have him : s.im ≠ 0 := by rw [hsim]; positivity
  have hne1 : s ≠ 1 := fun he => him (by rw [he]; simp)
  have hz : riemannZeta s ≠ 0 := hsdef ▸ boundary_zeta_ne_zero ht0
  have hzpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hz
  have hL2 : 2 ≤ Real.log (2 * t) := two_le_log_of_eight_le (by linarith only [ht])
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (2 * t) := ⟨_, rfl⟩
  rw [← hLdef] at hL2 ⊢
  -- The size of zeta and its derivative.
  have habs : |s.im| = 2 * t := by rw [hsim, abs_of_pos (by positivity)]
  have hzb : ‖riemannZeta s‖ ≤ 8 * L + 39 := by
    have h := norm_riemannZeta_le_log_near_one (s := s)
      (by
        rw [hsre, habs, ← hLdef]
        have : 0 < 1 / L := by positivity
        linarith only [this])
      (by rw [hsre]; norm_num) (by rw [habs]; linarith only [ht])
    rwa [habs, ← hLdef] at h
  have hdb : ‖deriv riemannZeta s‖ ≤ 110 * L ^ 2 := by
    have h := norm_deriv_riemannZeta_le_log_sq (s := s) (by rw [hsre]) (by rw [hsre]; norm_num)
      (by rw [habs]; linarith only [ht])
    rwa [habs, ← hLdef] at h
  -- The archimedean size.
  have hG : ‖Complex.Gammaℝ s‖ ^ 2 = 1 / Real.cosh (Real.pi * t) := by
    have h := gammaR_one_add_it_norm_sq (2 * t)
    have he : (1 : ℂ) + ((2 * t : ℝ) : ℂ) * I = s := by
      rw [hsdef]
      push_cast
      ring
    rw [he, show Real.pi * (2 * t) / 2 = Real.pi * t by ring] at h
    exact_mod_cast h
  have hG2 : ‖Complex.Gammaℝ s‖ ^ 2 ≤ 2 * Real.exp (-(Real.pi * t)) := by
    rw [hG, div_le_iff₀ (Real.cosh_pos _), Real.cosh_eq]
    have he : Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hp := mul_pos (Real.exp_pos (-(Real.pi * t))) (Real.exp_pos (-(Real.pi * t)))
    nlinarith only [he, hp]
  have hA : ‖eisLineLambda t‖ ^ 2 = ‖Complex.Gammaℝ s‖ ^ 2 * ‖riemannZeta s‖ ^ 2 := by
    unfold eisLineLambda reflectedCompletedLambda
    rw [← hsdef, norm_mul, mul_pow]
  -- The logarithmic derivative of `ξ`.
  have hlogxi : (logDeriv xi s).re ≤ L / 2 + 2 + ‖deriv riemannZeta s‖ / ‖riemannZeta s‖ := by
    have hre0 : 0 < s.re := by rw [hsre]; norm_num
    have he : logDeriv xi s = logDeriv archG s + logDeriv riemannZeta s := by
      rw [logDeriv_xi_fourFactor_offReal him hz, logDeriv_archG hre0 hne1]
    have hs' : s = ((1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by rw [hsdef, hs]
    have harch := ZeroConfigurationGeometry.norm_logDeriv_archG_sub_horizontalSlope_le_one
      (σ := 1) (X := 2 * t) one_pos (by linarith only [ht]) (by linarith only [ht])
    rw [← hs'] at harch
    have hslope := _root_.RHTower.norm_horizontalSlope_le (X := 2 * t) (by linarith only [ht])
    rw [← hLdef] at hslope
    have hG' : ‖logDeriv archG s‖ ≤ L / 2 + 2 := by
      have hsum : logDeriv archG s = (logDeriv archG s - horizontalSlope (2 * t)) +
          horizontalSlope (2 * t) := by ring
      rw [hsum]
      refine (norm_add_le _ _).trans ?_
      linarith only [harch, hslope]
    have hZ : ‖logDeriv riemannZeta s‖ = ‖deriv riemannZeta s‖ / ‖riemannZeta s‖ := by
      rw [logDeriv_apply, norm_div]
    rw [he]
    refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [hZ]
    linarith only [hG']
  have hval := msLineValue_one_re ht0
  rw [conj_eisLineLambda_mul_deriv_re ht0, ← hsdef] at hval
  rw [hval, ← hsdef]
  obtain ⟨G, hGdef⟩ : ∃ G, G = ‖Complex.Gammaℝ s‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = ‖riemannZeta s‖ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = ‖deriv riemannZeta s‖ := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x, x = Real.exp (-(Real.pi * t)) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hx0 : 0 < x := by rw [hxdef]; exact Real.exp_pos _
  rw [← hGdef, ← hxdef] at hG2
  rw [← hxdef, ← hZdef]
  rw [← hZdef] at hzb hzpos
  rw [← hDdef] at hdb
  rw [← hDdef, ← hZdef] at hlogxi
  have hA2 : ‖eisLineLambda t‖ ^ 2 = G * Z ^ 2 := by rw [hA, hGdef, hZdef]
  have hZ0 : 0 ≤ Z := hzpos.le
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have him2 : ((eisLineLambda t) ^ 2).im / t ≤ G * Z ^ 2 / 1 := by
    have h1 : ((eisLineLambda t) ^ 2).im ≤ ‖eisLineLambda t‖ ^ 2 := by
      have := Complex.abs_im_le_norm ((eisLineLambda t) ^ 2)
      rw [norm_pow] at this
      exact (le_abs_self _).trans this
    rw [hA2] at h1
    have hG2Z : 0 ≤ G * Z ^ 2 := by positivity
    calc
      _ ≤ (G * Z ^ 2) / t := div_le_div_of_nonneg_right h1 ht0.le
      _ ≤ G * Z ^ 2 / 1 := div_le_div_of_nonneg_left hG2Z one_pos (by linarith only [ht])
  rw [div_one] at him2
  have hmul : G * Z ^ 2 * ((logDeriv xi s).re - 1 / (1 + 4 * t ^ 2)) ≤
      G * Z * (Z * (L / 2 + 2) + D) := by
    have hfrac : 0 ≤ 1 / (1 + 4 * t ^ 2) := by positivity
    have h1 : (logDeriv xi s).re - 1 / (1 + 4 * t ^ 2) ≤ L / 2 + 2 + D / Z := by
      linarith only [hlogxi, hfrac]
    calc
      _ ≤ G * Z ^ 2 * (L / 2 + 2 + D / Z) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by
        field_simp
  rw [hA2]
  have hbr : Z * (2 * L + 9) + 4 * D ≤ 700 * L ^ 2 := by
    have h1 : Z * (2 * L + 9) ≤ (8 * L + 39) * (2 * L + 9) :=
      mul_le_mul_of_nonneg_right hzb (by linarith only [hL2])
    nlinarith only [h1, hdb, hL2]
  have hGZ : G * Z * (Z * (2 * L + 9) + 4 * D) ≤ 2 * x * Z * (700 * L ^ 2) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_right hG2 hZ0) hbr ?_ (by positivity)
    positivity
  have hsum : G * Z ^ 2 + 4 * (G * Z * (Z * (L / 2 + 2) + D)) = G * Z * (Z * (2 * L + 9) + 4 * D) := by
    ring
  have hfinal : 2 * x * Z * (700 * L ^ 2) = 1400 * x * Z * L ^ 2 := by ring
  linarith only [him2, hmul, hGZ, hsum, hfinal]

/-! ## The bound -/

/-- A logarithm against a square root, with room for all constants below. -/
private theorem seven_thousand_log_sq_le {t : ℝ} (ht : 10 ^ 7 ≤ t) :
    7396 * (Real.log t + 6) ^ 2 ≤ t := by
  have ht0 : 0 < t := by linarith only [ht]
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt t := ⟨_, rfl⟩
  have hr3000 : 3000 ≤ r := by
    rw [hr]
    exact Real.le_sqrt_of_sq_le (by nlinarith only [ht])
  have hr0 : 0 < r := by linarith only [hr3000]
  have hsq : r ^ 2 = t := by rw [hr, Real.sq_sqrt ht0.le]
  have hlog : Real.log t = 2 * Real.log r := by rw [← hsq, Real.log_pow]; norm_num
  have h1024 : Real.log (r / 1024) ≤ r / 1024 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hdiv : Real.log (r / 1024) = Real.log r - 10 * Real.log 2 := by
    rw [Real.log_div hr0.ne' (by norm_num), show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have hL : 86 * (Real.log t + 6) ≤ r := by
    rw [hlog]
    rw [hdiv] at h1024
    nlinarith only [h1024, hl2, hr3000]
  have hL0 : 0 ≤ Real.log t + 6 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ t by linarith only [ht])
    linarith only [this]
  have := pow_le_pow_left₀ (by positivity) hL 2
  rw [hsq] at this
  nlinarith only [this]

/-- The first mode carries at least half of the test on the middle range. -/
theorem half_norm_modeMellin_le {t : ℝ} (ht : 10 ^ 7 ≤ t) :
    ‖modeMellin t‖ / 2 ≤ ∫ y in Ioc 1 t, y * firstMode t y := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 < t := by linarith only [ht]
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(Real.pi * t) / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hEsq : Real.exp (-(Real.pi * t)) = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h5 : Real.exp (-5 * t) ≤ E := by
    rw [hE]
    apply Real.exp_le_exp.mpr
    nlinarith only [hπ4, ht0]
  have hlogπ : Real.log (Real.pi * t) ≤ Real.log t + 3 := by
    rw [Real.log_mul hπ0.ne' ht0.ne']
    have := Real.log_le_sub_one_of_pos hπ0
    linarith only [this, hπ4]
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log t + 6 := ⟨_, rfl⟩
  have hlogt := Real.log_nonneg ht1
  have hL0 : 0 ≤ L := by rw [hL]; linarith only [hlogt]
  have hsmall : Real.exp 1 * (Real.log (Real.pi * t) + 2) * E + Real.exp 1 * Real.exp (-5 * t) ≤
      Real.exp 1 * L * E := by
    have h1 : Real.exp 1 * Real.exp (-5 * t) ≤ Real.exp 1 * E :=
      mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
    have h2 : Real.exp 1 * (Real.log (Real.pi * t) + 2) * E ≤ Real.exp 1 * (L - 1) * E := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hE0.le
      rw [hL]
      linarith only [hlogπ]
    calc
      _ ≤ Real.exp 1 * (L - 1) * E + Real.exp 1 * E := add_le_add h2 h1
      _ = _ := by ring
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos (1 : ℝ)
  -- `(2e L E)² ≤ ‖M‖²`.
  have hM := norm_modeMellin_sq_ge ht0
  rw [hEsq] at hM
  have hkey : (2 * (Real.exp 1 * L * E)) ^ 2 ≤ ‖modeMellin t‖ ^ 2 := by
    refine le_trans ?_ hM
    have ht2 := seven_thousand_log_sq_le ht
    rw [← hL] at ht2
    have hπinv : (250 : ℝ)⁻¹ ≤ (2 * Real.pi)⁻¹ ^ 3 := by
      rw [inv_pow]
      refine inv_anti₀ (by positivity) ?_
      have h6 : 2 * Real.pi ≤ 6.3 := by linarith only [hπ4]
      have := pow_le_pow_left₀ (by positivity) h6 3
      norm_num at this ⊢
      linarith only [this]
    have heq : (2 * Real.pi)⁻¹ ^ 4 * (2 * Real.pi * t * E ^ 2) = (2 * Real.pi)⁻¹ ^ 3 * (t * E ^ 2) := by
      field_simp
    rw [heq]
    have hte : 0 ≤ t * E ^ 2 := by positivity
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hπinv hte)
    have he2 : Real.exp 1 ^ 2 ≤ 7.39 := by
      have := pow_le_pow_left₀ he0.le he.le 2
      norm_num at this ⊢
      linarith only [this]
    have hEL : 0 ≤ L ^ 2 * E ^ 2 := by positivity
    have : (2 * (Real.exp 1 * L * E)) ^ 2 = 4 * Real.exp 1 ^ 2 * (L ^ 2 * E ^ 2) := by ring
    rw [this]
    have h7 : 4 * Real.exp 1 ^ 2 * (L ^ 2 * E ^ 2) ≤ 4 * 7.39 * (L ^ 2 * E ^ 2) := by
      refine mul_le_mul_of_nonneg_right ?_ hEL
      linarith only [he2]
    have h8 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg E)
    have h9 : 0 ≤ L ^ 2 * E ^ 2 := hEL
    norm_num at h7 ⊢
    nlinarith only [h7, h8, h9]
  have hM0 := norm_nonneg (modeMellin t)
  have hlin : 2 * (Real.exp 1 * L * E) ≤ ‖modeMellin t‖ :=
    (sq_le_sq₀ (by positivity) hM0).mp hkey
  have hup := norm_modeMellin_le ht1
  rw [← hE] at hup
  linarith only [hup, hsmall, hlin]

/-- **The effective boundary bound.** The norm of the Eisenstein field at height one forces
`|ζ(1+2it)| ≥ 1 / (50000 t³ log²(2t))` for `t ≥ 10⁷`, with no use of the Euler product. -/
theorem norm_riemannZeta_boundary_lower {t : ℝ} (ht : 10 ^ 7 ≤ t) :
    1 / (50000 * t ^ 3 * Real.log (2 * t) ^ 2) ≤ ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 < t := by linarith only [ht]
  have hπ4 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hm := half_norm_modeMellin_le ht
  have hL2 := integral_firstMode_sq_ge ht1 (by positivity) hm
  have hms := eight_integral_firstMode_sq_le ht0 ht1
  have hup := msLineValue_re_le (show 100 ≤ t by linarith only [ht])
  have hM := norm_modeMellin_sq_ge ht0
  obtain ⟨x, hx⟩ : ∃ x, x = Real.exp (-(Real.pi * t)) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; exact Real.exp_pos _
  rw [← hx] at hup hM
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ := ⟨_, rfl⟩
  rw [← hZ] at hup ⊢
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (2 * t) := ⟨_, rfl⟩
  rw [← hLdef] at hup ⊢
  have hL0 : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by linarith only [ht])
  -- Combine the Mellin mass with the Maass–Selberg upper bound.
  have hsq : 4 * (‖modeMellin t‖ / 2) ^ 2 = ‖modeMellin t‖ ^ 2 := by ring
  rw [hsq] at hL2
  have ht4 : 0 < t ^ 4 := by positivity
  have hmass : (2 * Real.pi)⁻¹ ^ 3 * (x / t ^ 3) ≤ ‖modeMellin t‖ ^ 2 / t ^ 4 := by
    rw [le_div_iff₀ ht4]
    have he : (2 * Real.pi)⁻¹ ^ 3 * (x / t ^ 3) * t ^ 4 =
        (2 * Real.pi)⁻¹ ^ 4 * (2 * Real.pi * t * x) := by
      field_simp
    rw [he]
    exact hM
  have hchain : 8 * ((2 * Real.pi)⁻¹ ^ 3 * (x / t ^ 3)) ≤ 1400 * x * Z * L ^ 2 := by
    linarith only [hmass, hL2, hms, hup]
  have hπinv : (250 : ℝ)⁻¹ ≤ (2 * Real.pi)⁻¹ ^ 3 := by
    rw [inv_pow]
    refine inv_anti₀ (by positivity) ?_
    have h6 : 2 * Real.pi ≤ 6.3 := by linarith only [hπ4]
    have := pow_le_pow_left₀ (by positivity) h6 3
    norm_num at this ⊢
    linarith only [this]
  have hxt : 0 ≤ x / t ^ 3 := by positivity
  have hlow : 8 * ((250 : ℝ)⁻¹ * (x / t ^ 3)) ≤ 1400 * x * Z * L ^ 2 :=
    le_trans (by
      have := mul_le_mul_of_nonneg_right hπinv hxt
      linarith only [this]) hchain
  have hdiv : 1 / (43750 * t ^ 3) ≤ Z * L ^ 2 := by
    have hdx : x / t ^ 3 = x * (1 / t ^ 3) := by ring
    rw [hdx] at hlow
    have hcancel : x * (8 * 250⁻¹ * (1 / t ^ 3)) ≤ x * (1400 * (Z * L ^ 2)) := by
      calc
        _ = 8 * ((250 : ℝ)⁻¹ * (x * (1 / t ^ 3))) := by ring
        _ ≤ _ := hlow
        _ = _ := by ring
    have hc := le_of_mul_le_mul_left hcancel hx0
    have heq : 1 / (43750 * t ^ 3) = (8 * 250⁻¹ * (1 / t ^ 3)) / 1400 := by
      field_simp
      norm_num
    rw [heq, div_le_iff₀ (by norm_num)]
    linarith only [hc]
  have hLsq : 0 < L ^ 2 := by positivity
  have hfin : 1 / (43750 * t ^ 3) / L ^ 2 ≤ Z := by
    rw [div_le_iff₀ hLsq]
    exact hdiv
  refine le_trans ?_ hfin
  rw [div_div]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have ht3 : 0 < t ^ 3 := by positivity
  nlinarith only [mul_pos ht3 hLsq]

/-- `|ζ(1+it)| ≥ 1 / (6250 t³ log² t)` for `t ≥ 2·10⁷`. -/
theorem norm_riemannZeta_one_add_mul_I_lower {t : ℝ} (ht : 2 * 10 ^ 7 ≤ t) :
    1 / (6250 * t ^ 3 * Real.log t ^ 2) ≤ ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
  have h := norm_riemannZeta_boundary_lower (t := t / 2) (by linarith only [ht])
  have hs : (1 : ℂ) + 2 * (((t / 2 : ℝ) : ℂ) * I) = 1 + (t : ℂ) * I := by
    push_cast
    ring
  rw [hs, show 2 * (t / 2) = t by ring] at h
  refine le_trans (le_of_eq ?_) h
  rw [div_pow]
  ring

end MayerBoundaryNorm

end GaloisForLFunctions.RenormalizedIntersectionTheory
