import GaloisForLFunctions.ArtinMertens.TheTwistedVonMangoldtSeriesConvergesAtOne
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheExplicitFormulaForACharacter
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
import Mathlib.Analysis.Normed.Group.Tannery

/-! Match the smoothed primitive explicit formula to the host's centered Cesàro sum. -/

open Complex Filter Topology Finset WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

def zeroKernel (y : ℝ) (ρ : ℂ) : ℂ := ((y : ℂ) ^ ρ / (ρ * (ρ - 1))) / y

theorem zeroKernel_sum_eq_div (y : ℝ) :
    (∑' q : LZero χ, zeroKernel y q.point) =
      (∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))) / (y : ℂ) := by
  simp only [zeroKernel, tsum_div_const]

theorem norm_zeroKernel {y : ℝ} (hy : 0 < y) (ρ : ℂ) :
    ‖zeroKernel y ρ‖ = y ^ (ρ.re - 1) / (‖ρ‖ * ‖1 - ρ‖) := by
  rw [zeroKernel, norm_div, norm_div, norm_mul, norm_sub_rev ρ 1, Complex.norm_real,
    Real.norm_of_nonneg hy.le, Complex.norm_cpow_eq_rpow_re_of_pos hy, Real.rpow_sub_one hy.ne']
  ring

private theorem tendsto_zeroKernel_sum (hχ : χ ≠ 1) (hp : χ.IsPrimitive) :
    Tendsto (fun y : ℝ => ∑' q : LZero χ, zeroKernel y q.point) atTop (𝓝 0) := by
  let b (q : LZero χ) : ℝ := ‖(2 : ℂ) ^ q.point / (q.point * (q.point - 1))‖
  have hb : Summable b := (summable_cpow_div hχ hp (X := 2) (by norm_num)).norm
  have hpoint (q : LZero χ) : Tendsto (fun y : ℝ => zeroKernel y q.point) atTop (𝓝 0) := by
    have hre := (zero_re_mem hχ hp q).2
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hr := (tendsto_rpow_neg_atTop (sub_pos.mpr hre)).div_const (‖q.point‖ * ‖1 - q.point‖)
    simp only [zero_div, neg_sub] at hr
    refine hr.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (norm_zeroKernel hy _).symm
  have hmajor : ∀ᶠ y : ℝ in atTop, ∀ q : LZero χ, ‖zeroKernel y q.point‖ ≤ b q := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy q
    have hre := zero_re_mem hχ hp q
    rw [norm_zeroKernel (zero_lt_one.trans_le hy)]
    dsimp [b]
    have htwo := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) q.point
    rw [Complex.ofReal_ofNat] at htwo
    rw [norm_div, norm_mul, norm_sub_rev q.point 1, htwo]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact (Real.rpow_le_one_of_one_le_of_nonpos hy (sub_nonpos.mpr hre.2.le)).trans
      (Real.one_le_rpow (by norm_num) hre.1.le)
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb hpoint hmajor

omit [NeZero N] in
theorem sumLamChi_eq_ramp (χ : DirichletCharacter ℂ N) {y : ℝ} (hy : 1 ≤ y) :
    An.sumLamChi χ y = ∑ n ∈ Icc 1 ⌊y⌋₊, twistedVM χ n * ((y : ℂ) / n - 1) := by
  unfold An.sumLamChi
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨hn₁, hny⟩ := mem_Icc.mp hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn₁
  have hny' : (n : ℝ) ≤ y := (show (n : ℝ) ≤ ⌊y⌋₊ by exact_mod_cast hny).trans (Nat.floor_le (by linarith))
  rw [max_eq_left (sub_nonneg.mpr ((le_div_iff₀ hn₀).mpr (by simpa using hny')))]
  simp only [twistedVM, An.abelian₂, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one]
  ac_rfl

private theorem tendsto_ramp_div (hχ : χ ≠ 1) :
    Tendsto (fun y : ℝ => An.sumLamChi χ y / y) atTop (𝓝 (-An.logDerivativeAtOne χ)) := by
  have hM := GaloisForLFunctions.ArtinMertens.tendsto_sum_twist_vonMangoldt_div χ hχ
  have hP := GaloisForLFunctions.ArtinMertens.tendsto_twistPsi_div χ hχ
  rw [neg_div] at hM
  simpa only [sub_zero, An.logDerivativeAtOne] using (hM.sub hP).congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy₀ : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hy).ne'
    rw [sumLamChi_eq_ramp χ hy, GaloisForLFunctions.ArtinMertens.twistPsi]
    simp only [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    simp only [twistedVM]
    have hn₀ : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
    field_simp [hy₀, hn₀])

theorem smoothed_identity (hχ : χ ≠ 1) (hp : χ.IsPrimitive) :
    ∃ β : ℂ, ∀ y : ℝ, 1 < y →
      ‖An.gChi χ y + ∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1)) -
          (β + efGamma χ * Complex.log y)‖ ≤ efD / y := by
  obtain ⟨α, β, h⟩ := explicitFormula_uniform hχ hp
  have hα : α = -An.logDerivativeAtOne χ := by
    have hr := tendsto_ramp_div hχ
    have hz := tendsto_zeroKernel_sum hχ hp
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
    have hβ : Tendsto (fun y : ℝ => β / (y : ℂ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_zero, mul_zero] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hi).const_mul β
    have hlog : Tendsto (fun y : ℝ => Complex.log y / (y : ℂ)) atTop (𝓝 0) := by
      have ht := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have ht' := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
      refine ht'.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
      change ((Real.log y / y : ℝ) : ℂ) = _
      rw [Complex.ofReal_div, Complex.ofReal_log hy]
    have hl := ((hr.add hz).sub ((hβ.add (hlog.const_mul (efGamma χ))).add_const α))
    have hn := tendsto_norm.comp hl
    have hbound : ∀ᶠ y : ℝ in atTop,
        ‖An.sumLamChi χ y / y + (∑' q : LZero χ, zeroKernel y q.point) -
          (β / y + efGamma χ * (Complex.log y / y) + α)‖ ≤ efD / y / y := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      have hy₀ : 0 < y := zero_lt_one.trans hy
      have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₀.ne'
      have he := h y hy
      rw [← sumLamChi_eq_ramp χ hy.le] at he
      rw [zeroKernel_sum_eq_div]
      have halg (S Z L : ℂ) : S / (y : ℂ) + Z / y - (β / y + efGamma χ * (L / y) + α) =
          (S + Z - (α * (y : ℂ) + β + efGamma χ * L)) / y := by
        field_simp [hyc] <;> ring
      rw [halg, norm_div, Complex.norm_real, Real.norm_of_nonneg hy₀.le]
      exact div_le_div_of_nonneg_right he hy₀.le
    have hu : Tendsto (fun y : ℝ => efD / y / y) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (hi.const_mul efD).mul hi
    have hle := le_of_tendsto_of_tendsto hn hu hbound
    simp only [add_zero, zero_add, mul_zero] at hle
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp hle)).symm
  refine ⟨β, fun y hy => ?_⟩
  have he := h y hy
  rw [← sumLamChi_eq_ramp χ hy.le, hα] at he
  rw [An.gChi, if_neg hχ]
  convert he using 2 <;> ring

end

end QH
