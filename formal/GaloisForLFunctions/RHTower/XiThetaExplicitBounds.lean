import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit even theta-kernel bounds

The punctured even Jacobi theta kernel obeys the explicit decay
`evenKernel 0 t − 1 ≤ 3·e^{−πt}` for `t ≥ 1`: the integer series is
dominated termwise by the two-sided geometric series with ratio `e^{−πt}`,
whose total mass is `2r/(1−r) ≤ 3r` once `r ≤ 1/3`.  This is the explicit
head of the disc bounds for the completed zeta source. -/

open Real HurwitzZeta

namespace RHTower

noncomputable section

/-- `e^{−3} ≤ 1/3`. -/
theorem exp_neg_three_le : Real.exp (-3 : ℝ) ≤ 1 / 3 := by
  rw [Real.exp_neg]
  have h4 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  have hinv := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3)).mpr
    (by linarith : (3 : ℝ) ≤ Real.exp 3)
  rw [one_div]
  exact hinv

/-- **Explicit theta decay**: summing the theta series against the geometric
majorant with ratio bound `r` gives `evenKernel 0 t − 1 ≤ 2e^{−πt}/(1−r)` for
`t ≥ 1`.  The ratio bound is a free parameter: as `r → 0` the constant
approaches the exact leading coefficient `2`. -/
theorem evenKernel_zero_sub_one_le_of_le {t r : ℝ} (ht : 1 ≤ t)
    (hrr : Real.exp (-π * t) ≤ r) (hr1' : r < 1) :
    evenKernel 0 t - 1 ≤ 2 * Real.exp (-π * t) / (1 - r) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hr0 : 0 < Real.exp (-π * t) := Real.exp_pos _
  have hr1 : Real.exp (-π * t) < 1 := lt_of_le_of_lt hrr hr1'
  have h1mr : 0 < 1 - Real.exp (-π * t) := by linarith
  have hker' : HasSum (fun n : ℤ => if n = 0 then 0 else
      Real.exp (-π * (n : ℝ) ^ 2 * t)) (evenKernel 0 t - 1) := by
    simpa using hasSum_int_evenKernel₀ (0 : ℝ) ht0
  have hgeo := hasSum_geometric_of_lt_one hr0.le hr1
  have hnat : HasSum (fun n : ℕ => if n = 0 then 0 else
      Real.exp (-π * t) ^ n) ((1 - Real.exp (-π * t))⁻¹ - 1) := by
    have h := hasSum_ite_sub_hasSum hgeo 0
    simpa using h
  have hneg : HasSum (fun n : ℕ =>
      Real.exp (-π * t) ^ (n + 1)) ((1 - Real.exp (-π * t))⁻¹ - 1) := by
    have h := hgeo.mul_left (Real.exp (-π * t))
    have hval : Real.exp (-π * t) * (1 - Real.exp (-π * t))⁻¹ =
        (1 - Real.exp (-π * t))⁻¹ - 1 := by
      have hne := h1mr.ne'
      have h1 : Real.exp (-π * t) * (1 - Real.exp (-π * t))⁻¹ + 1 =
          (1 - Real.exp (-π * t))⁻¹ := by
        have hne' : 1 - Real.exp (-(π * t)) ≠ 0 := by
          rw [show -(π * t) = -π * t from by ring]
          exact h1mr.ne'
        field_simp
        ring
      linarith [h1]
    rw [hval] at h
    have hfun : (fun n : ℕ => Real.exp (-π * t) ^ (n + 1)) =
        fun n : ℕ => Real.exp (-π * t) * Real.exp (-π * t) ^ n := by
      funext n
      rw [pow_succ']
    rw [hfun]
    exact h
  have hcomp : HasSum (fun n : ℤ => if n = 0 then 0 else
      Real.exp (-π * t) ^ n.natAbs)
      (((1 - Real.exp (-π * t))⁻¹ - 1) +
        ((1 - Real.exp (-π * t))⁻¹ - 1)) := by
    apply HasSum.of_nat_of_neg_add_one
    · have hfun : (fun n : ℕ => if (n : ℤ) = 0 then 0 else
          Real.exp (-π * t) ^ ((n : ℤ)).natAbs) =
          fun n : ℕ => if n = 0 then 0 else
            Real.exp (-π * t) ^ n := by
        funext n
        simp [Int.natAbs_natCast]
      exact hfun ▸ hnat
    · have hfun : (fun n : ℕ => if (-((n : ℤ) + 1)) = 0 then 0 else
          Real.exp (-π * t) ^ ((-((n : ℤ) + 1))).natAbs) =
          fun n : ℕ => Real.exp (-π * t) ^ (n + 1) := by
        funext n
        have hne : (-((n : ℤ) + 1)) ≠ 0 := by omega
        have habs : ((-((n : ℤ) + 1))).natAbs = n + 1 := by omega
        rw [if_neg hne, habs]
      exact hfun ▸ hneg
  have hterm : ∀ n : ℤ, (if n = 0 then 0 else
      Real.exp (-π * (n : ℝ) ^ 2 * t)) ≤ (if n = 0 then 0 else
      Real.exp (-π * t) ^ n.natAbs) := by
    intro n
    rcases eq_or_ne n 0 with h0 | h0
    · simp [h0]
    · rw [if_neg h0, if_neg h0, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h1abs : (1 : ℝ) ≤ |(n : ℝ)| := by
        exact_mod_cast Int.one_le_abs h0
      have hA2 : (0 : ℝ) ≤ π * t * (((n : ℝ)) ^ 2 - |(n : ℝ)|) := by
        apply mul_nonneg (mul_pos Real.pi_pos ht0).le
        nlinarith [h1abs, sq_abs ((n : ℝ))]
      have hbridge : ((n.natAbs : ℝ)) = |(n : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hbridge]
      nlinarith [hA2]
  have hmain := hasSum_le hterm hker' hcomp
  have hfinal : ((1 - Real.exp (-π * t))⁻¹ - 1) +
      ((1 - Real.exp (-π * t))⁻¹ - 1) ≤
        2 * Real.exp (-π * t) / (1 - r) := by
    have hkey : (1 - Real.exp (-π * t))⁻¹ - 1 =
        Real.exp (-π * t) / (1 - Real.exp (-π * t)) := by
      have hne := h1mr.ne'
      have h1 : Real.exp (-π * t) / (1 - Real.exp (-π * t)) + 1 =
          (1 - Real.exp (-π * t))⁻¹ := by
        have hne' : 1 - Real.exp (-(π * t)) ≠ 0 := by
          rw [show -(π * t) = -π * t from by ring]
          exact h1mr.ne'
        field_simp
        ring
      linarith [h1]
    rw [hkey]
    have h2 : Real.exp (-π * t) / (1 - Real.exp (-π * t)) +
        Real.exp (-π * t) / (1 - Real.exp (-π * t)) =
        2 * Real.exp (-π * t) / (1 - Real.exp (-π * t)) := by
      ring
    rw [h2]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith)
      (by linarith)
  linarith [hmain, hfinal]

/-- The theta decay with the concrete ratio bound `1/3`. -/
theorem evenKernel_zero_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    evenKernel 0 t - 1 ≤ 3 * Real.exp (-π * t) := by
  have hr3 : Real.exp (-π * t) ≤ 1 / 3 := by
    have ht0 : (0 : ℝ) < t := by linarith
    have h1 : Real.exp (-π * t) ≤ Real.exp (-3) := by
      apply Real.exp_le_exp.mpr
      have hπ3 := Real.pi_gt_three
      nlinarith
    exact h1.trans exp_neg_three_le
  have h := evenKernel_zero_sub_one_le_of_le ht hr3 (by norm_num)
  calc evenKernel 0 t - 1 ≤ 2 * Real.exp (-π * t) / (1 - 1 / 3) := h
    _ = 3 * Real.exp (-π * t) := by ring

/-- The even kernel dominates its constant term. -/
theorem one_le_evenKernel_zero {t : ℝ} (ht : 0 < t) :
    1 ≤ evenKernel 0 t := by
  have hker : HasSum (fun n : ℤ => if n = 0 then 0 else
      Real.exp (-π * (n : ℝ) ^ 2 * t)) (evenKernel 0 t - 1) := by
    simpa using hasSum_int_evenKernel₀ (0 : ℝ) ht
  have h0 := hker.nonneg fun n => by positivity
  linarith

/-- Two-piece bound, outer part: for `t > 1` the modified kernel of the
even FE-pair is bounded by `3e^{−πt}`. -/
theorem norm_f_modif_le_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ 3 * Real.exp (-π * t) := by
  have hmem : t ∈ Set.Ioi (1 : ℝ) := ht
  have hnot : t ∉ Set.Ioo (0 : ℝ) 1 := by
    intro h
    exact absurd h.2 (by linarith)
  rw [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem hmem,
    Set.indicator_of_notMem hnot, add_zero]
  have hf : (hurwitzEvenFEPair 0).f t = ((evenKernel 0 t : ℝ) : ℂ) := rfl
  have hf₀ : (hurwitzEvenFEPair 0).f₀ = 1 := by
    simp [hurwitzEvenFEPair]
  rw [hf, hf₀]
  have hcast : ((evenKernel 0 t : ℝ) : ℂ) - 1 =
      (((evenKernel 0 t - 1 : ℝ)) : ℂ) := by
    push_cast
    ring
  have htpos : (0 : ℝ) < t := by linarith
  have hknn : (0 : ℝ) ≤ evenKernel 0 t - 1 := by
    linarith [one_le_evenKernel_zero htpos]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hknn]
  exact evenKernel_zero_sub_one_le ht.le

/-- Two-piece bound, inner part: for `0 < t < 1` the modified kernel is
bounded by `3t^{−1/2}e^{−π/t}` through the theta functional equation. -/
theorem norm_f_modif_le_of_lt_one {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      3 * t ^ (-(1 / 2) : ℝ) * Real.exp (-π / t) := by
  have hx1 : 1 < 1 / t := by
    rw [lt_div_iff₀ ht0]
    linarith
  have hxpos : 0 < 1 / t := by positivity
  have hFE := (hurwitzEvenFEPair 0).hf_modif_FE (1 / t) hxpos
  have harg : (1 : ℝ) / (1 / t) = t := by
    field_simp
  rw [harg] at hFE
  rw [hFE]
  have hg : (hurwitzEvenFEPair 0).g_modif (1 / t) =
      ((evenKernel 0 (1 / t) - 1 : ℝ) : ℂ) := by
    have hmem : (1 / t) ∈ Set.Ioi (1 : ℝ) := hx1
    have hnot : (1 / t) ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact absurd h.2 (by linarith)
    rw [WeakFEPair.g_modif, Pi.add_apply, Set.indicator_of_mem hmem,
      Set.indicator_of_notMem hnot, add_zero]
    have hgval : (hurwitzEvenFEPair 0).g (1 / t) =
        ((cosKernel 0 (1 / t) : ℝ) : ℂ) := rfl
    have hg₀ : (hurwitzEvenFEPair 0).g₀ = 1 := rfl
    rw [hgval, hg₀, ← evenKernel_eq_cosKernel_of_zero]
    push_cast
    ring
  rw [hg]
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
  rw [hε, hk]
  rw [norm_smul]
  have hkerbound := evenKernel_zero_sub_one_le hx1.le
  have hker_nonneg : 0 ≤ evenKernel 0 (1 / t) - 1 := by
    linarith [one_le_evenKernel_zero hxpos]
  have hnorm2 : ‖(((evenKernel 0 (1 / t) - 1 : ℝ)) : ℂ)‖ =
      evenKernel 0 (1 / t) - 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hker_nonneg]
  rw [hnorm2]
  have hnorm1 : ‖(1 : ℂ) * (((1 / t) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)‖ =
      (1 / t) ^ ((1 : ℝ) / 2) := by
    rw [one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  rw [hnorm1]
  have hpow : (1 / t) ^ ((1 : ℝ) / 2) = t ^ (-(1 / 2) : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one t, ← Real.rpow_mul ht0.le]
    norm_num
  rw [hpow]
  have hexp : Real.exp (-π * (1 / t)) = Real.exp (-π / t) := by
    congr 1
    ring
  calc t ^ (-(1 / 2) : ℝ) * (evenKernel 0 (1 / t) - 1)
      ≤ t ^ (-(1 / 2) : ℝ) * (3 * Real.exp (-π * (1 / t))) := by
        apply mul_le_mul_of_nonneg_left hkerbound
          (Real.rpow_nonneg ht0.le _)
    _ = 3 * t ^ (-(1 / 2) : ℝ) * Real.exp (-π / t) := by
        rw [hexp]
        ring

/-- Quartic exponential floor: `e^{−x} ≤ 24/x⁴` for `x > 0`. -/
theorem exp_neg_le_24_div_pow_four {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 24 / x ^ 4 := by
  have hsum := Real.sum_le_exp_of_nonneg hx.le 5
  have hterm : x ^ 4 / 24 ≤ Real.exp x := by
    calc x ^ 4 / 24
        = x ^ 4 / (4 : ℕ).factorial := by
          norm_num [Nat.factorial]
      _ ≤ ∑ i ∈ Finset.range 5, x ^ i / i.factorial := by
          apply Finset.single_le_sum
            (f := fun i : ℕ => x ^ i / (i.factorial : ℝ))
            (fun i _ => by positivity)
          norm_num
      _ ≤ Real.exp x := hsum
  have hex : 0 < Real.exp x := Real.exp_pos x
  have hx4 : 0 < x ^ 4 := by positivity
  have hmul : Real.exp (-x) * x ^ 4 ≤ 24 := by
    rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ hex]
    linarith [hterm]
  calc Real.exp (-x) = Real.exp (-x) * x ^ 4 / x ^ 4 := by
        field_simp
    _ ≤ 24 / x ^ 4 := by gcongr

/-- Outer exponential moment:
`∫_{1}^{∞} t·e^{−πt} dt = (1/π + 1/π²)·e^{−π}`. -/
theorem integral_Ioi_one_mul_exp_neg_pi :
    ∫ t in Set.Ioi (1 : ℝ), t * Real.exp (-π * t) =
      (1 / π + 1 / π ^ 2) * Real.exp (-π) := by
  have hπ := Real.pi_pos
  have hderiv : ∀ t ∈ Set.Ioi (1 : ℝ), HasDerivAt
      (fun u : ℝ => -(Real.exp (-π * u)) * (u / π + 1 / π ^ 2))
      (t * Real.exp (-π * t)) t := by
    intro t _
    have h0 : HasDerivAt (fun u : ℝ => -π * u) (-π) t := by
      simpa using (hasDerivAt_id t).const_mul (-π)
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-π * u))
        (Real.exp (-π * t) * (-π)) t :=
      (Real.hasDerivAt_exp (-π * t)).comp t h0
    have h2 : HasDerivAt (fun u : ℝ => u / π + 1 / π ^ 2) (1 / π) t := by
      simpa using ((hasDerivAt_id t).div_const π).add_const
        ((1 : ℝ) / π ^ 2)
    have h3 := (h1.neg).mul h2
    rw [show (fun u : ℝ => -(Real.exp (-π * u)) * (u / π + 1 / π ^ 2)) =
        (fun u : ℝ => -(Real.exp (-π * u))) * fun u => u / π + 1 / π ^ 2 by
      funext u
      rfl]
    apply h3.congr_deriv
    field_simp [Real.pi_ne_zero]
    simp only [Pi.neg_apply]
    ring_nf
  have hcont : ContinuousWithinAt
      (fun u : ℝ => -(Real.exp (-π * u)) * (u / π + 1 / π ^ 2))
      (Set.Ici 1) 1 := by
    apply Continuous.continuousWithinAt
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).neg).mul
      ((continuous_id.div_const π).add continuous_const)
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => t * Real.exp (-π * t)) (Set.Ioi 1) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := π) (by norm_num) le_rfl hπ
    have h' : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * Real.exp (-π * t)) (Set.Ioi 0) := by
      apply h.congr_fun ?_ measurableSet_Ioi
      intro t ht
      simp [Real.rpow_one]
    exact h'.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hscale : Filter.Tendsto (fun u : ℝ => π * u)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hπ Filter.tendsto_id
  have hA : Filter.Tendsto (fun u : ℝ => u * Real.exp (-π * u))
      Filter.atTop (nhds 0) := by
    have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n := 1)
    have hcomp := hbase.comp hscale
    have hfin := hcomp.const_mul (1 / π)
    rw [mul_zero] at hfin
    apply hfin.congr
    intro u
    simp only [Function.comp_apply, pow_one]
    have hne := hπ.ne'
    field_simp
  have hexp : Filter.Tendsto (fun u : ℝ => Real.exp (-π * u))
      Filter.atTop (nhds 0) := by
    have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n := 0)
    have hcomp := hbase.comp hscale
    apply hcomp.congr
    intro u
    simp only [Function.comp_apply, pow_zero, one_mul]
    congr 1
    ring
  have hlim : Filter.Tendsto
      (fun u : ℝ => -(Real.exp (-π * u)) * (u / π + 1 / π ^ 2))
      Filter.atTop (nhds 0) := by
    have hcombined := (hA.const_mul (-(1 / π))).add
      (hexp.const_mul (-(1 / π ^ 2)))
    rw [mul_zero, mul_zero, add_zero] at hcombined
    apply hcombined.congr
    intro u
    field_simp
    ring
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcont hderiv hint hlim
  rw [hFTC]
  rw [mul_one]
  field_simp
  ring

/-- Outer Mellin piece: for exponents `u ≤ 5/4` the weighted modified
kernel integrates over `(1,∞)` to at most `3(1/π + 1/π²)e^{−π}`. -/
theorem outer_mellin_piece_le {u : ℝ} (hu : u ≤ 5 / 4) :
    ∫ t in Set.Ioi (1 : ℝ),
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      3 * ((1 / π + 1 / π ^ 2) * Real.exp (-π)) := by
  have hπ := Real.pi_pos
  have hgint : MeasureTheory.IntegrableOn
      (fun t : ℝ => 3 * (t * Real.exp (-π * t))) (Set.Ioi 1) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := π) (by norm_num) le_rfl hπ
    have h' : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * Real.exp (-π * t)) (Set.Ioi 0) := by
      apply h.congr_fun ?_ measurableSet_Ioi
      intro t ht
      simp [Real.rpow_one]
    exact (h'.mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul 3
  have hle : ∀ t ∈ Set.Ioi (1 : ℝ),
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
        3 * (t * Real.exp (-π * t)) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hpow : t ^ (u - 1) ≤ t := by
      calc t ^ (u - 1) ≤ t ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
        _ = t := Real.rpow_one t
    have hker := norm_f_modif_le_of_one_lt ht1
    have hnn : 0 ≤ ‖(hurwitzEvenFEPair 0).f_modif t‖ := norm_nonneg _
    calc t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
        ≤ t * (3 * Real.exp (-π * t)) := by
          apply mul_le_mul hpow hker hnn ht0.le
      _ = 3 * (t * Real.exp (-π * t)) := by ring
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun t : ℝ =>
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
    (g := fun t : ℝ => 3 * (t * Real.exp (-π * t)))
    (μ := MeasureTheory.volume.restrict (Set.Ioi 1))
    (by
      apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards with t
      intro ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      positivity)
    hgint
    (by
      apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards with t
      intro ht
      exact hle t ht)
  calc ∫ t in Set.Ioi (1 : ℝ),
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ ∫ t in Set.Ioi (1 : ℝ), 3 * (t * Real.exp (-π * t)) := hmono
    _ = 3 * ∫ t in Set.Ioi (1 : ℝ), t * Real.exp (-π * t) :=
        MeasureTheory.integral_const_mul 3 _
    _ = 3 * ((1 / π + 1 / π ^ 2) * Real.exp (-π)) := by
        rw [integral_Ioi_one_mul_exp_neg_pi]

/-- The elementary inner weight integral: `∫_{(0,1)} t^{7/4} dt = 4/11`. -/
theorem integral_Ioo_rpow_seven_quarters :
    ∫ t in Set.Ioo (0 : ℝ) 1, t ^ ((7 : ℝ) / 4) = 4 / 11 := by
  have h := integral_rpow (a := 0) (b := 1) (r := 7 / 4)
    (Or.inl (by norm_num))
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [h]
  rw [Real.one_rpow, Real.zero_rpow (by norm_num : (7:ℝ)/4 + 1 ≠ 0)]
  norm_num

/-- The inner-piece majorant `72/π⁴ · t^{7/4}` is integrable on `(0,1)`. -/
private theorem integrableOn_inner_majorant :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => 72 / π ^ 4 * t ^ ((7 : ℝ) / 4)) (Set.Ioo 0 1) := by
  have h' : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ ((7 : ℝ) / 4)) (Set.Ioo 0 1) :=
    ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := 1) (r := 7 / 4) (by norm_num)).1).mono_set
      Set.Ioo_subset_Ioc_self
  exact h'.const_mul _

/-- **Inner-piece domination.**  On `(0,1)` the weighted modified-theta norm is at most
`72/π⁴ · t^{7/4}`: the kernel bound `3 t^{-1/2} e^{-π/t}` meets `e^{-π/t} ≤ 24 t⁴/π⁴`, and
`t^{u-3/2} ≤ t^{-9/4}` for `u ≥ -3/4`. -/
private theorem inner_integrand_le_majorant {u : ℝ} (hu : -(3 / 4) ≤ u) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
        72 / π ^ 4 * t ^ ((7 : ℝ) / 4) := by
  have hπ := Real.pi_pos

  intro t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : t < 1 := ht.2
  have hker := norm_f_modif_le_of_lt_one ht0 ht1
  have hpow0 : (0 : ℝ) ≤ t ^ (u - 1) := Real.rpow_nonneg ht0.le _
  have step1 : t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      t ^ (u - 1) * (3 * t ^ (-(1 / 2) : ℝ) * Real.exp (-π / t)) :=
    mul_le_mul_of_nonneg_left hker hpow0
  have hcollect : t ^ (u - 1) *
      (3 * t ^ (-(1 / 2) : ℝ) * Real.exp (-π / t)) =
      3 * t ^ (u - 3 / 2) * Real.exp (-π / t) := by
    rw [show t ^ (u - 1) * (3 * t ^ (-(1 / 2) : ℝ) *
        Real.exp (-π / t)) =
        3 * (t ^ (u - 1) * t ^ (-(1 / 2) : ℝ)) *
          Real.exp (-π / t) from by ring,
      ← Real.rpow_add ht0,
      show (u - 1) + (-(1 / 2) : ℝ) = u - 3 / 2 from by ring]
  have hexp4 : Real.exp (-π / t) ≤ 24 * t ^ (4 : ℝ) / π ^ 4 := by
    have hx : (0 : ℝ) < π / t := by positivity
    have h := exp_neg_le_24_div_pow_four hx
    have harg : -(π / t) = -π / t := by ring
    rw [harg] at h
    calc Real.exp (-π / t) ≤ 24 / (π / t) ^ 4 := h
      _ = 24 * t ^ (4 : ℝ) / π ^ 4 := by
          rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) from by norm_num,
            Real.rpow_natCast]
          field_simp
  have step2 : 3 * t ^ (u - 3 / 2) * Real.exp (-π / t) ≤
      3 * t ^ (-(9 / 4) : ℝ) * (24 * t ^ (4 : ℝ) / π ^ 4) := by
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 3)
      exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le
        (by linarith)
    · exact hexp4
    · positivity
    · positivity
  have hfinal : 3 * t ^ (-(9 / 4) : ℝ) * (24 * t ^ (4 : ℝ) / π ^ 4) =
      72 / π ^ 4 * t ^ ((7 : ℝ) / 4) := by
    rw [show (3 : ℝ) * t ^ (-(9 / 4) : ℝ) *
        (24 * t ^ (4 : ℝ) / π ^ 4) =
        72 / π ^ 4 * (t ^ (-(9 / 4) : ℝ) * t ^ (4 : ℝ)) from by ring,
      ← Real.rpow_add ht0]
    norm_num
  calc t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ t ^ (u - 1) * (3 * t ^ (-(1 / 2) : ℝ) * Real.exp (-π / t)) :=
        step1
    _ = 3 * t ^ (u - 3 / 2) * Real.exp (-π / t) := hcollect
    _ ≤ 3 * t ^ (-(9 / 4) : ℝ) * (24 * t ^ (4 : ℝ) / π ^ 4) := step2
    _ = 72 / π ^ 4 * t ^ ((7 : ℝ) / 4) := hfinal

/-- Inner Mellin piece: for exponents `u ≥ −3/4` the weighted modified
kernel integrates over `(0,1)` to at most `(72/π⁴)·(4/11)`. -/
theorem inner_mellin_piece_le {u : ℝ} (hu : -(3 / 4) ≤ u) :
    ∫ t in Set.Ioo (0 : ℝ) 1,
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      72 / π ^ 4 * (4 / 11) := by
  have hπ := Real.pi_pos
  have hgint := integrableOn_inner_majorant
  have hle := inner_integrand_le_majorant hu
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun t : ℝ =>
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
    (g := fun t : ℝ => 72 / π ^ 4 * t ^ ((7 : ℝ) / 4))
    (μ := MeasureTheory.volume.restrict (Set.Ioo 0 1))
    (by
      apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      filter_upwards with t
      intro ht
      have ht0 : (0 : ℝ) < t := ht.1
      positivity)
    hgint
    (by
      apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      filter_upwards with t
      intro ht
      exact hle t ht)
  calc ∫ t in Set.Ioo (0 : ℝ) 1,
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
          72 / π ^ 4 * t ^ ((7 : ℝ) / 4) := hmono
    _ = 72 / π ^ 4 * ∫ t in Set.Ioo (0 : ℝ) 1, t ^ ((7 : ℝ) / 4) :=
        MeasureTheory.integral_const_mul _ _
    _ = 72 / π ^ 4 * (4 / 11) := by
        rw [integral_Ioo_rpow_seven_quarters]

/-- The weighted norm integrand is integrable on the inner piece. -/
theorem inner_integrand_integrableOn {u : ℝ} (hu : -(3 / 4) ≤ u) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      (Set.Ioo 0 1) := by
  have hπ := Real.pi_pos
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (hurwitzEvenFEPair 0).f_modif
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
      ((hurwitzEvenFEPair 0).hf_modif_int.aestronglyMeasurable).mono_measure
        (MeasureTheory.Measure.restrict_mono Set.Ioo_subset_Ioi_self
          le_rfl)
    have h2 : ContinuousOn (fun t : ℝ => t ^ (u - 1)) (Set.Ioo 0 1) :=
      fun t ht => (Real.continuousAt_rpow_const t _
        (Or.inl (ne_of_gt ht.1))).continuousWithinAt
    exact (h2.aestronglyMeasurable measurableSet_Ioo).mul h1.norm
  apply MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => 72 / π ^ 4 * t ^ ((7 : ℝ) / 4))
    integrableOn_inner_majorant hmeas
  apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards with t
  intro ht
  have hnorm : ‖t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖‖ =
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _)
  rw [hnorm]
  exact inner_integrand_le_majorant hu t ht
/-- The weighted norm integrand is integrable on the outer piece. -/
theorem outer_integrand_integrableOn {u : ℝ} (hu : u ≤ 5 / 4) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      (Set.Ioi 1) := by
  have hπ := Real.pi_pos
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (hurwitzEvenFEPair 0).f_modif
        (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
      ((hurwitzEvenFEPair 0).hf_modif_int.aestronglyMeasurable).mono_measure
        (MeasureTheory.Measure.restrict_mono
          (Set.Ioi_subset_Ioi (by norm_num)) le_rfl)
    have h2 : ContinuousOn (fun t : ℝ => t ^ (u - 1)) (Set.Ioi 1) :=
      fun t ht => (Real.continuousAt_rpow_const t _
        (Or.inl (ne_of_gt (lt_trans one_pos ht)))).continuousWithinAt
    exact (h2.aestronglyMeasurable measurableSet_Ioi).mul h1.norm
  apply MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => 3 * (t * Real.exp (-π * t)))
    (by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := 1) (b := π) (by norm_num) le_rfl hπ
      have h' : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.exp (-π * t)) (Set.Ioi 0) := by
        apply h.congr_fun ?_ measurableSet_Ioi
        intro t ht
        simp [Real.rpow_one]
      exact (h'.mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul 3)
    hmeas
  apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t
  intro ht
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpow : t ^ (u - 1) ≤ t := by
    calc t ^ (u - 1) ≤ t ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
      _ = t := Real.rpow_one t
  have hker := norm_f_modif_le_of_one_lt ht1
  calc t ^ (u - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ t * (3 * Real.exp (-π * t)) :=
        mul_le_mul hpow hker (norm_nonneg _) ht0.le
    _ = 3 * (t * Real.exp (-π * t)) := by ring

/-- **Certified strip bound for the Mellin transform of the modified
kernel**: on `Re w ∈ [−¾, 5/4]` the transform is bounded by the sum of
the two certified piece constants. -/
theorem norm_mellin_f_modif_le {w : ℂ}
    (hw1 : -(3 / 4) ≤ w.re) (hw2 : w.re ≤ 5 / 4) :
    ‖mellin (hurwitzEvenFEPair 0).f_modif w‖ ≤
      72 / π ^ 4 * (4 / 11) +
        3 * ((1 / π + 1 / π ^ 2) * Real.exp (-π)) := by
  rw [mellin]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hcongr : (∫ t in Set.Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖) =
      ∫ t in Set.Ioi (0 : ℝ),
        t ^ (w.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.sub_re, Complex.one_re]
  rw [hcongr]
  have hsplit : Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, _⟩ | h1)
      · exact h0
      · linarith
    · intro h0
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr h
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_le.mpr hx.2)
  have hIci : MeasureTheory.IntegrableOn (fun t : ℝ =>
      t ^ (w.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      (Set.Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact outer_integrand_integrableOn hw2
  rw [← hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ici
    (inner_integrand_integrableOn hw1) hIci]
  have h1 := inner_mellin_piece_le (u := w.re) hw1
  have h2 := outer_mellin_piece_le (u := w.re) hw2
  have hIci_eq : (∫ t in Set.Ici (1 : ℝ),
      t ^ (w.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) =
      ∫ t in Set.Ioi (1 : ℝ),
        t ^ (w.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ :=
    MeasureTheory.integral_Ici_eq_integral_Ioi
  rw [hIci_eq]
  linarith [h1, h2]

/-- **Certified strip bound for the completed zeta source**: for
`Re s ∈ [−3/2, 5/2]`,
`‖Λ₀(s)‖ ≤ 72/π⁴·(4/11) + 3(1/π + 1/π²)e^{−π}`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ}
    (h1 : -(3 / 2) ≤ s.re) (h2 : s.re ≤ 5 / 2) :
    ‖completedRiemannZeta₀ s‖ ≤
      72 / π ^ 4 * (4 / 11) +
        3 * ((1 / π + 1 / π ^ 2) * Real.exp (-π)) := by
  have hdef : completedRiemannZeta₀ s =
      mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2 := by
    rw [completedRiemannZeta₀, completedHurwitzZetaEven₀,
      WeakFEPair.Λ₀]
  rw [hdef]
  have hre : (s / 2).re = s.re / 2 := by
    rw [Complex.div_re]
    simp
    ring
  have hb := norm_mellin_f_modif_le
    (w := s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2n]
  linarith [hb, norm_nonneg (mellin (hurwitzEvenFEPair 0).f_modif
    (s / 2))]

/-- Numeric evaluation of the certified strip constant: `≤ 2/5`. -/
theorem stripConstant_le_two_fifths :
    72 / π ^ 4 * (4 / 11) +
      3 * ((1 / π + 1 / π ^ 2) * Real.exp (-π)) ≤ 2 / 5 := by
  have hπ3 := Real.pi_gt_three
  have hπ := Real.pi_pos
  have h81 : (81 : ℝ) ≤ π ^ 4 := by
    have h9 : (9 : ℝ) ≤ π ^ 2 := by nlinarith
    nlinarith
  have hexp : Real.exp (-π) ≤ 1 / 20 := by
    have h1 : Real.exp (-π) ≤ Real.exp (-3) := by
      apply Real.exp_le_exp.mpr
      linarith
    have he := Real.exp_one_gt_d9
    have h20 : (20 : ℝ) ≤ Real.exp 3 := by
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h3]
      have hepos := Real.exp_pos 1
      have hsq : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by
        nlinarith [he]
      have hcube : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 := by
        nlinarith [he, hsq, hepos]
      nlinarith [hcube]
    have h2 : Real.exp (-3 : ℝ) ≤ 1 / 20 := by
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr h20
    linarith
  have hexp0 : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  have hA : 72 / π ^ 4 * (4 / 11) ≤ 288 / 891 := by
    rw [show (72 : ℝ) / π ^ 4 * (4 / 11) = 288 / (11 * π ^ 4) from by
      field_simp
      ring]
    apply div_le_div₀ (by norm_num) le_rfl (by nlinarith)
      (by nlinarith)
  have h1p : 1 / π ≤ 1 / 3 := by
    rw [one_div, one_div]
    exact (inv_le_inv₀ hπ (by norm_num)).mpr hπ3.le
  have h2p : 1 / π ^ 2 ≤ 1 / 9 := by
    rw [one_div, one_div]
    apply (inv_le_inv₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hB : 3 * ((1 / π + 1 / π ^ 2) * Real.exp (-π)) ≤
      3 * ((1 / 3 + 1 / 9) * (1 / 20)) := by
    apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
    apply mul_le_mul (by linarith) hexp hexp0 (by norm_num)
  have hAB : (288 : ℝ) / 891 + 3 * ((1 / 3 + 1 / 9) * (1 / 20)) ≤
      2 / 5 := by norm_num
  linarith

/-- The punctured kernel dominates twice its leading exponential:
`2e^{−πt} ≤ evenKernel 0 t − 1` for `t > 0`. -/
theorem two_exp_le_evenKernel_zero_sub_one {t : ℝ} (ht : 0 < t) :
    2 * Real.exp (-π * t) ≤ evenKernel 0 t - 1 := by
  have hker : HasSum (fun n : ℤ => if n = 0 then 0 else
      Real.exp (-π * (n : ℝ) ^ 2 * t)) (evenKernel 0 t - 1) := by
    simpa using hasSum_int_evenKernel₀ (0 : ℝ) ht
  have hpair : ((if (1 : ℤ) = 0 then 0 else
      Real.exp (-π * ((1 : ℤ) : ℝ) ^ 2 * t)) +
      (if (-1 : ℤ) = 0 then 0 else
      Real.exp (-π * ((-1 : ℤ) : ℝ) ^ 2 * t))) =
      2 * Real.exp (-π * t) := by
    norm_num
    ring
  have hsum2 : ∑ n ∈ ({1, -1} : Finset ℤ), (if n = 0 then 0 else
      Real.exp (-π * (n : ℝ) ^ 2 * t)) = 2 * Real.exp (-π * t) := by
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
    exact hpair
  have hle := hker.summable.sum_le_tsum ({1, -1} : Finset ℤ)
    (fun n _ => by
      rcases eq_or_ne n 0 with h | h
      · simp [h]
      · rw [if_neg h]
        positivity)
  rw [hsum2, hker.tsum_eq] at hle
  exact hle

/-- The FE-modified kernel is nonnegative on all of `(0, ∞)`. -/
theorem f_modif_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ ((hurwitzEvenFEPair 0).f_modif t).re ∧
      ((hurwitzEvenFEPair 0).f_modif t).im = 0 := by
  rcases lt_trichotomy t 1 with h1 | h1 | h1
  · have hx1 : 1 < 1 / t := by
      rw [lt_div_iff₀ ht]
      linarith
    have hxpos : 0 < 1 / t := by positivity
    have hFE := (hurwitzEvenFEPair 0).hf_modif_FE (1 / t) hxpos
    have harg : (1 : ℝ) / (1 / t) = t := by field_simp
    rw [harg] at hFE
    rw [hFE]
    have hg : (hurwitzEvenFEPair 0).g_modif (1 / t) =
        ((evenKernel 0 (1 / t) - 1 : ℝ) : ℂ) := by
      have hmem : (1 / t) ∈ Set.Ioi (1 : ℝ) := hx1
      have hnot : (1 / t) ∉ Set.Ioo (0 : ℝ) 1 := by
        intro h
        exact absurd h.2 (by linarith)
      rw [WeakFEPair.g_modif, Pi.add_apply, Set.indicator_of_mem hmem,
        Set.indicator_of_notMem hnot, add_zero]
      have hgval : (hurwitzEvenFEPair 0).g (1 / t) =
          ((cosKernel 0 (1 / t) : ℝ) : ℂ) := rfl
      have hg₀ : (hurwitzEvenFEPair 0).g₀ = 1 := rfl
      rw [hgval, hg₀, ← evenKernel_eq_cosKernel_of_zero]
      push_cast
      ring
    rw [hg]
    have hker : 0 ≤ evenKernel 0 (1 / t) - 1 := by
      linarith [one_le_evenKernel_zero hxpos]
    have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
    have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
    rw [hε, hk]
    have hrp : (0 : ℝ) ≤ (1 / t) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg hxpos.le _
    constructor
    · rw [smul_eq_mul, one_mul, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      exact mul_nonneg hrp hker
    · rw [smul_eq_mul, one_mul, ← Complex.ofReal_mul,
        Complex.ofReal_im]
  · subst h1
    have hval : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
      rw [WeakFEPair.f_modif, Pi.add_apply,
        Set.indicator_of_notMem (by simp : (1:ℝ) ∉ Set.Ioi (1:ℝ)),
        Set.indicator_of_notMem (by
          intro h
          exact absurd h.2 (by norm_num)), add_zero]
    rw [hval]
    simp
  · have hmem : t ∈ Set.Ioi (1 : ℝ) := h1
    have hnot : t ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact absurd h.2 (by linarith)
    rw [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem hmem,
      Set.indicator_of_notMem hnot, add_zero]
    have hf : (hurwitzEvenFEPair 0).f t = ((evenKernel 0 t : ℝ) : ℂ) :=
      rfl
    have hf₀ : (hurwitzEvenFEPair 0).f₀ = 1 := by
      simp [hurwitzEvenFEPair]
    rw [hf, hf₀]
    have hker : 0 ≤ evenKernel 0 t - 1 := by
      linarith [one_le_evenKernel_zero ht]
    constructor
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
      linarith
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.one_im]
      ring

/-- Exact outer norm of the modified kernel: for `t > 1` it is the centered
theta kernel itself. -/
theorem norm_f_modif_eq_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ = evenKernel 0 t - 1 := by
  have hmem : t ∈ Set.Ioi (1 : ℝ) := ht
  have hnot : t ∉ Set.Ioo (0 : ℝ) 1 := by
    intro h
    exact absurd h.2 (by linarith)
  rw [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem hmem,
    Set.indicator_of_notMem hnot, add_zero]
  have hf : (hurwitzEvenFEPair 0).f t = ((evenKernel 0 t : ℝ) : ℂ) := rfl
  have hf₀ : (hurwitzEvenFEPair 0).f₀ = 1 := by
    simp [hurwitzEvenFEPair]
  rw [hf, hf₀]
  have hcast : ((evenKernel 0 t : ℝ) : ℂ) - 1 =
      (((evenKernel 0 t - 1 : ℝ)) : ℂ) := by
    push_cast
    ring
  have htpos : (0 : ℝ) < t := by linarith
  have hknn : (0 : ℝ) ≤ evenKernel 0 t - 1 := by
    linarith [one_le_evenKernel_zero htpos]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hknn]

/-- Exact inner norm of the modified kernel: for `0 < t < 1` the theta
functional equation reflects it to the centered kernel at `1/t`. -/
theorem norm_f_modif_eq_of_lt_one {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ =
      t ^ (-(1 / 2) : ℝ) * (evenKernel 0 (1 / t) - 1) := by
  have hx1 : 1 < 1 / t := by
    rw [lt_div_iff₀ ht0]
    linarith
  have hxpos : 0 < 1 / t := by positivity
  have hFE := (hurwitzEvenFEPair 0).hf_modif_FE (1 / t) hxpos
  have harg : (1 : ℝ) / (1 / t) = t := by
    field_simp
  rw [harg] at hFE
  rw [hFE]
  have hg : (hurwitzEvenFEPair 0).g_modif (1 / t) =
      ((evenKernel 0 (1 / t) - 1 : ℝ) : ℂ) := by
    have hmem : (1 / t) ∈ Set.Ioi (1 : ℝ) := hx1
    have hnot : (1 / t) ∉ Set.Ioo (0 : ℝ) 1 := by
      intro h
      exact absurd h.2 (by linarith)
    rw [WeakFEPair.g_modif, Pi.add_apply, Set.indicator_of_mem hmem,
      Set.indicator_of_notMem hnot, add_zero]
    have hgval : (hurwitzEvenFEPair 0).g (1 / t) =
        ((cosKernel 0 (1 / t) : ℝ) : ℂ) := rfl
    have hg₀ : (hurwitzEvenFEPair 0).g₀ = 1 := rfl
    rw [hgval, hg₀, ← evenKernel_eq_cosKernel_of_zero]
    push_cast
    ring
  rw [hg]
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
  rw [hε, hk]
  rw [norm_smul]
  have hker_nonneg : 0 ≤ evenKernel 0 (1 / t) - 1 := by
    linarith [one_le_evenKernel_zero hxpos]
  have hnorm2 : ‖(((evenKernel 0 (1 / t) - 1 : ℝ)) : ℂ)‖ =
      evenKernel 0 (1 / t) - 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hker_nonneg]
  rw [hnorm2]
  have hnorm1 : ‖(1 : ℂ) * (((1 / t) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)‖ =
      (1 / t) ^ ((1 : ℝ) / 2) := by
    rw [one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  rw [hnorm1]
  have hpow : (1 / t) ^ ((1 : ℝ) / 2) = t ^ (-(1 / 2) : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one t, ← Real.rpow_mul ht0.le]
    norm_num
  rw [hpow]

end

end RHTower
