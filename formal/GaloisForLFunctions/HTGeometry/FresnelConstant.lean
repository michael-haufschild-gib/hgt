import GaloisForLFunctions.HTGeometry.FresnelDampedTail
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The half-log scattering constant

The improper Fresnel integral evaluates to the Watson constant:

`∫₀^∞ u^{-1/2} e^{iu} du = √π e^{iπ/4}`.

The proof compares the truncated integral with the damped Euler integral at scale `ε - i`, whose
value is `Γ(1/2)(ε-i)^{-1/2}` by the complex-scaled Euler evaluation.  Three estimates close the
comparison: the damped tail is `2R^{-1/2}` uniformly in `ε`, the damping error on `[0,R]` is at most
`(2/3) ε R^{3/2}`, and the scale value is continuous at `-i`.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem dampedKernel_sub_fresnelKernel_norm_le {ε u : ℝ} (hε : 0 ≤ ε) (hu : 0 < u) :
    ‖dampedKernel ((ε : ℂ) - I) u - fresnelKernel u‖ ≤ ε * u ^ ((1:ℝ)/2) := by
  have hsplit : dampedKernel ((ε : ℂ) - I) u
      = ((u ^ (-(1:ℝ)/2) : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * I) * ((Real.exp (-(ε * u)) : ℝ) : ℂ)) := by
    rw [dampedKernel]
    congr 1
    have harg : -(((ε : ℂ) - I) * (u : ℂ)) = (u : ℂ) * I + ((-(ε * u) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.ofReal_exp]
  have hdiff : dampedKernel ((ε : ℂ) - I) u - fresnelKernel u
      = ((u ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp ((u : ℂ) * I)
        * (((Real.exp (-(ε * u)) - 1 : ℝ)) : ℂ) := by
    rw [hsplit, fresnelKernel]
    push_cast
    ring
  have hnorm : ‖dampedKernel ((ε : ℂ) - I) u - fresnelKernel u‖
      = u ^ (-(1:ℝ)/2) * |Real.exp (-(ε * u)) - 1| := by
    rw [hdiff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Complex.norm_exp, abs_of_pos (Real.rpow_pos_of_pos hu _)]
    simp
  have hexp : |Real.exp (-(ε * u)) - 1| ≤ ε * u := by
    have hnn : 0 ≤ ε * u := by positivity
    have h1 : Real.exp (-(ε * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h2 : 1 - Real.exp (-(ε * u)) ≤ ε * u := by
      have := Real.add_one_le_exp (-(ε * u))
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [hnorm]
  have hpow : u ^ (-(1:ℝ)/2) * (ε * u) = ε * u ^ ((1:ℝ)/2) := by
    have hval : u ^ (-(1:ℝ)/2) * u = u ^ ((1:ℝ)/2) := by
      have h1 : u = u ^ (1:ℝ) := (Real.rpow_one u).symm
      calc u ^ (-(1:ℝ)/2) * u = u ^ (-(1:ℝ)/2) * u ^ (1:ℝ) := by rw [← h1]
        _ = u ^ (-(1:ℝ)/2 + 1) := (Real.rpow_add hu _ _).symm
        _ = u ^ ((1:ℝ)/2) := by ring_nf
    calc u ^ (-(1:ℝ)/2) * (ε * u) = (u ^ (-(1:ℝ)/2) * u) * ε := by ring
      _ = u ^ ((1:ℝ)/2) * ε := by rw [hval]
      _ = ε * u ^ ((1:ℝ)/2) := by ring
  calc u ^ (-(1:ℝ)/2) * |Real.exp (-(ε * u)) - 1|
      ≤ u ^ (-(1:ℝ)/2) * (ε * u) := by
        apply mul_le_mul_of_nonneg_left hexp (Real.rpow_pos_of_pos hu _).le
    _ = ε * u ^ ((1:ℝ)/2) := hpow

/-- The damping error on a bounded interval. -/
theorem norm_integral_damping_error_le {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) :
    ‖(∫ u in (0:ℝ)..R, dampedKernel ((ε : ℂ) - I) u) - ∫ u in (0:ℝ)..R, fresnelKernel u‖
      ≤ ε * ((2:ℝ)/3 * R ^ ((3:ℝ)/2)) := by
  have hintd : IntervalIntegrable (dampedKernel ((ε : ℂ) - I)) volume 0 R := by
    have hbase : IntervalIntegrable (fun u : ℝ => u ^ (-(1:ℝ)/2)) volume 0 R :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hmeas : AEStronglyMeasurable (dampedKernel ((ε : ℂ) - I))
        (volume.restrict (Set.uIoc 0 R)) := by
      apply Measurable.aestronglyMeasurable
      unfold dampedKernel
      fun_prop
    refine IntervalIntegrable.mono_fun hbase hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    have hu0 : 0 < u := by
      rw [Set.uIoc_of_le hR.le] at hu
      exact hu.1
    have hval : ‖dampedKernel ((ε : ℂ) - I) u‖ ≤ |u ^ (-(1:ℝ)/2)| := by
      rw [dampedKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hre : (-(((ε : ℂ) - I) * (u : ℂ))).re = -(ε * u) := by
        simp [Complex.mul_re]
      rw [hre]
      have hexp : Real.exp (-(ε * u)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hε, hu0]
      nlinarith [hexp, abs_nonneg (u ^ (-(1:ℝ)/2)), Real.exp_pos (-(ε * u))]
    rw [Real.norm_eq_abs]
    exact hval
  have hintf : IntervalIntegrable fresnelKernel volume 0 R :=
    intervalIntegrable_fresnelKernel 0 R
  have hmajor : IntervalIntegrable (fun u : ℝ => ε * u ^ ((1:ℝ)/2)) volume 0 R :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul ε
  rw [← intervalIntegral.integral_sub hintd hintf]
  have hbound : ‖∫ u in (0:ℝ)..R, (dampedKernel ((ε : ℂ) - I) u - fresnelKernel u)‖
      ≤ ∫ u in (0:ℝ)..R, ε * u ^ ((1:ℝ)/2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hR.le ?_ hmajor
    filter_upwards with u hu
    exact dampedKernel_sub_fresnelKernel_norm_le hε hu.1
  have hvalue : (∫ u in (0:ℝ)..R, ε * u ^ ((1:ℝ)/2)) = ε * ((2:ℝ)/3 * R ^ ((3:ℝ)/2)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    have hexp : (1:ℝ)/2 + 1 = (3:ℝ)/2 := by ring
    rw [hexp, Real.zero_rpow (by norm_num)]
    ring
  rw [hvalue] at hbound
  exact hbound

/-- The ray integral splits into a truncation and a tail. -/
theorem integral_Ioi_dampedKernel_split {c : ℂ} (hc : 0 < c.re) {R : ℝ} (hR : 0 < R) :
    (∫ u in Set.Ioi (0:ℝ), dampedKernel c u)
      = (∫ u in (0:ℝ)..R, dampedKernel c u) + ∫ u in Set.Ioi R, dampedKernel c u := by
  have hint := integrableOn_dampedKernel hc
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 R ∪ Set.Ioi R := (Set.Ioc_union_Ioi_eq_Ioi hR.le).symm
  have hdisj : Disjoint (Set.Ioc (0:ℝ) R) (Set.Ioi R) := Set.Ioc_disjoint_Ioi_same
  have hsub₁ : Set.Ioc (0:ℝ) R ⊆ Set.Ioi (0:ℝ) := fun x hx => hx.1
  have hsub₂ : Set.Ioi R ⊆ Set.Ioi (0:ℝ) := Set.Ioi_subset_Ioi hR.le
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi
      ((hint.mono_set hsub₁)) ((hint.mono_set hsub₂)),
    intervalIntegral.integral_of_le hR.le]

/-- The damped Euler value at the scale `ε - i`. -/
theorem integral_Ioi_dampedKernel_eq {ε : ℝ} (hε : 0 < ε) :
    (∫ u in Set.Ioi (0:ℝ), dampedKernel ((ε : ℂ) - I) u)
      = Complex.Gamma (1/2) / ((ε : ℂ) - I) ^ ((1:ℂ)/2) := by
  have hre : 0 < ((ε : ℂ) - I).re := by
    simp [hε]
  have h := gammaScaledIntegral_eq (a := (1/2 : ℂ)) (by norm_num) hre
  rw [gammaScaledIntegral] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact dampedKernel_eq_cpow ht

/-- **The half-log scattering constant.**  The improper Fresnel integral is the Euler value at the
boundary scale `-i`. -/
theorem tendsto_fresnelTruncated_value :
    Tendsto fresnelTruncated atTop (𝓝 (Complex.Gamma (1/2) / (-I) ^ ((1:ℂ)/2))) := by
  obtain ⟨S, hS⟩ := exists_tendsto_fresnelTruncated
  set L : ℂ := Complex.Gamma (1/2) / (-I) ^ ((1:ℂ)/2) with hL
  have hslit : (-I) ∈ Complex.slitPlane := by
    right
    simp
  have hcont : Tendsto (fun ε : ℝ => Complex.Gamma (1/2) / ((ε : ℂ) - I) ^ ((1:ℂ)/2))
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
    have hmap : Tendsto (fun ε : ℝ => ((ε : ℂ) - I)) (𝓝[>] (0:ℝ)) (𝓝 (-I)) := by
      have hbase : Tendsto (fun ε : ℝ => ((ε : ℂ) - I)) (𝓝 (0:ℝ)) (𝓝 ((0 : ℂ) - I)) := by
        exact ((Complex.continuous_ofReal.tendsto 0).sub tendsto_const_nhds)
      rw [zero_sub] at hbase
      exact hbase.mono_left nhdsWithin_le_nhds
    have hcpow : ContinuousAt (fun z : ℂ => z ^ ((1:ℂ)/2)) (-I) :=
      continuousAt_cpow_const hslit
    have hne : ((-I) : ℂ) ^ ((1:ℂ)/2) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      intro hcon
      simp at hcon
    have hcomp := (hcpow.tendsto.comp hmap)
    have hconst : Tendsto (fun _ : ℝ => Complex.Gamma (1/2)) (𝓝[>] (0:ℝ))
        (𝓝 (Complex.Gamma (1/2))) := tendsto_const_nhds
    have hdiv := hconst.div hcomp hne
    rw [hL]
    exact hdiv
  clear_value L
  have hkey : ∀ R : ℝ, 0 < R →
      ‖S - L‖ ≤ ‖S - fresnelTruncated R‖ + 2 * R ^ (-(1:ℝ)/2) := by
    intro R hR
    have hlimL : Tendsto
        (fun ε : ℝ => ‖S - Complex.Gamma (1/2) / ((ε : ℂ) - I) ^ ((1:ℂ)/2)‖)
        (𝓝[>] (0:ℝ)) (𝓝 ‖S - L‖) := (tendsto_const_nhds.sub hcont).norm
    have hrhs : Tendsto
        (fun ε : ℝ => ‖S - fresnelTruncated R‖ + ε * ((2:ℝ)/3 * R ^ ((3:ℝ)/2))
          + 2 * R ^ (-(1:ℝ)/2))
        (𝓝[>] (0:ℝ)) (𝓝 (‖S - fresnelTruncated R‖ + 2 * R ^ (-(1:ℝ)/2))) := by
      have hbase : Tendsto (fun ε : ℝ => ε * ((2:ℝ)/3 * R ^ ((3:ℝ)/2))) (𝓝[>] (0:ℝ))
          (𝓝 0) := by
        have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have hmul := hid.mul_const ((2:ℝ)/3 * R ^ ((3:ℝ)/2))
        rw [zero_mul] at hmul
        exact hmul
      have h2 := ((tendsto_const_nhds (x := ‖S - fresnelTruncated R‖)
        (f := 𝓝[>] (0:ℝ))).add hbase).add
        (tendsto_const_nhds (x := 2 * R ^ (-(1:ℝ)/2)))
      simpa using h2
    refine le_of_tendsto_of_tendsto hlimL hrhs ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hsplit := integral_Ioi_dampedKernel_split (c := (ε : ℂ) - I) (by simp [hε0]) hR
    have hval := integral_Ioi_dampedKernel_eq hε0
    rw [hsplit] at hval
    have herr := norm_integral_damping_error_le hε0.le hR
    have htail := norm_integral_Ioi_dampedKernel_le (c := (ε : ℂ) - I)
      (by
        have hnorm : ‖((ε : ℂ) - I)‖ ^ 2 = ε ^ 2 + 1 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp
          ring
        nlinarith [norm_nonneg ((ε : ℂ) - I), hnorm, sq_nonneg ε,
          sq_nonneg (‖((ε : ℂ) - I)‖ - 1)])
      (by simp [hε0]) hR
    have hrw : S - Complex.Gamma (1/2) / ((ε : ℂ) - I) ^ ((1:ℂ)/2)
        = (S - fresnelTruncated R)
          + (fresnelTruncated R - ∫ u in (0:ℝ)..R, dampedKernel ((ε : ℂ) - I) u)
          - ∫ u in Set.Ioi R, dampedKernel ((ε : ℂ) - I) u := by
      rw [← hval]
      ring
    have htri : ‖S - Complex.Gamma (1/2) / ((ε : ℂ) - I) ^ ((1:ℂ)/2)‖
        ≤ ‖S - fresnelTruncated R‖
          + ‖fresnelTruncated R - ∫ u in (0:ℝ)..R, dampedKernel ((ε : ℂ) - I) u‖
          + ‖∫ u in Set.Ioi R, dampedKernel ((ε : ℂ) - I) u‖ := by
      rw [hrw]
      have h1 := norm_sub_le
        ((S - fresnelTruncated R)
          + (fresnelTruncated R - ∫ u in (0:ℝ)..R, dampedKernel ((ε : ℂ) - I) u))
        (∫ u in Set.Ioi R, dampedKernel ((ε : ℂ) - I) u)
      have h2 := norm_add_le (S - fresnelTruncated R)
        (fresnelTruncated R - ∫ u in (0:ℝ)..R, dampedKernel ((ε : ℂ) - I) u)
      linarith [h1, h2]
    have herr' : ‖fresnelTruncated R - ∫ u in (0:ℝ)..R, dampedKernel ((ε : ℂ) - I) u‖
        ≤ ε * ((2:ℝ)/3 * R ^ ((3:ℝ)/2)) := by
      rw [fresnelTruncated, norm_sub_rev]
      exact herr
    linarith [htri, herr', htail]
  have hzero : ‖S - L‖ ≤ 0 := by
    have hlim : Tendsto (fun R : ℝ => ‖S - fresnelTruncated R‖ + 2 * R ^ (-(1:ℝ)/2))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => ‖S - fresnelTruncated R‖) atTop (𝓝 (0:ℝ)) := by
        have hsub : Tendsto (fun R : ℝ => S - fresnelTruncated R) atTop (𝓝 (0:ℂ)) := by
          have hd := (tendsto_const_nhds (x := S) (f := atTop (α := ℝ))).sub hS
          rw [sub_self] at hd
          exact hd
        have hn := hsub.norm
        rw [norm_zero] at hn
        exact hn
      have h2 : Tendsto (fun R : ℝ => 2 * R ^ (-(1:ℝ)/2)) atTop (𝓝 (0:ℝ)) := by
        have hbase : Tendsto (fun R : ℝ => R ^ (-(1:ℝ)/2)) atTop (𝓝 (0:ℝ)) := by
          have hb := tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)
          refine hb.congr fun R => ?_
          congr 1
          ring
        have hmul := hbase.const_mul (2:ℝ)
        rw [mul_zero] at hmul
        exact hmul
      have hadd := h1.add h2
      rw [add_zero] at hadd
      exact hadd
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    exact hkey R hR
  have hSL : S = L := by
    have hnz : ‖S - L‖ = 0 := le_antisymm hzero (norm_nonneg _)
    have hz : S - L = 0 := norm_eq_zero.mp hnz
    exact sub_eq_zero.mp hz
  rw [← hSL]
  exact hS

/-- The boundary scale value in closed form. -/
theorem gamma_half_div_neg_I_cpow :
    Complex.Gamma (1/2) / (-I) ^ ((1:ℂ)/2)
      = ((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I) := by
  have hcpow : (-I) ^ ((1:ℂ)/2) = Complex.exp (-((Real.pi : ℂ)/4) * I) := by
    rw [Complex.cpow_def_of_ne_zero (by simp), Complex.log_neg_I]
    congr 1
    ring
  have hne : Complex.exp (-((Real.pi : ℂ)/4) * I) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.Gamma_one_half_eq, hcpow]
  rw [div_eq_iff hne, mul_assoc, ← Complex.exp_add]
  have hsum : ((Real.pi/4 : ℝ) : ℂ) * I + -((Real.pi : ℂ)/4) * I = 0 := by
    push_cast
    ring
  rw [hsum, Complex.exp_zero, mul_one]

/-- **The Watson constant.**  `∫₀^∞ u^{-1/2} e^{iu} du = √π e^{iπ/4}`. -/
theorem tendsto_fresnelTruncated_sqrt_pi :
    Tendsto fresnelTruncated atTop
      (𝓝 (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))) := by
  rw [← gamma_half_div_neg_I_cpow]
  exact tendsto_fresnelTruncated_value

/-- **The quantitative Watson approximation.**  The truncation error of the Fresnel integral is
`2 R^{-1/2}`. -/
theorem norm_watson_sub_fresnelTruncated_le {R : ℝ} (hR : 0 < R) :
    ‖((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I) - fresnelTruncated R‖
      ≤ 2 * R ^ (-(1:ℝ)/2) := by
  set W : ℂ := ((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I) with hW
  have hlim : Tendsto (fun b : ℝ => ‖fresnelTruncated b - fresnelTruncated R‖) atTop
      (𝓝 ‖W - fresnelTruncated R‖) := by
    have hsub : Tendsto (fun b : ℝ => fresnelTruncated b - fresnelTruncated R) atTop
        (𝓝 (W - fresnelTruncated R)) := by
      rw [hW]
      exact tendsto_fresnelTruncated_sqrt_pi.sub tendsto_const_nhds
    exact hsub.norm
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop R] with b hb
  rw [fresnelTruncated_sub R b]
  exact norm_integral_fresnelKernel_le hR hb

end

end GaloisForLFunctions.HTGeometry
