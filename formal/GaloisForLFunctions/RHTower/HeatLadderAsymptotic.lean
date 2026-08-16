import GaloisForLFunctions.RHTower.HeatLadderCoefficients

/-!
# The all-order heat-aperture expansion

Truncating the Jonquière expansion after `K+1` regular terms leaves an energy error of order
`x^{(K+σ)/2}`, so the heat aperture energy agrees with the finite moment sum `heatLadderMoments`
to that order.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The uniform bound of the regular Jonquière polynomial on the window. -/
noncomputable def regPolyConst (s : ℂ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), ‖jonquiereRegCoeff s k‖ * Real.pi ^ k

theorem regPolyConst_nonneg (s : ℂ) (K : ℕ) : 0 ≤ regPolyConst s K := by
  refine Finset.sum_nonneg fun k _ => ?_
  have := Real.pi_pos
  positivity

theorem norm_jonquiereRegPoly_le (s : ℂ) (K : ℕ) {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    ‖jonquiereRegPoly s K θ‖ ≤ regPolyConst s K := by
  rw [jonquiereRegPoly, regPolyConst]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg θ) hθ k) (norm_nonneg _)

/-- The uniform bound of the all-order principal part. -/
noncomputable def germPrincipalOrderConst (s : ℂ) (K : ℕ) : ℝ :=
  ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + regPolyConst s K

theorem germPrincipalOrderConst_nonneg (s : ℂ) (K : ℕ) : 0 ≤ germPrincipalOrderConst s K := by
  have := regPolyConst_nonneg s K
  rw [germPrincipalOrderConst]
  positivity

theorem norm_germPrincipalOrder_le (s : ℂ) (K : ℕ) {θ : ℝ} (hne : θ ≠ 0) (hθ : |θ| ≤ Real.pi) :
    ‖germPrincipalOrder s K θ‖
      ≤ germPrincipalOrderConst s K * (|θ| ^ (s.re - 1) + 1) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hpow : ‖(((|θ| : ℝ)) : ℂ) ^ (s - 1)‖ = |θ| ^ (s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.one_re]
  have hnn : (0 : ℝ) ≤ |θ| ^ (s.re - 1) := Real.rpow_nonneg (abs_nonneg θ) _
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hpow]
  have hlead := norm_jonquiereLeadAt_le s θ
  have hreg := norm_jonquiereRegPoly_le s K hθ
  rw [germPrincipalOrderConst]
  nlinarith [norm_nonneg (jonquiereLead s), norm_nonneg (jonquiereLeadNeg s),
    regPolyConst_nonneg s K]

/-- The constant in the all-order quadratic error bound. -/
noncomputable def heatLadderErrorConst (s : ℂ) (K : ℕ) : ℝ :=
  jonquiereOrderConst s K
    * (2 * germPrincipalOrderConst s K + jonquiereOrderConst s K * Real.pi ^ (K + 1))

theorem heatLadderErrorConst_nonneg (s : ℂ) (K : ℕ) : 0 ≤ heatLadderErrorConst s K := by
  have h1 := jonquiereOrderConst_nonneg s K
  have h2 := germPrincipalOrderConst_nonneg s K
  have := Real.pi_pos
  rw [heatLadderErrorConst]
  positivity

/-- **The squared germ differs from its all-order principal part by `O(|θ|^{K+σ})`.** -/
theorem norm_germSqOrder_sub_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) :
    ∀ θ ∈ Ioc (-Real.pi) Real.pi, θ ≠ 0 →
      ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
          - germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)‖
        ≤ heatLadderErrorConst s K * (|θ| ^ ((K : ℝ) + s.re) + |θ| ^ ((K : ℝ) + 1)) := by
  intro θ hθ hne
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have habs : |θ| ≤ Real.pi := by
    rcases abs_cases θ with ⟨hv, _⟩ | ⟨hv, _⟩
    · rw [hv]; exact hθ.2
    · rw [hv]; linarith [hθ.1]
  have hd := norm_phaseGerm_sub_principalOrder_le h0 h1 K θ hθ hne
  have hp := norm_germPrincipalOrder_le s K hne habs
  have hCnn : 0 ≤ jonquiereOrderConst s K := jonquiereOrderConst_nonneg s K
  have hPnn : 0 ≤ germPrincipalOrderConst s K := germPrincipalOrderConst_nonneg s K
  have hrp : (0 : ℝ) ≤ |θ| ^ (s.re - 1) := Real.rpow_nonneg (abs_nonneg θ) _
  have hpowle : |θ| ^ (K + 1) ≤ Real.pi ^ (K + 1) :=
    pow_le_pow_left₀ (abs_nonneg θ) habs (K + 1)
  have hg : ‖phaseGerm s θ‖
      ≤ (germPrincipalOrderConst s K + jonquiereOrderConst s K * Real.pi ^ (K + 1))
        * (|θ| ^ (s.re - 1) + 1) := by
    have hsplit : ‖phaseGerm s θ‖
        ≤ ‖germPrincipalOrder s K θ‖ + ‖phaseGerm s θ - germPrincipalOrder s K θ‖ := by
      have := norm_add_le (germPrincipalOrder s K θ) (phaseGerm s θ - germPrincipalOrder s K θ)
      simpa using this
    have htail : jonquiereOrderConst s K * |θ| ^ (K + 1)
        ≤ (jonquiereOrderConst s K * Real.pi ^ (K + 1)) * (|θ| ^ (s.re - 1) + 1) := by
      have h1' : jonquiereOrderConst s K * |θ| ^ (K + 1)
          ≤ jonquiereOrderConst s K * Real.pi ^ (K + 1) :=
        mul_le_mul_of_nonneg_left hpowle hCnn
      nlinarith [mul_nonneg hCnn (pow_nonneg hpi.le (K + 1))]
    linarith [hsplit, hp, hd, htail]
  have hid : phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
      - germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)
      = (phaseGerm s θ - germPrincipalOrder s K θ) * (starRingEnd ℂ) (phaseGerm s θ)
        + germPrincipalOrder s K θ
          * (starRingEnd ℂ) (phaseGerm s θ - germPrincipalOrder s K θ) := by
    rw [map_sub]
    ring
  have hstep : ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
      - germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)‖
      ≤ ‖phaseGerm s θ - germPrincipalOrder s K θ‖
        * (‖phaseGerm s θ‖ + ‖germPrincipalOrder s K θ‖) := by
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    ring_nf
    nlinarith [norm_nonneg (phaseGerm s θ - germPrincipalOrder s K θ), norm_nonneg (phaseGerm s θ),
      norm_nonneg (germPrincipalOrder s K θ)]
  refine hstep.trans ?_
  set D : ℝ := 2 * germPrincipalOrderConst s K + jonquiereOrderConst s K * Real.pi ^ (K + 1)
    with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    have := mul_nonneg hCnn (pow_nonneg hpi.le (K + 1))
    linarith
  have hsum : ‖phaseGerm s θ‖ + ‖germPrincipalOrder s K θ‖ ≤ D * (|θ| ^ (s.re - 1) + 1) := by
    rw [hD]
    nlinarith [hg, hp]
  have hprod : |θ| ^ ((K : ℝ) + 1) * (|θ| ^ (s.re - 1) + 1)
      = |θ| ^ ((K : ℝ) + s.re) + |θ| ^ ((K : ℝ) + 1) := by
    rw [mul_add, mul_one, ← Real.rpow_add hpos]
    congr 2
    ring
  have hnatr : |θ| ^ (K + 1) = |θ| ^ ((K : ℝ) + 1) := by
    rw [← Real.rpow_natCast |θ| (K + 1)]
    congr 1
    push_cast
    ring
  calc ‖phaseGerm s θ - germPrincipalOrder s K θ‖
        * (‖phaseGerm s θ‖ + ‖germPrincipalOrder s K θ‖)
      ≤ (jonquiereOrderConst s K * |θ| ^ (K + 1)) * (D * (|θ| ^ (s.re - 1) + 1)) := by
        refine mul_le_mul hd hsum (by positivity) ?_
        exact mul_nonneg hCnn (pow_nonneg (abs_nonneg θ) (K + 1))
    _ = heatLadderErrorConst s K * (|θ| ^ ((K : ℝ) + s.re) + |θ| ^ ((K : ℝ) + 1)) := by
        rw [heatLadderErrorConst, ← hD, hnatr, ← hprod]
        ring

/-! ## Decay rates -/

theorem tendsto_rpow_neg_mul_exp {a : ℝ} (ha : 0 < a) (p : ℝ) :
    Tendsto (fun x : ℝ => x ^ (-p) * Real.exp (-(a / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  simp only [Function.comp_apply]
  rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
  congr 2
  field_simp

/-- The Gaussian main term of a real moment is an exact power of the aperture. -/
theorem norm_heatMomentTerm_ofReal {lam : ℝ} {x : ℝ} (hx : 0 < x) :
    ‖heatMomentTerm x ((lam : ℝ) : ℂ)‖
      = ((4 * Real.pi) ^ (lam / 2) * ‖Complex.Gamma ((((lam : ℝ) : ℂ) + 1) / 2)‖
          / Real.sqrt Real.pi) * x ^ (lam / 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbase : (((4 * Real.pi * x : ℝ)) : ℂ) ^ (((lam : ℝ) : ℂ) / 2)
      = (((4 * Real.pi : ℝ)) : ℂ) ^ (((lam : ℝ) : ℂ) / 2)
        * ((x : ℝ) : ℂ) ^ (((lam : ℝ) : ℂ) / 2) := by
    rw [show ((4 * Real.pi * x : ℝ) : ℂ) = (((4 * Real.pi : ℝ)) : ℂ) * ((x : ℝ) : ℂ) by
      push_cast; ring, Complex.mul_cpow_ofReal_nonneg (by positivity) hx.le]
  rw [heatMomentTerm, hbase]
  rw [norm_div, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < 4 * Real.pi),
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hre : ((((lam : ℝ) : ℂ) / 2)).re = lam / 2 := by
    simp
  rw [hre]
  ring

/-- The explicit exponentially small moment error from equation `(6)`. -/
noncomputable def heatMomentErr (lam x : ℝ) : ℝ :=
  (1 / Real.pi) * (x ^ (-(1 : ℝ) / 2)
    * (Real.exp (-(Real.pi / (4 * x))) * heatTailConst * (Real.pi ^ (lam + 1) / (lam + 1))
      + Real.exp (-(Real.pi / (8 * x)))
          * (1 / 2 * (8 * Real.pi * x) ^ ((lam + 1) / 2) * Real.Gamma ((lam + 1) / 2))))

theorem tendsto_heatMomentErr_div {lam : ℝ} (hlam : -1 < lam) :
    Tendsto (fun x : ℝ => heatMomentErr lam x / x ^ (lam / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT1 : Tendsto (fun x : ℝ =>
      (1 / Real.pi) * (heatTailConst * (Real.pi ^ (lam + 1) / (lam + 1)))
        * (x ^ (-((1 + lam) / 2)) * Real.exp (-((Real.pi / 4) / x))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (tendsto_rpow_neg_mul_exp (a := Real.pi / 4) (by positivity) ((1 + lam) / 2)).const_mul
      ((1 / Real.pi) * (heatTailConst * (Real.pi ^ (lam + 1) / (lam + 1))))
    rw [mul_zero] at h
    exact h
  have hT2 : Tendsto (fun x : ℝ =>
      (1 / Real.pi) * ((1 / 2 * Real.Gamma ((lam + 1) / 2)) * (8 * Real.pi) ^ ((lam + 1) / 2))
        * Real.exp (-((Real.pi / 8) / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (tendsto_exp_neg_div_nhdsGT_zero (a := Real.pi / 8) (by positivity)).const_mul
      ((1 / Real.pi) * ((1 / 2 * Real.Gamma ((lam + 1) / 2)) * (8 * Real.pi) ^ ((lam + 1) / 2)))
    rw [mul_zero] at h
    exact h
  have hsum := hT1.add hT2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hsplit : (8 * Real.pi * x) ^ ((lam + 1) / 2)
      = (8 * Real.pi) ^ ((lam + 1) / 2) * x ^ ((lam + 1) / 2) :=
    Real.mul_rpow (by positivity) hx0.le
  have he4 : Real.exp (-(Real.pi / (4 * x))) = Real.exp (-((Real.pi / 4) / x)) := by
    congr 2
    field_simp
  have he8 : Real.exp (-(Real.pi / (8 * x))) = Real.exp (-((Real.pi / 8) / x)) := by
    congr 2
    field_simp
  have h1 : x ^ (-1 / 2 + lam * (-1 / 2) : ℝ) * x ^ (lam * (1 / 2) : ℝ) = x ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h2 : x ^ (-1 / 2 : ℝ) * x ^ (1 / 2 + lam * (1 / 2) : ℝ) = x ^ (lam * (1 / 2) : ℝ) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [heatMomentErr, hsplit, he4, he8]
  field_simp
  ring_nf
  linear_combination (2 * (heatTailConst * Real.pi ^ (1 + lam)
      * Real.exp (Real.pi * x⁻¹ * (-1 / 4)) * (1 + lam)⁻¹)) * h1
    - (Real.Gamma (1 / 2 + lam * (1 / 2)) * (Real.pi * 8) ^ (1 / 2 + lam * (1 / 2))
      * Real.exp (Real.pi * x⁻¹ * (-1 / 8))) * h2

/-! ## The energy error -/

/-- **The all-order energy error bound.** -/
theorem norm_heatEnergy_sub_ladderMoments_le {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (K : ℕ)
    {x : ℝ} (hx : 0 < x) :
    ‖heatEnergy s x - heatLadderMoments s K x‖
      ≤ heatLadderErrorConst s K
        * (realHeatMoment x ((K : ℝ) + s.re) + realHeatMoment x ((K : ℝ) + 1)) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlam1 : (0 : ℝ) < (K : ℝ) + s.re := by
    have := Nat.cast_nonneg (α := ℝ) K
    linarith
  have hlam2 : (0 : ℝ) < (K : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) K
    linarith
  set C : ℝ := heatLadderErrorConst s K with hC
  have hCnn : 0 ≤ C := heatLadderErrorConst_nonneg s K
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hdiff : heatEnergy s x - heatLadderMoments s K x
      = (1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (-Real.pi) Real.pi,
          ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
            - (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)))
            * heatMultiplier x θ := by
    rw [heatEnergy, ← heatLadderMoments_eq h0 h1 hx K, ← mul_sub]
    congr 1
    rw [← MeasureTheory.integral_sub (integrableOn_germSq_mul_heatMultiplier h0 h1 hx)
      (integrableOn_principalOrderSq_mul_heatMultiplier h0 h1 hx K)]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    ring
  have hsrc : IntegrableOn
      (fun θ : ℝ => ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
        - (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)))
          * heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
    refine ((integrableOn_germSq_mul_heatMultiplier h0 h1 hx).sub
      (integrableOn_principalOrderSq_mul_heatMultiplier h0 h1 hx K)).congr ?_
    filter_upwards with θ
    simp only [Pi.sub_apply]
    ring
  have hmaj : IntegrableOn
      (fun θ : ℝ => C * (|θ| ^ ((K : ℝ) + s.re) * heatMultiplierValue x θ)
        + C * (|θ| ^ ((K : ℝ) + 1) * heatMultiplierValue x θ)) (Ioc (-Real.pi) Real.pi) :=
    ((integrableOn_rpow_mul_heatMultiplierValue hx hlam1).const_mul C).add
      ((integrableOn_rpow_mul_heatMultiplierValue hx hlam2).const_mul C)
  have hptwise : (fun θ : ℝ => ‖((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
        - (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)))
          * heatMultiplier x θ‖)
      ≤ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
        fun θ : ℝ => C * (|θ| ^ ((K : ℝ) + s.re) * heatMultiplierValue x θ)
          + C * (|θ| ^ ((K : ℝ) + 1) * heatMultiplierValue x θ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hne0] with θ hθ hne
    rw [norm_mul, norm_heatMultiplier hx]
    have hb := norm_germSqOrder_sub_le h0' h1 K θ hθ hne
    have hvn : 0 ≤ heatMultiplierValue x θ := heatMultiplierValue_nonneg hx θ
    calc ‖(phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
          - (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ))‖
          * heatMultiplierValue x θ
        ≤ (C * (|θ| ^ ((K : ℝ) + s.re) + |θ| ^ ((K : ℝ) + 1))) * heatMultiplierValue x θ :=
          mul_le_mul_of_nonneg_right hb hvn
      _ = C * (|θ| ^ ((K : ℝ) + s.re) * heatMultiplierValue x θ)
            + C * (|θ| ^ ((K : ℝ) + 1) * heatMultiplierValue x θ) := by ring
  have hstep : ‖∫ θ in Ioc (-Real.pi) Real.pi,
      ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
        - (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ)))
          * heatMultiplier x θ‖
      ≤ ∫ θ in Ioc (-Real.pi) Real.pi, (C * (|θ| ^ ((K : ℝ) + s.re) * heatMultiplierValue x θ)
          + C * (|θ| ^ ((K : ℝ) + 1) * heatMultiplierValue x θ)) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    exact MeasureTheory.setIntegral_mono_ae_restrict hsrc.norm hmaj hptwise
  have hval : (∫ θ in Ioc (-Real.pi) Real.pi,
      (C * (|θ| ^ ((K : ℝ) + s.re) * heatMultiplierValue x θ)
        + C * (|θ| ^ ((K : ℝ) + 1) * heatMultiplierValue x θ)))
      = C * (2 * Real.pi)
        * (realHeatMoment x ((K : ℝ) + s.re) + realHeatMoment x ((K : ℝ) + 1)) := by
    rw [MeasureTheory.integral_add
      ((integrableOn_rpow_mul_heatMultiplierValue hx hlam1).const_mul C)
      ((integrableOn_rpow_mul_heatMultiplierValue hx hlam2).const_mul C),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, realHeatMoment,
      realHeatMoment]
    field_simp
  rw [hdiff, norm_mul]
  have hnorm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  rw [hnorm]
  have hfin := mul_le_mul_of_nonneg_left (hstep.trans (le_of_eq hval))
    (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
  refine hfin.trans (le_of_eq ?_)
  field_simp

/-- **The all-order heat-aperture expansion `(1)`.**  Truncating the Jonquière expansion after
`K+1` regular terms leaves an energy error that vanishes in the small-aperture limit. -/
theorem tendsto_heatEnergy_sub_ladderMoments {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (K : ℕ) :
    Tendsto (fun x : ℝ => heatEnergy s x - heatLadderMoments s K x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hlam1 : (0 : ℝ) < (K : ℝ) + s.re := by
    have := Nat.cast_nonneg (α := ℝ) K
    linarith
  have hlam2 : (0 : ℝ) < (K : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) K
    linarith
  have hlim : Tendsto (fun x : ℝ => heatLadderErrorConst s K
      * (realHeatMoment x ((K : ℝ) + s.re) + realHeatMoment x ((K : ℝ) + 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsum := (tendsto_realHeatMoment hlam1).add (tendsto_realHeatMoment hlam2)
    rw [add_zero] at hsum
    have := hsum.const_mul (heatLadderErrorConst s K)
    rw [mul_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact norm_heatEnergy_sub_ladderMoments_le h0 h1 K hx

/-- **Every real window moment has the Gaussian decay rate.** -/
theorem isBigO_realHeatMoment {lam : ℝ} (hlam : -1 < lam) :
    (fun x : ℝ => realHeatMoment x lam) =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (lam / 2)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set A : ℝ := (4 * Real.pi) ^ (lam / 2) * ‖Complex.Gamma ((((lam : ℝ) : ℂ) + 1) / 2)‖
      / Real.sqrt Real.pi with hA
  have hle1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ 1 :=
    Filter.eventually_of_mem (nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))) fun x hx => hx
  have herr : ∀ᶠ x in 𝓝[>] (0 : ℝ), heatMomentErr lam x / x ^ (lam / 2) < 1 :=
    (tendsto_heatMomentErr_div hlam).eventually (gt_mem_nhds (by norm_num))
  rw [Asymptotics.isBigO_iff]
  refine ⟨A + 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hle1, herr] with x hx hx1 hx2
  have hx0 : (0 : ℝ) < x := hx
  have hxp : (0 : ℝ) < x ^ (lam / 2) := Real.rpow_pos_of_pos hx0 _
  have hlamre : ((((lam : ℝ)) : ℂ)).re = lam := by simp
  have hb := norm_heatMoment_sub_term_le (lam := (((lam : ℝ)) : ℂ)) (by rw [hlamre]; exact hlam)
    hx0 hx1
  rw [hlamre] at hb
  have hterm := norm_heatMomentTerm_ofReal (lam := lam) hx0
  have hsplit : realHeatMoment x lam
      ≤ ‖heatMomentTerm x ((lam : ℝ) : ℂ)‖ + heatMomentErr lam x := by
    rw [← norm_heatMoment_ofReal hx0 lam]
    have := norm_sub_le (heatMoment x ((lam : ℝ) : ℂ)) (heatMomentTerm x ((lam : ℝ) : ℂ))
    have h2 : ‖heatMoment x ((lam : ℝ) : ℂ)‖
        ≤ ‖heatMomentTerm x ((lam : ℝ) : ℂ)‖
          + ‖heatMoment x ((lam : ℝ) : ℂ) - heatMomentTerm x ((lam : ℝ) : ℂ)‖ := by
      have := norm_add_le (heatMomentTerm x ((lam : ℝ) : ℂ))
        (heatMoment x ((lam : ℝ) : ℂ) - heatMomentTerm x ((lam : ℝ) : ℂ))
      simpa using this
    refine h2.trans ?_
    have hbb : ‖heatMoment x ((lam : ℝ) : ℂ) - heatMomentTerm x ((lam : ℝ) : ℂ)‖
        ≤ heatMomentErr lam x := by
      rw [heatMomentErr]
      exact hb
    linarith
  have herrle : heatMomentErr lam x ≤ x ^ (lam / 2) := by
    have := (div_lt_one hxp).mp hx2
    linarith
  rw [Real.norm_of_nonneg (realHeatMoment_nonneg hx0 lam),
    Real.norm_of_nonneg hxp.le]
  rw [hterm] at hsplit
  nlinarith [hsplit, herrle, hxp]

/-- **The all-order heat-aperture expansion `(1)` with its truncation rate.** -/
theorem isBigO_heatEnergy_sub_ladderMoments {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (K : ℕ) :
    (fun x : ℝ => heatEnergy s x - heatLadderMoments s K x)
      =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (((K : ℝ) + s.re) / 2)) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hlam1 : (-1 : ℝ) < (K : ℝ) + s.re := by linarith
  have hlam2 : (-1 : ℝ) < (K : ℝ) + 1 := by linarith
  have hb1 := isBigO_realHeatMoment hlam1
  have hb2 := isBigO_realHeatMoment hlam2
  have hb3 : (fun x : ℝ => x ^ (((K : ℝ) + 1) / 2))
      =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (((K : ℝ) + s.re) / 2)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    have hle1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ 1 :=
      Filter.eventually_of_mem (nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))) fun x hx => hx
    filter_upwards [self_mem_nhdsWithin, hle1] with x hx hx1
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hsum : (fun x : ℝ => realHeatMoment x ((K : ℝ) + s.re) + realHeatMoment x ((K : ℝ) + 1))
      =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (((K : ℝ) + s.re) / 2)) := hb1.add (hb2.trans hb3)
  refine Asymptotics.IsBigO.trans ?_ hsum
  rw [Asymptotics.isBigO_iff]
  refine ⟨heatLadderErrorConst s K, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hnn : 0 ≤ realHeatMoment x ((K : ℝ) + s.re) + realHeatMoment x ((K : ℝ) + 1) :=
    add_nonneg (realHeatMoment_nonneg hx0 _) (realHeatMoment_nonneg hx0 _)
  rw [Real.norm_of_nonneg hnn]
  exact norm_heatEnergy_sub_ladderMoments_le h0 h1 K hx0

end RHTower
