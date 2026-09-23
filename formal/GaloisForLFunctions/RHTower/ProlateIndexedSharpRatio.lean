import GaloisForLFunctions.RHTower.ProlateIndexedSharpSideConditions

/-!
# The sharp amplitude ratio at the canonical family

`prolateBand_sq_ratio_sharp`, instantiated at `signedModeRadialData` with the pair anchor as the
matching point and the leakage collar as the collar.  Every hypothesis is eventual: the separation
facts and the exactness bundle as in the crude instantiation, the anchored barrier through
`prolateLogDeriv_le_anchoredBarrier_on_collar`, and the defect bound through
`prolateRiccatiDefect_le_one` fed by `eventually_pairAnchor_defect_condition`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The collar phase of a rung. -/
def sharpCollarPhase (k : ℕ) (a : ℝ) : ℝ :=
  signedModeRadialBandwidth a
    * bandEndpointPhase (signedModeRadialData a k).s prolateLeakageCollar

/-- The upper transport exponent of a rung on the window from the pair anchor to the collar. -/
def sharpTransportUpper (m n k : ℕ) (a : ℝ) : ℝ :=
  ∫ t in pairAnchorPoint m n a..prolateLeakageCollar,
    (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ))
        (prolateBandScale (signedModeRadialBandwidth a) (signedModeRadialData a k).s)
        (prolateBandScaleDeriv (signedModeRadialBandwidth a) (signedModeRadialData a k).s) t
      + prolateBandErrorMajorant (signedModeRadialBandwidth a) (signedModeRadialData a k).s
          (pairAnchorPoint m n a) prolateLeakageCollar t)

/-- The lower transport exponent of a rung on the same window. -/
def sharpTransportLower (m n k : ℕ) (a : ℝ) : ℝ :=
  ∫ t in pairAnchorPoint m n a..prolateLeakageCollar,
    (sturmSharpMajorant (fun t => 1 - t ^ (2 : ℕ))
        (prolateBandScale (signedModeRadialBandwidth a) (signedModeRadialData a k).s)
        (prolateBandScaleDeriv (signedModeRadialBandwidth a) (signedModeRadialData a k).s) t
      - prolateBandErrorMajorant (signedModeRadialBandwidth a) (signedModeRadialData a k).s
          (pairAnchorPoint m n a) prolateLeakageCollar t)

/-- **The sharp amplitude ratio, at the canonical family.** -/
theorem eventually_prolateBand_sq_ratio_sharp (m n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R (pairAnchorPoint m n a) ^ (2 : ℕ)
        ≤ 4050 * Real.pi ^ (3 : ℕ) * (sharpCollarPhase m a / sharpCollarPhase n a)
          * Real.exp (2 * sharpCollarPhase n a - 2 * sharpCollarPhase m a
            + sharpTransportUpper m n n a - sharpTransportLower m n m a)
          * (signedModeRadialData a m).R (pairAnchorPoint m n a) ^ (2 : ℕ) := by
  set x₀ : ℝ := prolatePairAnchor m n with hx₀def
  have hx₀ : 0 < x₀ := prolatePairAnchor_pos m n
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hcollar : 600 * (1 - prolateLeakageCollar) ≤ 1 / 4 := prolateLeakageCollar_collar
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  have hclarge : ∀ᶠ a : ℝ in atTop,
      x₀ ^ (2 : ℕ) / prolateLeakageCollar ^ (2 : ℕ) ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop _
  have hcfloor : ∀ᶠ a : ℝ in atTop, 1 / collarPhaseFloor ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcTop.eventually_ge_atTop (1 : ℝ), hclarge, hcfloor,
    eventually_signedModeRadialData_s_pos n,
    eventually_signedModeRadialData_s_le n (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_signedModeRadialData_s_nonneg m,
    eventually_signedModeRadialData_s_le m (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_two_mul_s_le_pairAnchorPoint_sq m n n (Or.inr rfl),
    eventually_two_mul_s_le_pairAnchorPoint_sq m n m (Or.inl rfl),
    eventually_pairAnchor_defect_condition m n n (Or.inr rfl),
    eventually_pairAnchor_defect_condition m n m (Or.inl rfl)]
    with a hapos hc1a hclargea hcfloora hsn0 hsn8 hsm0 hsm8 h2sn h2sm hdefn hdefm
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hc0 : 0 < c := by linarith
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ (2 : ℕ) = x₀ ^ (2 : ℕ) / c := pairAnchorPoint_sq hc0
  have hy₀α : y₀ ≤ prolateLeakageCollar := by
    have hsq : y₀ ^ (2 : ℕ) ≤ prolateLeakageCollar ^ (2 : ℕ) := by
      rw [hy₀sq, div_le_iff₀ hc0]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < prolateLeakageCollar ^ (2 : ℕ))] at hclargea
      linarith [hclargea]
    nlinarith [hy₀0, hαh]
  have hsy0n : (signedModeRadialData a n).s < y₀ ^ (2 : ℕ) := by nlinarith [h2sn, hsn0]
  have hsy0m : (signedModeRadialData a m).s < y₀ ^ (2 : ℕ) := by
    rcases eq_or_lt_of_le hsm0 with h | h
    · rw [← h]
      positivity
    · nlinarith [h2sm, h]
  have hsn1 : (signedModeRadialData a n).s < 1 := by linarith
  have hsm1 : (signedModeRadialData a m).s < 1 := by linarith
  -- the exactness bundles
  have hExn := signedModeRadialData_isExact_of_pos hapos n
  have hExm := signedModeRadialData_isExact_of_pos hapos m
  have hsmn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a n).R :=
    hExn.2.2.2.2.2.1
  have hsmm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a m).R :=
    hExm.2.2.2.2.2.1
  have hRn1 : (signedModeRadialData a n).R 1 = 1 := hExn.2.2.2.2.2.2.2.1
  have hRm1 : (signedModeRadialData a m).R 1 = 1 := hExm.2.2.2.2.2.2.2.1
  have heign : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c (signedModeRadialData a n).R y
        = -((signedModeRadialData a n).s * c ^ (2 : ℕ)) * (signedModeRadialData a n).R y := by
    have hchi : (signedModeRadialData a n).chi = -((signedModeRadialData a n).s * c ^ (2 : ℕ)) := by
      have hs := hExn.2.2.2.2.2.2.2.2.2.2.1
      rw [← hcdef] at hs
      have hcne : c ≠ 0 := hc0.ne'
      rw [hs, radialSeparationRatio]
      field_simp
    intro y _
    rw [hExn.2.2.2.2.2.2.2.2.2.1 y, hchi]
  have heigm : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c (signedModeRadialData a m).R y
        = -((signedModeRadialData a m).s * c ^ (2 : ℕ)) * (signedModeRadialData a m).R y := by
    have hchi : (signedModeRadialData a m).chi = -((signedModeRadialData a m).s * c ^ (2 : ℕ)) := by
      have hs := hExm.2.2.2.2.2.2.2.2.2.2.1
      rw [← hcdef] at hs
      have hcne : c ≠ 0 := hc0.ne'
      rw [hs, radialSeparationRatio]
      field_simp
    intro y _
    rw [hExm.2.2.2.2.2.2.2.2.2.1 y, hchi]
  have hoden : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv (signedModeRadialData a n).R) x
      + 2 * x * deriv (signedModeRadialData a n).R x
      - ((signedModeRadialData a n).s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ))
        * (signedModeRadialData a n).R x = 0 := hExn.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hodem : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv (signedModeRadialData a m).R) x
      + 2 * x * deriv (signedModeRadialData a m).R x
      - ((signedModeRadialData a m).s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ))
        * (signedModeRadialData a m).R x = 0 := hExm.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- positivity
  have hsqrtn : Real.sqrt (signedModeRadialData a n).s ≤ y₀ := by
    have := Real.sqrt_le_sqrt hsy0n.le
    rwa [Real.sqrt_sq hy₀0.le] at this
  have hsqrtm : Real.sqrt (signedModeRadialData a m).s ≤ y₀ := by
    have := Real.sqrt_le_sqrt hsy0m.le
    rwa [Real.sqrt_sq hy₀0.le] at this
  have hposn : ∀ t ∈ Icc y₀ 1, 0 < (signedModeRadialData a n).R t := by
    intro t ht
    exact prolate_pos_on_right_of_radial_turning hsn0.le hsmn heign hRn1 t
      ⟨le_trans hsqrtn ht.1, ht.2⟩
  have hposm : ∀ t ∈ Icc y₀ 1, 0 < (signedModeRadialData a m).R t := by
    intro t ht
    exact prolate_pos_on_right_of_radial_turning hsm0 hsmm heigm hRm1 t
      ⟨le_trans hsqrtm ht.1, ht.2⟩
  -- barriers and defects
  have hbarn : ∀ y ∈ Icc y₀ prolateLeakageCollar,
      prolateLogDeriv (signedModeRadialData a n).R y
        ≤ prolateAnchoredBarrier c (-((signedModeRadialData a n).s * c ^ (2 : ℕ))) y :=
    prolateLogDeriv_le_anchoredBarrier_on_collar hc0 hsn1 hy₀0 hy₀α hα1 h2sn hsn0.le hsmn
      heign hRn1 hposn
  have hbarm : ∀ y ∈ Icc y₀ prolateLeakageCollar,
      prolateLogDeriv (signedModeRadialData a m).R y
        ≤ prolateAnchoredBarrier c (-((signedModeRadialData a m).s * c ^ (2 : ℕ))) y :=
    prolateLogDeriv_le_anchoredBarrier_on_collar hc0 hsm1 hy₀0 hy₀α hα1 h2sm hsm0 hsmm
      heigm hRm1 hposm
  have hδn : ∀ y ∈ Icc y₀ prolateLeakageCollar,
      prolateRiccatiDefect c (signedModeRadialData a n).s y ≤ 1 := by
    intro y hy
    exact prolateRiccatiDefect_le_one hc0 hy₀0 hsn1 hsy0n hy.1 hy.2 hα1 hdefn
  have hδm : ∀ y ∈ Icc y₀ prolateLeakageCollar,
      prolateRiccatiDefect c (signedModeRadialData a m).s y ≤ 1 := by
    intro y hy
    exact prolateRiccatiDefect_le_one hc0 hy₀0 hsm1 hsy0m hy.1 hy.2 hα1 hdefm
  -- collar phases
  have hzn : 0 < c * bandEndpointPhase (signedModeRadialData a n).s prolateLeakageCollar := by
    have hpos := collarPhaseFloor_le (s := (signedModeRadialData a n).s) hsn8
    have := collarPhaseFloor_pos
    nlinarith [hpos, hc0]
  have hzm : 1 ≤ c * bandEndpointPhase (signedModeRadialData a m).s prolateLeakageCollar := by
    have hpos := collarPhaseFloor_le (s := (signedModeRadialData a m).s) hsm8
    have hκ := collarPhaseFloor_pos
    have hone : 1 ≤ c * collarPhaseFloor := by
      rw [div_le_iff₀ hκ] at hcfloora
      linarith [hcfloora]
    nlinarith [hone, hpos, hc0]
  exact prolateBand_sq_ratio_sharp hc0 hy₀0 hy₀α hαh hα1 hcollar hsn0 hsn8 hsy0n hsm0 hsm8 hsy0m
    hsmn heign hoden hRn1 hposn hbarn hδn hsmm heigm hodem hRm1 hposm hbarm hδm hzn hzm


/-- **The anchor scale-logarithm converges.**  The bandwidth cancels between the two apertures, so
the difference of the two logarithms at the pair anchor tends to a constant of the two indices. -/
theorem tendsto_pairAnchor_scaleLog (m n : ℕ) :
    Tendsto (fun a : ℝ =>
        Real.log (pairAnchorPoint m n a ^ (2 : ℕ) - (signedModeRadialData a m).s)
          - Real.log (pairAnchorPoint m n a ^ (2 : ℕ) - (signedModeRadialData a n).s))
      atTop (𝓝 (Real.log (prolatePairAnchor m n ^ (2 : ℕ) - (4 * (m : ℝ) + 1))
        - Real.log (prolatePairAnchor m n ^ (2 : ℕ) - (4 * (n : ℝ) + 1)))) := by
  set x₀ : ℝ := prolatePairAnchor m n with hx₀def
  have hxm : 4 * (4 * (m : ℝ) + 1) < x₀ ^ (2 : ℕ) := prolatePairAnchor_sq_gt m n m (Or.inl rfl)
  have hxn : 4 * (4 * (n : ℝ) + 1) < x₀ ^ (2 : ℕ) := prolatePairAnchor_sq_gt m n n (Or.inr rfl)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hgapm : (0 : ℝ) < x₀ ^ (2 : ℕ) - (4 * (m : ℝ) + 1) := by linarith
  have hgapn : (0 : ℝ) < x₀ ^ (2 : ℕ) - (4 * (n : ℝ) + 1) := by linarith
  have hsm := tendsto_signedModeRadialBandwidth_mul_s_atTop m
  have hsn := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hlm : Tendsto (fun a : ℝ => Real.log (x₀ ^ (2 : ℕ) - signedModeRadialBandwidth a
      * (signedModeRadialData a m).s)) atTop
      (𝓝 (Real.log (x₀ ^ (2 : ℕ) - (4 * (m : ℝ) + 1)))) := by
    refine (Real.continuousAt_log hgapm.ne').tendsto.comp ?_
    exact tendsto_const_nhds.sub hsm
  have hln : Tendsto (fun a : ℝ => Real.log (x₀ ^ (2 : ℕ) - signedModeRadialBandwidth a
      * (signedModeRadialData a n).s)) atTop
      (𝓝 (Real.log (x₀ ^ (2 : ℕ) - (4 * (n : ℝ) + 1)))) := by
    refine (Real.continuousAt_log hgapn.ne').tendsto.comp ?_
    exact tendsto_const_nhds.sub hsn
  have hhm : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a m).s < x₀ ^ (2 : ℕ) / 2 := by
    refine hsm.eventually (eventually_lt_nhds ?_)
    linarith
  have hhn : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s < x₀ ^ (2 : ℕ) / 2 := by
    refine hsn.eventually (eventually_lt_nhds ?_)
    linarith
  refine (hlm.sub hln).congr' ?_
  filter_upwards [tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ), hhm, hhn]
    with a hc1 hham hhan
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  have hsq : pairAnchorPoint m n a ^ (2 : ℕ) = x₀ ^ (2 : ℕ) / signedModeRadialBandwidth a :=
    pairAnchorPoint_sq hc0
  have hval : ∀ k : ℕ, pairAnchorPoint m n a ^ (2 : ℕ) - (signedModeRadialData a k).s
      = (x₀ ^ (2 : ℕ) - signedModeRadialBandwidth a * (signedModeRadialData a k).s)
        / signedModeRadialBandwidth a := by
    intro k
    rw [hsq]
    field_simp
  have hposm : (0 : ℝ) < x₀ ^ (2 : ℕ) - signedModeRadialBandwidth a * (signedModeRadialData a m).s := by
    nlinarith [hham, hgapm, hm0]
  have hposn : (0 : ℝ) < x₀ ^ (2 : ℕ) - signedModeRadialBandwidth a * (signedModeRadialData a n).s := by
    nlinarith [hhan, hgapn, hn0]
  rw [hval m, hval n, Real.log_div hposm.ne' hc0.ne', Real.log_div hposn.ne' hc0.ne']
  ring

end RHTower

end
