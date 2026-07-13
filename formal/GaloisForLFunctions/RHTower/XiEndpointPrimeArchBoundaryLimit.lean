import GaloisForLFunctions.RHTower.XiEndpointReflectionDefectEnergy

/-!
# Cofinal prime--Gamma realization of the endpoint curvature

The endpoint curvature in `XiEndpointReflectionDefectEnergy` is not left as zero data.  Along the
explicit positive-real-part approach `s_n = 1 / (n + 3)`, the normalized continued prime--Gamma
source agrees pointwise with the completed Xi logarithmic derivative and converges to the upper
completion boundary `z = i/2`.  Thus the fixed scalar in the endpoint norm budget is a genuine
cofinal source value.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

def xiEndpointEpsilon (n : ℕ) : ℂ := 1 / ((n : ℂ) + 3)

def xiEndpointApproach (n : ℕ) : ℂ :=
  (1 / 2 - xiEndpointEpsilon n) * I

def normalizedContinuedPrimeArchSource (z : ℂ) : ℂ :=
  -continuedPrimeArchSourceRelativeTrace z / z

theorem tendsto_xiEndpointEpsilon_zero :
    Tendsto xiEndpointEpsilon atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).comp
    (Filter.tendsto_add_atTop_nat 2)
  convert h using 1
  funext n
  simp [xiEndpointEpsilon, Function.comp_apply, Nat.cast_add]
  ring

theorem tendsto_xiEndpointApproach :
    Tendsto xiEndpointApproach atTop (𝓝 (I / 2)) := by
  have h := (tendsto_xiEndpointEpsilon_zero.const_sub (1 / 2 : ℂ)).mul_const I
  have htarget : (1 / 2 : ℂ) * I = I / 2 := by ring
  simpa only [xiEndpointApproach, sub_zero, htarget] using h

lemma xiEndpointApproach_source_eq (n : ℕ) :
    normalizedContinuedPrimeArchSource (xiEndpointApproach n) =
      -logDeriv XiC (xiEndpointApproach n) / xiEndpointApproach n := by
  let ε : ℝ := 1 / ((n : ℝ) + 3)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (0 : ℝ) < (n : ℝ) + 3 := by linarith
  have hεpos : 0 < ε := by positivity
  have hεhalf : ε < 1 / 2 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hεone : ε < 1 := lt_trans hεhalf (by norm_num)
  have hεC : xiEndpointEpsilon n = (ε : ℂ) := by
    simp [xiEndpointEpsilon, ε]
  have hs : 1 / 2 + xiEndpointApproach n * I = (ε : ℂ) := by
    rw [xiEndpointApproach, hεC]
    rw [mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
    ring
  have hspos : 0 < (1 / 2 + xiEndpointApproach n * I).re := by
    rw [hs]
    simpa using hεpos
  have hs1 : 1 / 2 + xiEndpointApproach n * I ≠ 1 := by
    rw [hs]
    exact_mod_cast ne_of_lt hεone
  have hzeta : riemannZeta (1 / 2 + xiEndpointApproach n * I) ≠ 0 := by
    rw [hs]
    exact riemannZeta_real_strip_ne_zero hεpos hεone
  have hXi : XiC (xiEndpointApproach n) ≠ 0 := by
    change xi (1 / 2 + xiEndpointApproach n * I) ≠ 0
    exact (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  rw [normalizedContinuedPrimeArchSource,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta,
    ← logDeriv_XiC_eq_relativeResolventTrace hXi]

theorem tendsto_normalizedContinuedPrimeArchSource_endpoint :
    Tendsto (fun n : ℕ =>
      normalizedContinuedPrimeArchSource (xiEndpointApproach n))
      atTop (𝓝 (-logDeriv XiC (I / 2) / (I / 2))) := by
  have hXi : XiC (I / 2) ≠ 0 := by
    intro h
    have hzero : xi 0 = 0 := by
      change xi (1 / 2 + (I / 2) * I) = 0 at h
      have harg : (1 / 2 : ℂ) + (I / 2) * I = 0 := by
        field_simp
        rw [Complex.I_sq]
        ring
      rw [harg] at h
      exact h
    let ρ : XiDivisorSupport := ⟨0, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hs := xi_divisor_support_re_mem_open_unit ρ
    norm_num at hs
  have hXiAn : AnalyticAt ℂ XiC (I / 2) :=
    XiC_analytic (I / 2) (Set.mem_univ _)
  have hlog : ContinuousAt (logDeriv XiC) (I / 2) := by
    change ContinuousAt (fun z => deriv XiC z / XiC z) (I / 2)
    exact hXiAn.deriv.continuousAt.div hXiAn.continuousAt hXi
  have hz0 : (I / 2 : ℂ) ≠ 0 := div_ne_zero I_ne_zero (by norm_num)
  have hnorm : ContinuousAt (fun z => -logDeriv XiC z / z) (I / 2) :=
    hlog.neg.div continuousAt_id hz0
  have ht := hnorm.tendsto.comp tendsto_xiEndpointApproach
  exact ht.congr' (Filter.Eventually.of_forall fun n =>
    (xiEndpointApproach_source_eq n).symm)

end

end RHTower
