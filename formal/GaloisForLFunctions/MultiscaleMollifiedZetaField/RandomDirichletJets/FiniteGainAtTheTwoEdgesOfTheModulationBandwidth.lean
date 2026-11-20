import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheLogarithmicGainOfMovingFractionalOrders
import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheContinuousProfileOfTheFractionalModulationEnergy

/-!
# Finite logarithmic gain at collapsing and expanding bandwidth

The two singular edges have different limiting responses. At vanishing
relative bandwidth, increasing the order to retain log gain λ gives
the exponential response exp(λt)-1 across the logarithmic coordinate.
At unbounded bandwidth, decreasing the order to retain the same gain
gives the constant response exp(λ)-1 away from the stationary endpoint.
-/

noncomputable section
open Filter Topology MeasureTheory
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

private def moment (s q : ℝ) := ((1+q)^(s+1)-1)/(q*(s+1))

private theorem moment_rewrite {q : ℝ} (hq : 0 < q) (s : ℝ) :
    moment s q = ((1+q)*Real.exp (s*Real.log (1+q))-1)/(q*s+q) := by
  have hb : 0 < 1+q := add_pos zero_lt_one hq
  rw [moment,Real.rpow_add hb,Real.rpow_one,Real.rpow_def_of_pos hb,mul_comm (Real.log (1+q)) s]
  ring

private theorem moment_rescale {q : ℝ} (hq : 0 < q) (s : ℝ) :
    moment s q = ((1+q⁻¹)*Real.exp (s*Real.log (1+q))-q⁻¹)/(s+1) := by
  rw [moment_rewrite hq,← mul_div_mul_left _ _ (inv_ne_zero hq.ne')]
  congr 1
  · calc q⁻¹*((1+q)*Real.exp (s*Real.log (1+q))-1)
           = (q⁻¹+q⁻¹*q)*Real.exp (s*Real.log (1+q))-q⁻¹ := by ring
         _ = _ := by rw [inv_mul_cancel₀ hq.ne',add_comm]
  · rw [mul_add,←mul_assoc,inv_mul_cancel₀ hq.ne',one_mul]

private theorem continuum_at_finite_gain (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 2 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcut : Tendsto N atTop atTop) {ℓ : ℝ}
    (hL : Tendsto (fun k => modulationLogGain (s k) (M k) (N k)) atTop (𝓝 ℓ)) :
    let q := fun k => Real.log (N k)/Real.log (M k)
    Tendsto (fun k => relativeMoebiusModulationEnergy (s k) (M k) (N k)-
      (moment (2*s k) (q k)-2*moment (s k) (q k)+1)) atTop (𝓝 0) := by
  intro q
  have hq (k : ℕ) : 0 < q k := div_pos
    (Real.log_pos (by exact_mod_cast (show 1 < N k by have := hN k; omega)))
    (Real.log_pos (by exact_mod_cast (show 1 < M k by have := hM k; omega)))
  have hH := tendsto_squarefree_harmonic_diagonal_atTop N (fun k => by have := hN k; omega) hcut
  have htop := (((Real.continuous_exp.continuousAt.tendsto.comp hL).sub_const 1).pow 2)
  have hsmall := (hH.inv_tendsto_atTop.const_mul (24+|squarefreeHarmonicConstant|)).mul htop
  apply squeeze_zero_norm _ (by simpa only [mul_zero,zero_mul] using hsmall)
  intro k
  have he := moebius_modulation_continuum_error (hs k) (hM k) (hN k)
  dsimp only at he
  rw [modulation_response_integral (hs k) (hq k)] at he
  have hbase : 0 < 1+q k := add_pos zero_lt_one (hq k)
  have hr : fractionalModulationLoss (s k) (M k) (N k) = Real.exp (modulationLogGain (s k) (M k) (N k))-1 := by
    change (1+q k)^(s k)-1=Real.exp (s k*Real.log (1+q k))-1
    rw [Real.rpow_def_of_pos hbase,mul_comm (s k)]
  rw [hr] at he
  simpa only [moment,q,Real.norm_eq_abs,Pi.inv_apply,Function.comp_def,div_eq_mul_inv] using he

/-- The exact mean-square reading at finite nonzero log gain and vanishing
bandwidth. Fractional order may grow without bound. -/
theorem moebius_energy_at_collapsing_bandwidth (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 2 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcut : Tendsto N atTop atTop) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hL : Tendsto (fun k => modulationLogGain (s k) (M k) (N k)) atTop (𝓝 ℓ))
    (hb : Tendsto (fun k => Real.log (N k)/Real.log (M k)) atTop (𝓝 0)) :
    Tendsto (fun k => relativeMoebiusModulationEnergy (s k) (M k) (N k)) atTop
      (𝓝 ((Real.exp (2*ℓ)-1)/(2*ℓ)-2*((Real.exp ℓ-1)/ℓ)+1)) := by
  let q (k : ℕ) := Real.log (N k)/Real.log (M k)
  let L (k : ℕ) := modulationLogGain (s k) (M k) (N k)
  have hp (k : ℕ) : 0 < q k := div_pos
    (Real.log_pos (by exact_mod_cast (show 1 < N k by have := hN k; omega)))
    (Real.log_pos (by exact_mod_cast (show 1 < M k by have := hM k; omega)))
  have hq : Tendsto q atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hb,Eventually.of_forall hp⟩
  have hd : Tendsto (fun t : ℝ => t⁻¹*Real.log (1+t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [smul_eq_mul,Real.log_one,sub_zero,inv_one] using (Real.hasDerivAt_log (x:=1) one_ne_zero).tendsto_slope_zero_right
  have hr := (hd.comp hq).inv₀ one_ne_zero
  have hr' : Tendsto (fun k => q k/Real.log (1+q k)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,mul_inv_rev,inv_inv,inv_one,div_eq_mul_inv,mul_comm] using hr
  have hqs : Tendsto (fun k => q k*s k) atTop (𝓝 ℓ) := by
    have h := hL.mul hr'
    rw [mul_one] at h
    apply h.congr
    intro k
    change s k*Real.log (1+q k)*(q k/Real.log (1+q k))=q k*s k
    field_simp [(Real.log_pos (lt_add_of_pos_right _ (hp k))).ne']
  have h1 : Tendsto (fun k => 1+q k) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x:=(1:ℝ))).add hb
  have hm (a : ℝ) (ha : 0 < a) :
      Tendsto (fun k => moment (a*s k) (q k)) atTop (𝓝 ((Real.exp (a*ℓ)-1)/(a*ℓ))) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp (hL.const_mul a)
    have hg := ((h1.mul he).sub_const 1).div ((hqs.const_mul a).add hb) (by simpa using (mul_pos ha hℓ).ne')
    simp only [one_mul,add_zero] at hg
    apply hg.congr
    intro k
    rw [moment_rewrite (hp k)]
    change ((1+q k)*Real.exp (a*L k)-1)/(a*(q k*s k)+q k) = _
    rw [show a*L k=(a*s k)*Real.log (1+q k) from (mul_assoc _ _ _).symm]
    congr 1
    ring
  have hj := (((hm 2 zero_lt_two).sub ((hm 1 zero_lt_one).const_mul 2)).add_const 1)
  simp only [one_mul] at hj
  have h := (continuum_at_finite_gain M N s hM hN hs hcut hL).add hj
  simpa only [q,zero_add,sub_add_cancel] using h

/-- At unbounded relative bandwidth and bounded logarithmic gain, the
mean-square reading reaches the limiting endpoint value. -/
theorem moebius_energy_at_expanding_bandwidth (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 2 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcut : Tendsto N atTop atTop) {ℓ : ℝ}
    (hL : Tendsto (fun k => modulationLogGain (s k) (M k) (N k)) atTop (𝓝 ℓ))
    (hb : Tendsto (fun k => Real.log (N k)/Real.log (M k)) atTop atTop) :
    Tendsto (fun k => relativeMoebiusModulationEnergy (s k) (M k) (N k)) atTop
      (𝓝 ((Real.exp ℓ-1)^2)) := by
  let q (k : ℕ) := Real.log (N k)/Real.log (M k)
  let L (k : ℕ) := modulationLogGain (s k) (M k) (N k)
  have hp (k : ℕ) : 0 < q k := div_pos
    (Real.log_pos (by exact_mod_cast (show 1 < N k by have := hN k; omega)))
    (Real.log_pos (by exact_mod_cast (show 1 < M k by have := hM k; omega)))
  have hlog : Tendsto (fun k => Real.log (1+q k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono (fun _ => le_add_of_nonneg_left zero_le_one) hb)
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have h := hL.mul hlog.inv_tendsto_atTop
    rw [mul_zero] at h
    apply h.congr
    intro k
    change s k*Real.log (1+q k)*(Real.log (1+q k))⁻¹=s k
    rw [mul_assoc,mul_inv_cancel₀ (Real.log_pos (lt_add_of_pos_right _ (hp k))).ne',mul_one]
  have hi : Tendsto (fun k => (q k)⁻¹) atTop (𝓝 0) := hb.inv_tendsto_atTop
  have h1 := (tendsto_const_nhds (x:=(1:ℝ))).add hi
  have hm (a : ℝ) : Tendsto (fun k => moment (a*s k) (q k)) atTop (𝓝 (Real.exp (a*ℓ))) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp (hL.const_mul a)
    have h := ((h1.mul he).sub hi).div ((hs0.const_mul a).add_const 1) (by simp)
    simp only [add_zero,one_mul,sub_zero,mul_zero,zero_add,div_one] at h
    apply h.congr
    intro k
    rw [moment_rescale (hp k)]
    change ((1+(q k)⁻¹)*Real.exp (a*L k)-(q k)⁻¹)/(a*s k+1)=_
    dsimp only [L,modulationLogGain]
    rw [mul_assoc]
  have hj := (((hm 2).sub ((hm 1).const_mul 2)).add_const 1)
  simp only [one_mul] at hj
  have h := (continuum_at_finite_gain M N s hM hN hs hcut hL).add hj
  rw [show Real.exp (2*ℓ)-2*Real.exp ℓ+1=(Real.exp ℓ-1)^2 by rw [two_mul ℓ,Real.exp_add]; ring] at h
  simpa only [q,zero_add,sub_add_cancel] using h


end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
