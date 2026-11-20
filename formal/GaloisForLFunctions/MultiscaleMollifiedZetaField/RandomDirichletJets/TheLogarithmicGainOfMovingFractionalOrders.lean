import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheSquarefreeDistributionOfTheModulationError
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Moving fractional orders on the critical Möbius row

The highest-frequency multiplier has logarithm L = s log(1 + log N/log M).
For every interior logarithmic quantile u, Bernoulli's inequality puts
the multiplier above exp(uL) on an asymptotic fraction 1-u of the mass.
Consequently L detects vanishing, and measures half the logarithm of the
energy to leading order at large gain, with no relation between the
growth rates of the fractional order, carrier and section length.
-/

noncomputable section
open Filter Topology MeasureTheory
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

/-- Logarithm of the shifted multiplier at the top mode. -/
def modulationLogGain (s : ℝ) (M N : ℕ) := s*Real.log (1+Real.log N/Real.log M)

private theorem bandwidth_nonneg {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) :
    0 ≤ Real.log N/Real.log M :=
  div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hN))
    (Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ M)))

private theorem gain_nonneg {s : ℝ} (hs : 0 ≤ s) {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) :
    0 ≤ modulationLogGain s M N := mul_nonneg hs
      (Real.log_nonneg (le_add_of_nonneg_right (bandwidth_nonneg hM hN)))

private theorem endpoint_response {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) (s : ℝ) :
    fractionalModulationLoss s M N = Real.exp (modulationLogGain s M N)-1 := by
  rw [fractionalModulationLoss, Real.rpow_def_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (bandwidth_nonneg hM hN)),
    modulationLogGain, mul_comm s]

private theorem quantile_response_lower {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) {s u : ℝ}
    (hs : 0 ≤ s) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    Real.exp (u*modulationLogGain s M N)-1 ≤ modulationQuantile s M N u := by
  let q := Real.log N/Real.log M
  have hq : 0 ≤ q := bandwidth_nonneg hM hN
  have hb : 0 < 1+q := add_pos_of_pos_of_nonneg zero_lt_one hq
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hb.le u)
    (rpow_one_add_le_one_add_mul_self (show -1 ≤ q by linarith only [hq]) hu.1 hu.2) hs
  rw [←Real.rpow_mul hb.le,Real.rpow_def_of_pos hb] at h
  have he : u*modulationLogGain s M N = Real.log (1+q)*(u*s) := by dsimp [q,modulationLogGain]; ring
  rw [he,modulationQuantile,mul_div_assoc]
  exact sub_le_sub_right h 1

private theorem energy_nonneg {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (s : ℝ) :
    0 ≤ relativeMoebiusModulationEnergy s M N := div_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (harmonicMoebiusDiagonal_pos_of_one_le hN).le

private theorem energy_upper {s : ℝ} (hs : 0 ≤ s) {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) :
    relativeMoebiusModulationEnergy s M N ≤ (Real.exp (modulationLogGain s M N)-1)^2 := by
  rw [← endpoint_response hM hN]
  have H := (optimal_fractional_modulation_energy_iff hs hM hN _).mpr le_rfl criticalMoebiusAmplitude
  rw [relativeMoebiusModulationEnergy,div_le_iff₀ (harmonicMoebiusDiagonal_pos_of_one_le hN),
    harmonicMoebiusDiagonal_at_nat]
  simpa only [criticalMoebiusAmplitude_norm_sq] using H

/-- A fixed fraction of the actual row sees the exponential of every
interior fraction of the top logarithmic gain, uniformly in order. -/
theorem moving_modulation_inner_bound (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcutoff : Tendsto N atTop atTop) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ k in atTop, ((1-u)/2)*(Real.exp (u*modulationLogGain (s k) (M k) (N k))-1)^2
      ≤ relativeMoebiusModulationEnergy (s k) (M k) (N k) := by
  let D := 24+|squarefreeHarmonicConstant|
  let c := (1-u)/2
  let H (k : ℕ) := harmonicMoebiusDiagonal (N k)
  have hc : 0 < c := half_pos (sub_pos.mpr hu1)
  have hcut := (tendsto_squarefree_harmonic_diagonal_atTop N hN hcutoff).eventually_ge_atTop (D/c)
  filter_upwards [hcut] with k hk
  rw [div_le_iff₀ hc] at hk
  let L := modulationLogGain (s k) (M k) (N k)
  have huI : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.le,hu1.le⟩
  have hH : 0 < H k := harmonicMoebiusDiagonal_pos_of_one_le (hN k)
  obtain h0|hp := (hs k).eq_or_lt
  · rw [← h0]
    simpa only [modulationLogGain,zero_mul,mul_zero,Real.exp_zero,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0)]
      using energy_nonneg (hN k) (M k) 0
  have hmass := (abs_le.mp ((uniform_squarefree_quantile_discrepancy hp (hM k) (hN k)).2 u huI)).2
  have hm : squarefreeModulationMass (s k) (M k) (N k) u / H k ≤ D/H k+u := (sub_le_iff_le_add).mp hmass
  have hmul := (div_le_iff₀ hH).mp hm
  rw [add_mul,div_mul_cancel₀ _ hH.ne'] at hmul
  have hband : c*H k ≤ H k-squarefreeModulationMass (s k) (M k) (N k) u := by
    change D ≤ H k*((1-u)/2) at hk
    dsimp only [c]
    linarith only [hmul,hk]
  have hh := (moebius_modulation_energy_sandwich hp (hM k) (hN k) huI).1
  have hb := quantile_response_lower (hM k) (hN k) hp.le huI
  have hl : 0 ≤ Real.exp (u*L)-1 := sub_nonneg.mpr
    (Real.one_le_exp (mul_nonneg hu.le (gain_nonneg hp.le (hM k) (hN k))))
  have he := mul_le_mul (pow_le_pow_left₀ hl hb 2) hband (mul_nonneg hc.le hH.le) (sq_nonneg _)
  have hfinal := he.trans hh
  apply le_of_mul_le_mul_right (a:=H k) _ hH
  change (Real.exp (u*L)-1)^2*(c*H k) ≤ _ at hfinal
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hfinal

/-- For moving fractional orders, the mean-square error vanishes precisely
when the order times the logarithm of one plus the relative bandwidth vanishes. -/
theorem moving_modulation_vanishes_iff (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcutoff : Tendsto N atTop atTop) :
    Tendsto (fun k => relativeMoebiusModulationEnergy (s k) (M k) (N k)) atTop (𝓝 0) ↔
      Tendsto (fun k => modulationLogGain (s k) (M k) (N k)) atTop (𝓝 0) := by
  let L (k : ℕ) := modulationLogGain (s k) (M k) (N k)
  let E (k : ℕ) := relativeMoebiusModulationEnergy (s k) (M k) (N k)
  have hL (k : ℕ) : 0 ≤ L k := gain_nonneg (hs k) (hM k) (hN k)
  constructor
  · intro H
    have hl := moving_modulation_inner_bound M N s hM hN hs hcutoff (u:=1/2) (by norm_num) (by norm_num)
    have hsq : Tendsto (fun k => L k^2) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _ (by simpa only [mul_zero] using H.const_mul 16)
      filter_upwards [hl] with k hk
      have hb := Real.add_one_le_exp ((1/2)*L k)
      have he : (1/2)*L k ≤ Real.exp ((1/2)*L k)-1 := by linarith only [hb]
      have hp := pow_le_pow_left₀ (mul_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) (hL k)) he 2
      change ((1-(1/2:ℝ))/2)*(Real.exp ((1/2)*L k)-1)^2 ≤ E k at hk
      linarith only [hp,hk]
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq (hL _),Real.sqrt_zero] using h
  · intro H
    have h := ((Real.continuous_exp.continuousAt.tendsto.comp H).sub_const 1).pow 2
    exact squeeze_zero (fun k => energy_nonneg (hN k) (M k) (s k))
      (fun k => energy_upper (hs k) (hM k) (hN k))
      (by simpa only [Function.comp_def,Real.exp_zero,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0)] using h)

private theorem log_energy_upper {s : ℝ} (hs : 0 ≤ s) {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) :
    Real.log (1+relativeMoebiusModulationEnergy s M N) ≤ 2*modulationLogGain s M N := by
  let L := modulationLogGain s M N
  have he := energy_upper hs hM hN
  have h1 : 1 ≤ Real.exp L := Real.one_le_exp (gain_nonneg hs hM hN)
  have hpos := add_pos_of_pos_of_nonneg zero_lt_one (energy_nonneg hN M s)
  apply (Real.log_le_log hpos ?_).trans_eq (Real.log_exp (2*L))
  rw [two_mul, Real.exp_add]
  change relativeMoebiusModulationEnergy s M N ≤ (Real.exp L-1)^2 at he
  linarith only [he,h1]

private theorem log_energy_inner (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcutoff : Tendsto N atTop atTop) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ k in atTop, 2*u*modulationLogGain (s k) (M k) (N k)+Real.log ((1-u)/4) ≤
      Real.log (1+relativeMoebiusModulationEnergy (s k) (M k) (N k)) := by
  filter_upwards [moving_modulation_inner_bound M N s hM hN hs hcutoff hu hu1] with k hh
  let L := modulationLogGain (s k) (M k) (N k)
  let a := Real.exp (u*L)
  let c := (1-u)/2
  let E := relativeMoebiusModulationEnergy (s k) (M k) (N k)
  have hc : 0 < c := half_pos (sub_pos.mpr hu1)
  have hc1 : c ≤ 1 := by dsimp only [c]; linarith only [hu]
  have he : a^2 ≤ 2*((a-1)^2+1) := by linarith only [sq_nonneg (a-2)]
  have hb := mul_le_mul_of_nonneg_left he (half_pos hc).le
  have hbound : c/2*(a*a) ≤ 1+E := by
    change c*(a-1)^2 ≤ E at hh
    linarith only [hb,hh,hc1]
  have hc' : c/2=(1-u)/4 := by dsimp only [c]; ring
  have hlog := Real.log_le_log (mul_pos (half_pos hc) (mul_pos (Real.exp_pos _) (Real.exp_pos _))) hbound
  rw [Real.log_mul (half_pos hc).ne' (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
    show a*a=Real.exp (u*L+u*L) from (Real.exp_add _ _).symm,Real.log_exp,hc'] at hlog
  change 2*u*L+_ ≤ _
  linarith only [hlog]

/-- At diverging logarithmic gain the observed log energy has exact
slope two, even for orders increasing arbitrarily faster than the length. -/
theorem moving_modulation_exponential_rate (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcutoff : Tendsto N atTop atTop)
    (hgain : Tendsto (fun k => modulationLogGain (s k) (M k) (N k)) atTop atTop) :
    Tendsto (fun k => Real.log (1+relativeMoebiusModulationEnergy (s k) (M k) (N k))/
      (2*modulationLogGain (s k) (M k) (N k))) atTop (𝓝 1) := by
  let L (k : ℕ) := modulationLogGain (s k) (M k) (N k)
  let E (k : ℕ) := relativeMoebiusModulationEnergy (s k) (M k) (N k)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨u,hbu,hu1⟩ := exists_between (max_lt hb zero_lt_one)
    have hu : 0 < u := (le_max_right _ _).trans_lt hbu
    have hb' : b < u := (le_max_left _ _).trans_lt hbu
    let c := Real.log ((1-u)/4)
    have hpos : 0 < 2*(u-b) := mul_pos zero_lt_two (sub_pos.mpr hb')
    filter_upwards [log_energy_inner M N s hM hN hs hcutoff hu hu1,
      hgain.eventually_gt_atTop (-c/(2*(u-b))), hgain.eventually_gt_atTop 0] with k he hk h0
    apply (lt_div_iff₀ (mul_pos zero_lt_two h0)).mpr
    have h := (div_lt_iff₀ hpos).mp hk
    change -c < L k*(2*(u-b)) at h
    change 2*u*L k+c ≤ Real.log (1+E k) at he
    change b*(2*L k) < Real.log (1+E k)
    linarith only [h,he]
  · intro b hb
    filter_upwards [hgain.eventually_gt_atTop 0] with k hk
    exact ((div_le_one (mul_pos zero_lt_two hk)).mpr (log_energy_upper (hs k) (hM k) (hN k))).trans_lt hb

/-- Divergence of the actual error is equivalent to divergence of the
logarithmic gain. -/
theorem moving_modulation_diverges_iff (M N : ℕ → ℕ) (s : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hs : ∀ k, 0 ≤ s k)
    (hcutoff : Tendsto N atTop atTop) :
    Tendsto (fun k => relativeMoebiusModulationEnergy (s k) (M k) (N k)) atTop atTop ↔
      Tendsto (fun k => modulationLogGain (s k) (M k) (N k)) atTop atTop := by
  let L (k : ℕ) := modulationLogGain (s k) (M k) (N k)
  let E (k : ℕ) := relativeMoebiusModulationEnergy (s k) (M k) (N k)
  constructor
  · intro H
    have he : Tendsto (fun k => 1+E k) atTop atTop := tendsto_atTop_mono
      (fun k => le_add_of_nonneg_left zero_le_one) H
    have hl := Real.tendsto_log_atTop.comp he
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hl.eventually_ge_atTop (2*b)] with k hk
    have hh := log_energy_upper (hs k) (hM k) (hN k)
    change 2*b ≤ Real.log (1+E k) at hk
    change Real.log (1+E k) ≤ 2*L k at hh
    change b ≤ L k
    linarith only [hh,hk]
  · intro H
    have hi := log_energy_inner M N s hM hN hs hcutoff (u:=1/2) (by norm_num) (by norm_num)
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hi,H.eventually_ge_atTop (b-Real.log ((1-(1/2:ℝ))/4))] with k hk he
    have hu : Real.log (1+E k) ≤ E k := by
      have h := Real.log_le_sub_one_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (energy_nonneg (hN k) (M k) (s k)))
      simpa only [add_sub_cancel_left] using h
    change 2*(1/2:ℝ)*L k+Real.log ((1-(1/2:ℝ))/4) ≤ Real.log (1+E k) at hk
    change b-Real.log ((1-(1/2:ℝ))/4) ≤ L k at he
    change b ≤ E k
    linarith only [hk,he,hu]


end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
