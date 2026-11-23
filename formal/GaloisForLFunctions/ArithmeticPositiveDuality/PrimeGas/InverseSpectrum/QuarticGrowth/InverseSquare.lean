import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.Rate

/-! # The ordinary zeta abscissa from inverse-square decay of projection losses -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- At positive inverse temperature, an inverse-square trace loss uniformly suppresses the complex partition loss at large height. -/
def inverseSquareClockStable (σ : ℝ) : Prop :=
  0 < σ ∧ ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
    ∀ (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P)),
      traceLoss (projected P) ≤ M/t^2 → ‖relativePartition (physicalSpectrum P hd hc) (⟨σ,t⟩:ℂ)‖ < ε

private theorem stable_above_one {σ : ℝ} (hs : 1 < σ) : inverseSquareClockStable σ := by
  have hσ := zero_lt_one.trans hs
  have hw : 1/2 ≤ σ := (by norm_num : (1/2:ℝ)≤1).trans hs.le
  let q := quarticClockOrder σ
  have hq : q < 2 := max_lt (by norm_num) (by linarith only [hs])
  obtain ⟨_,_,C,hC,hbound⟩ := quartic_clock_power_bounds hw
  refine ⟨hσ,?_⟩
  intro M hM ε hε
  have hlim : Tendsto (fun t : ℝ => (C*M)*t^(q-2)) atTop (𝓝 0) := by
    have he := (tendsto_rpow_neg_atTop (sub_pos.mpr hq)).const_mul (C*M)
    simpa only [neg_sub,mul_zero] using he
  filter_upwards [eventually_ge_atTop (1:ℝ),hlim.eventually_lt_const (pow_pos hε 4)] with t ht hsmall
  intro P hd hc hD
  let z : ℂ := ⟨σ,t⟩
  let X := ‖relativePartition (physicalSpectrum P hd hc) z‖
  have ht' := zero_lt_one.trans_le ht
  have hK := (quarticCoefficient_isLeast 0 (z := z) hw).1 P hd hc
  change X^(4:ℝ) ≤ quarticClockCoefficient σ t*traceLoss (projected P) at hK
  rw [show X^(4:ℝ) = X^4 from Real.rpow_natCast _ 4] at hK
  have he := mul_le_mul (hbound t ht).2 hD (traceLoss_nonneg P hd hc) (mul_nonneg hC.le (Real.rpow_nonneg ht'.le _))
  have hpow : (C*t^q)*(M/t^2) = (C*M)*t^(q-2) := by
    rw [Real.rpow_sub ht',Real.rpow_two]
    ring
  have hh := ((hK.trans he).trans_eq hpow).trans_lt hsmall
  exact lt_of_not_ge (fun hn => hh.not_ge (pow_le_pow_left₀ hε.le hn 4))

private theorem stable_forces_one {σ : ℝ} (h : inverseSquareClockStable σ) : 1 < σ := by
  by_contra! hs
  let W := 8*(1+Real.pi)
  have hW : 0 < W := mul_pos (by norm_num) (add_pos zero_lt_one Real.pi_pos)
  have hM : 0 < 2*W^2 := mul_pos (by norm_num) (sq_pos_of_pos hW)
  have hε : 0 < 1/(8*W) := one_div_pos.mpr (mul_pos (by norm_num) hW)
  obtain ⟨t,hw,ht,hsmall⟩ := ((eventually_ge_atTop W).and ((eventually_ge_atTop (1:ℝ)).and (h.2 _ hM _ hε))).exists
  obtain ⟨P,hd,hc,hL,hD⟩ := clock_scale_physical_witness h.1 hw
  have hcost : traceLoss (projected P) ≤ (2*W^2)/t^2 := hD.le.trans_eq (by change 2*(W/t)^2 = _; rw [div_pow]; ring)
  have hlimit := hsmall P hd hc hcost
  have hsep := div_le_div_of_nonneg_right (Real.one_le_rpow ht (sub_nonneg.mpr hs)) (mul_nonneg (by norm_num : (0:ℝ)≤8) hW.le)
  exact (hsep.trans_lt hL).not_gt hlimit

/-- Uniform stability under inverse-square loss is equivalent to the trace half-plane of the original gas. -/
theorem inverseSquareClockStable_iff (σ : ℝ) : inverseSquareClockStable σ ↔ 1 < σ :=
  ⟨stable_forces_one,stable_above_one⟩

/-- The physical stability test recovers absolute convergence of every finite-rank surviving partition. -/
theorem inverseSquare_iff_summable_partition {r : ℕ} (b : SpectralBand r) (s : ℂ) :
    inverseSquareClockStable s.re ↔ Summable (fun n => ((b n).val:ℂ)^s) :=
  (inverseSquareClockStable_iff _).trans (summable_band_cpow_iff b s).symm

/-- At the real temperature of a squared amplitude, stability recovers its Hilbert-space normalizability. -/
theorem inverseSquare_iff_summable_born {r : ℕ} (b : SpectralBand r) (s : ℂ) :
    inverseSquareClockStable (2*s.re) ↔ Summable (fun n => ‖((b n).val:ℂ)^s‖^2) := by
  rw [inverseSquareClockStable_iff,summable_band_born_iff]
  constructor <;> intro h <;> linarith only [h]

/-- The boundary of stability for squared amplitudes is precisely the isometric cyclic-order composition law. -/
theorem split_isometric_iff_inverseSquare_frontier (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      s ∈ frontier {w : ℂ | inverseSquareClockStable (2*w.re)} := by
  rw [split_isometry_iff_surviving_frontier (hotEdge 0) s]
  have he : {w : ℂ | inverseSquareClockStable (2*w.re)} =
      {w : ℂ | Summable (fun n => ‖(((hotEdge 0) n).val:ℂ)^w‖^2)} :=
    Set.ext (fun w => inverseSquare_iff_summable_born (hotEdge 0) w)
  rw [he]

#print axioms inverseSquareClockStable_iff
#print axioms inverseSquare_iff_summable_partition
#print axioms inverseSquare_iff_summable_born
#print axioms split_isometric_iff_inverseSquare_frontier

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
