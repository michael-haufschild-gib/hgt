import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.BornBounds
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.SurvivingPartition

/-! # A single ordinary trace controls the relative partition through its pole

Iteration of the Born inequality gives an explicit modulus on each bounded
window inside the positive half-plane. On the composition line the power is four.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

def halveExponent (β : GibbsExponent) : GibbsExponent :=
  ⟨β.val/2,show 0 < β.val/(2:ℝ) from div_pos β.property (by norm_num)⟩

def dyadicExponent (β : GibbsExponent) : ℕ → GibbsExponent
  | 0 => β
  | n+1 => halveExponent (dyadicExponent β n)

private theorem double_halve (β : GibbsExponent) : doubleExponent (halveExponent β) = β := by
  apply Subtype.ext
  change β.val/2*2 = β.val
  ring

theorem dyadicExponent_val (β : GibbsExponent) (m : ℕ) : (dyadicExponent β m).val = β.val * (1/2:ℝ)^m := by
  induction m with
  | zero => simp [dyadicExponent]
  | succ m ih => change (dyadicExponent β m).val/2 = _; rw [ih,pow_succ]; ring

theorem dyadicExponent_tendsto_zero (β : GibbsExponent) : Tendsto (fun n => (dyadicExponent β n).val) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul β.val
  simpa only [dyadicExponent_val,mul_zero] using h

/-- The m-fold square-root response costs at most the original error times the (2^m−1)-st power of the rank. -/
theorem dyadic_error_bound (β : GibbsExponent) {r : ℕ} (b c : SpectralBand r) (m : ℕ) :
    detectorError (powerResponse (dyadicExponent β m)) b c ^ (2^m) ≤
      (r:ℝ)^(2^m-1) * detectorError (powerResponse β) b c := by
  induction m with
  | zero => simp [dyadicExponent]
  | succ m ih =>
    let X := detectorError (powerResponse (dyadicExponent β (m+1))) b c
    let Y := detectorError (powerResponse (dyadicExponent β m)) b c
    let Z := detectorError (powerResponse β) b c
    have hs := amplitude_sq_le_rank_mul_born (halveExponent (dyadicExponent β m)) b c
    rw [double_halve] at hs
    change X^2 ≤ (r:ℝ)*Y at hs
    have hp : 0 < 2^m := pow_pos (Nat.zero_lt_succ 1) _
    have hk : (2:ℕ)^(m+1) = 2*2^m := by rw [pow_succ,Nat.mul_comm]
    change X^(2^(m+1)) ≤ (r:ℝ)^(2^(m+1)-1)*Z
    rw [hk]
    calc
      _ = (X^2)^(2^m) := pow_mul _ _ _
      _ ≤ ((r:ℝ)*Y)^(2^m) := pow_le_pow_left₀ (sq_nonneg _) hs _
      _ = (r:ℝ)^(2^m)*Y^(2^m) := mul_pow _ _ _
      _ ≤ (r:ℝ)^(2^m)*((r:ℝ)^(2^m-1)*Z) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [← mul_assoc,← pow_add,show 2^m+(2^m-1) = 2*2^m-1 by omega]

theorem reference_error_eq_reading (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) :
    detectorError f (hotEdge r) b = relativeReading f b := by
  apply tsum_congr
  intro n
  exact abs_of_nonneg (drop_nonneg f b n)

/-- Every dyadic relative loss has sharp coefficient one for a single physical omission. -/
theorem rankOne_dyadic_loss_factor_iff (β : GibbsExponent) (m : ℕ) (K : ℝ) :
    (∀ (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P)),
      relativeReading (powerResponse (dyadicExponent β m)) (physicalSpectrum P hd hc)^(2^m) ≤
      K * relativeReading (powerResponse β) (physicalSpectrum P hd hc)) ↔ 1 ≤ K := by
  constructor
  · intro h
    let S (δ : GibbsExponent) (p : SpectralBand 1 × SpectralBand 1) := relativeReading (powerResponse δ) p.2
    have hs (δ : GibbsExponent) : Continuous (S δ) := (continuous_relativeReading _ 1).comp continuous_snd
    have he := edgePair_mem_closed_of_physical 0 (isClosed_le ((hs (dyadicExponent β m)).pow (2^m))
      (continuous_const.mul (hs β))) (fun _ Q _ _ hQ cQ => h Q hQ cQ)
    have h₁ (δ : GibbsExponent) : relativeReading (powerResponse δ) (coldEdge 1) = 1 := by
      simp only [relativeReading_cold,relativeHead,Finset.sum_range_one,powerResponse,occupationWeight_zero,
        Real.one_rpow,Real.zero_rpow δ.property.ne',sub_zero]
    change relativeReading _ (coldEdge 1)^(2^m) ≤ K * relativeReading _ (coldEdge 1) at he
    simpa only [h₁,one_pow,mul_one] using he
  · intro h P hd hc
    let b := physicalSpectrum P hd hc
    have he := dyadic_error_bound β (hotEdge 1) b m
    simp only [reference_error_eq_reading,Nat.cast_one,one_pow,one_mul] at he
    exact he.trans (le_mul_of_one_le_left (relativeReading_bounds _ b).1 h)

private theorem double_unit_reading {r : ℕ} (b : SpectralBand r) :
    relativeReading (powerResponse (doubleExponent unitExponent)) b = relativeReading quadraticResponse b := by
  simp only [relativeReading,spectralDrop,powerResponse,doubleExponent,unitExponent,one_mul,Real.rpow_two,quadraticResponse]

/-- Fourth-trace deficit controls the complex relative partition at every dyadic positive threshold. -/
theorem trace_controls_relativePartition (P : Projection) {r : ℕ} (hd : MissingDimension P r)
    (hc : Conserving (projected P)) (m : ℕ) {z : ℂ}
    (hz : (dyadicExponent (doubleExponent unitExponent) m).val ≤ z.re) :
    ‖relativePartition (physicalSpectrum P hd hc) z‖^(2^m) ≤
      (‖z‖ / (dyadicExponent (doubleExponent unitExponent) m).val)^(2^m) *
      (r:ℝ)^(2^m-1) * traceLoss (projected P) := by
  let b := physicalSpectrum P hd hc
  let δ := dyadicExponent (doubleExponent unitExponent) m
  have ha := dyadic_error_bound (doubleExponent unitExponent) (hotEdge r) b m
  simp only [reference_error_eq_reading,double_unit_reading] at ha
  rw [show relativeReading quadraticResponse b = traceLoss (projected P) from quadratic_physicalReading P hd hc] at ha
  have h := pow_le_pow_left₀ (norm_nonneg _) (relativePartition_norm_le b δ hz) (2^m)
  rw [mul_pow] at h
  exact (h.trans (mul_le_mul_of_nonneg_left ha (pow_nonneg (div_nonneg (norm_nonneg _) δ.property.le) _))).trans_eq
    (mul_assoc _ _ _).symm

/-- At and to the right of the isometric line, the complex loss satisfies a fourth-power bound. -/
theorem critical_trace_bound (P : Projection) {r : ℕ} (hd : MissingDimension P r) (hc : Conserving (projected P))
    {z : ℂ} (hz : 1/2 ≤ z.re) :
    ‖relativePartition (physicalSpectrum P hd hc) z‖^4 ≤ (‖z‖/(1/2:ℝ))^4 * (r:ℝ)^3 * traceLoss (projected P) := by
  have he : (dyadicExponent (doubleExponent unitExponent) 2).val = 1/2 := by
    norm_num [dyadicExponent,halveExponent,doubleExponent,unitExponent]
  have hz' : (dyadicExponent (doubleExponent unitExponent) 2).val ≤ z.re := by rwa [he]
  simpa only [he,show (2:ℕ)^2 = 4 by norm_num,show (4:ℕ)-1 = 3 by norm_num] using
    trace_controls_relativePartition P hd hc 2 hz'

/-- The measured fourth-trace loss bounds the shift of the actual Laurent constant. -/
theorem trace_controls_pole_constant (P : Projection) {r : ℕ} (hd : MissingDimension P r) (hc : Conserving (projected P)) :
    ∃ c : ℝ, Tendsto (fun z : ℂ => survivingPartition (physicalSpectrum P hd hc) z - 1/(z-1))
      (𝓝[≠] 1) (𝓝 (c:ℂ)) ∧ (Real.eulerMascheroniConstant-c)^2 ≤ (r:ℝ)*traceLoss (projected P) := by
  let b := physicalSpectrum P hd hc
  refine ⟨_,surviving_finite_part b,?_⟩
  rw [sub_sub_cancel]
  have h := amplitude_sq_le_rank_mul_born unitExponent (hotEdge r) b
  simpa only [reference_error_eq_reading,double_unit_reading,b,quadratic_physicalReading] using h

#print axioms dyadic_error_bound
#print axioms rankOne_dyadic_loss_factor_iff
#print axioms trace_controls_relativePartition
#print axioms critical_trace_bound
#print axioms trace_controls_pole_constant

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
