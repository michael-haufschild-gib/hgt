import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Transition

/-! # The unobserved common divisor in two Gibbs samples -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open CopyExchange Filter Topology

/-- Normalized Gibbs weight of the common scale on a line of fixed reduced ratio. -/
def commonScaleWeight (x : ℝ) (k : ℕ+) : ℂ :=
  heat ((4*x:ℝ):ℂ) k / riemannZeta ((4*x:ℝ):ℂ)

theorem common_scale_summable_iff (x : ℝ) :
    (Summable fun k => ‖heat ((4*x:ℝ):ℂ) k‖) ↔ 1/4 < x := by
  rw [heat_abs_summable,Complex.ofReal_re]
  constructor <;> intro h <;> linarith

theorem commonScaleWeight_hasSum {x : ℝ} (hx : 1/4 < x) : HasSum (commonScaleWeight x) 1 := by
  have h : 1 < ((4*x:ℝ):ℂ).re := by change 1 < 4*x; linarith
  have hs := (heat_hasSum ⟨((4*x:ℝ):ℂ),h⟩).div_const (riemannZeta ((4*x:ℝ):ℂ))
  rw [div_self (riemannZeta_ne_zero_of_one_lt_re h)] at hs
  exact hs

theorem commonScaleWeight_positive {x : ℝ} (hx : 1/4 < x) (k : ℕ+) :
    ∃ r : ℝ, 0 < r ∧ (r:ℂ) = commonScaleWeight x k := by
  let β : TraceTemperature := ⟨4*x,by linarith⟩
  have hz : 0 < ∑' n, thermalWeight β n := (thermalWeight_pos β 1).trans_le
    ((thermalWeight_summable β).le_tsum 1 (fun n _ => (thermalWeight_pos β n).le))
  refine ⟨_,div_pos (thermalWeight_pos β k) hz,?_⟩
  rw [Complex.ofReal_div,thermalWeight_partition]
  change (thermalWeight β k:ℂ) / riemannZeta (β.val:ℂ) = heat (β.val:ℂ) k / riemannZeta (β.val:ℂ)
  simp only [thermalWeight,heat,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]

/-- The joint weight of a reduced ratio and its common divisor factors into their individual weights. -/
theorem gapAmplitude_disintegrates {x : ℝ} (hx : 1/2 < x) {a b : ℕ+} (hc : a.Coprime b) (k : ℕ+) :
    gapAmplitude x (a*k,b*k) = overlapCoefficient x (gapFrequency (a,b)) * commonScaleWeight x k := by
  let s : ℂ := ((x+x:ℝ):ℂ)
  have hs : ((4*x:ℝ):ℂ) = s+s := by dsimp [s]; push_cast; ring
  have hpos : 1 < (s+s).re := by change 1 < ((x+x:ℝ):ℂ).re + ((x+x:ℝ):ℂ).re; simp only [Complex.ofReal_re]; linarith
  rw [overlapCoefficient_reduced hx hc,commonScaleWeight,Complex.ofReal_add (x+x) (x+x),hs]
  change heat s ((a*k)*(b*k)) / (‖riemannZeta s‖:ℂ)^2 =
    (heat s (a*b)/(‖riemannZeta s‖:ℂ)^2 * riemannZeta (s+s)) * (heat (s+s) k / riemannZeta (s+s))
  have hcancel (A H : ℂ) : (A*riemannZeta (s+s))*(H/riemannZeta (s+s)) = A*H := by
    have hr : riemannZeta (s+s)*(H/riemannZeta (s+s)) = H := by
      rw [← mul_div_assoc,mul_div_cancel_left₀ _ (riemannZeta_ne_zero_of_one_lt_re hpos)]
    rw [mul_assoc,hr]
  rw [hcancel]
  simp only [heat_mul,heat_add]
  ring

/-- The line readings over all primitive directions form a normalized mass function. -/
theorem primitive_lines_total {x : ℝ} (hx : 1/2 < x) :
    (∑' d : _root_.RHTower.ThetaCuspPrimitiveDirection, overlapCoefficient x (gapFrequency d.val)) = 1 := by
  let e := _root_.RHTower.thetaCuspPrimitiveRayIndexEquivPositivePair
  have hsum := (e.summable_iff (f := gapAmplitude x)).mpr (Summable.of_norm (gapAmplitude_summable hx))
  have htotal : (∑' q, gapAmplitude x q) = 1 := by
    have he := squared_floor_eq_carrier hx 0
    simpa [finiteOverlapFloor_zero_time,expSeriesCarrier,expChar] using he.symm
  have ht : (∑' (d : _root_.RHTower.ThetaCuspPrimitiveDirection) (k : ℕ+), gapAmplitude x (e (d,k))) = 1 :=
    hsum.tsum_prod.symm.trans ((e.tsum_eq (gapAmplitude x)).trans htotal)
  rw [← ht]
  apply tsum_congr
  rintro ⟨⟨a,b⟩,hc⟩
  change overlapCoefficient x (gapFrequency (a,b)) = ∑' k : ℕ+, gapAmplitude x (a*k,b*k)
  simp_rw [gapAmplitude_disintegrates hx hc]
  rw [tsum_mul_left,(commonScaleWeight_hasSum (by linarith : 1/4 < x)).tsum_eq,mul_one]

/-- Forgetting the observed direction gives the same scale law as conditioning on any one direction. -/
theorem common_scale_marginal {x : ℝ} (hx : 1/2 < x) (k : ℕ+) :
    (∑' d : _root_.RHTower.ThetaCuspPrimitiveDirection, gapAmplitude x (d.val.1*k,d.val.2*k)) =
      commonScaleWeight x k := by
  have h (d : _root_.RHTower.ThetaCuspPrimitiveDirection) :=
    gapAmplitude_disintegrates hx d.property k
  rw [tsum_congr h,tsum_mul_right,primitive_lines_total hx,one_mul]

/-- At the full gas threshold the common scale still has a normalized inverse-square distribution. -/
theorem commonScaleWeight_critical (k : ℕ+) :
    commonScaleWeight (1/2) k = 1 / ((((k:ℕ):ℂ)^2)*riemannZeta 2) := by
  rw [commonScaleWeight,show ((4*(1/2):ℝ):ℂ) = 2 by norm_num]
  have he : heat 2 k = ((k:ℕ):ℂ)⁻¹ * ((k:ℕ):ℂ)⁻¹ := by
    rw [show (2:ℂ) = 1+1 by norm_num,heat_add,heat_eq_cpow,Complex.cpow_neg_one]
  rw [he]
  simp only [pow_two,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Pointwise convergence of the scale probabilities holds across critical damping. -/
theorem commonScaleWeight_tendsto_critical (k : ℕ+) :
    Tendsto (fun x : ℝ => commonScaleWeight x k) (𝓝 (1/2)) (𝓝 (1 / ((((k:ℕ):ℂ)^2)*riemannZeta 2))) := by
  rw [← commonScaleWeight_critical k]
  let g := fun x : ℝ => ((4*x:ℝ):ℂ)
  have hg : Continuous g := by unfold g; fun_prop
  have hgval : g (1/2) = 2 := by unfold g; norm_num
  have hz := (differentiableAt_riemannZeta (by rw [hgval]; norm_num : g (1/2) ≠ 1)).continuousAt
  have hh : Continuous (fun x : ℝ => heat (g x) k) := by unfold heat g; fun_prop
  exact hh.continuousAt.div (hz.comp hg.continuousAt)
    (riemannZeta_ne_zero_of_one_lt_re (s := g (1/2)) (by rw [hgval]; norm_num))

#print axioms common_scale_summable_iff
#print axioms commonScaleWeight_hasSum
#print axioms commonScaleWeight_positive
#print axioms gapAmplitude_disintegrates
#print axioms primitive_lines_total
#print axioms common_scale_marginal
#print axioms commonScaleWeight_critical
#print axioms commonScaleWeight_tendsto_critical

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
