import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CumulativeQuadratureOfTheGcdDeficit
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# Multiplicative spacings of the eighth-power gcd shortfall

The half-logarithmic arithmetic asymptotic identifies a finite difference
of deficits with a multiplicative spacing of the two endpoints. This is
the moving-dilation principle of Ponge and Tian (arXiv:2605.25591,
Lemma 2.17) applied to the exponential of the actual gcd shortfall.
The reciprocal right-endpoint readings have a second logarithmic scale.
-/

noncomputable section
open Filter
open scoped Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem log_nat_top : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Exponentiating twice the accumulated shortfall gives a positive
asymptotic multiple of the integer endpoint. -/
theorem eighth_exponential_deficit_density :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun k : ℕ => Real.exp (2*powerGridGcdDeficit 8 k)/(k:ℝ))
      atTop (𝓝 A) := by
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  refine ⟨Real.exp (2*c), Real.exp_pos _,
    (Real.continuous_exp.continuousAt.tendsto.comp (hc.const_mul 2)).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  change Real.exp (2*(powerGridGcdDeficit 8 k-(1/2)*Real.log k)) = _
  rw [show 2*(powerGridGcdDeficit 8 k-(1/2)*Real.log k) =
    2*powerGridGcdDeficit 8 k - Real.log k by ring, Real.exp_sub, Real.exp_log (Nat.cast_pos.mpr hk)]

/-- Two diverging endpoint sequences differ by finite accumulated shortfall
L precisely when their ratio tends to exp(2L). The endpoints need not be
ordered or follow any fixed rounding rule. -/
theorem eighth_deficit_spacing_iff {ι : Type*} {l : Filter ι} {u v : ι → ℕ}
    (hu : Tendsto u l atTop) (hv : Tendsto v l atTop) (L : ℝ) :
    Tendsto (fun i => powerGridGcdDeficit 8 (v i) - powerGridGcdDeficit 8 (u i)) l (𝓝 L) ↔
      Tendsto (fun i => (v i:ℝ)/(u i:ℝ)) l (𝓝 (Real.exp (2*L))) := by
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  have hd := (hc.comp hv).sub (hc.comp hu)
  rw [sub_self] at hd
  have he : Tendsto (fun i => (powerGridGcdDeficit 8 (v i)-powerGridGcdDeficit 8 (u i)) -
      (1/2:ℝ)*Real.log ((v i:ℝ)/(u i:ℝ))) l (𝓝 0) := by
    apply hd.congr'
    filter_upwards [hu.eventually (eventually_ge_atTop 1), hv.eventually (eventually_ge_atTop 1)]
      with i hui hvi
    rw [Real.log_div (Nat.cast_pos.mpr hvi).ne' (Nat.cast_pos.mpr hui).ne']
    change (_ - _)-(_ - _) = _
    ring
  constructor
  · intro h
    have ht := Real.continuous_exp.continuousAt.tendsto.comp ((h.sub he).const_mul 2)
    rw [sub_zero] at ht
    apply ht.congr'
    filter_upwards [hu.eventually (eventually_ge_atTop 1), hv.eventually (eventually_ge_atTop 1)]
      with i hui hvi
    change Real.exp (2*((_ - _)-((_ - _)-(1/2)*Real.log ((v i:ℝ)/(u i:ℝ))))) = _
    convert Real.exp_log (div_pos (Nat.cast_pos.mpr hvi) (Nat.cast_pos.mpr hui)) using 2 <;> ring
  · intro h
    have ht := he.add ((h.log (Real.exp_pos _).ne').const_mul (1/2:ℝ))
    rw [Real.log_exp, zero_add, show (1/2:ℝ)*(2*L)=L by ring] at ht
    exact ht.congr fun i => sub_add_cancel ..

/-- The reciprocal readings at the eighth-power endpoints possess a finite
part after subtracting log log k. -/
theorem eighth_reciprocal_deficit_finite_part :
    ∃ B : ℝ, Tendsto (fun k : ℕ => gcdDeficitLogSum 8 k - Real.log (Real.log k))
      atTop (𝓝 B) := by
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  obtain ⟨d,hd,_⟩ := gcd_log_sum_limiting_error 8
  have hr := ((hc.const_add 1).div_atTop log_nat_top).add_const (1/2:ℝ)
  rw [zero_add] at hr
  have hratio : Tendsto (fun k : ℕ => (1+powerGridGcdDeficit 8 k) / Real.log k) atTop (𝓝 (1/2:ℝ)) := by
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 2] with k hk
    have hl := (Real.log_pos (Nat.one_lt_cast.mpr hk : (1:ℝ)<k)).ne'
    change (1+(powerGridGcdDeficit 8 k-(1/2)*Real.log k))/Real.log k+1/2 = _
    field_simp <;> ring
  have hlog := hratio.log (by norm_num : (1/2:ℝ) ≠ 0)
  refine ⟨Real.log (1/2)-d, (hlog.sub hd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hD : 0 ≤ powerGridGcdDeficit 8 k := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have h₁ : 0 < 1 + powerGridGcdDeficit 8 k := by linarith only [hD]
  have hl := Real.log_pos (Nat.one_lt_cast.mpr hk : (1:ℝ) < k)
  change Real.log ((1+powerGridGcdDeficit 8 k)/Real.log k) -
    (Real.log (1+powerGridGcdDeficit 8 k)-gcdDeficitLogSum 8 k) = _
  rw [Real.log_div h₁.ne' hl.ne']
  ring

#print axioms eighth_exponential_deficit_density
#print axioms eighth_deficit_spacing_iff
#print axioms eighth_reciprocal_deficit_finite_part

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
