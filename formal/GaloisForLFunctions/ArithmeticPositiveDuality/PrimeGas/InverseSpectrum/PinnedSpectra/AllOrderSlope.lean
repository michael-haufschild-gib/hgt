import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Ceilings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.LogSlope

/-! # Critical-line response on a single prime with all trace orders constrained -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

def allOrderResponse (σ t R : ℝ) : ℝ :=
  sSup ((fun b : SpectralBand 1 => ‖relativePartition b (⟨σ,t⟩:ℂ)‖) '' (physicalSpectra 1 ∩ ceilingFiber (1/R)))

theorem physical_all_order_envelope {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    (highWindowFactor σ/5)*(t/R^σ) < allOrderResponse σ t R ∧ allOrderResponse σ t R ≤ ((σ+1)/σ)*(t/R^σ) := by
  let A := (fun b : SpectralBand 1 => ‖relativePartition b (⟨σ,t⟩:ℂ)‖) '' (physicalSpectra 1 ∩ ceilingFiber (1/R))
  obtain ⟨b,hb,hL⟩ := physical_all_orders_probe hs ht hR
  have hx : ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ∈ A := ⟨b,hb,rfl⟩
  have hup (x : ℝ) (hx : x ∈ A) : x ≤ ((σ+1)/σ)*(t/R^σ) := by
    obtain ⟨c,hc,rfl⟩ := hx
    exact own_moment_amplitude_cap hs ht hR c (hc.2 ⟨σ,hs⟩)
  exact ⟨hL.trans_le (le_csSup ⟨_,hup⟩ hx),csSup_le ⟨_,hx⟩ hup⟩

theorem all_order_log_slope {σ : ℝ} (hs : 0 < σ) :
    Tendsto (fun t : ℝ => Real.log (allOrderResponse σ t (t^2))/Real.log t) atTop (𝓝 (1-2*σ)) := by
  apply log_slope_of_power_bounds (div_pos (highWindowFactor_pos σ) (by norm_num : (0:ℝ)<5)) (div_pos (add_pos hs zero_lt_one) hs)
  intro t ht
  have ht' := zero_lt_one.trans_le ht
  have he : t/(t^2)^σ = t^(1-2*σ) := by rw [Real.rpow_sub ht',Real.rpow_one,Real.rpow_mul ht'.le,Real.rpow_two]
  obtain ⟨h1,h2⟩ := physical_all_order_envelope hs ht ((le_mul_of_one_le_right ht'.le ht).trans_eq (sq t).symm)
  simpa only [he] using And.intro h1.le h2

/-- The growth rate per additional quantum survives exact preservation of the entire low-energy prefix. -/
theorem all_order_prime_rate {σ : ℝ} (hs : 0 < σ) (p : Nat.Primes) :
    Tendsto (fun k : ℕ => let t := ((p:ℕ):ℝ)^k; Real.log (allOrderResponse σ t (t^2))/(k:ℝ)) atTop
      (𝓝 ((1-2*σ)*Real.log (p:ℕ))) := by
  let a : ℝ := (p:ℕ)
  have hp : 1 < a := by change (1:ℝ) < ((p:ℕ):ℝ); exact_mod_cast p.property.one_lt
  have ht : Tendsto (fun k : ℕ => a^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hp
  have he := ((all_order_log_slope hs).comp ht).mul_const (Real.log a)
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  change Real.log (allOrderResponse σ (a^k) ((a^k)^2))/Real.log (a^k)*Real.log a = _
  rw [Real.log_pow]
  field_simp [(Real.log_pos hp).ne',(Nat.cast_pos.mpr hk : (0:ℝ)<k).ne']

theorem all_order_one_prime_iff_split {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    Tendsto (fun k : ℕ => let t := ((p:ℕ):ℝ)^k; Real.log (allOrderResponse s.re t (t^2))/(k:ℝ)) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro h
    have he := tendsto_nhds_unique (all_order_prime_rate hs p) h
    have hp : (1:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.property.one_lt
    have hz := (mul_eq_zero.mp he).resolve_right (Real.log_pos hp).ne'
    linarith only [hz]
  · intro h
    simpa only [show 1-2*s.re=0 by rw [h]; norm_num,zero_mul] using all_order_prime_rate hs p

#print axioms physical_all_order_envelope
#print axioms all_order_log_slope
#print axioms all_order_prime_rate
#print axioms all_order_one_prime_iff_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
