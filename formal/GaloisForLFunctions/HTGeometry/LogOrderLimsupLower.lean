import GaloisForLFunctions.HTGeometry.LogOrderLimsupBound

/-!
# Logarithmic order from below

Companion to `limsup_log_one_add_div_log_le`.  A sequence dominated by a degree-`d` polynomial has
a bounded logarithmic order quotient, and any exponent attained infinitely often is a lower bound
for the limsup.  Together these pin the order exponent between the two sides of an order law.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The logarithmic order quotient of a polynomially dominated sequence is bounded above. -/
theorem isBoundedUnder_log_one_add_div_log {f : ℕ → ℝ} {C : ℝ} {d : ℕ} (hC : 0 < C)
    (hf : ∀ N, 0 ≤ f N) (hbound : ∀ N, f N ≤ C * ((N : ℝ) + 1) ^ d) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)) := by
  refine ⟨(d : ℝ) + Real.log (1 + C) / Real.log 2, ?_⟩
  rw [eventually_map]
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
  have hle : 1 + f N ≤ (1 + C) * ((N : ℝ) + 1) ^ d := by nlinarith [hbound N, hpow1, hC]
  have key : Real.log (1 + f N) ≤ Real.log (1 + C) + (d : ℝ) * Real.log ((N : ℝ) + 1) := by
    calc Real.log (1 + f N) ≤ Real.log ((1 + C) * ((N : ℝ) + 1) ^ d) :=
          Real.log_le_log (by linarith [hf N]) hle
      _ = Real.log (1 + C) + (d : ℝ) * Real.log ((N : ℝ) + 1) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlogC : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  rw [div_le_iff₀ hlogpos]
  have hexp : Real.log (1 + C) ≤ Real.log (1 + C) / Real.log 2 * Real.log ((N : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  nlinarith [key, hexp]

/-- **Logarithmic order bound from below.**  An exponent attained infinitely often bounds the
logarithmic order quotient from below. -/
theorem le_limsup_log_one_add_div_log {f : ℕ → ℝ} {β : ℝ}
    (hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)))
    (hfreq : ∃ᶠ N : ℕ in atTop, ((N : ℝ) + 1) ^ β ≤ f N) :
    β ≤ Filter.limsup (fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)) atTop := by
  refine Filter.le_limsup_of_frequently_le ?_ hbdd
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_
  rintro N ⟨hfN, hN⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hpowpos : (0 : ℝ) < ((N : ℝ) + 1) ^ β := by positivity
  have hlow : Real.log (((N : ℝ) + 1) ^ β) ≤ Real.log (1 + f N) :=
    Real.log_le_log hpowpos (by linarith)
  rw [Real.log_rpow (by linarith)] at hlow
  rw [le_div_iff₀ hlogpos]
  linarith


/-- **Logarithmic order bound from real-exponent polynomial domination.**  The real-exponent form
of `limsup_log_one_add_div_log_le`. -/
theorem limsup_log_one_add_div_log_le_rpow {f : ℕ → ℝ} {C d : ℝ} (hC : 0 < C) (hd : 0 ≤ d)
    (hf : ∀ N, 0 ≤ f N) (hbound : ∀ N, f N ≤ C * ((N : ℝ) + 1) ^ d) :
    Filter.limsup (fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)) atTop ≤ d := by
  set g : ℕ → ℝ := fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1) with hg
  set h : ℕ → ℝ := fun N => d + Real.log (1 + C) / Real.log ((N : ℝ) + 1) with hh
  have hcob : IsCoboundedUnder (· ≤ ·) atTop g :=
    isCoboundedUnder_le_of_le atTop (fun N => div_nonneg
      (Real.log_nonneg (by linarith [hf N]))
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)))
  have hlogtop : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hhlim : Tendsto h atTop (𝓝 d) := by
    have h0 : Tendsto (fun N : ℕ => Real.log (1 + C) / Real.log ((N : ℝ) + 1)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hlogtop
    simpa [hh] using tendsto_const_nhds.add h0
  have hgh : ∀ᶠ N in atTop, g N ≤ h N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ d :=
      Real.one_le_rpow (by linarith) hd
    have hle : 1 + f N ≤ (1 + C) * ((N : ℝ) + 1) ^ d := by nlinarith [hbound N, hpow1, hC]
    have key : Real.log (1 + f N) ≤ Real.log (1 + C) + d * Real.log ((N : ℝ) + 1) := by
      calc Real.log (1 + f N) ≤ Real.log ((1 + C) * ((N : ℝ) + 1) ^ d) :=
            Real.log_le_log (by linarith [hf N]) hle
        _ = Real.log (1 + C) + d * Real.log ((N : ℝ) + 1) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by linarith)]
    rw [hg, hh, div_le_iff₀ hlogpos, add_mul, div_mul_cancel₀ _ hlogpos.ne']
    linarith [key]
  calc Filter.limsup g atTop ≤ Filter.limsup h atTop :=
        limsup_le_limsup hgh hcob hhlim.isBoundedUnder_le
    _ = d := hhlim.limsup_eq

end GaloisForLFunctions.HTGeometry
