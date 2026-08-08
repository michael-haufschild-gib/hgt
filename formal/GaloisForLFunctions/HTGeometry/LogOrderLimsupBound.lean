import Mathlib

/-!
# Logarithmic order from polynomial growth

A nonnegative sequence dominated by a polynomial of degree `d` has logarithmic order at most `d`:
the limsup of `log(1 + f N) / log(N + 1)` is bounded by `d` (`limsup_log_one_add_div_log_le`).

This is the analytic capstone for order laws of the shape `Ψ = limsup log(1 + a_N) / log(N+1) ≤ d`:
once a coefficient sequence is bounded by a degree-`d` polynomial (for instance an additive
convolution power bounded by a binomial count), its logarithmic growth exponent cannot exceed `d`.
The one-sided constant `log(1 + C)` is washed out by the diverging denominator `log(N + 1)`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Logarithmic order bound from polynomial domination.**  If `0 ≤ f N ≤ C·(N+1)^d` for all `N`
(with `C > 0`), then `limsup_N log(1 + f N) / log(N + 1) ≤ d`.  The dominating polynomial contributes
`d·log(N+1)` to the numerator and a constant `log(1+C)` that vanishes against the denominator. -/
theorem limsup_log_one_add_div_log_le {f : ℕ → ℝ} {C : ℝ} {d : ℕ} (hC : 0 < C)
    (hf : ∀ N, 0 ≤ f N) (hbound : ∀ N, f N ≤ C * ((N : ℝ) + 1) ^ d) :
    Filter.limsup (fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)) Filter.atTop ≤ (d : ℝ) := by
  set g : ℕ → ℝ := fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1) with hg
  set h : ℕ → ℝ := fun N => (d : ℝ) + Real.log (1 + C) / Real.log ((N : ℝ) + 1) with hh
  have hcob : IsCoboundedUnder (· ≤ ·) atTop g :=
    isCoboundedUnder_le_of_le atTop (fun N => div_nonneg
      (Real.log_nonneg (by linarith [hf N]))
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)))
  have hlogtop : Tendsto (fun N : ℕ => Real.log ((N:ℝ)+1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hhlim : Tendsto h atTop (𝓝 (d:ℝ)) := by
    have h0 : Tendsto (fun N : ℕ => Real.log (1+C) / Real.log ((N:ℝ)+1)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hlogtop
    simpa [hh] using tendsto_const_nhds.add h0
  have hgh : ∀ᶠ N in atTop, g N ≤ h N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hlogpos : 0 < Real.log ((N:ℝ)+1) := Real.log_pos (by linarith)
    have hpow1 : (1:ℝ) ≤ ((N:ℝ)+1)^d := one_le_pow₀ (by linarith)
    have hle : 1 + f N ≤ (1 + C) * ((N:ℝ)+1) ^ d := by nlinarith [hbound N, hpow1, hC]
    have key : Real.log (1 + f N) ≤ Real.log (1+C) + (d:ℝ) * Real.log ((N:ℝ)+1) := by
      calc Real.log (1 + f N) ≤ Real.log ((1+C) * ((N:ℝ)+1)^d) :=
            Real.log_le_log (by linarith [hf N]) hle
        _ = Real.log (1+C) + (d:ℝ) * Real.log ((N:ℝ)+1) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [hg, hh, div_le_iff₀ hlogpos, add_mul, div_mul_cancel₀ _ hlogpos.ne']
    linarith [key]
  calc Filter.limsup g atTop ≤ Filter.limsup h atTop :=
        limsup_le_limsup hgh hcob hhlim.isBoundedUnder_le
    _ = (d:ℝ) := hhlim.limsup_eq

/-- **Absorbing finitely many exceptional indices.**  An eventual bound on the logarithmic order
quotient of the positive part becomes a global subpower bound after enlarging the constant. -/
theorem exists_global_subpower_of_eventually {f : ℕ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hev : ∀ᶠ N in atTop, Real.log (1 + max (f N) 0) / Real.log ((N : ℝ) + 1) < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, f N ≤ C * ((N : ℝ) + 1) ^ lam := by
  obtain ⟨Q₀, hQ₀⟩ := hev.exists_forall_of_atTop
  set Q : ℕ := max Q₀ 1 with hQdef
  set C : ℝ := 1 + ∑ N ∈ Finset.range Q, max (f N) 0 with hCdef
  have hsum0 : 0 ≤ ∑ N ∈ Finset.range Q, max (f N) 0 :=
    Finset.sum_nonneg fun N _ => le_max_right _ _
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  refine ⟨C, by linarith, fun N => ?_⟩
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ lam := Real.one_le_rpow (by linarith) hlam
  have hmax : f N ≤ max (f N) 0 := le_max_left _ _
  rcases lt_or_ge N Q with hN | hN
  · have hmem : max (f N) 0 ≤ ∑ P ∈ Finset.range Q, max (f P) 0 :=
      Finset.single_le_sum (f := fun P : ℕ => max (f P) 0)
        (fun P _ => le_max_right _ _) (Finset.mem_range.mpr hN)
    have hle : max (f N) 0 ≤ C := by rw [hCdef]; linarith
    nlinarith [hmax, hle, hpow1]
  · have hN1 : 1 ≤ N := le_trans (le_max_right Q₀ 1) hN
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hlog : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    have hbound := hQ₀ N (le_trans (le_max_left Q₀ 1) hN)
    rw [div_lt_iff₀ hlog] at hbound
    have hlogle : Real.log (1 + max (f N) 0) ≤ Real.log (((N : ℝ) + 1) ^ lam) := by
      rw [Real.log_rpow (by linarith)]
      linarith
    have hposArg : (0 : ℝ) < 1 + max (f N) 0 := by
      have := le_max_right (f N) 0
      linarith
    have hle : 1 + max (f N) 0 ≤ ((N : ℝ) + 1) ^ lam := by
      have hexp := Real.exp_le_exp.mpr hlogle
      rwa [Real.exp_log hposArg, Real.exp_log (by positivity)] at hexp
    nlinarith [hmax, hle, hpow1, hC1]

/-- The logarithmic order quotients of a positive part are nonnegative. -/
theorem log_one_add_max_div_log_nonneg (f : ℕ → ℝ) (N : ℕ) :
    0 ≤ Real.log (1 + max (f N) 0) / Real.log ((N : ℝ) + 1) := by
  have hnum : 0 ≤ Real.log (1 + max (f N) 0) :=
    Real.log_nonneg (by linarith [le_max_right (f N) 0])
  have hden : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  positivity

/-- **Direct absorption.**  An eventual bare subpower bound becomes a global one after enlarging
the constant. -/
theorem exists_global_subpower_of_eventually_le {f : ℕ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hev : ∀ᶠ N in atTop, f N ≤ ((N : ℝ) + 1) ^ lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, f N ≤ C * ((N : ℝ) + 1) ^ lam := by
  obtain ⟨Q, hQ⟩ := hev.exists_forall_of_atTop
  set C : ℝ := 1 + ∑ N ∈ Finset.range Q, max (f N) 0 with hCdef
  have hsum0 : 0 ≤ ∑ N ∈ Finset.range Q, max (f N) 0 :=
    Finset.sum_nonneg fun N _ => le_max_right _ _
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  refine ⟨C, by linarith, fun N => ?_⟩
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ lam := Real.one_le_rpow (by linarith) hlam
  rcases lt_or_ge N Q with hN | hN
  · have hmem : max (f N) 0 ≤ ∑ P ∈ Finset.range Q, max (f P) 0 :=
      Finset.single_le_sum (f := fun P : ℕ => max (f P) 0)
        (fun P _ => le_max_right _ _) (Finset.mem_range.mpr hN)
    have hle : f N ≤ C := by
      have := le_max_left (f N) 0
      rw [hCdef]
      linarith
    nlinarith [hle, hpow1]
  · nlinarith [hQ N hN, hpow1, hC1]

end GaloisForLFunctions.HTGeometry
