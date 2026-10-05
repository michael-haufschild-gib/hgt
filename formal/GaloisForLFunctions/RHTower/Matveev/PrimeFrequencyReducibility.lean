import GaloisForLFunctions.RHTower.Matveev.EffectiveBaker
import GaloisForLFunctions.HTGeometry.CombinationModeDiophantineDivisor

/-!
# Combination-mode reducibility for prime frequencies

For distinct primes `p₁, …, p_s` the frequency vector `ℓ = (log pᵢ)` is polynomially Diophantine:
there are `γ > 0` and `κ ∈ ℕ` with

`|m · ℓ| ≥ γ · H(m)^{−κ}`,  `H(m) = max(3, maxᵢ |mᵢ|)`,

for every nonzero integer mode `m`.  This is the effective Baker bound
(`effectiveBakerBound_holds`), since `2 + |m|₁ ≤ (s + 1) H(m)`.  Consequently every
combination-mode cohomological equation `Dh = g` with analytic data `|ĝ(m)| ≤ e^{−ρ|m|₁}` has its
mode-divided solution in `L²`: the cocycle is reducible.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset GaloisForLFunctions.HTGeometry

/-- `2 + |m|₁ ≤ (s + 1) H(m)`. -/
theorem two_add_modeNorm_le {s : ℕ} (mv : Fin s → ℤ) :
    (2 : ℝ) + modeNorm mv ≤ (s + 1) * modeHeight mv := by
  have hsup : ∀ i, (mv i).natAbs ≤ modeHeight mv := fun i =>
    le_trans (Finset.le_sup (f := fun j => (mv j).natAbs) (mem_univ i)) (le_max_right _ _)
  have hnorm : modeNorm mv ≤ s * modeHeight mv := by
    unfold modeNorm
    calc ∑ i, (mv i).natAbs ≤ ∑ _i : Fin s, modeHeight mv := sum_le_sum fun i _ => hsup i
      _ = s * modeHeight mv := by simp
  have h3 : 3 ≤ modeHeight mv := le_max_left _ _
  have : 2 + modeNorm mv ≤ (s + 1) * modeHeight mv := by nlinarith
  exact_mod_cast this

/-- **Lemma R(ii): prime logarithms are polynomially Diophantine.** -/
theorem exists_primeFrequency_diophantine {s : ℕ} (p : Fin s → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ κ : ℕ, ∀ mv : Fin s → ℤ, mv ≠ 0 →
      γ / (modeHeight mv : ℝ) ^ κ ≤ |modeForm (fun i => Real.log (p i)) mv| := by
  obtain ⟨c, C, hc, hC, hbound⟩ := effectiveBakerBound_holds p hp hprime
  set κ := ⌈C⌉₊ with hκ
  refine ⟨c / ((s : ℝ) + 1) ^ κ, by positivity, κ, fun mv hmv => ?_⟩
  have hform : modeForm (fun i => Real.log (p i)) mv = primeLogForm p mv := rfl
  have hnorm : coeffHeight mv = modeNorm mv := rfl
  rw [hform]
  refine le_trans ?_ (hbound mv hmv)
  rw [hnorm]
  have hH3 : (3 : ℝ) ≤ modeHeight mv := by exact_mod_cast le_max_left 3 _
  have hbase := two_add_modeNorm_le mv
  have hpos : (0 : ℝ) < 2 + modeNorm mv := by positivity
  have hY1 : (1 : ℝ) ≤ ((s : ℝ) + 1) * modeHeight mv := by nlinarith
  -- `(2 + |m|₁)^{−C} ≥ ((s+1) H)^{−κ}`
  have h1 : (((s : ℝ) + 1) * modeHeight mv) ^ (-(κ : ℝ)) ≤ (2 + (modeNorm mv : ℝ)) ^ (-C) := by
    calc (((s : ℝ) + 1) * modeHeight mv) ^ (-(κ : ℝ))
        ≤ (((s : ℝ) + 1) * modeHeight mv) ^ (-C) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [Nat.le_ceil C])
      _ ≤ (2 + (modeNorm mv : ℝ)) ^ (-C) :=
          Real.rpow_le_rpow_of_nonpos hpos hbase (by linarith)
  have h2 : (((s : ℝ) + 1) * modeHeight mv) ^ (-(κ : ℝ)) =
      1 / (((s : ℝ) + 1) ^ κ * (modeHeight mv : ℝ) ^ κ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, mul_pow, one_div]
  calc c / ((s : ℝ) + 1) ^ κ / (modeHeight mv : ℝ) ^ κ
      = c * (((s : ℝ) + 1) * modeHeight mv) ^ (-(κ : ℝ)) := by
        rw [h2]; field_simp
    _ ≤ c * (2 + (modeNorm mv : ℝ)) ^ (-C) := mul_le_mul_of_nonneg_left h1 hc.le

/-- **Combination-mode reducibility for prime frequencies.**  For distinct primes and analytic
data `|ĝ(m)| ≤ e^{−ρ|m|₁}`, the mode-divided solution `ĥ(m) = ĝ(m)/(m · ℓ)` is square-summable. -/
theorem summable_primeModeDivisor {s : ℕ} (p : Fin s → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) {ρ : ℝ} (hρ : 0 < ρ) (ĝ : (Fin s → ℤ) → ℂ)
    (hĝ : ∀ mv, ‖ĝ mv‖ ≤ Real.exp (-ρ * (modeNorm mv : ℝ))) :
    Summable (fun mv : {mv : Fin s → ℤ // mv ≠ 0} =>
      ‖ĝ (mv : Fin s → ℤ)‖ ^ (2 : ℕ) /
        (modeForm (fun i => Real.log (p i)) (mv : Fin s → ℤ)) ^ (2 : ℕ)) := by
  obtain ⟨γ, hγ, κ, hdioph⟩ := exists_primeFrequency_diophantine p hp hprime
  exact summable_modeDivisor_of_diophantine _ hγ hρ κ hdioph ĝ hĝ

/-- **Logarithmic recurrence time.**  For distinct primes there is `C` with
`τ₀(ν) = max(0, −log |Σ νᵢ log pᵢ|) ≤ C log(2 + |ν|₁)` for every nonzero `ν`. -/
theorem exists_neg_log_primeLogForm_le {d : ℕ} (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Fin d → ℤ, ν ≠ 0 →
      max 0 (-Real.log |primeLogForm p ν|) ≤ C * Real.log (2 + (coeffHeight ν : ℝ)) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := effectiveBakerBound_holds p hp hprime
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|Real.log c| / Real.log 2 + C, by positivity, fun ν hν => ?_⟩
  set H : ℝ := 2 + (coeffHeight ν : ℝ) with hH
  have hH2 : 2 ≤ H := by rw [hH]; have := (Nat.cast_nonneg (coeffHeight ν) : (0 : ℝ) ≤ _); linarith
  have hlH : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH2
  have hb := hbound ν hν
  have hpos : 0 < c * H ^ (-C) := by positivity
  have hlog : Real.log c - C * Real.log H ≤ Real.log |primeLogForm p ν| := by
    have := Real.log_le_log hpos hb
    rwa [Real.log_mul hc.ne' (by positivity), Real.log_rpow (by linarith), neg_mul,
      ← sub_eq_add_neg] at this
  have hc' : -Real.log c ≤ |Real.log c| / Real.log 2 * Real.log H := by
    have h1 : -Real.log c ≤ |Real.log c| := neg_le_abs _
    have h2 : |Real.log c| ≤ |Real.log c| / Real.log 2 * Real.log H := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlH (abs_nonneg _)
    linarith
  refine max_le (mul_nonneg (by positivity) (by linarith)) ?_
  nlinarith

end GaloisForLFunctions.RHTower.Matveev
