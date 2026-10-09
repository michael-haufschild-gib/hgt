import GaloisForLFunctions.RHTower.RiemannAutocorrFiniteTranslation

/-!
# Exact finite paired-log cancellations

The only finite cancellation of paired-log kernel rows is the repeated
logarithmic coordinate at indices zero and one. Every coefficient at an
index at least two is detected by the full shift family.
-/

open Real Complex
open scoped BigOperators
open Zeta23

noncomputable section

namespace RHTower

/-- The finite translate coefficients obtained by merging both logarithmic signs. -/
def finitePairedLogSpectrum (v : ℕ →₀ ℂ) : ℝ →₀ ℂ :=
  v.mapDomain (fun n : ℕ => Real.log n) + v.mapDomain (fun n : ℕ => -Real.log n)

/-- The merged translate spectrum synthesizes the literal paired-log potential. -/
theorem finitePairedLogSpectrum_synthesis (v : ℕ →₀ ℂ) (y : ℝ) :
    (finitePairedLogSpectrum v).sum (fun a c => c * ((riemannAutocorr (y + a) : ℝ) : ℂ)) =
      v.sum (fun n c => c * (pairedLogKernel y n : ℂ)) := by
  change (Finsupp.linearCombination ℂ (fun a : ℝ => ((riemannAutocorr (y + a) : ℝ) : ℂ)))
    (finitePairedLogSpectrum v) = _
  rw [finitePairedLogSpectrum, map_add, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply]
  simp only [Function.comp_apply, smul_eq_mul, Finsupp.sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [pairedLogKernel, Complex.ofReal_add, sub_eq_add_neg]
  ring

private theorem log_nat_fibre_of_two_le (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    Real.log (m : ℝ) = Real.log (n : ℝ) ↔ m = n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  constructor
  · intro h
    by_cases hm : m = 0
    · subst m
      simp only [Nat.cast_zero, Real.log_zero] at h
      exact False.elim (hnlog.ne' h.symm)
    · have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      exact Nat.cast_injective (Real.log_injOn_pos hmpos (lt_trans zero_lt_one hn1) h)
  · rintro rfl
    rfl

/-- Positive logarithmic coordinates recover their coefficient exactly. -/
theorem finitePairedLogSpectrum_apply_log (v : ℕ →₀ ℂ) (n : ℕ) (hn : 2 ≤ n) :
    finitePairedLogSpectrum v (Real.log n) = v n := by
  classical
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hpos : (v.mapDomain (fun m : ℕ => Real.log m)) (Real.log n) = v n := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_eq_single n]
    · simp
    · intro m _ hmn
      exact Finsupp.single_eq_of_ne' ((log_nat_fibre_of_two_le n hn m).not.mpr hmn)
    · intro _
      simp
  have hneg : (v.mapDomain (fun m : ℕ => -Real.log m)) (Real.log n) = 0 := by
    apply Finsupp.mapDomain_notin_range
    rintro ⟨m, hm⟩
    linarith [Real.log_natCast_nonneg m]
  change (v.mapDomain (fun m : ℕ => Real.log m)) (Real.log n) +
    (v.mapDomain (fun m : ℕ => -Real.log m)) (Real.log n) = v n
  rw [hpos, hneg, add_zero]

private theorem finsupp_eq_zero_one_of_tail_zero (v : ℕ →₀ ℂ)
    (h : ∀ n : ℕ, 2 ≤ n → v n = 0) :
    v = Finsupp.single 0 (v 0) + Finsupp.single 1 (v 1) := by
  ext n
  by_cases h0 : n = 0
  · subst n
    simp
  · by_cases h1 : n = 1
    · subst n
      simp
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne h0,
        Finsupp.single_eq_of_ne h1, add_zero, h n (by omega)]

private theorem finitePairedLogSpectrum_zero_one (a b : ℂ) :
    finitePairedLogSpectrum (Finsupp.single 0 a + Finsupp.single 1 b) =
      Finsupp.single 0 (2 * (a + b)) := by
  simp [finitePairedLogSpectrum, Finsupp.mapDomain_add, ← Finsupp.single_add, two_mul]

/-- Exact algebraic kernel of the finite logarithmic spectrum. -/
theorem finitePairedLogSpectrum_eq_zero_iff (v : ℕ →₀ ℂ) :
    finitePairedLogSpectrum v = 0 ↔ v 0 + v 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → v n = 0 := by
  constructor
  · intro hd
    have htail (n : ℕ) (hn : 2 ≤ n) : v n = 0 := by
      rw [← finitePairedLogSpectrum_apply_log v n hn, hd]
      rfl
    have hv := finsupp_eq_zero_one_of_tail_zero v htail
    rw [hv, finitePairedLogSpectrum_zero_one] at hd
    have hz : (2 : ℂ) * (v 0 + v 1) = 0 := by
      simpa using congrArg (fun d : ℝ →₀ ℂ => d 0) hd
    exact ⟨(mul_eq_zero.mp hz).resolve_left (by norm_num), htail⟩
  · rintro ⟨hzero, htail⟩
    rw [finsupp_eq_zero_one_of_tail_zero v htail, finitePairedLogSpectrum_zero_one,
      hzero, mul_zero, Finsupp.single_zero]

/-- Complete finite cancellation classification for complex coefficients of
the actual real paired-log kernel. -/
theorem finite_pairedLogKernel_complex_sum_eq_zero_iff (v : ℕ →₀ ℂ) :
    (∀ y : ℝ, v.sum (fun n c => c * (pairedLogKernel y n : ℂ)) = 0) ↔
      v 0 + v 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → v n = 0 := by
  have h := riemannAutocorr_translate_sum_eq_zero_iff (finitePairedLogSpectrum v)
  simp only [finitePairedLogSpectrum_synthesis] at h
  exact h.trans (finitePairedLogSpectrum_eq_zero_iff v)

/-- The native real finite kernel has exactly the zero/one alias and no
other finite cancellation. -/
theorem finite_pairedLogKernel_sum_eq_zero_iff (v : ℕ →₀ ℝ) :
    (∀ y : ℝ, v.sum (fun n c => c * pairedLogKernel y n) = 0) ↔
      v 0 + v 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → v n = 0 := by
  let w : ℕ →₀ ℂ := v.mapRange Complex.ofReal (by simp)
  have hw (n : ℕ) : w n = (v n : ℂ) := rfl
  have hsum (y : ℝ) : w.sum (fun n c => c * (pairedLogKernel y n : ℂ)) =
      ((v.sum (fun n c => c * pairedLogKernel y n) : ℝ) : ℂ) := by
    dsimp only [w]
    rw [Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
    simp only [Finsupp.sum, Complex.ofReal_sum, Complex.ofReal_mul]
  have h := finite_pairedLogKernel_complex_sum_eq_zero_iff w
  simpa only [hsum, hw, ← Complex.ofReal_add, Complex.ofReal_eq_zero] using h

end RHTower
