import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve
import GaloisForLFunctions.RHTower.ExteriorSatake
import GaloisForLFunctions.RHTower.AdamsOperations

/-!
# Detecting a local determinant in its logarithmic coefficients

The prime-power logarithmic coefficients in arXiv:2610.18928 are the
power sums of the Satake parameters. Newton's identity bounds each
coefficient of the inverse Euler factor from the power sums alone.
In particular a unit determinant forces some power sum of order at most
the rank to have modulus at least one, without a temperedness assumption.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SelbergClass.LocalPowerSums

/-- The trace of the k-th powers, with multiplicity. -/
abbrev tracePow (s : Multiset ℂ) (k : ℕ) : ℂ := (s.map (fun z => z^k)).sum

private def interiorPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k}

private theorem interior_card (k : ℕ) : (interiorPairs k).card ≤ k-1 := by
  have hi : Set.InjOn Prod.fst (interiorPairs k : Set (ℕ × ℕ)) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd h
    have h₁ := Finset.mem_antidiagonal.mp (mem_filter.mp hab).1
    have h₂ := Finset.mem_antidiagonal.mp (mem_filter.mp hcd).1
    change a = c at h
    exact Prod.ext h (by dsimp at h₁ h₂; omega)
  have h := Finset.card_le_card_of_injOn Prod.fst
    (t := Finset.Ioo 0 k) (fun a ha => Finset.mem_Ioo.mpr (mem_filter.mp ha).2) hi
  simpa using h

private theorem newton_majorant (s : Multiset ℂ) (k : ℕ) (hk : 0 < k) :
    (k : ℝ)*‖s.esymm k‖ ≤ ‖tracePow s k‖ +
      ∑ a ∈ interiorPairs k, ‖s.esymm a.1‖ * ‖tracePow s a.2‖ := by
  have h := multiset_newton_general s k hk
  rw [eq_sub_iff_add_eq] at h
  have hh := (norm_add_le _ _ : ‖tracePow s k +
    ∑ a ∈ interiorPairs k, (-1 : ℂ)^a.1 * s.esymm a.1 * tracePow s a.2‖ ≤ _)
  change tracePow s k + ∑ a ∈ interiorPairs k, _ = _ at h
  rw [h] at hh
  refine le_trans (by simpa [norm_mul] using hh) (add_le_add_left ?_ _)
  simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] using
    norm_sum_le (interiorPairs k) (fun a => (-1 : ℂ)^a.1 * s.esymm a.1 * tracePow s a.2)

private theorem remainder_majorant (s : Multiset ℂ) (k : ℕ) (B : NNReal)
    (hE : ∀ j < k, ‖s.esymm j‖ ≤ (B : ℝ)^j)
    (hP : ∀ j, 0 < j → j < k → ‖tracePow s j‖ ≤ (B : ℝ)^j) :
    (∑ a ∈ interiorPairs k, ‖s.esymm a.1‖ * ‖tracePow s a.2‖) ≤
      ((k-1 : ℕ) : ℝ)*(B : ℝ)^k := by
  calc
    _ ≤ ∑ _a ∈ interiorPairs k, (B : ℝ)^k := by
      apply sum_le_sum
      intro a ha
      have ha' := mem_filter.mp ha
      have he := Finset.mem_antidiagonal.mp ha'.1
      have hi : 0 < a.1 ∧ a.1 < k := ha'.2
      rw [← he, pow_add]
      exact mul_le_mul (hE _ hi.2) (hP _ (by omega) (by omega)) (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast interior_card k) (by positivity)

/-- A geometric bound on logarithmic coefficients propagates to exterior coefficients
with constant one at every degree. -/
theorem exterior_bound (s : Multiset ℂ) (B : NNReal) (k : ℕ) :
    (∀ j, 0 < j → j ≤ k → ‖tracePow s j‖ ≤ (B : ℝ)^j) → ‖s.esymm k‖ ≤ (B : ℝ)^k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hP
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · have he j (hj : j < k) := ih j hj (fun t ht hjt => hP _ ht (hjt.trans hj.le))
      have h := (newton_majorant s k hk).trans (add_le_add (hP _ hk le_rfl)
        (remainder_majorant s k B he (fun j h₁ h₂ => hP j h₁ h₂.le)))
      have hc : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
        rw [Nat.cast_sub (by omega),Nat.cast_one]
      rw [hc] at h
      apply le_of_mul_le_mul_left (a := (k : ℝ)) _ (by exact_mod_cast hk)
      linarith only [h]

/-- The last moment pays for any deficit in the first k−1 moments. -/
theorem last_trace_lower (s : Multiset ℂ) (B : NNReal) (k : ℕ+) :
    (∀ j, 0 < j → j < k → ‖tracePow s j‖ ≤ (B : ℝ)^j) →
      (k : ℝ)*‖s.esymm k‖ - ((k : ℝ)-1)*(B : ℝ)^(k : ℕ) ≤ ‖tracePow s k‖ := by
  intro hP
  have he j (hj : j < k) := exterior_bound s B j
    (fun t ht htj => hP t ht (htj.trans_lt hj))
  have h := (newton_majorant s k k.pos).trans
    (add_le_add_left (remainder_majorant s k B he hP) _)
  rw [Nat.cast_sub (by exact k.pos), Nat.cast_one] at h
  linarith only [h]

/-- Any nonempty spectrum with sufficiently large determinant has a large logarithmic
coefficient within its own rank. -/
theorem determinant_detection (z : ℂ) (rest : Multiset ℂ) (B : NNReal) :
    let s := z ::ₘ rest
    (B : ℝ)^s.card ≤ ‖s.prod‖ → ∃ j, 0 < j ∧ j ≤ s.card ∧ (B : ℝ)^j ≤ ‖tracePow s j‖ := by
  dsimp only
  intro hd
  by_contra! ha
  let s := z ::ₘ rest
  have hk : 0 < s.card := by simp [s]
  have hl := last_trace_lower s B ⟨s.card,hk⟩ (fun j hj hlt => (ha j hj hlt.le).le)
  change (s.card : ℝ)*‖s.esymm s.card‖ - ((s.card : ℝ)-1)*(B : ℝ)^s.card ≤ ‖tracePow s s.card‖ at hl
  rw [multiset_esymm_card_eq_prod] at hl
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (s.card : ℝ))
  have he := ha s.card hk le_rfl
  change (s.card : ℝ) * (B : ℝ)^s.card ≤ (s.card : ℝ)*‖s.prod‖ at hm
  change ‖tracePow s s.card‖ < (B : ℝ)^s.card at he
  linarith only [hl,hm,he]

end GaloisForLFunctions.SelbergClass.LocalPowerSums

#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.exterior_bound
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.last_trace_lower
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.determinant_detection
