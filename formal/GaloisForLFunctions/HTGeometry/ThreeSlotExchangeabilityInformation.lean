import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry

/-!
# Three-slot exchangeability information and global formation properness

The ordered three-slot laws of an alternating reflected pair differ by one adjacent transposition.
Their relative entropy is exactly the Jeffreys divergence of the two phases, it survives every
common Markov recovery unchanged, and it is additive over independent formation depth.  Uniformly
bounded work along unbounded depth is therefore equivalent to neutrality of the reflected pair.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

variable {A : Type*} [MeasurableSpace A]

/-! ## The two ordered three-slot laws -/

/-- Ordered three-slot law with the reflected phase in the middle slot. -/
def slotAlpha (P Q : Measure A) : Measure (A × A × A) := P.prod (Q.prod P)

/-- Ordered three-slot law with the reflected phase in the last slot. -/
def slotBeta (P Q : Measure A) : Measure (A × A × A) := P.prod (P.prod Q)

instance isProbabilityMeasure_slotAlpha (P Q : Measure A) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : IsProbabilityMeasure (slotAlpha P Q) := by
  rw [slotAlpha]; infer_instance

instance isProbabilityMeasure_slotBeta (P Q : Measure A) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : IsProbabilityMeasure (slotBeta P Q) := by
  rw [slotBeta]; infer_instance

/-- **Permutation information identity.**  The adjacent transposition of the second and third
formation slots costs exactly the Jeffreys divergence of the two reflected phases. -/
theorem klDiv_slotAlpha_slotBeta (P Q : Measure A) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    klDiv (slotAlpha P Q) (slotBeta P Q) = klDiv P Q + klDiv Q P := by
  rw [slotAlpha, slotBeta, klDiv_prod, klDiv_self, zero_add, klDiv_prod, add_comm]

/-- Reflection of the two phases leaves the permutation information unchanged. -/
theorem klDiv_slot_reflection (P Q : Measure A) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    klDiv (slotAlpha Q P) (slotBeta Q P) = klDiv (slotAlpha P Q) (slotBeta P Q) := by
  rw [klDiv_slotAlpha_slotBeta, klDiv_slotAlpha_slotBeta, add_comm]

/-- **Strict zero locus.** -/
theorem klDiv_slot_eq_zero_iff (P Q : Measure A) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    klDiv (slotAlpha P Q) (slotBeta P Q) = 0 ↔ P = Q := by
  rw [klDiv_slotAlpha_slotBeta, add_eq_zero]
  constructor
  · rintro ⟨h, -⟩
    exact klDiv_eq_zero_iff.1 h
  · rintro rfl
    simp

/-! ## Common recovery is information-neutral -/

/-- **Recovery neutrality.**  Adjoining an independent conditional recovery coordinate through one
common Markov kernel changes no permutation information. -/
theorem klDiv_slot_recovery {H : Type*} [MeasurableSpace H] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (κ : Kernel (A × A × A) H) [IsMarkovKernel κ] :
    klDiv (slotAlpha P Q ⊗ₘ κ) (slotBeta P Q ⊗ₘ κ) = klDiv P Q + klDiv Q P := by
  rw [klDiv_compProd_left, klDiv_slotAlpha_slotBeta]

/-! ## Global formation properness -/

/-- Complete exchangeability work of `m` independent ordered three-slot experiments. -/
def slotWork (P Q : Measure A) (m : ℕ) : ℝ≥0∞ :=
  klDiv (Measure.pi fun _ : Fin m => slotAlpha P Q) (Measure.pi fun _ : Fin m => slotBeta P Q)

/-- **Exact conservation.** -/
theorem slotWork_eq (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (m : ℕ) :
    slotWork P Q m = m * (klDiv P Q + klDiv Q P) := by
  rw [slotWork, klDiv_pi]
  simp only [klDiv_slotAlpha_slotBeta, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem slotWork_add (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m n : ℕ) : slotWork P Q (m + n) = slotWork P Q m + slotWork P Q n := by
  rw [slotWork_eq, slotWork_eq, slotWork_eq]
  push_cast
  rw [add_mul]

/-- **Global formation properness.**  Uniformly bounded work across unbounded formation depth is
possible exactly on the neutral locus. -/
theorem slotWork_bddAbove_iff (P Q : Measure A) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ m : ℕ, slotWork P Q m ≤ C) ↔ P = Q := by
  constructor
  · rintro ⟨C, hC, hbdd⟩
    by_contra hne
    have hJ : klDiv P Q + klDiv Q P ≠ 0 := by
      intro h
      exact hne ((klDiv_slot_eq_zero_iff P Q).1 (by rw [klDiv_slotAlpha_slotBeta, h]))
    set J : ℝ≥0∞ := klDiv P Q + klDiv Q P with hJdef
    have h1 := hbdd 1
    rw [slotWork_eq] at h1
    simp only [Nat.cast_one, one_mul] at h1
    have hJtop : J ≠ ⊤ := fun h => hC (top_le_iff.1 (h ▸ h1))
    have hJpos : 0 < J.toReal := ENNReal.toReal_pos hJ hJtop
    obtain ⟨m, hm⟩ := exists_nat_gt (C.toReal / J.toReal)
    have hle := hbdd m
    rw [slotWork_eq] at hle
    have hreal : (m : ℝ) * J.toReal ≤ C.toReal := by
      have := ENNReal.toReal_mono hC hle
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
    rw [div_lt_iff₀ hJpos] at hm
    linarith
  · rintro rfl
    exact ⟨0, by simp, fun m => by simp [slotWork_eq]⟩

/-! ## Reflection-family selection -/

/-- **Reflection-family selection.**  For a reflection-separating family, bounded global three-slot
work occurs exactly at the reflection fixed point. -/
theorem slotWork_bddAbove_iff_neutral {X : Type*} (p : X → Measure A)
    [∀ x, IsProbabilityMeasure (p x)] (rfl' : X → X) (x₀ : X)
    (hsep : ∀ x, p x = p (rfl' x) ↔ x = x₀) (x : X) :
    (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ m : ℕ, slotWork (p x) (p (rfl' x)) m ≤ C) ↔ x = x₀ := by
  rw [slotWork_bddAbove_iff, hsep]

/-- The logistic reflected family on a two-letter alphabet. -/
def logisticPhase (x : ℝ) : unitInterval :=
  ⟨Real.exp x / (1 + Real.exp x), by
    have h := Real.exp_pos x
    constructor
    · positivity
    · rw [div_le_one (by linarith)]
      linarith⟩

@[simp] theorem coe_logisticPhase (x : ℝ) :
    (logisticPhase x : ℝ) = Real.exp x / (1 + Real.exp x) := rfl

/-- The logistic family is reflection-separating. -/
theorem logisticPhase_eq_iff (x : ℝ) : logisticPhase x = logisticPhase (-x) ↔ x = 0 := by
  have hx := Real.exp_pos x
  have hnx := Real.exp_pos (-x)
  have hone : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; simp
  constructor
  · intro h
    have h' : Real.exp x / (1 + Real.exp x) = Real.exp (-x) / (1 + Real.exp (-x)) := by
      simpa using congrArg (fun y : unitInterval => (y : ℝ)) h
    rw [div_eq_div_iff (by linarith) (by linarith)] at h'
    have hexp : Real.exp x = Real.exp (-x) := by nlinarith [h', hone]
    have := Real.exp_injective hexp
    linarith
  · rintro rfl
    norm_num

end

end GaloisForLFunctions.HTGeometry
