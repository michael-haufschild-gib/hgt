import GaloisForLFunctions.RHTower.ThetaQuantileTranslationHistory
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionDerivativeHistory

/-!
# A common positive weight for finite arithmetic and actual Euler histories

One explicit positive weight admits every shift of a finite alphabet,
independently of its complex coefficients. The literal finite source class
is its finite sum of actual translation classes, belongs to the ordinary
derivative history, and vanishes in that history quotient. The actual
finite Euler deletion and every individual prime letter share one weight.
-/

open MeasureTheory Set

namespace RHTower

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

noncomputable section

/-- A coefficient-independent positive weight for the entire finite arithmetic alphabet. -/
def thetaFiniteArithmeticHistoryWeight (D : Finset ℕ) : ℝ :=
  Real.exp (-2 * ∑ d ∈ D, |Real.log (d : ℝ)|)

theorem thetaFiniteArithmeticHistoryWeight_pos (D : Finset ℕ) :
    0 < thetaFiniteArithmeticHistoryWeight D := Real.exp_pos _

theorem thetaFiniteArithmeticHistoryWeight_le_one (D : Finset ℕ) :
    thetaFiniteArithmeticHistoryWeight D ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := Finset.sum_nonneg (fun d (_ : d ∈ D) => abs_nonneg (Real.log (d : ℝ)))
  linarith

theorem thetaFiniteArithmeticHistoryWeight_lt_two (D : Finset ℕ) :
    thetaFiniteArithmeticHistoryWeight D < 2 := by
  have h := thetaFiniteArithmeticHistoryWeight_le_one D
  linarith

/-- All letters have strict Gaussian slack at this single positive weight. -/
theorem thetaFiniteArithmeticHistoryWeight_admits (D : Finset ℕ) (d : ℕ) (hd : d ∈ D) :
    thetaFiniteArithmeticHistoryWeight D < 2 * Real.exp (-2 * |Real.log (d : ℝ)|) := by
  have hlog : |Real.log (d : ℝ)| ≤ ∑ i ∈ D, |Real.log (i : ℝ)| :=
    Finset.single_le_sum (fun i (_ : i ∈ D) => abs_nonneg (Real.log (i : ℝ))) hd
  have hle : thetaFiniteArithmeticHistoryWeight D ≤
      Real.exp (-2 * |Real.log (d : ℝ)|) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpos := Real.exp_pos (-2 * |Real.log (d : ℝ)|)
  linarith

private theorem toLp_finite_sum_as_classes (μ : Measure ℝ) (D : Finset ℕ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ d ∈ D, MemLp (f d) 2 μ) :
    (memLp_finsetSum D hf).toLp (fun x => ∑ d ∈ D, f d x) =
      ∑ d ∈ D, l2Family μ (fun _ x => f d x) 0 := by
  classical
  revert hf
  induction D using Finset.induction_on with
  | empty => intro hf; simp only [Finset.sum_empty]; rfl
  | @insert d D hnot ih =>
    intro hf
    have hfd := hf d (Finset.mem_insert_self d D)
    have hfD : ∀ i ∈ D, MemLp (f i) 2 μ :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum := memLp_finsetSum D hfD
    have he : (memLp_finsetSum (insert d D) hf).toLp (fun x => ∑ i ∈ insert d D, f i x) =
        (hfd.add hsum).toLp (f d + fun x => ∑ i ∈ D, f i x) := by
      apply MemLp.toLp_congr
      apply ae_of_all
      intro x
      change (∑ i ∈ insert d D, f i x) = f d x + ∑ i ∈ D, f i x
      rw [Finset.sum_insert hnot]
    rw [he, MemLp.toLp_add hfd hsum, Finset.sum_insert hnot,
      l2Family_eq_toLp μ (fun _ x => f d x) 0 hfd, ih hfD]

/-- Every literal complex word is admitted, including empty support and arbitrary cancellation. -/
theorem finiteComplexArithmeticThetaShift_memLp_history_weight
    (D : Finset ℕ) (c : ℕ → ℂ) :
    MemLp (finiteComplexArithmeticThetaShift D c) 2
      (thetaPowerWeightedMeasure (thetaFiniteArithmeticHistoryWeight D)) := by
  have hf : ∀ d ∈ D,
      MemLp (fun x : ℝ => c d • (thetaRealShiftSource (Real.log (d : ℝ)) x : ℂ)) 2
        (thetaPowerWeightedMeasure (thetaFiniteArithmeticHistoryWeight D)) := by
    intro d hd
    exact (thetaRealShiftSource_ofReal_memLp (thetaFiniteArithmeticHistoryWeight D)
      (Real.log (d : ℝ)) (thetaFiniteArithmeticHistoryWeight_pos D)
      (thetaFiniteArithmeticHistoryWeight_admits D d hd)).const_smul (c d)
  change MemLp (fun x : ℝ => ∑ d ∈ D, c d • (thetaRealShiftSource (Real.log (d : ℝ)) x : ℂ))
    2 (thetaPowerWeightedMeasure (thetaFiniteArithmeticHistoryWeight D))
  exact memLp_finsetSum D hf

/-- The actual `toLp` class of the full finite word in its explicitly selected carrier. -/
def thetaGradedArithmeticVector (D : Finset ℕ) (c : ℕ → ℂ) :
    Lp ℂ 2 (thetaPowerWeightedMeasure (thetaFiniteArithmeticHistoryWeight D)) :=
  (finiteComplexArithmeticThetaShift_memLp_history_weight D c).toLp
    (finiteComplexArithmeticThetaShift D c)

/-- Finite synthesis agrees with the literal function class, rather than defining it that way. -/
theorem thetaGradedArithmeticVector_eq_sum (D : Finset ℕ) (c : ℕ → ℂ) :
    thetaGradedArithmeticVector D c =
      ∑ d ∈ D, c d • thetaWeightedTranslationClass (thetaFiniteArithmeticHistoryWeight D)
        (Real.log (d : ℝ) : ℂ) := by
  classical
  let q := thetaFiniteArithmeticHistoryWeight D
  let f : ℕ → ℝ → ℂ := fun d x => c d • (thetaRealShiftSource (Real.log (d : ℝ)) x : ℂ)
  have htrans : ∀ d ∈ D,
      MemLp (fun x : ℝ => (thetaRealShiftSource (Real.log (d : ℝ)) x : ℂ)) 2
        (thetaPowerWeightedMeasure q) :=
    fun d hd => thetaRealShiftSource_ofReal_memLp q (Real.log (d : ℝ))
      (thetaFiniteArithmeticHistoryWeight_pos D) (thetaFiniteArithmeticHistoryWeight_admits D d hd)
  have hf : ∀ d ∈ D, MemLp (f d) 2 (thetaPowerWeightedMeasure q) :=
    fun d hd => (htrans d hd).const_smul (c d)
  have hsum := memLp_finsetSum D hf
  have he : finiteComplexArithmeticThetaShift D c = (fun x => ∑ d ∈ D, f d x) := by
    funext x
    simp only [finiteComplexArithmeticThetaShift, f, thetaRealShiftSource, smul_eq_mul]
  rw [thetaGradedArithmeticVector,
    (finiteComplexArithmeticThetaShift_memLp_history_weight D c).toLp_congr hsum
      (ae_of_all _ fun x => congrFun he x),
    toLp_finite_sum_as_classes (thetaPowerWeightedMeasure q) D f hf]
  apply Finset.sum_congr rfl
  intro d hd
  rw [l2Family_eq_toLp (thetaPowerWeightedMeasure q) (fun _ x => f d x) 0 (hf d hd)]
  change ((htrans d hd).const_smul (c d)).toLp _ = _
  rw [MemLp.toLp_const_smul (c d) (htrans d hd),
    thetaWeightedTranslationClass_eq_toLp q (Real.log (d : ℝ)) (htrans d hd)]
  rfl

theorem thetaGradedArithmeticVector_mem_derivativeHistory (D : Finset ℕ) (c : ℕ → ℂ) :
    thetaGradedArithmeticVector D c ∈
      thetaWeightedDerivativeHistory (thetaFiniteArithmeticHistoryWeight D) := by
  rw [thetaGradedArithmeticVector_eq_sum]
  apply Submodule.sum_mem
  intro d hd
  exact (thetaWeightedDerivativeHistory (thetaFiniteArithmeticHistoryWeight D)).smul_mem (c d)
    (thetaWeightedTranslationClass_mem_derivativeHistory_of_abs
      (thetaFiniteArithmeticHistoryWeight D) (Real.log (d : ℝ))
      (thetaFiniteArithmeticHistoryWeight_pos D) (thetaFiniteArithmeticHistoryWeight_admits D d hd))

theorem thetaGradedArithmeticVector_quotient_zero (D : Finset ℕ) (c : ℕ → ℂ) :
    (thetaWeightedDerivativeHistory (thetaFiniteArithmeticHistoryWeight D)).mkQ
      (thetaGradedArithmeticVector D c) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (thetaGradedArithmeticVector_mem_derivativeHistory D c)

/-- A single positive carrier works for every complex coefficient choice on the finite alphabet. -/
theorem exists_pos_weight_finiteArithmetic_history (D : Finset ℕ) :
    ∃ q : ℝ, 0 < q ∧ q < 2 ∧ ∀ c : ℕ → ℂ,
      ∃ h : MemLp (finiteComplexArithmeticThetaShift D c) 2 (thetaPowerWeightedMeasure q),
        h.toLp _ ∈ thetaWeightedDerivativeHistory q ∧
          (thetaWeightedDerivativeHistory q).mkQ (h.toLp _) = 0 := by
  refine ⟨thetaFiniteArithmeticHistoryWeight D, thetaFiniteArithmeticHistoryWeight_pos D,
    thetaFiniteArithmeticHistoryWeight_lt_two D, ?_⟩
  intro c
  exact ⟨finiteComplexArithmeticThetaShift_memLp_history_weight D c,
    thetaGradedArithmeticVector_mem_derivativeHistory D c, thetaGradedArithmeticVector_quotient_zero D c⟩

/-- The old exact Möbius expansion identifies the actual Euler source with the complex word. -/
theorem thetaPrimeDeletion_eq_finiteComplexWord
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (fun x => (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) =
      finiteComplexArithmeticThetaShift (thetaPrimeDeletionWords S)
        (fun d => (thetaPrimeDeletionWordCoefficient d : ℂ)) := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  funext x
  simp only [finiteArithmeticThetaShift, finiteComplexArithmeticThetaShift,
    Complex.ofReal_sum, Complex.ofReal_mul]

theorem thetaPrimeDeletion_memLp_history_weight
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    MemLp (fun x => (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) 2
      (thetaPowerWeightedMeasure (thetaFiniteArithmeticHistoryWeight (thetaPrimeDeletionWords S))) := by
  rw [thetaPrimeDeletion_eq_finiteComplexWord S hS]
  exact finiteComplexArithmeticThetaShift_memLp_history_weight _ _

/-- Literal finite Euler deletion class at its explicitly selected positive weight. -/
def thetaGradedPrimeDeletionVector (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Lp ℂ 2 (thetaPowerWeightedMeasure (thetaFiniteArithmeticHistoryWeight (thetaPrimeDeletionWords S))) :=
  (thetaPrimeDeletion_memLp_history_weight S hS).toLp
    (fun x => (thetaPrimeDeletion S thetaCuspFullSource x : ℂ))

theorem thetaGradedPrimeDeletionVector_eq_arithmeticVector
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaGradedPrimeDeletionVector S hS =
      thetaGradedArithmeticVector (thetaPrimeDeletionWords S)
        (fun d => (thetaPrimeDeletionWordCoefficient d : ℂ)) :=
  (thetaPrimeDeletion_memLp_history_weight S hS).toLp_congr
    (finiteComplexArithmeticThetaShift_memLp_history_weight _ _)
    (ae_of_all _ fun x => congrFun (thetaPrimeDeletion_eq_finiteComplexWord S hS) x)

theorem thetaGradedPrimeDeletionVector_mem_derivativeHistory
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaGradedPrimeDeletionVector S hS ∈
      thetaWeightedDerivativeHistory (thetaFiniteArithmeticHistoryWeight (thetaPrimeDeletionWords S)) := by
  rw [thetaGradedPrimeDeletionVector_eq_arithmeticVector]
  exact thetaGradedArithmeticVector_mem_derivativeHistory _ _

theorem thetaGradedPrimeDeletionVector_quotient_zero
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (thetaWeightedDerivativeHistory (thetaFiniteArithmeticHistoryWeight (thetaPrimeDeletionWords S))).mkQ
      (thetaGradedPrimeDeletionVector S hS) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (thetaGradedPrimeDeletionVector_mem_derivativeHistory S hS)

theorem thetaPrimeDeletionWords_letter_mem (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) :
    p ∈ thetaPrimeDeletionWords S := by
  unfold thetaPrimeDeletionWords
  refine Finset.mem_image.mpr ⟨{p}, ?_, by simp⟩
  exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hp)

theorem thetaFiniteEulerHistoryWeight_admits_prime (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) :
    thetaFiniteArithmeticHistoryWeight (thetaPrimeDeletionWords S) <
      2 * Real.exp (-2 * |Real.log (p : ℝ)|) :=
  thetaFiniteArithmeticHistoryWeight_admits _ p (thetaPrimeDeletionWords_letter_mem S p hp)

/-- Every prime letter and the literal full Euler deletion vanish in one common history quotient. -/
theorem exists_pos_weight_finitePrimeEuler_history
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ q : ℝ, 0 < q ∧ q < 2 ∧
      (∀ p ∈ S, ∃ h : MemLp (fun x : ℝ => (thetaRealShiftSource (Real.log (p : ℝ)) x : ℂ)) 2
          (thetaPowerWeightedMeasure q),
        h.toLp _ ∈ thetaWeightedDerivativeHistory q ∧
          (thetaWeightedDerivativeHistory q).mkQ (h.toLp _) = 0) ∧
      (∃ h : MemLp (fun x => (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) 2
          (thetaPowerWeightedMeasure q),
        h.toLp _ ∈ thetaWeightedDerivativeHistory q ∧
          (thetaWeightedDerivativeHistory q).mkQ (h.toLp _) = 0) := by
  let q := thetaFiniteArithmeticHistoryWeight (thetaPrimeDeletionWords S)
  have hq := thetaFiniteArithmeticHistoryWeight_pos (thetaPrimeDeletionWords S)
  refine ⟨q, hq, thetaFiniteArithmeticHistoryWeight_lt_two (thetaPrimeDeletionWords S), ?_, ?_⟩
  · intro p hp
    have hmargin := thetaFiniteEulerHistoryWeight_admits_prime S p hp
    have hm := thetaRealShiftSource_ofReal_memLp q (Real.log (p : ℝ)) hq hmargin
    have hmem := thetaWeightedTranslationClass_mem_derivativeHistory_of_abs
      q (Real.log (p : ℝ)) hq hmargin
    rw [thetaWeightedTranslationClass_eq_toLp q (Real.log (p : ℝ)) hm] at hmem
    exact ⟨hm, hmem, (Submodule.Quotient.mk_eq_zero _).mpr hmem⟩
  · exact ⟨thetaPrimeDeletion_memLp_history_weight S hS,
      thetaGradedPrimeDeletionVector_mem_derivativeHistory S hS,
      thetaGradedPrimeDeletionVector_quotient_zero S hS⟩

end

end RHTower
