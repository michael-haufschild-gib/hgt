import GaloisForLFunctions.RHTower.ThetaPowerWeightedDerivativeHistory
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionWeightedAdmission

/-!
# Admitted finite Euler deletions belong to actual derivative history

Each arithmetic translate is represented by its literal source function in
the fixed weighted carrier. Finite sums commute with the L² quotient, so the
exact signed Euler word belongs to the closed span of actual derivatives.
-/

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem toLp_finsetSum_as_classes (μ : Measure ℝ) (D : Finset ℕ)
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

/-- The literal admitted finite word, without identifying its history generators by definition. -/
theorem finiteArithmeticThetaShift_admitted_derivativeHistory
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) (hc : c b ≠ 0)
    (q : ℝ) (hq : 0 < q) (hqb : q < 2 / (b : ℝ) ^ 2) :
    ∃ h : MemLp (fun x => ((finiteArithmeticThetaShift D c x : ℝ) : ℂ)) 2
        (thetaPowerWeightedMeasure q),
      h.toLp _ ∈ thetaWeightedDerivativeHistory q := by
  classical
  have hb0 := hpositive b hb
  have hqexpb : q < 2 * Real.exp (-2 * Real.log (b : ℝ)) := by
    rw [thetaArithmeticTerminalThreshold_eq b hb0]
    exact hqb
  have hlog (d : ℕ) (hd : d ∈ D) : 0 ≤ Real.log (d : ℝ) := by
    apply Real.log_nonneg
    have hd1 : 1 ≤ d := by have := hpositive d hd; omega
    exact_mod_cast hd1
  have hqexp (d : ℕ) (hd : d ∈ D) : q < 2 * Real.exp (-2 * Real.log (d : ℝ)) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hpositive d hd
    have hdb : Real.log (d : ℝ) ≤ Real.log (b : ℝ) :=
      Real.log_le_log hd0 (by exact_mod_cast hmax d hd)
    exact lt_of_lt_of_le hqexpb (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have htrans (d : ℕ) (hd : d ∈ D) :
      MemLp (fun x : ℝ => ((thetaCuspFullSource (x + Real.log (d : ℝ)) : ℝ) : ℂ)) 2
        (thetaPowerWeightedMeasure q) := by
    have hqd : q < 2 / (d : ℝ) ^ 2 := by
      rw [← thetaArithmeticTerminalThreshold_eq d (hpositive d hd)]
      exact hqexp d hd
    have h := (finiteArithmeticThetaShift_ofReal_memLp_iff {d} (fun _ => 1) d (by simp)
      (by simpa using hpositive d hd) (by simp) (by norm_num) q hq).mpr hqd
    simpa only [finiteArithmeticThetaShift, Finset.sum_singleton, one_mul] using h
  have hadmit := (finiteArithmeticThetaShift_ofReal_memLp_iff D c b hb hpositive hmax hc q hq).mpr hqb
  refine ⟨hadmit, ?_⟩
  let f : ℕ → ℝ → ℂ := fun d x => (c d : ℂ) •
    ((thetaCuspFullSource (x + Real.log (d : ℝ)) : ℝ) : ℂ)
  have hf : ∀ d ∈ D, MemLp (f d) 2 (thetaPowerWeightedMeasure q) :=
    fun d hd => (htrans d hd).const_smul (c d : ℂ)
  have hsum := memLp_finsetSum D hf
  have he : (fun x => ((finiteArithmeticThetaShift D c x : ℝ) : ℂ)) =
      (fun x => ∑ d ∈ D, f d x) := by
    funext x
    simp only [finiteArithmeticThetaShift, Complex.ofReal_sum, Complex.ofReal_mul, f, smul_eq_mul]
  rw [hadmit.toLp_congr hsum (ae_of_all _ fun x => congrFun he x),
    toLp_finsetSum_as_classes (thetaPowerWeightedMeasure q) D f hf]
  apply Submodule.sum_mem
  intro d hd
  have hv : l2Family (thetaPowerWeightedMeasure q) (fun _ x => f d x) 0 =
      (c d : ℂ) • thetaWeightedTranslationClass q (Real.log (d : ℝ) : ℂ) := by
    rw [l2Family_eq_toLp (thetaPowerWeightedMeasure q) (fun _ x => f d x) 0 (hf d hd)]
    change ((htrans d hd).const_smul (c d : ℂ)).toLp _ = _
    rw [MemLp.toLp_const_smul, thetaWeightedTranslationClass_eq_toLp q (Real.log (d : ℝ))
      (htrans d hd)]
  rw [hv]
  exact (thetaWeightedDerivativeHistory q).smul_mem (c d : ℂ)
    (thetaWeightedTranslationClass_mem_derivativeHistory q (Real.log (d : ℝ)) hq (hlog d hd) (hqexp d hd))

/-- Every admitted finite prime deletion belongs to the literal closed derivative history. -/
theorem thetaPrimeDeletion_admitted_derivativeHistory
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (q : ℝ) (hq : 0 < q)
    (hmargin : q < 2 / (((∏ p ∈ S, p : ℕ) : ℝ) ^ 2)) :
    ∃ h : MemLp (fun x => ((thetaPrimeDeletion S thetaCuspFullSource x : ℝ) : ℂ)) 2
        (thetaPowerWeightedMeasure q),
      h.toLp _ ∈ thetaWeightedDerivativeHistory q := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  exact finiteArithmeticThetaShift_admitted_derivativeHistory
    (thetaPrimeDeletionWords S) thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p)
    (thetaPrimeDeletionWords_top_mem S) (thetaPrimeDeletionWords_positive S hS)
    (thetaPrimeDeletionWords_le_top S hS) (thetaPrimeDeletionWordCoefficient_top_ne_zero S hS)
    q hq hmargin

end

end RHTower
