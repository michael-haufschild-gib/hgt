import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization

/-!
# Scheme covariance of a finite family of Gibbs systems

A family of theories requires weights in addition to each theory's Gibbs
partition. The energy-shift law of arXiv:2611.16364, appendix A.1, acts on
these weights and on the external control. This module applies that law to
the corpus's finite Gibbs partition, including the normalized theory law.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.Thermodynamics
open _root_.HTGeometry

variable {I A : Type*} [Fintype I] [Fintype A]

/-- Logarithmic family weights are independent of the spectrum within a theory. -/
def theoryWeight (β : ℝ) (E : I → A → ℝ) (w U : I → ℝ) (i : I) : ℝ :=
  Real.exp (w i + β * U i) * finiteGibbsPartition β (E i)

def theoryPartition (β : ℝ) (E : I → A → ℝ) (w U : I → ℝ) : ℝ :=
  ∑ i, theoryWeight β E w U i

def theoryProbability (β : ℝ) (E : I → A → ℝ) (w U : I → ℝ) (i : I) : ℝ :=
  theoryWeight β E w U i / theoryPartition β E w U

/-- Arbitrary new controls are compensated by the uniquely prescribed logarithmic weight shift. -/
theorem theoryWeight_scheme_covariance (β : ℝ) (E : I → A → ℝ)
    (w U F V : I → ℝ) (i : I) :
    theoryWeight β (fun j a => E j a + F j)
      (fun j => w j + β * (F j + U j - V j)) V i =
      theoryWeight β E w U i := by
  unfold theoryWeight
  rw [finiteGibbsPartition_add_const, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem theoryPartition_scheme_covariance (β : ℝ) (E : I → A → ℝ)
    (w U F V : I → ℝ) :
    theoryPartition β (fun j a => E j a + F j)
      (fun j => w j + β * (F j + U j - V j)) V =
      theoryPartition β E w U := by
  simp only [theoryPartition, theoryWeight_scheme_covariance]

theorem theoryProbability_scheme_covariance (β : ℝ) (E : I → A → ℝ)
    (w U F V : I → ℝ) (i : I) :
    theoryProbability β (fun j a => E j a + F j)
      (fun j => w j + β * (F j + U j - V j)) V i =
      theoryProbability β E w U i := by
  simp only [theoryProbability, theoryWeight_scheme_covariance, theoryPartition_scheme_covariance]

/-- Transforming the external control with the energy leaves the family measure unchanged. -/
theorem theoryWeight_matched_control (β : ℝ) (E : I → A → ℝ)
    (w U F : I → ℝ) (i : I) :
    theoryWeight β (fun j a => E j a + F j) w (fun j => U j + F j) i =
      theoryWeight β E w U i := by
  have h := theoryWeight_scheme_covariance β E w U F (fun j => U j + F j) i
  simpa only [show (fun j => w j + β * (F j + U j - (U j + F j))) = w by
    funext j; ring] using h

theorem theoryPartition_matched_control (β : ℝ) (E : I → A → ℝ)
    (w U F : I → ℝ) :
    theoryPartition β (fun j a => E j a + F j) w (fun j => U j + F j) =
      theoryPartition β E w U := by
  simp only [theoryPartition, theoryWeight_matched_control]

theorem theoryProbability_matched_control (β : ℝ) (E : I → A → ℝ)
    (w U F : I → ℝ) (i : I) :
    theoryProbability β (fun j a => E j a + F j) w (fun j => U j + F j) i =
      theoryProbability β E w U i := by
  simp only [theoryProbability, theoryWeight_matched_control, theoryPartition_matched_control]

variable [Nonempty A]

theorem theoryWeight_pos (β : ℝ) (E : I → A → ℝ) (w U : I → ℝ) (i : I) :
    0 < theoryWeight β E w U i :=
  mul_pos (Real.exp_pos _) (finiteGibbsPartition_pos β (E i))

/-- With a fixed family measure, preserving each weight forces exact control compensation. -/
theorem theoryWeight_fixed_measure_iff (b : ℝ) (E : I → A → ℝ)
    (w U F V : I → ℝ) (i : I) :
    theoryWeight (Real.exp b) (fun j a => E j a + F j) w V i =
        theoryWeight (Real.exp b) E w U i ↔
      V i = U i + F i := by
  unfold theoryWeight
  rw [finiteGibbsPartition_add_const, ← mul_assoc,
    mul_left_inj' (finiteGibbsPartition_pos (Real.exp b) (E i)).ne',
    ← Real.exp_add, Real.exp_inj]
  constructor <;> intro h
  · have he : Real.exp b * (V i - U i - F i) = 0 := by linarith only [h]
    have hz := (mul_eq_zero.mp he).resolve_left (Real.exp_ne_zero b)
    linarith only [hz]
  · rw [h]
    ring

variable [Nonempty I]

theorem theoryPartition_pos (β : ℝ) (E : I → A → ℝ) (w U : I → ℝ) :
    0 < theoryPartition β E w U := by
  exact Finset.sum_pos (fun i _ => theoryWeight_pos β E w U i) Finset.univ_nonempty

theorem theoryProbability_normalized (β : ℝ) (E : I → A → ℝ) (w U : I → ℝ) :
    ∑ i, theoryProbability β E w U i = 1 := by
  rw [theoryProbability, ← Finset.sum_div]
  exact div_self (theoryPartition_pos β E w U).ne'

#print axioms theoryProbability_scheme_covariance
#print axioms theoryWeight_fixed_measure_iff
#print axioms theoryProbability_normalized

end GaloisForLFunctions.HTGeometry.Thermodynamics
