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
    ← Real.exp_add, Real.exp_eq_exp]
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
  simp only [theoryProbability, ← Finset.sum_div]
  exact div_self (theoryPartition_pos β E w U).ne'

/-- A control mismatch multiplies each theory's weight by its own exponential tilt. -/
theorem theoryWeight_control_ratio (β : ℝ) (E : I → A → ℝ)
    (w U F V : I → ℝ) (i : I) :
    theoryWeight β (fun j a => E j a + F j) w V i =
      Real.exp (β * (V i - U i - F i)) * theoryWeight β E w U i := by
  unfold theoryWeight
  rw [finiteGibbsPartition_add_const, ← mul_assoc, ← mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem theoryWeight_common_control_shift (β c : ℝ) (E : I → A → ℝ)
    (w U F : I → ℝ) (i : I) :
    theoryWeight β (fun j a => E j a + F j) w (fun j => U j + F j + c) i =
      Real.exp (β * c) * theoryWeight β E w U i := by
  rw [theoryWeight_control_ratio]
  congr 2
  ring

theorem theoryPartition_common_control_shift (β c : ℝ) (E : I → A → ℝ)
    (w U F : I → ℝ) :
    theoryPartition β (fun j a => E j a + F j) w (fun j => U j + F j + c) =
      Real.exp (β * c) * theoryPartition β E w U := by
  simp only [theoryPartition, theoryWeight_common_control_shift, Finset.mul_sum]

theorem theoryProbability_common_control_shift (β c : ℝ) (E : I → A → ℝ)
    (w U F : I → ℝ) (i : I) :
    theoryProbability β (fun j a => E j a + F j) w (fun j => U j + F j + c) i =
      theoryProbability β E w U i := by
  unfold theoryProbability
  rw [theoryWeight_common_control_shift, theoryPartition_common_control_shift]
  field_simp [(theoryPartition_pos β E w U).ne']

/-- Fixed-measure normalized laws preserve controls exactly modulo a common additive constant. -/
theorem theoryProbability_fixed_measure_iff (b : ℝ) (E : I → A → ℝ) (w U F V : I → ℝ) :
    (∀ i, theoryProbability (Real.exp b) (fun j a => E j a + F j) w V i =
      theoryProbability (Real.exp b) E w U i) ↔
        ∃ c : ℝ, ∀ i, V i = U i + F i + c := by
  constructor
  · intro h
    have hr (i : I) : Real.exp (Real.exp b * (V i - U i - F i)) * theoryPartition (Real.exp b) E w U =
        theoryPartition (Real.exp b) (fun j a => E j a + F j) w V := by
      have he := congrArg (fun x : ℝ =>
        x * theoryPartition (Real.exp b) (fun j a => E j a + F j) w V *
          theoryPartition (Real.exp b) E w U) (h i)
      unfold theoryProbability at he
      rw [theoryWeight_control_ratio] at he
      field_simp [(theoryPartition_pos (Real.exp b) E w U).ne',
        (theoryPartition_pos (Real.exp b) (fun j a => E j a + F j) w V).ne'] at he
      apply (mul_left_inj' (theoryWeight_pos (Real.exp b) E w U i).ne').mp
      nlinarith only [he]
    obtain ⟨i₀⟩ := ‹Nonempty I›
    refine ⟨V i₀ - U i₀ - F i₀, ?_⟩
    intro i
    have he : Real.exp (Real.exp b * (V i - U i - F i)) =
        Real.exp (Real.exp b * (V i₀ - U i₀ - F i₀)) := by
      apply (mul_left_inj' (theoryPartition_pos (Real.exp b) E w U).ne').mp
      rw [hr i, hr i₀]
    have hx := Real.exp_injective he
    have hz : Real.exp b * ((V i - U i - F i) - (V i₀ - U i₀ - F i₀)) = 0 := by
      linarith only [hx]
    have hoffset := (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero b)
    linarith only [hoffset]
  · rintro ⟨c, hc⟩
    have hf : V = fun i => U i + F i + c := funext hc
    rw [hf]
    exact fun i => theoryProbability_common_control_shift (Real.exp b) c E w U F i

#print axioms theoryProbability_scheme_covariance
#print axioms theoryWeight_fixed_measure_iff
#print axioms theoryProbability_normalized
#print axioms theoryProbability_fixed_measure_iff

end GaloisForLFunctions.HTGeometry.Thermodynamics
