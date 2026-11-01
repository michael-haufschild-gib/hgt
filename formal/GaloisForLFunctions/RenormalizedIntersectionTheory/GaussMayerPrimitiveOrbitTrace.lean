import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveOrbitWords
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEvenWordDeterminant
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerUnitEvenWordDeterminant

/-! Absolute regrouping of the actual even-word logarithm into primitive
pair cycles. The finite rotation count cancels the primitive length exactly. -/

open Complex
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerFredholm MayerWords MayerCycleIndex MayerEvenWordIndex MayerOrbitWords
open MayerOrbitDeterminant MayerUnitOrbitDeterminant
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitTrace

private def wordTerm (w z : ℂ) (a : EvenWord) : ℂ :=
  z^(2*a.1+2) / ((a.1+1 : ℕ) : ℂ) * wordTrace w (2*a.1+1) a.2

private def rotationTerm (w z : ℂ) (c : Orbit) (r : ℕ+) : ℂ :=
  z^(2*(r.val*cycleLength c)) / ((r.val : ℂ)*(cycleLength c : ℂ)) *
    (((multiplier c ^ r.val : ℝ) : ℂ)^(-w) /
      (1-1/((multiplier c ^ r.val : ℝ) : ℂ)^2))

/-- Contribution of a primitive pair cycle repeated a positive number of times. -/
def repetitionTerm (w z : ℂ) (c : Orbit) (r : ℕ+) : ℂ :=
  z^(2*(r.val*cycleLength c)) / (r.val : ℂ) *
    (((multiplier c ^ r.val : ℝ) : ℂ)^(-w) /
      (1-1/((multiplier c ^ r.val : ℝ) : ℂ)^2))

/-- Primitive pair-cycle logarithm; the source bounds below certify its
absolute convergence on the stated spectral domains. -/
def orbitExponent (w z : ℂ) : ℂ := ∑' c : Orbit, ∑' r : ℕ+, repetitionTerm w z c r

private theorem source_rotationTerm (w z : ℂ) (p : CycleIndex (ℕ × ℕ)) :
    wordTerm w z (sourceCycleEquiv.symm p) = rotationTerm w z p.1 p.2.1 :=
  source_trace_term w z p

private theorem repetition_eq_length_mul (w z : ℂ) (c : Orbit) (r : ℕ+) :
    repetitionTerm w z c r = (cycleLength c : ℂ)*rotationTerm w z c r := by
  have hl : (cycleLength c : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (cycleLength_pos c)
  let F := z^(2*(r.val*cycleLength c))
  let T := ((multiplier c ^ r.val : ℝ) : ℂ)^(-w) /
    (1-1/((multiplier c ^ r.val : ℝ) : ℂ)^2)
  change F/(r.val : ℂ)*T = (cycleLength c : ℂ)*(F/((r.val : ℂ)*(cycleLength c : ℂ))*T)
  calc
    _ = ((F/(r.val : ℂ))/(cycleLength c : ℂ))*(cycleLength c : ℂ)*T := by
      rw [div_mul_cancel₀ _ hl]
    _ = _ := by rw [div_div]; ring

private theorem sum_rotations (w z : ℂ) (c : Orbit) (r : ℕ+) :
    (∑' i : Fin (cycleLength c), wordTerm w z (sourceCycleEquiv.symm ⟨c,r,i⟩)) =
      repetitionTerm w z c r := by
  simp only [source_rotationTerm,tsum_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  exact (repetition_eq_length_mul w z c r).symm

private theorem sum_norm_rotations (w z : ℂ) (c : Orbit) (r : ℕ+) :
    (∑' i : Fin (cycleLength c), ‖wordTerm w z (sourceCycleEquiv.symm ⟨c,r,i⟩)‖) =
      ‖repetitionTerm w z c r‖ := by
  simp only [source_rotationTerm,tsum_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [repetition_eq_length_mul]
  simp only [norm_mul,Complex.norm_natCast]

private theorem hasSum_wordTerm {w z : ℂ}
    (hs : Summable (fun a : EvenWord => ‖wordTerm w z a‖)) :
    HasSum (wordTerm w z) (evenWordExponent w z) := by
  have hc : Summable (wordTerm w z) := Summable.of_norm hs
  have hn := hc.hasSum.sigma (fun n => (hc.sigma_factor n).hasSum)
  have he : evenWordExponent w z = ∑' a : EvenWord, wordTerm w z a := by
    simpa only [evenWordExponent,wordTerm,tsum_mul_left] using hn.tsum_eq
  rw [he]
  exact hc.hasSum

private theorem summable_norm_cycleTerms {w z : ℂ}
    (hs : Summable (fun a : EvenWord => ‖wordTerm w z a‖)) :
    Summable (fun p : CycleIndex (ℕ × ℕ) =>
      ‖wordTerm w z (sourceCycleEquiv.symm p)‖) :=
  (sourceCycleEquiv.symm.summable_iff
    (f := fun a : EvenWord => ‖wordTerm w z a‖)).mpr hs

private theorem hasSum_cycleTerms {w z : ℂ}
    (hs : Summable (fun a : EvenWord => ‖wordTerm w z a‖)) :
    HasSum (fun p : CycleIndex (ℕ × ℕ) =>
      wordTerm w z (sourceCycleEquiv.symm p)) (evenWordExponent w z) :=
  (sourceCycleEquiv.symm.hasSum_iff (f := wordTerm w z)
    (a := evenWordExponent w z)).mpr (hasSum_wordTerm hs)

private theorem hasSum_norm_repetitions {w z : ℂ}
    (hnorm : Summable (fun p : CycleIndex (ℕ × ℕ) =>
      ‖wordTerm w z (sourceCycleEquiv.symm p)‖)) (c : Orbit) :
    HasSum (fun r : ℕ+ => ‖repetitionTerm w z c r‖)
      (∑' q : ℕ+ × Fin (cycleLength c),
        ‖wordTerm w z (sourceCycleEquiv.symm ⟨c,q⟩)‖) := by
  refine HasSum.prod_fiberwise
    (f := fun q : ℕ+ × Fin (cycleLength c) =>
      ‖wordTerm w z (sourceCycleEquiv.symm ⟨c,q⟩)‖)
    (g := fun r : ℕ+ => ‖repetitionTerm w z c r‖)
    (hnorm.sigma_factor c).hasSum ?_
  intro r
  rw [← sum_norm_rotations w z c r,tsum_fintype]
  exact hasSum_fintype _

private theorem hasSum_repetitions {w z : ℂ}
    (hc : Summable (fun p : CycleIndex (ℕ × ℕ) =>
      wordTerm w z (sourceCycleEquiv.symm p))) (c : Orbit) :
    HasSum (fun r : ℕ+ => repetitionTerm w z c r)
      (∑' q : ℕ+ × Fin (cycleLength c), wordTerm w z (sourceCycleEquiv.symm ⟨c,q⟩)) := by
  refine HasSum.prod_fiberwise
    (f := fun q : ℕ+ × Fin (cycleLength c) =>
      wordTerm w z (sourceCycleEquiv.symm ⟨c,q⟩))
    (g := fun r : ℕ+ => repetitionTerm w z c r)
    (hc.sigma_factor c).hasSum ?_
  intro r
  rw [← sum_rotations w z c r,tsum_fintype]
  exact hasSum_fintype _

private theorem regroup {w z : ℂ}
    (hs : Summable (fun a : EvenWord => ‖wordTerm w z a‖)) :
    Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖) ∧
      evenWordExponent w z = orbitExponent w z := by
  have hnorm := summable_norm_cycleTerms hs
  have hc : Summable (fun p : CycleIndex (ℕ × ℕ) =>
      wordTerm w z (sourceCycleEquiv.symm p)) := Summable.of_norm hnorm
  have hrep : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖) := by
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨?_,?_⟩
    · exact fun c => (hasSum_norm_repetitions hnorm c).summable
    · exact hnorm.sigma.congr (fun c => (hasSum_norm_repetitions hnorm c).tsum_eq.symm)
  have hout : HasSum (fun c : Orbit => ∑' r : ℕ+, repetitionTerm w z c r)
      (evenWordExponent w z) := by
    apply (hasSum_cycleTerms hs).sigma
      (g := fun c : Orbit => ∑' r : ℕ+, repetitionTerm w z c r)
    intro c
    rw [(hasSum_repetitions hc c).tsum_eq]
    exact (hc.sigma_factor c).hasSum
  exact ⟨hrep,hout.tsum_eq.symm⟩

/-- The actual signed Mayer determinant has an absolutely convergent primitive
pair-cycle logarithm near spectral parameter zero for `Re w>1`. -/
theorem exists_signed_determinant_eq_orbitExponent {w : ℂ} (hw : 1 < w.re) :
    ∃ R > 0, ∀ z : ℂ, ‖z‖ < R →
      Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖) ∧
      determinant w (zero_lt_one.trans hw) z * determinant w (zero_lt_one.trans hw) (-z) =
        exp (-orbitExponent w z) := by
  obtain ⟨R,hR,h⟩ := exists_signed_determinant_and_absolute_evenWordSeries hw
  refine ⟨R,hR,fun z hz => ?_⟩
  obtain ⟨hs,he⟩ := h z hz
  obtain ⟨hr,heq⟩ := regroup hs
  exact ⟨hr,he.trans (congrArg (fun t : ℂ => exp (-t)) heq)⟩

/-- The primitive pair-cycle logarithm reaches the closed unit spectral disk
for `Re w>2`, with absolute convergence before any geometric expansion. -/
theorem signed_determinant_eq_orbitExponent_on_closed_unit {w z : ℂ}
    (hw : 2 < w.re) (hz : ‖z‖ ≤ 1) :
    Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖) ∧
      determinant w (show 0 < w.re by linarith only [hw]) z *
        determinant w (show 0 < w.re by linarith only [hw]) (-z) =
      exp (-orbitExponent w z) := by
  obtain ⟨hr,heq⟩ := regroup (summable_norm_evenWordSeries_on_closed_unit hw hz)
  exact ⟨hr,(signed_determinant_eq_evenWordExponent_on_closed_unit hw hz).trans
    (congrArg (fun t : ℂ => exp (-t)) heq)⟩

#print axioms exists_signed_determinant_eq_orbitExponent
#print axioms signed_determinant_eq_orbitExponent_on_closed_unit
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitTrace
