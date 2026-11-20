import GaloisForLFunctions.HTGeometry.Thermofield.TwoCopyDynamics
import GaloisForLFunctions.HTGeometry.Quantum.ChargeSectorPinching
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss

/-!
# Thermofield coherence with an inaccessible register

The branch-overlap partial trace in Kanno and Soda (arXiv:2611.26368, §7.3)
becomes a sector pinching for a thermofield double. Splitting the second copy
into two registers keeps exactly those gaps whose eigenstates carry the same
inaccessible label. Their magnitudes are the thermal Wightman weights.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry Matrix Quantum

noncomputable section

variable {α κ λ : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype λ] [DecidableEq λ]

/-- Thermofield coefficients after resolving the right energy label into two registers. -/
def splitAmplitude [DecidableEq κ] (e : α ≃ κ × λ) (β : ℝ)
    (E : α → ℝ) (t : ℝ) : (α × κ) × λ → ℂ :=
  fun ⟨⟨a, k⟩, l⟩ =>
    if e a = (k, l) then
      Complex.exp (Complex.I * (t : ℂ) * (E a : ℂ)) *
        (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ)
    else 0

private theorem phase_star (t x : ℝ) :
    star (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
      Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

private theorem gap_phase_mul (β : ℝ) (E : α → ℝ) (t : ℝ) (a b : α) :
    (Complex.exp (Complex.I * (t : ℂ) * (E a : ℂ)) *
        (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ)) *
      star (Complex.exp (Complex.I * (t : ℂ) * (E b : ℂ)) *
        (Real.sqrt (finiteGibbsStateWeight β E b) : ℂ)) =
    Complex.exp (Complex.I * (t : ℂ) * ((E a - E b : ℝ) : ℂ)) *
      (finiteKMSWightmanWeight β E a b : ℂ) := by
  rw [star_mul, phase_star, Complex.star_def, Complex.conj_ofReal,
    ← sqrt_weight_mul, Complex.ofReal_mul]
  rw [show Complex.I * (t : ℂ) * ((E a - E b : ℝ) : ℂ) =
      Complex.I * (t : ℂ) * (E a : ℂ) + -(Complex.I * (t : ℂ) * (E b : ℂ)) by
        push_cast
        ring, Complex.exp_add]
  ring

omit [DecidableEq α] [Fintype α] in
/-- Tracing the lost register retains a coherence precisely when its two labels agree. -/
theorem splitAmplitude_reduced_apply [DecidableEq κ] (e : α ≃ κ × λ)
    (β : ℝ) (E : α → ℝ) (t : ℝ) (a b : α) (k j : κ) :
    pureStateReducedLeft (splitAmplitude e β E t) (a, k) (b, j) =
      if (e a).1 = k ∧ (e b).1 = j ∧ (e a).2 = (e b).2 then
        Complex.exp (Complex.I * (t : ℂ) * ((E a - E b : ℝ) : ℂ)) *
          (finiteKMSWightmanWeight β E a b : ℂ)
      else 0 := by
  classical
  rw [pureStateReducedLeft_apply, Finset.sum_eq_single (e a).2]
  · simp only [splitAmplitude, Prod.ext_iff, eq_self, and_true, star_ite, star_zero]
    by_cases ha : (e a).1 = k <;> by_cases hb : (e b).1 = j <;>
      by_cases hl : (e a).2 = (e b).2 <;>
      simp only [ha, hb, hl, eq_comm (a := (e b).2), true_and, false_and,
        and_true, and_false, if_true, if_false, zero_mul, mul_zero, gap_phase_mul]
  · intro l _ hl
    have h : e a ≠ (k, l) := fun he => hl (congrArg Prod.snd he).symm
    simp only [splitAmplitude, if_neg h, zero_mul]
  · exact fun h => (h (Finset.mem_univ _)).elim

variable {ν : Type*} [DecidableEq ν]

/-- Reduced state in its support basis, with one basis vector per energy level. -/
def fragmentState (lost : α → ν) (β : ℝ) (E : α → ℝ)
    (t : ℝ) : Matrix α α ℂ :=
  chargePinch lost (evolve E (t : ℂ) (fun i j => (finiteKMSWightmanWeight β E i j : ℂ)))

theorem fragmentState_apply (lost : α → ν) (β : ℝ) (E : α → ℝ)
    (t : ℝ) (a b : α) :
    fragmentState lost β E t a b = if lost a = lost b then
      Complex.exp (Complex.I * (t : ℂ) * ((E a - E b : ℝ) : ℂ)) *
        (finiteKMSWightmanWeight β E a b : ℂ) else 0 :=
  chargePinch_apply _ _ _ _

/-- Compression to the occupied basis of the accessible physical registers. -/
theorem splitAmplitude_reduced_compress [DecidableEq κ] (e : α ≃ κ × λ)
    (β : ℝ) (E : α → ℝ) (t : ℝ) :
    (pureStateReducedLeft (splitAmplitude e β E t)).submatrix
        (fun a => (a, (e a).1)) (fun a => (a, (e a).1)) =
      fragmentState (fun a => (e a).2) β E t := by
  ext a b
  rw [Matrix.submatrix_apply, splitAmplitude_reduced_apply, fragmentState_apply]
  simp only [true_and]

/-- A finer inaccessible label can be imposed by pinching the state for a coarser label. -/
theorem chargePinch_fragmentState (lost : α → ν)
    {μ : Type*} [DecidableEq μ] (f : ν → μ) (β : ℝ) (E : α → ℝ) (t : ℝ) :
    chargePinch lost (fragmentState (f ∘ lost) β E t) = fragmentState lost β E t := by
  ext a b
  by_cases h : lost a = lost b
  · simp only [chargePinch_apply, fragmentState_apply, h, if_true,
      Function.comp_apply, congrArg f h]
  · simp only [chargePinch_apply, fragmentState_apply, if_neg h]

/-- Phases hidden by the trace form exactly the gaps crossing inaccessible labels. -/
theorem fragmentState_eq_iff (lost : α → ν) (β : ℝ) (E : α → ℝ) (s t : ℝ) :
    fragmentState lost β E s = fragmentState lost β E t ↔
      ∀ a b, lost a = lost b →
        Complex.exp (Complex.I * ((t - s : ℝ) : ℂ) * ((E a - E b : ℝ) : ℂ)) = 1 := by
  have hphase (a b : α) :
      Complex.exp (Complex.I * (t : ℂ) * ((E a - E b : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (s : ℂ) * ((E a - E b : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((t - s : ℝ) : ℂ) * ((E a - E b : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  constructor
  · intro h a b hl
    have hab := congrArg (fun A : Matrix α α ℂ => A a b) h
    simp only [fragmentState_apply, hl, if_true] at hab
    rw [hphase] at hab
    have hw : (finiteKMSWightmanWeight β E a b : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (finiteKMSWightmanWeight_pos β E a b).ne'
    have h' := (mul_right_cancel₀ hw hab).symm
    apply mul_left_cancel₀ (Complex.exp_ne_zero
      (Complex.I * (s : ℂ) * ((E a - E b : ℝ) : ℂ)))
    simpa only [mul_one] using h'
  · intro h
    ext a b
    by_cases hl : lost a = lost b
    · simp only [fragmentState_apply, hl, if_true]
      conv_rhs => rw [hphase, h a b hl, mul_one]
    · simp only [fragmentState_apply, if_neg hl]

/-- The exact Hilbert–Schmidt separation is the Gibbs weight of the detected phase
differences, with all differences between inaccessible sectors deleted. -/
theorem fragmentState_hsSq (lost : α → ν) (β : ℝ) (E : α → ℝ) (s t : ℝ) :
    hsSqRe (fragmentState lost β E s - fragmentState lost β E t) =
      ∑ a, ∑ b, if lost b = lost a then
        (finiteKMSWightmanWeight β E b a) ^ 2 *
          ‖Complex.exp (Complex.I * (s : ℂ) * ((E b - E a : ℝ) : ℂ)) -
            Complex.exp (Complex.I * (t : ℂ) * ((E b - E a : ℝ) : ℂ))‖ ^ 2
      else 0 := by
  rw [hsSqRe_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : lost b = lost a
  · simp only [Matrix.sub_apply, fragmentState_apply, h, if_true,
      ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (finiteKMSWightmanWeight_pos β E b a), mul_pow, mul_comm]
  · simp only [Matrix.sub_apply, fragmentState_apply, if_neg h, sub_self, norm_zero,
      zero_pow (Nat.succ_ne_zero 1)]

#print axioms splitAmplitude_reduced_apply
#print axioms splitAmplitude_reduced_compress
#print axioms chargePinch_fragmentState
#print axioms fragmentState_eq_iff
#print axioms fragmentState_hsSq

end

end GaloisForLFunctions.HTGeometry.Thermofield
