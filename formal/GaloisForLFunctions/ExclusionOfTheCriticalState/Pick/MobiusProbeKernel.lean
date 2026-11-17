import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ReciprocalProbeKernel
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.SchurRadialRegularization

/-!
# Three-parameter half-plane normalization of the actual Weil kernel

Vertical translation, positive dilation, and inversion combine into
`exp(r)/(D + iτ) + iυ`. Every safe probe symbol remains in the right
half-plane. The transformed Carathéodory kernel is diagonally congruent
to the original kernel times exp(r), so all complex finite sign tests
are preserved, independently of the chosen normalization parameters.
-/

open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
noncomputable section

def mobiusDenominator (τ t : ℝ) : ℂ := (symbol t : ℂ) + (τ : ℂ) * Complex.I

theorem mobiusDenominator_ne_zero (τ t : ℝ) : mobiusDenominator τ t ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hz : symbol t = 0 := by
    simpa only [mobiusDenominator, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.zero_re] using hr
  exact (symbol_pos t).ne' hz

/-- A common half-plane Möbius transformation, with every denominator justified. -/
def mobiusProbeSymbol (r τ υ t : ℝ) : ℂ :=
  (Real.exp r : ℂ) / mobiusDenominator τ t + (υ : ℂ) * Complex.I

theorem mobiusProbeSymbol_re (r τ υ t : ℝ) :
    (mobiusProbeSymbol r τ υ t).re = Real.exp r * symbol t / (symbol t ^ 2 + τ ^ 2) := by
  simp only [mobiusProbeSymbol, mobiusDenominator, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

/-- Every normalized safe symbol has strictly positive real part. -/
theorem mobiusProbeSymbol_re_pos (r τ υ t : ℝ) : 0 < (mobiusProbeSymbol r τ υ t).re := by
  rw [mobiusProbeSymbol_re]
  exact div_pos (mul_pos (Real.exp_pos r) (symbol_pos t))
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos (symbol_pos t)) (sq_nonneg τ))

def mobiusProbeKernel (r τ υ s t : ℝ) : ℂ :=
  (mobiusProbeSymbol r τ υ s + conj (mobiusProbeSymbol r τ υ t)) /
    ((node s + node t : ℝ) : ℂ)

/-- Exact diagonal congruence; the final imaginary translation cancels from the kernel. -/
theorem mobiusProbeKernel_congruence (r τ υ s t : ℝ) :
    mobiusDenominator τ s * conj (mobiusDenominator τ t) * mobiusProbeKernel r τ υ s t =
      (Real.exp r : ℂ) *
        (bareMixedEnergy (probe (node s)) (probe (node t)) : ℂ) := by
  have hs : (1 / 2 : ℝ) < node s := by unfold node; linarith only [abs_nonneg s]
  have ht : (1 / 2 : ℝ) < node t := by unfold node; linarith only [abs_nonneg t]
  have hds := mobiusDenominator_ne_zero τ s
  have hdt : conj (mobiusDenominator τ t) ≠ 0 :=
    (map_ne_zero _).mpr (mobiusDenominator_ne_zero τ t)
  have hn : ((node s + node t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith only [hs, ht])
  rw [bareMixedEnergy_probe hs ht]
  change mobiusDenominator τ s * conj (mobiusDenominator τ t) * mobiusProbeKernel r τ υ s t =
    (Real.exp r : ℂ) * (((symbol s + symbol t) / (node s + node t) : ℝ) : ℂ)
  unfold mobiusProbeKernel mobiusProbeSymbol
  simp only [map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  push_cast at hn
  field_simp [hds, hdt, hn]
  simp only [mobiusDenominator, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The real part of the original complex-coefficient Weil quadratic form. -/
def complexProbeQuadratic (n : ℕ) (p : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  (∑ i, ∑ j, conj (c i) * c j *
    (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ)).re

/-- Complex coefficients carry exactly the sum of their real and imaginary Weil energies. -/
theorem complexProbeQuadratic_re_im (n : ℕ) (p : Fin n → ℝ) (c : Fin n → ℂ) :
    complexProbeQuadratic n p c = sourceQuadratic n p (fun i => (c i).re) +
      sourceQuadratic n p (fun i => (c i).im) := by
  unfold complexProbeQuadratic sourceQuadratic
  simp only [Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private theorem complexProbeQuadratic_ofReal (n : ℕ) (p c : Fin n → ℝ) :
    complexProbeQuadratic n p (fun i => (c i : ℂ)) = sourceQuadratic n p c := by
  rw [complexProbeQuadratic_re_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, sourceQuadratic, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- Allowing complex coefficients does not create a negative witness absent from the real form. -/
theorem complexProbeQuadratic_negative_iff_real (n : ℕ) (p : Fin n → ℝ) :
    (∃ c : Fin n → ℂ, complexProbeQuadratic n p c < 0) ↔
      ∃ c : Fin n → ℝ, sourceQuadratic n p c < 0 := by
  constructor
  · rintro ⟨c, hc⟩
    rw [complexProbeQuadratic_re_im] at hc
    by_cases hr : sourceQuadratic n p (fun i => (c i).re) < 0
    · exact ⟨fun i => (c i).re, hr⟩
    · exact ⟨fun i => (c i).im, by linarith only [hc, le_of_not_gt hr]⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun i => (c i : ℂ), by rwa [complexProbeQuadratic_ofReal]⟩

def mobiusQuadratic (r τ υ : ℝ) (n : ℕ) (p : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  (∑ i, ∑ j, conj (c i) * c j * mobiusProbeKernel r τ υ (p i) (p j)).re

def mobiusCoefficients {n : ℕ} (τ : ℝ) (p : Fin n → ℝ) (c : Fin n → ℂ) (i : Fin n) : ℂ :=
  conj (mobiusDenominator τ (p i)) * c i

/-- The entire complex quadratic form is recovered by one invertible coefficient change. -/
theorem mobiusQuadratic_recovery (r τ υ : ℝ) (n : ℕ) (p : Fin n → ℝ) (c : Fin n → ℂ) :
    mobiusQuadratic r τ υ n p (mobiusCoefficients τ p c) =
      Real.exp r * complexProbeQuadratic n p c := by
  have he : (∑ i, ∑ j, conj (mobiusCoefficients τ p c i) * mobiusCoefficients τ p c j *
      mobiusProbeKernel r τ υ (p i) (p j)) =
      (Real.exp r : ℂ) * (∑ i, ∑ j, conj (c i) * c j *
        (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [mobiusCoefficients, map_mul, Complex.conj_conj]
    calc
      _ = conj (c i) * c j * (mobiusDenominator τ (p i) *
          conj (mobiusDenominator τ (p j)) * mobiusProbeKernel r τ υ (p i) (p j)) := by ring
      _ = _ := by rw [mobiusProbeKernel_congruence]; ring
  unfold mobiusQuadratic complexProbeQuadratic
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem mobiusCoefficients_inverse (τ : ℝ) (n : ℕ)
    (p : Fin n → ℝ) (c : Fin n → ℂ) :
    mobiusCoefficients τ p (fun i => c i / conj (mobiusDenominator τ (p i))) = c := by
  funext i
  have hd : conj (mobiusDenominator τ (p i)) ≠ 0 :=
    (map_ne_zero _).mpr (mobiusDenominator_ne_zero τ (p i))
  unfold mobiusCoefficients
  field_simp

/-- All complex negative Weil witnesses survive every member of this normalization family. -/
theorem mobiusQuadratic_negative_iff (r τ υ : ℝ) (n : ℕ) (p : Fin n → ℝ) :
    (∃ c : Fin n → ℂ, mobiusQuadratic r τ υ n p c < 0) ↔
      ∃ c : Fin n → ℂ, complexProbeQuadratic n p c < 0 := by
  constructor
  · rintro ⟨c, hc⟩
    let b := fun i => c i / conj (mobiusDenominator τ (p i))
    have he := mobiusQuadratic_recovery r τ υ n p b
    rw [show mobiusCoefficients τ p b = c from mobiusCoefficients_inverse τ n p c] at he
    rw [he] at hc
    refine ⟨b, lt_of_not_ge ?_⟩
    intro hb
    exact (not_le_of_gt hc) (mul_nonneg (Real.exp_pos r).le hb)
  · rintro ⟨c, hc⟩
    refine ⟨mobiusCoefficients τ p c, ?_⟩
    rw [mobiusQuadratic_recovery]
    exact mul_neg_of_pos_of_neg (Real.exp_pos r) hc

/-- Positive-semidefiniteness of the full complex form is normalization invariant. -/
theorem mobiusQuadratic_nonnegative_iff (r τ υ : ℝ) (n : ℕ) (p : Fin n → ℝ) :
    (∀ c : Fin n → ℂ, 0 ≤ mobiusQuadratic r τ υ n p c) ↔
      ∀ c : Fin n → ℂ, 0 ≤ complexProbeQuadratic n p c := by
  constructor
  · intro h c
    have hc := h (mobiusCoefficients τ p c)
    rw [mobiusQuadratic_recovery] at hc
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos r)).mp hc
  · intro h c
    let b := fun i => c i / conj (mobiusDenominator τ (p i))
    have he := mobiusQuadratic_recovery r τ υ n p b
    rw [show mobiusCoefficients τ p b = c from mobiusCoefficients_inverse τ n p c] at he
    rw [he]
    exact mul_nonneg (Real.exp_pos r).le (h b)

/-- Neither complexification nor half-plane normalization alters real Weil negativity. -/
theorem mobiusQuadratic_negative_iff_real (r τ υ : ℝ) (n : ℕ) (p : Fin n → ℝ) :
    (∃ c : Fin n → ℂ, mobiusQuadratic r τ υ n p c < 0) ↔
      ∃ c : Fin n → ℝ, sourceQuadratic n p c < 0 := by
  rw [mobiusQuadratic_negative_iff, complexProbeQuadratic_negative_iff_real]

#print axioms mobiusProbeSymbol_re_pos
#print axioms mobiusProbeKernel_congruence
#print axioms mobiusQuadratic_recovery
#print axioms mobiusQuadratic_negative_iff
#print axioms mobiusQuadratic_nonnegative_iff
#print axioms mobiusQuadratic_negative_iff_real
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
