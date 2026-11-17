import GaloisForLFunctions.ExclusionOfTheCriticalState.WeilsFormOnProbesIsTheCaratheodoryKernelOfXi
import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss

/-!
# Reciprocal normalization preserves every finite probe sign test

Under the Cayley transform, reflection of disc values is reciprocation of
right-half-plane values. This common disc symmetry, used in the Pick-body
description of arXiv:2610.28972, acts on the Weil probe kernel by invertible
diagonal congruence. Positive and negative finite tests are therefore preserved.
The probe symbol is strictly positive at every exponent `5 + |t|`, so all
denominators and changes of coefficients are justified unconditionally.
-/

open scoped BigOperators

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick

noncomputable section

/-- A probe exponent that lies in the critical energy domain for every parameter. -/
def node (t : ℝ) : ℝ := 5 + |t|

/-- The real logarithmic derivative of xi at an admissible probe exponent. -/
def symbol (t : ℝ) : ℝ := probeSymbol (node t)

theorem symbol_pos (t : ℝ) : 0 < symbol t := by
  have ht : (1 / 2 : ℝ) < node t := by unfold node; linarith [abs_nonneg t]
  have h := congrArg Complex.re (probeSymbol_eq_logDeriv_xiCent ht)
  simp only [Complex.ofReal_re] at h
  rw [symbol, h]
  exact _root_.RHTower.re_logDeriv_xiCent_pos (by simpa using ht)

/-- Reciprocation is reflection in Cayley coordinates. -/
theorem cayley_reciprocal (t : ℝ) :
    (1 / symbol t - 1) / (1 / symbol t + 1) =
      -((symbol t - 1) / (symbol t + 1)) := by
  have hs := symbol_pos t
  have h0 := hs.ne'
  have h1 : symbol t + 1 ≠ 0 := by linarith [symbol_pos t]
  have h2 : 1 + symbol t ≠ 0 := by positivity
  have hi : 1 / symbol t + 1 ≠ 0 := by positivity
  field_simp [h0, h1, h2] <;> ring

/-- The Carathéodory kernel obtained by reciprocating all symbol values. -/
def reciprocalKernel (s t : ℝ) : ℝ :=
  (1 / symbol s + 1 / symbol t) / (node s + node t)

/-- Common reflection of Schur values gives an exact diagonal congruence of Weil kernels. -/
theorem reciprocal_kernel_congruence (s t : ℝ) :
    reciprocalKernel s t =
      bareMixedEnergy (probe (node s)) (probe (node t)) / (symbol s * symbol t) := by
  have hs : (1 / 2 : ℝ) < node s := by unfold node; linarith [abs_nonneg s]
  have ht : (1 / 2 : ℝ) < node t := by unfold node; linarith [abs_nonneg t]
  rw [bareMixedEnergy_probe hs ht]
  change (1 / symbol s + 1 / symbol t) / (node s + node t) =
    ((symbol s + symbol t) / (node s + node t)) / (symbol s * symbol t)
  have hs0 := (symbol_pos s).ne'
  have ht0 := (symbol_pos t).ne'
  have hn : node s + node t ≠ 0 := by linarith
  field_simp <;> ring

/-- Reciprocal normalization transports the entire quadratic form, not just its diagonal. -/
theorem reciprocal_quadratic (n : ℕ) (p c : Fin n → ℝ) :
    (∑ i, ∑ j, c i * c j * reciprocalKernel (p i) (p j)) =
      ∑ i, ∑ j, (c i / symbol (p i)) * (c j / symbol (p j)) *
        bareMixedEnergy (probe (node (p i))) (probe (node (p j))) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [reciprocal_kernel_congruence]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The inverse coefficient transformation recovers every original Weil direction. -/
theorem reciprocal_quadratic_recovery (n : ℕ) (p c : Fin n → ℝ) :
    (∑ i, ∑ j, (c i * symbol (p i)) * (c j * symbol (p j)) *
      reciprocalKernel (p i) (p j)) =
      ∑ i, ∑ j, c i * c j *
        bareMixedEnergy (probe (node (p i))) (probe (node (p j))) := by
  rw [reciprocal_quadratic]
  simp only [mul_div_cancel_right₀ _ (symbol_pos _).ne']

/-- Reciprocation neither creates nor destroys a negative finite probe witness. -/
theorem reciprocal_negative_iff (n : ℕ) (p : Fin n → ℝ) :
    (∃ c : Fin n → ℝ, (∑ i, ∑ j, c i * c j * reciprocalKernel (p i) (p j)) < 0) ↔
      ∃ c : Fin n → ℝ, (∑ i, ∑ j, c i * c j *
        bareMixedEnergy (probe (node (p i))) (probe (node (p j)))) < 0 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c i / symbol (p i), by rwa [reciprocal_quadratic] at hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c i * symbol (p i), by rwa [reciprocal_quadratic_recovery]⟩

/-- Positive-semidefiniteness of each finite probe matrix is invariant under normalization. -/
theorem reciprocal_nonnegative_iff (n : ℕ) (p : Fin n → ℝ) :
    (∀ c : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * reciprocalKernel (p i) (p j)) ↔
      ∀ c : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j *
        bareMixedEnergy (probe (node (p i))) (probe (node (p j))) := by
  constructor
  · intro h c
    have hc := h (fun i => c i * symbol (p i))
    rwa [reciprocal_quadratic_recovery] at hc
  · intro h c
    rw [reciprocal_quadratic]
    exact h _

#print axioms symbol_pos
#print axioms cayley_reciprocal
#print axioms reciprocal_kernel_congruence
#print axioms reciprocal_negative_iff
#print axioms reciprocal_nonnegative_iff

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
