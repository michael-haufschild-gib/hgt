import GaloisForLFunctions.RHTower.Sieve.VinogradovWeightedGrouping

namespace RHTower.Sieve

open scoped BigOperators ComplexConjugate

noncomputable section

def finitePhaseChar (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem finitePhaseChar_zero : finitePhaseChar 0 = 1 := by
  simp [finitePhaseChar]

theorem finitePhaseChar_add (x y : ℝ) :
    finitePhaseChar (x + y) = finitePhaseChar x * finitePhaseChar y := by
  rw [finitePhaseChar, finitePhaseChar, finitePhaseChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem finitePhaseChar_neg (x : ℝ) :
    finitePhaseChar (-x) = conj (finitePhaseChar x) := by
  change Complex.exp (((2 * Real.pi * (-x) : ℝ) : ℂ) * Complex.I) =
    conj (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem norm_finitePhaseChar (x : ℝ) : ‖finitePhaseChar x‖ = 1 := by
  rw [finitePhaseChar, Complex.norm_exp]
  simp

theorem finitePhaseChar_re (x : ℝ) :
    (finitePhaseChar x).re = Real.cos (2 * Real.pi * x) := by
  rw [finitePhaseChar, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero]

theorem prod_finitePhaseChar
    {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∏ i : ι, finitePhaseChar (f i) = finitePhaseChar (∑ i : ι, f i) := by
  classical
  have hprod : ∀ s : Finset ι,
      ∏ i ∈ s, finitePhaseChar (f i) = finitePhaseChar (∑ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [finitePhaseChar_zero]
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, finitePhaseChar_add, ih]
  simpa using hprod Finset.univ

def finitePhaseSum {α : Type*} [Fintype α] (f : α → ℝ) : ℂ :=
  ∑ a : α, finitePhaseChar (f a)

theorem finitePhaseSum_pow
    {α : Type*} [Fintype α] (f : α → ℝ) (b : ℕ) :
    finitePhaseSum f ^ b =
      ∑ u : Fin b → α, finitePhaseChar (∑ i : Fin b, f (u i)) := by
  rw [finitePhaseSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro u _
  exact prod_finitePhaseChar (fun i : Fin b => f (u i))

theorem conj_finitePhaseSum
    {α : Type*} [Fintype α] (f : α → ℝ) :
    conj (finitePhaseSum f) = finitePhaseSum (fun a => -f a) := by
  unfold finitePhaseSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (finitePhaseChar_neg (f a)).symm

theorem finitePhaseMoment_expansion
    {α : Type*} [Fintype α] (f : α → ℝ) (b : ℕ) :
    ((Complex.normSq (finitePhaseSum f) : ℝ) : ℂ) ^ b =
      ∑ uv : (Fin b → α) × (Fin b → α),
        finitePhaseChar
          ((∑ i : Fin b, f (uv.1 i)) - ∑ i : Fin b, f (uv.2 i)) := by
  calc
    ((Complex.normSq (finitePhaseSum f) : ℝ) : ℂ) ^ b =
        (finitePhaseSum f * conj (finitePhaseSum f)) ^ b := by
      rw [Complex.mul_conj]
    _ = finitePhaseSum f ^ b * conj (finitePhaseSum f) ^ b := mul_pow _ _ _
    _ = (∑ u : Fin b → α, finitePhaseChar (∑ i : Fin b, f (u i))) *
        (∑ v : Fin b → α, finitePhaseChar (∑ i : Fin b, -f (v i))) := by
      rw [finitePhaseSum_pow, conj_finitePhaseSum, finitePhaseSum_pow]
    _ = ∑ uv : (Fin b → α) × (Fin b → α),
        finitePhaseChar (∑ i : Fin b, f (uv.1 i)) *
          finitePhaseChar (∑ i : Fin b, -f (uv.2 i)) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
    _ = ∑ uv : (Fin b → α) × (Fin b → α),
        finitePhaseChar
          ((∑ i : Fin b, f (uv.1 i)) - ∑ i : Fin b, f (uv.2 i)) := by
      apply Finset.sum_congr rfl
      intro uv _
      rw [← finitePhaseChar_add]
      congr 1
      rw [Finset.sum_neg_distrib]
      ring

theorem finitePhaseMoment_expansion_real
    {α : Type*} [Fintype α] (f : α → ℝ) (b : ℕ) :
    Complex.normSq (finitePhaseSum f) ^ b =
      ∑ uv : (Fin b → α) × (Fin b → α),
        Real.cos (2 * Real.pi *
          ((∑ i : Fin b, f (uv.1 i)) - ∑ i : Fin b, f (uv.2 i))) := by
  have h := congrArg Complex.re (finitePhaseMoment_expansion f b)
  have hl : (((Complex.normSq (finitePhaseSum f) : ℝ) : ℂ) ^ b).re =
      Complex.normSq (finitePhaseSum f) ^ b := by
    exact (congrArg Complex.re
      (Complex.ofReal_pow (Complex.normSq (finitePhaseSum f)) b)).symm
  rw [hl, Complex.re_sum] at h
  simpa only [finitePhaseChar_re] using h

end

end RHTower.Sieve
