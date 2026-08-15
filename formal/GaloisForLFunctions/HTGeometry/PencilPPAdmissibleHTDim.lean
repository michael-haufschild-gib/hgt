import GaloisForLFunctions.HTGeometry.PencilHTDimension
import GaloisForLFunctions.HTGeometry.PencilFromPPAdmissible

/-!
# An admissible configuration realizes its complex hypertranscendentally

A periodic-pencil admissible configuration is a periodic-pencil separation with `ℂ`-linear facet
phases, so it carries the exact annihilator and the exact differential matroid.  A direction off
every facet kernel exists because a finite product of nonzero linear forms is a nonzero polynomial.
Hence the intrinsic hypertranscendental realization dimension never exceeds the periodic-pencil
dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

/-! ### A direction off finitely many hyperplanes -/

theorem exists_forall_dot_ne_zero {d : ℕ} {A : Type*} [Fintype A] (U : A → Fin d → ℂ)
    (hU : ∀ B, U B ≠ 0) : ∃ w : Fin d → ℂ, ∀ B, ∑ i, U B i * w i ≠ 0 := by
  classical
  have hform : ∀ B : A, (∑ i, MvPolynomial.C (U B i) * MvPolynomial.X i) ≠ 0 := by
    intro B h0
    obtain ⟨i₀, hi₀⟩ : ∃ i, U B i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hU B (funext hcon)
    apply hi₀
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single i₀ 1)) h0
    rw [MvPolynomial.coeff_zero] at hc
    rw [← hc, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single i₀]
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos rfl, mul_one]
    · intro j _ hj
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg (fun h => hj (by
        have hij := Finsupp.single_left_injective (b := (1 : ℕ)) one_ne_zero h
        exact hij)), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ i₀) hcon
  have hpne : (∏ B : A, (∑ i, MvPolynomial.C (U B i) * MvPolynomial.X i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun B _ => hform B
  obtain ⟨w, hw⟩ : ∃ w : Fin d → ℂ,
      MvPolynomial.eval w (∏ B : A, (∑ i, MvPolynomial.C (U B i) * MvPolynomial.X i)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hpne (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  refine ⟨w, fun B h0 => hw ?_⟩
  rw [map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ B) ?_
  rw [map_sum, ← h0]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-! ### The realization and the dimension comparison -/

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
theorem ppAdmissible_form_ne_zero {d : ℕ} {faces : A → Finset V}
    (hne : ∀ B, (faces B).Nonempty) {a : V → Fin d → ℂ} {U : A → Fin d → ℂ}
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) (B : A) : U B ≠ 0 := by
  obtain ⟨-, hli⟩ := hadm B
  obtain ⟨v₀, hv₀⟩ := hne B
  intro h0
  refine hli.ne_zero (some ⟨v₀, hv₀⟩) ?_
  show (∑ i, U B i * a v₀ i) = 0
  exact Finset.sum_eq_zero fun i _ => by rw [show U B i = 0 from congrFun h0 i, zero_mul]

omit [DecidableEq A] in
set_option maxHeartbeats 4000000 in
/-- **An admissible configuration realizes its complex hypertranscendentally in the same
dimension.** -/
theorem htRealizableDim_of_ppAdmissible {d : ℕ} [Nonempty A] (faces : A → Finset V)
    (hne : ∀ B, (faces B).Nonempty)
    (a : V → Fin d → ℂ) (hindep : LinearIndependent ℚ a) (U : A → Fin d → ℂ)
    (hadm : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    HTRealizableDim (facetFinset faces) d := by
  classical
  set S := pencilOfPPAdmissible faces hne a U hadm with hS
  obtain ⟨w, hw⟩ := exists_forall_dot_ne_zero U (ppAdmissible_form_ne_zero hne hadm)
  refine htRealizableDim_of_pencil (facetFinset faces)
    (fun F => facetForm (U (facetIndex faces F))) a w hindep ?_ ?_ ?_
  · intro F hF h0
    refine hw (facetIndex faces F) ?_
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := facetForm_apply (U (facetIndex faces F)) w
    rw [h0] at this
    exact (mul_eq_zero.mp this.symm).resolve_left h2
  · intro F hF v hv
    exact S.outside F hF v hv
  · intro F hF g hg v hv
    exact S.inside F hF g hg v hv

omit [DecidableEq A] in
/-- **`htDim ≤ ppDim`.**  Whenever the periodic-pencil dimension is attained, the intrinsic
hypertranscendental realization dimension does not exceed it. -/
theorem htDim_le_ppDim [Nonempty A] (faces : A → Finset V) (hne : ∀ B, (faces B).Nonempty)
    (hattained : {d | ∃ (a : V → Fin d → ℂ), LinearIndependent ℚ a ∧
      ∃ (U : A → Fin d → ℂ), PPAdmissible faces (fun B v => ∑ i, U B i * a v i)}.Nonempty) :
    htDim (facetFinset faces) ≤ ppDim faces := by
  obtain ⟨a, hindep, U, hadm⟩ := Nat.sInf_mem hattained
  exact Nat.sInf_le (htRealizableDim_of_ppAdmissible faces hne a hindep U hadm)

end

end GaloisForLFunctions.HTGeometry
