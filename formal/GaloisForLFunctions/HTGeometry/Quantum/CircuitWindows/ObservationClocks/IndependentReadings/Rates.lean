import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import Mathlib.Algebra.Polynomial.Roots

/-! # A countable resonance set for nearly equally spaced clock rates -/

open Polynomial Set
namespace GaloisForLFunctions.HTGeometry.ObservationClocks.IndependentReadings
noncomputable section
variable {I : Type*} [Fintype I]

/-- At parameter z between zero and one the jth rate is within z^(j+1)
of its unperturbed integer value. -/
def rate (z : ℝ) (j : ℕ) : ℝ := (j+1:ℕ)+z^(j+1)

abbrev Rows (n : ℕ) (I : Type*) := (j : Fin n) × (fun _ : Fin n => I) j

def rowFrequency (n : ℕ) (f : I→ℝ) (z : ℝ) (p : Rows n I) := rate z p.1.val*f p.2

private def test {n : ℕ} (c : Fin n→ℝ) : ℝ[X] :=
  C (∑ j, c j*(j.val+1:ℕ))+∑ j, monomial (j.val+1) (c j)

private theorem test_coeff {n : ℕ} (c : Fin n→ℝ) (j : Fin n) :
    (test c).coeff (j.val+1)=c j := by
  classical
  simp [test,coeff_monomial,Fin.val_inj]

private theorem test_at {n : ℕ} (m : Rows n I→ℤ) (f : I→ℝ) (z : ℝ) :
    (test (fun j => finiteTorusCharacterDetuning (fun i => m ⟨j,i⟩) f)).eval z=
      finiteTorusCharacterDetuning m (rowFrequency n f z) := by
  simp only [test,eval_add,eval_C,eval_finset_sum,eval_monomial,finiteTorusCharacterDetuning,
    rowFrequency,Fintype.sum_sigma,rate,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_mul,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Given an independent frequency vector, outside one countable set of
parameters its copies at every finite list of these rates are jointly
independent. No arithmetic condition on the base frequencies beyond
their original independence is needed. -/
theorem countable_clock_resonances (f : I→ℝ) (hf : RationallyIndependentFrequency f) :
    ∃ B : Set ℝ, B.Countable ∧ ∀ z∉B, ∀ n : ℕ, RationallyIndependentFrequency (rowFrequency n f z) := by
  classical
  let bad (n : ℕ) (m : Rows n I→ℤ) := {z | m≠0 ∧ finiteTorusCharacterDetuning m (rowFrequency n f z)=0}
  have hfinite (n : ℕ) (m : Rows n I→ℤ) : (bad n m).Finite := by
    by_cases hm : m=0
    · simp [bad,hm]
    let c (j : Fin n) := finiteTorusCharacterDetuning (fun i => m ⟨j,i⟩) f
    have hn : test c≠0 := by
      intro hz
      apply hm
      funext p
      obtain ⟨j,i⟩ := p
      have hj : c j=0 := by rw [←test_coeff c j,hz,coeff_zero]
      exact congrFun (hf _ hj) i
    apply (test c).finite_setOf_isRoot hn |>.subset
    exact fun z hz => (test_at m f z).trans hz.2
  refine ⟨⋃ n : ℕ, ⋃ m : Rows n I→ℤ, bad n m,
    countable_iUnion fun n => countable_iUnion fun m => (hfinite n m).countable,?_⟩
  intro z hz n m hzero
  by_contra hm
  exact hz (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨m,hm,hzero⟩⟩)

#print axioms countable_clock_resonances
end
end GaloisForLFunctions.HTGeometry.ObservationClocks.IndependentReadings
