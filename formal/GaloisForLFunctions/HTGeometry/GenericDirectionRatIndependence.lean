import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

/-!
# A direction on which rationally independent forms stay rationally independent

Frequency separation for an exponential-polynomial argument needs a test direction `b` on which the
real parts of the relevant phases are `ℚ`-linearly independent, so that distinct integer frequency
vectors have distinct real parts and a finite exponential-polynomial rigidity theorem applies.

The obstruction set is a countable union of kernels of nonzero real-linear functionals, hence a
null set for the Haar measure of the ambient real vector space; its complement is therefore
nonempty.

* `exists_direction_ratIndependent_re` — the direction exists;
* `intVector_injective_of_ratIndependent` — rationally independent reals separate integer vectors.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nonzero complex-linear form has a nonzero real part as a real-linear functional. -/
theorem reLm_comp_ne_zero {d : ℕ} {w : (Fin d → ℂ) →ₗ[ℂ] ℂ} (hw : w ≠ 0) :
    Complex.reLm.comp (w.restrictScalars ℝ) ≠ 0 := by
  intro hzero
  refine hw (LinearMap.ext fun b => ?_)
  have hre : ∀ x : Fin d → ℂ, (w x).re = 0 := by
    intro x
    have := congrArg (fun f : (Fin d → ℂ) →ₗ[ℝ] ℝ => f x) hzero
    simpa using this
  have h1 : (w b).re = 0 := hre b
  have h2 : (Complex.I * w b).re = 0 := by
    have hsm : w (Complex.I • b) = Complex.I * w b := by
      rw [map_smul]
      rfl
    rw [← hsm]
    exact hre _
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    neg_eq_zero] at h2
  refine Complex.ext ?_ ?_
  · simpa using h1
  · simpa using h2

/-- **A generic direction keeps rationally independent forms rationally independent.** -/
theorem exists_direction_ratIndependent_re {d L : ℕ}
    (v : Fin L → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (hv : LinearIndependent ℚ v) :
    ∃ b : Fin d → ℂ, LinearIndependent ℚ fun l => (v l b).re := by
  classical
  by_contra hcon0
  have hcon := not_exists.mp hcon0
  -- the combination attached to a rational coefficient vector
  set W : (Fin L → ℚ) → ((Fin d → ℂ) →ₗ[ℂ] ℂ) := fun c => ∑ l, (c l) • v l with hW
  have hWne : ∀ c : Fin L → ℚ, c ≠ 0 → W c ≠ 0 := by
    intro c hc hzero
    obtain ⟨l, hl⟩ : ∃ l, c l ≠ 0 := Function.ne_iff.mp hc
    exact hl (Fintype.linearIndependent_iff.mp hv c hzero l)
  have hWapply : ∀ (c : Fin L → ℚ) (b : Fin d → ℂ),
      (W c b).re = ∑ l, (c l : ℝ) * (v l b).re := by
    intro c b
    rw [hW]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Rat.smul_def, Complex.mul_re]
    simp
  -- the obstruction set for one rational coefficient vector
  set K : {c : Fin L → ℚ // c ≠ 0} → Set (Fin d → ℂ) := fun c =>
    (LinearMap.ker (Complex.reLm.comp ((W c.1).restrictScalars ℝ)) : Set (Fin d → ℂ)) with hK
  have hnull : ∀ c, volume (K c) = 0 := by
    intro c
    refine Measure.addHaar_submodule volume _ ?_
    intro htop
    refine reLm_comp_ne_zero (hWne c.1 c.2) ?_
    refine LinearMap.ext fun b => ?_
    have hb : b ∈ LinearMap.ker (Complex.reLm.comp ((W c.1).restrictScalars ℝ)) := by
      rw [htop]; trivial
    simpa using hb
  have hcover : (Set.univ : Set (Fin d → ℂ)) ⊆ ⋃ c, K c := by
    intro b _
    obtain ⟨g, hgsum, l, hgl⟩ := Fintype.not_linearIndependent_iff.mp (hcon b)
    have hg0 : g ≠ 0 := fun h => hgl (by rw [h]; rfl)
    refine Set.mem_iUnion.mpr ⟨⟨g, hg0⟩, ?_⟩
    rw [hK]
    show Complex.reLm ((W g).restrictScalars ℝ b) = 0
    show (W g b).re = 0
    rw [hWapply]
    rw [← hgsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Rat.smul_def]
  have hzero : volume (Set.univ : Set (Fin d → ℂ)) = 0 :=
    measure_mono_null hcover (measure_iUnion_null hnull)
  exact (isOpen_univ.measure_ne_zero volume Set.univ_nonempty) hzero

/-- Rationally independent reals separate integer coefficient vectors. -/
theorem intVector_injective_of_ratIndependent {L : ℕ} {β : Fin L → ℝ}
    (hβ : LinearIndependent ℚ β) {μ ν : Fin L → ℤ}
    (h : ∑ l, (μ l : ℝ) * β l = ∑ l, (ν l : ℝ) * β l) : μ = ν := by
  classical
  have hsub : ∑ l, ((μ l - ν l : ℤ) : ℚ) • β l = 0 := by
    have hexp : ∀ l : Fin L, ((μ l - ν l : ℤ) : ℚ) • β l
        = (μ l : ℝ) * β l - (ν l : ℝ) * β l := by
      intro l
      rw [Rat.smul_def]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun l _ => hexp l, Finset.sum_sub_distrib, h, sub_self]
  have hall := Fintype.linearIndependent_iff.mp hβ (fun l => ((μ l - ν l : ℤ) : ℚ)) hsub
  funext l
  have := hall l
  have hz : (μ l - ν l : ℤ) = 0 := by exact_mod_cast this
  omega

end

end GaloisForLFunctions.HTGeometry
