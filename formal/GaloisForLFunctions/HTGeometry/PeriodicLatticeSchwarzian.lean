import GaloisForLFunctions.HTGeometry.PeriodicLatticeFibers
import Mathlib.Analysis.Meromorphic.Order

/-!
# Exact Schwarzian double poles at the periodic branch points

The numerator of the cleared Schwarzian is a unit at an ordinary branch
point, while its denominator has exact order two. This local valuation
identity supplies infinitely many genuine double poles.
-/

noncomputable section
open Complex

namespace GaloisForLFunctions.HTGeometry.PeriodicLatticeSchwarzian

open PeriodicLatticeSections PeriodicLatticeBranching
open PeriodicLatticeFibers

def numerator (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  2*deriv f z*deriv (deriv (deriv f)) z-3*(deriv (deriv f) z)^2

def denominator (f : ℂ → ℂ) (z : ℂ) : ℂ := 2*(deriv f z)^2

def schwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ := numerator f z/denominator f z

theorem latticeMap_meromorphic (w : ℂ) : MeromorphicAt latticeMap w := by
  have hn : AnalyticAt ℂ (fun z => PeriodicLatticeSections.numerator (phase z)) w := by
    unfold PeriodicLatticeSections.numerator phase
    fun_prop
  have hd : AnalyticAt ℂ (fun z => PeriodicLatticeSections.denominator (phase z)) w := by
    unfold PeriodicLatticeSections.denominator phase
    fun_prop
  exact hn.meromorphicAt.div hd.meromorphicAt

theorem schwarzian_standard (f : ℂ → ℂ) (z : ℂ) :
    schwarzian f z=deriv (deriv (deriv f)) z/deriv f z-
      (3/2)*(deriv (deriv f) z/deriv f z)^2 := by
  by_cases hz : deriv f z=0
  · simp [schwarzian,numerator,denominator,hz]
  · dsimp [schwarzian,numerator,denominator]
    field_simp

theorem exact_double_pole {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (ho : analyticOrderAt (fun w => f w-f z) z=2) :
    meromorphicOrderAt (schwarzian f) z=(-2 : ℤ) := by
  have h1 : analyticOrderAt (deriv f) z=1 := by
    have hh := analyticOrderAt_deriv_of_pos (f := fun w => f w-f z)
      (hf.sub analyticAt_const) (n := 1) ho
    simpa only [deriv_sub_const_fun,Nat.cast_one] using hh
  have h2 : analyticOrderAt (deriv (deriv f)) z=0 :=
    analyticOrderAt_deriv_of_pos hf.deriv (n := 0) (by simpa using h1)
  have hd0 : deriv f z=0 := by
    by_contra h
    have hh := hf.deriv.analyticOrderAt_eq_zero.mpr h
    rw [h1] at hh
    norm_num at hh
  have hd2 : deriv (deriv f) z ≠ 0 := hf.deriv.deriv.analyticOrderAt_eq_zero.mp h2
  have hN : AnalyticAt ℂ (numerator f) z := by
    have hf1 := hf.deriv
    have hf2 := hf1.deriv
    have hf3 := hf2.deriv
    unfold numerator
    fun_prop
  have hD : AnalyticAt ℂ (denominator f) z := by
    have hf1 := hf.deriv
    unfold denominator
    fun_prop
  have hN0 : analyticOrderAt (numerator f) z=0 := by
    apply hN.analyticOrderAt_eq_zero.mpr
    simp [numerator,hd0,hd2]
  have hD2 : analyticOrderAt (denominator f) z=2 := by
    have he : denominator f=(fun _ : ℂ => (2 : ℂ))*(deriv f)^2 := rfl
    have hc : analyticOrderAt (fun _ : ℂ => (2 : ℂ)) z=0 :=
      (show AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) z by fun_prop).analyticOrderAt_eq_zero.mpr
        (by norm_num)
    rw [he,analyticOrderAt_mul (by fun_prop) (hf.deriv.pow 2),
      analyticOrderAt_pow hf.deriv,h1,hc]
    norm_num [nsmul_eq_mul]
  change meromorphicOrderAt (numerator f/denominator f) z=(-2 : ℤ)
  rw [meromorphicOrderAt_div hN.meromorphicAt hD.meromorphicAt,
    hN.meromorphicOrderAt_eq,hD.meromorphicOrderAt_eq,hN0,hD2]
  norm_num

/-- The explicit periodic parameter has infinitely many genuine Schwarzian double poles. -/
theorem infinitely_many_double_poles :
    ∃ ρ : ℤ → ℂ, Function.Injective ρ ∧ ∀ k,
      meromorphicOrderAt (schwarzian (parameterMap (Real.log 2))) (ρ k)=(-2 : ℤ) := by
  obtain ⟨ρ,hρ,hb⟩ := infinitely_many_simple_branch_points
  exact ⟨ρ,hρ,fun k => exact_double_pole (hb k).1 (hb k).2⟩

/-- Exact lattice labeling and simple distinguished fibers coexist with infinitely
many Schwarzian double poles of the very same meromorphic parameter. -/
theorem labeled_fibers_infinite_double_poles :
    (∀ (j : ℤ) (w : ℂ), latticeMap w=fiberMark j →
      (∃ k : ℤ, w=j+3*k) ∧
        analyticOrderAt (fun z => latticeMap z-fiberMark j) w=1) ∧
    ∃ ρ : ℤ → ℂ, Function.Injective ρ ∧ ∀ k,
      meromorphicOrderAt (schwarzian latticeMap) (ρ k)=(-2 : ℤ) := by
  refine ⟨fun j w hw => ⟨every_fiber_labeled j ((latticeMap_fiber_iff j w).mp hw),
    every_actual_fiber_simple j hw⟩,branchPoint,branchPoint_injective,fun k => ?_⟩
  exact exact_double_pole (latticeMap_branch_order k).1 (latticeMap_branch_order k).2

end GaloisForLFunctions.HTGeometry.PeriodicLatticeSchwarzian
