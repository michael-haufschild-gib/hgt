import GaloisForLFunctions.HTGeometry.ChoquetBoundaryFunctionSystem
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Complex.Order

/-!
# The extreme states of `C(X, ℂ)` are the point evaluations

Milman's theorem shows that every extreme point of the state body of a function system is a point
evaluation.  For the *full* system `S = ⊤` the converse also holds: every point evaluation is
extreme.  So the extreme points of the state body of `C(X, ℂ)` are exactly the point evaluations,
and the Choquet boundary of `C(X, ℂ)` is all of `X`.

The proof is Urysohn's lemma plus the observation that a property of functionals which is closed,
convex, and true at every point evaluation holds throughout the state body
(`stateBody_subset_of_isClosed_convex`).  Linearity, unitality, positivity, contractivity, and the
domination `|φ(h f)| ≤ ‖h‖ φ(f)` for `f ≥ 0` are all of this shape, so none of them has to be
carried as a hypothesis.

Given `δₓ = a φ + b ψ` and a Urysohn function `f` vanishing at `x` and equal to `1` off a
neighbourhood where `g - g x` is small, positivity forces `φ f = 0`, and then domination kills the
far-away part of `g`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set

open scoped ComplexOrder

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

omit [CompactSpace X] [T2Space X] in
/-- A closed convex property true at every point evaluation holds on the whole state body. -/
theorem stateBody_subset_of_isClosed_convex {S : Submodule ℂ C(X, ℂ)} {P : Set (↥S → ℂ)}
    (hclosed : IsClosed P) (hconv : Convex ℝ P) (hδ : ∀ x : X, evalPoint S x ∈ P) :
    stateBody S ⊆ P :=
  closure_minimal (convexHull_min (by rintro _ ⟨x, rfl⟩; exact hδ x) hconv) hclosed

/-- Evaluation of a functional on the full system at a continuous function. -/
def topEval (φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ) (f : C(X, ℂ)) : ℂ :=
  φ ⟨f, Submodule.mem_top⟩

omit [CompactSpace X] [T2Space X] in
@[simp]
theorem topEval_evalPoint (x : X) (f : C(X, ℂ)) : topEval (evalPoint ⊤ x) f = f x := rfl

omit [CompactSpace X] [T2Space X] in
theorem continuous_topEval (f : C(X, ℂ)) :
    Continuous fun φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ => topEval φ f :=
  continuous_apply _

/-! ### Properties inherited by the whole state body -/

omit [CompactSpace X] [T2Space X] in
theorem topEval_add_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (a b : C(X, ℂ)) :
    topEval φ (a + b) = topEval φ a + topEval φ b := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | topEval ψ (a + b) = topEval ψ a
      + topEval ψ b}) ?_ ?_ ?_ hφ
  · exact isClosed_eq (continuous_topEval _) ((continuous_topEval _).add (continuous_topEval _))
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    rw [h₁, h₂]
    ring
  · intro x
    simp

omit [CompactSpace X] [T2Space X] in
theorem topEval_smul_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (c : ℂ) (a : C(X, ℂ)) :
    topEval φ (c • a) = c * topEval φ a := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | topEval ψ (c • a) = c * topEval ψ a})
    ?_ ?_ ?_ hφ
  · exact isClosed_eq (continuous_topEval _) (continuous_const.mul (continuous_topEval _))
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    rw [h₁, h₂]
    ring
  · intro x
    simp

omit [CompactSpace X] [T2Space X] in
theorem topEval_one_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) : topEval φ 1 = 1 := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | topEval ψ 1 = 1}) ?_ ?_ ?_ hφ
  · exact isClosed_eq (continuous_topEval _) continuous_const
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    rw [h₁, h₂, mul_one, mul_one, ← Complex.ofReal_add, hst, Complex.ofReal_one]
  · intro x
    simp

omit [CompactSpace X] [T2Space X] in
theorem topEval_nonneg_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) {f : C(X, ℂ)} (hf : ∀ y : X, 0 ≤ f y) :
    0 ≤ topEval φ f := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | 0 ≤ topEval ψ f}) ?_ ?_ ?_ hφ
  · exact isClosed_le continuous_const (continuous_topEval _)
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    exact add_nonneg (mul_nonneg (by exact_mod_cast hs) h₁)
      (mul_nonneg (by exact_mod_cast ht) h₂)
  · intro x
    simpa using hf x

omit [T2Space X] in
theorem topEval_norm_le_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (f : C(X, ℂ)) :
    ‖topEval φ f‖ ≤ ‖f‖ := by
  refine stateBody_subset_of_isClosed_convex (P := {ψ | ‖topEval ψ f‖ ≤ ‖f‖}) ?_ ?_ ?_ hφ
  · exact isClosed_le ((continuous_topEval _).norm) continuous_const
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    calc ‖(s : ℂ) * ψ₁ ⟨f, _⟩ + (t : ℂ) * ψ₂ ⟨f, _⟩‖
        ≤ ‖(s : ℂ) * ψ₁ ⟨f, _⟩‖ + ‖(t : ℂ) * ψ₂ ⟨f, _⟩‖ := norm_add_le _ _
      _ = s * ‖ψ₁ ⟨f, _⟩‖ + t * ‖ψ₂ ⟨f, _⟩‖ := by
          simp [abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * ‖f‖ + t * ‖f‖ := by
          gcongr
      _ = ‖f‖ := by rw [← add_mul, hst, one_mul]
  · intro x
    exact f.norm_coe_le_norm x

omit [T2Space X] in
theorem topEval_mul_le_of_mem {φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ}
    (hφ : φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ))) (h f : C(X, ℂ)) (hf : ∀ y : X, 0 ≤ f y) :
    ‖topEval φ (h * f)‖ ≤ ‖h‖ * (topEval φ f).re := by
  refine stateBody_subset_of_isClosed_convex
    (P := {ψ | ‖topEval ψ (h * f)‖ ≤ ‖h‖ * (topEval ψ f).re}) ?_ ?_ ?_ hφ
  · exact isClosed_le ((continuous_topEval _).norm)
      (continuous_const.mul (Complex.continuous_re.comp (continuous_topEval _)))
  · intro ψ₁ h₁ ψ₂ h₂ s t hs ht hst
    simp only [Set.mem_setOf_eq, topEval, Pi.add_apply, Pi.smul_apply, Complex.real_smul] at *
    have hre : ((s : ℂ) * ψ₁ ⟨f, Submodule.mem_top⟩ + (t : ℂ) * ψ₂ ⟨f, Submodule.mem_top⟩).re
        = s * (ψ₁ ⟨f, Submodule.mem_top⟩).re + t * (ψ₂ ⟨f, Submodule.mem_top⟩).re := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hre]
    calc ‖(s : ℂ) * ψ₁ ⟨h * f, Submodule.mem_top⟩ + (t : ℂ) * ψ₂ ⟨h * f, Submodule.mem_top⟩‖
        ≤ ‖(s : ℂ) * ψ₁ ⟨h * f, Submodule.mem_top⟩‖
          + ‖(t : ℂ) * ψ₂ ⟨h * f, Submodule.mem_top⟩‖ := norm_add_le _ _
      _ = s * ‖ψ₁ ⟨h * f, Submodule.mem_top⟩‖ + t * ‖ψ₂ ⟨h * f, Submodule.mem_top⟩‖ := by
          simp [abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * (‖h‖ * (ψ₁ ⟨f, Submodule.mem_top⟩).re)
          + t * (‖h‖ * (ψ₂ ⟨f, Submodule.mem_top⟩).re) := by gcongr
      _ = ‖h‖ * (s * (ψ₁ ⟨f, Submodule.mem_top⟩).re + t * (ψ₂ ⟨f, Submodule.mem_top⟩).re) := by
          ring
  · intro y
    simp only [Set.mem_setOf_eq, topEval_evalPoint, ContinuousMap.mul_apply]
    have hfy := hf y
    rw [Complex.le_def] at hfy
    simp only [Complex.zero_re, Complex.zero_im] at hfy
    have hnorm : ‖f y‖ = (f y).re := by
      have hval : f y = ((f y).re : ℂ) := by
        apply Complex.ext <;> simp [← hfy.2]
      conv_lhs => rw [hval]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfy.1]
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm y) hfy.1

/-! ### Point evaluations are extreme -/

/-- **Every point evaluation is an extreme state of `C(X, ℂ)`.** -/
theorem evalPoint_mem_extremePoints_top (x : X) :
    evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x
      ∈ (stateBody (⊤ : Submodule ℂ C(X, ℂ))).extremePoints ℝ := by
  refine ⟨range_evalPoint_subset_stateBody _ ⟨x, rfl⟩, ?_⟩
  rintro φ₁ hφ₁ φ₂ hφ₂ ⟨a, b, ha, hb, hab, hcomb⟩
  have key : ∀ g : C(X, ℂ), topEval φ₁ g = g x := by
    intro g
    have hzero : ∀ ε : ℝ, 0 < ε → ‖topEval φ₁ g - g x‖ ≤ ε := by
      intro ε hε
      set h : C(X, ℂ) := g + (-(g x)) • (1 : C(X, ℂ)) with hh
      have hhx : h x = 0 := by
        show g x + (-(g x)) * (1 : ℂ) = 0
        ring
      have hhval : ∀ y, h y = g y - g x := by
        intro y
        show g y + (-(g x)) * (1 : ℂ) = g y - g x
        ring
      have hhtop : topEval φ₁ h = topEval φ₁ g - g x := by
        rw [hh, topEval_add_of_mem hφ₁, topEval_smul_of_mem hφ₁, topEval_one_of_mem hφ₁]
        ring
      -- the neighbourhood on which `h` is small
      set U : Set X := {y | ‖h y‖ < ε} with hU
      have hUopen : IsOpen U := isOpen_lt (map_continuous h).norm continuous_const
      have hxU : x ∈ U := by simp [hU, hhx, hε]
      obtain ⟨f₀, hf0x, hf01, hf0mem⟩ :=
        exists_continuous_zero_one_of_isClosed (isClosed_singleton (X := X))
          hUopen.isClosed_compl (by
            rw [Set.disjoint_singleton_left]
            simpa using hxU)
      set f : C(X, ℂ) := ⟨fun y => ((f₀ y : ℝ) : ℂ), by fun_prop⟩ with hf
      have hfnonneg : ∀ y, (0 : ℂ) ≤ f y := by
        intro y
        rw [Complex.le_def]
        simp only [hf, ContinuousMap.coe_mk, Complex.ofReal_re, Complex.ofReal_im,
          Complex.zero_re, Complex.zero_im]
        refine ⟨(hf0mem y).1, ?_⟩
        simp
      have hfx : f x = 0 := by simp [hf, hf0x rfl]
      -- positivity forces `φ₁ f = 0`
      have hcombf : (a : ℂ) * topEval φ₁ f + (b : ℂ) * topEval φ₂ f = 0 := by
        have := congrFun hcomb ⟨f, Submodule.mem_top⟩
        simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul] at this
        rw [show topEval φ₁ f = φ₁ ⟨f, Submodule.mem_top⟩ from rfl,
          show topEval φ₂ f = φ₂ ⟨f, Submodule.mem_top⟩ from rfl, this]
        simpa [topEval] using hfx
      have hf1 : topEval φ₁ f = 0 := by
        have h1 := topEval_nonneg_of_mem hφ₁ hfnonneg
        have h2 := topEval_nonneg_of_mem hφ₂ hfnonneg
        have hpos1 : (0 : ℂ) ≤ (a : ℂ) * topEval φ₁ f :=
          mul_nonneg (by exact_mod_cast ha.le) h1
        have hpos2 : (0 : ℂ) ≤ (b : ℂ) * topEval φ₂ f :=
          mul_nonneg (by exact_mod_cast hb.le) h2
        have hz : (a : ℂ) * topEval φ₁ f = 0 := by
          by_contra hne
          have hlt : (0 : ℂ) < (a : ℂ) * topEval φ₁ f := lt_of_le_of_ne hpos1 (Ne.symm hne)
          have : (0 : ℂ) < (a : ℂ) * topEval φ₁ f + (b : ℂ) * topEval φ₂ f :=
            lt_of_lt_of_le hlt (le_add_of_nonneg_right hpos2)
          rw [hcombf] at this
          exact lt_irrefl _ this
        have hane : (a : ℂ) ≠ 0 := by
          simpa using ne_of_gt ha
        exact (mul_eq_zero.mp hz).resolve_left hane
      -- split `h` into a small part and a part killed by `φ₁ f = 0`
      have hsplit : h = h * ((1 : C(X, ℂ)) - f) + h * f := by ring
      have hsmall : ‖h * ((1 : C(X, ℂ)) - f)‖ ≤ ε := by
        rw [ContinuousMap.norm_le _ hε.le]
        intro y
        by_cases hy : y ∈ U
        · have h1 : ‖h y‖ ≤ ε := le_of_lt hy
          have h2 : ‖(1 : C(X, ℂ)) y - f y‖ ≤ 1 := by
            have hy1 := hf0mem y
            have : ((1 : C(X, ℂ)) y - f y) = ((1 - f₀ y : ℝ) : ℂ) := by
              simp [hf]
            rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
            constructor <;> [linarith [hy1.2]; linarith [hy1.1]]
          calc ‖(h * ((1 : C(X, ℂ)) - f)) y‖ = ‖h y‖ * ‖(1 : C(X, ℂ)) y - f y‖ := by
                simp
            _ ≤ ε * 1 := by gcongr
            _ = ε := mul_one ε
        · have hfy : f y = 1 := by simp [hf, hf01 hy]
          have hzero : (h * ((1 : C(X, ℂ)) - f)) y = 0 := by simp [hfy]
          rw [hzero, norm_zero]
          exact hε.le
      have hbig : ‖topEval φ₁ (h * f)‖ ≤ 0 := by
        have := topEval_mul_le_of_mem hφ₁ h f hfnonneg
        rw [hf1] at this
        simpa using this
      have : ‖topEval φ₁ h‖ ≤ ε := by
        conv_lhs => rw [hsplit]
        rw [topEval_add_of_mem hφ₁]
        calc ‖topEval φ₁ (h * ((1 : C(X, ℂ)) - f)) + topEval φ₁ (h * f)‖
            ≤ ‖topEval φ₁ (h * ((1 : C(X, ℂ)) - f))‖ + ‖topEval φ₁ (h * f)‖ := norm_add_le _ _
          _ ≤ ε + 0 := by
              gcongr
              exact (topEval_norm_le_of_mem hφ₁ _).trans hsmall
          _ = ε := add_zero ε
      rwa [hhtop] at this
    have hzz : ‖topEval φ₁ g - g x‖ ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      have h2 := hzero (‖topEval φ₁ g - g x‖ / 2) (by linarith)
      linarith
    have hz0 : topEval φ₁ g - g x = 0 :=
      norm_eq_zero.mp (le_antisymm hzz (norm_nonneg _))
    exact sub_eq_zero.mp hz0
  funext v
  have := key (v : C(X, ℂ))
  simpa [topEval] using this

/-- **The extreme states of `C(X, ℂ)` are exactly the point evaluations.**  One inclusion is
Milman's theorem, the other is the Urysohn argument. -/
theorem extremePoints_stateBody_top :
    (stateBody (⊤ : Submodule ℂ C(X, ℂ))).extremePoints ℝ
      = Set.range (evalPoint (⊤ : Submodule ℂ C(X, ℂ))) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact extremePoints_closure_convexHull_subset (isCompact_range_evalPoint _)
      (isCompact_stateBody _)
  · rintro _ ⟨x, rfl⟩
    exact evalPoint_mem_extremePoints_top x

/-- **The Choquet boundary of `C(X, ℂ)` is all of `X`.** -/
theorem choquetBoundary_top : choquetBoundary (⊤ : Submodule ℂ C(X, ℂ)) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, choquetBoundary, Set.mem_setOf_eq]
  exact evalPoint_mem_extremePoints_top x

theorem separating_top (x y : X) (hxy : x ≠ y) :
    ∃ s ∈ (⊤ : Submodule ℂ C(X, ℂ)), (s : C(X, ℂ)) x ≠ s y := by
  obtain ⟨f₀, hf0x, hf0y, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_singleton (X := X)) (isClosed_singleton)
      (by simpa using hxy)
  refine ⟨⟨fun z => ((f₀ z : ℝ) : ℂ), by fun_prop⟩, Submodule.mem_top, ?_⟩
  have hx : f₀ x = 0 := hf0x rfl
  have hy : f₀ y = 1 := hf0y rfl
  simp [hx, hy]

/-- **The Shilov boundary of `C(X, ℂ)` is all of `X`.**  The theory is non-degenerate: for the full
algebra no proper closed subset computes the norms. -/
theorem shilovBoundary_top : shilovBoundary (⊤ : Submodule ℂ C(X, ℂ)) = Set.univ := by
  rw [shilovBoundary_eq_closure_choquetBoundary _ Submodule.mem_top
      (fun s _ => Submodule.mem_top) separating_top,
    choquetBoundary_top, closure_univ]

end ShilovLocal

end GaloisForLFunctions.HTGeometry
