import GaloisForLFunctions.HTGeometry.BrouwerFixedPoint
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Fixed points on finite simplices

Shift coordinates to have sum one, take their positive parts, and normalize.
This gives a continuous retraction onto the standard simplex. Brouwer's
theorem then gives the fixed-point property for continuous simplex maps.
-/

noncomputable section
open Set Finset

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private def simplexShift (x : ι → ℝ) (i : ι) : ℝ :=
  x i + (1 - ∑ j, x j) / Fintype.card ι

private theorem sum_simplexShift (x : ι → ℝ) : ∑ i, simplexShift x i = 1 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [simplexShift, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

private theorem simplexPositiveSum_pos (x : ι → ℝ) :
    0 < ∑ i, max 0 (simplexShift x i) := by
  have h := sum_le_sum (s := univ) (fun i _ => le_max_right 0 (simplexShift x i))
  rw [sum_simplexShift] at h
  exact zero_lt_one.trans_le h

/-- A continuous retraction onto the standard simplex, defined on all coordinates. -/
def simplexRetraction (x : ι → ℝ) : ι → ℝ :=
  fun i => max 0 (simplexShift x i) / ∑ j, max 0 (simplexShift x j)

theorem simplexRetraction_mem (x : ι → ℝ) : simplexRetraction x ∈ stdSimplex ℝ ι := by
  refine ⟨fun i => div_nonneg (le_max_left _ _) (simplexPositiveSum_pos x).le, ?_⟩
  simp only [simplexRetraction, ← sum_div]
  exact div_self (simplexPositiveSum_pos x).ne'

omit [Nonempty ι] in
theorem simplexRetraction_eq {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) :
    simplexRetraction x = x := by
  have hs (i : ι) : max 0 (simplexShift x i) = x i := by
    simp only [simplexShift, hx.2, sub_self, zero_div, add_zero, max_eq_right (hx.1 i)]
  funext i
  simp only [simplexRetraction, hs, hx.2, div_one]

theorem continuous_simplexRetraction : Continuous (simplexRetraction (ι := ι)) := by
  have hs (i : ι) : Continuous (fun x : ι → ℝ => max 0 (simplexShift x i)) := by
    apply continuous_const.max
    exact (continuous_apply i).add
      ((continuous_const.sub (continuous_finsetSum univ fun j _ => continuous_apply j)).div_const _)
  apply continuous_pi
  intro i
  exact (hs i).div (continuous_finsetSum univ fun j _ => hs j)
    (fun x => (simplexPositiveSum_pos x).ne')

/-- Every continuous self-map of a nonempty finite simplex has a fixed point. -/
theorem exists_fixedPoint_stdSimplex
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι) (hf : Continuous f) :
    ∃ x, f x = x := by
  let r : (ι → ℝ) → stdSimplex ℝ ι := fun x =>
    ⟨simplexRetraction x, simplexRetraction_mem x⟩
  have hr : Continuous r := continuous_simplexRetraction.subtype_mk _
  let K : Set (EuclideanSpace ℝ ι) :=
    WithLp.toLp 2 '' stdSimplex ℝ ι
  let P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x =>
    WithLp.toLp 2 (simplexRetraction x.ofLp)
  have hP : Continuous P := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
    (continuous_simplexRetraction.comp (PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)))
  have hPmem (x : EuclideanSpace ℝ ι) : P x ∈ K :=
    ⟨simplexRetraction x.ofLp, simplexRetraction_mem _, rfl⟩
  have hPid (x : EuclideanSpace ℝ ι) (hx : x ∈ K) : P x = x := by
    rcases hx with ⟨y, hy, rfl⟩
    change WithLp.toLp 2 (simplexRetraction y) = WithLp.toLp 2 y
    rw [simplexRetraction_eq hy]
  have hKb : Bornology.IsBounded K :=
    ((isCompact_stdSimplex ℝ ι).image
      (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))).isBounded
  let T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x =>
    WithLp.toLp 2 (f (r x.ofLp) : ι → ℝ)
  have hT : Continuous T := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
    (continuous_subtype_val.comp
      (hf.comp (hr.comp (PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)))))
  have hTmem (x : EuclideanSpace ℝ ι) (_ : x ∈ K) : T x ∈ K :=
    ⟨(f (r x.ofLp) : ι → ℝ), (f (r x.ofLp)).property, rfl⟩
  obtain ⟨x, hx, hfix⟩ :=
    GaloisForLFunctions.exists_fixedPoint_of_retraction hP hPmem hPid hKb hT hTmem
  rcases hx with ⟨y, hy, rfl⟩
  have hry : r y = ⟨y, hy⟩ := Subtype.ext (simplexRetraction_eq hy)
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  have he := congrArg WithLp.ofLp hfix
  change (f (r y) : ι → ℝ) = y at he
  rw [hry] at he
  change (f ⟨y, hy⟩).val = y
  exact he

end GaloisForLFunctions.HTGeometry
