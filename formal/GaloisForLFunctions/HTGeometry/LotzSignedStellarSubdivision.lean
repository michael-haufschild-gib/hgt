import GaloisForLFunctions.HTGeometry.LotzStellarCones
import GaloisForLFunctions.HTGeometry.LotzSignedCutIdentity

/-!
# Signed stellar subdivision of geometric cones

This formalizes the general-position signed indicator relation behind Lotz,
arXiv:2609.09335, Lemma 3.5 and Proposition 3.6. It applies to every finite
basis and every added ray whose coordinates are nonzero. The exceptional
set is explicitly the finite union of coordinate and pair-ratio walls.
No geometric or analytic proof obligations are left to callers.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [AddCommGroup E] [Module ℝ E]

/-- Signs of the nonzero coordinates of the added ray. -/
def lotzStellarSign (a : ι → ℝˣ) (i : ι) : Bool := decide (0 < (a i : ℝ))

/-- Ratios turn replacement-cone membership into a one-dimensional endpoint problem. -/
def lotzStellarRatios (b : Basis ι ℝ E) (a : ι → ℝˣ) (y : E) (i : ι) : ℝ :=
  b.equivFun y i/(a i : ℝ)

/-- The exceptional walls are the coordinate and pair-ratio hyperplanes. -/
def lotzStellarExceptional (b : Basis ι ℝ E) (a : ι → ℝˣ) : Set E :=
  {y | (∃ i, b.equivFun y i=0) ∨
    ∃ i j, i≠j ∧ (a j : ℝ)*b.equivFun y i=(a i : ℝ)*b.equivFun y j}

omit [Nonempty ι] in
/-- The explicit geometric walls are exactly the failure of generic ratio coordinates. -/
theorem lotzStellar_generic_iff (b : Basis ι ℝ E) (a : ι → ℝˣ) (y : E) :
    y ∉ lotzStellarExceptional b a ↔ lotzStellarRatios b a y ∈ lotzGenericRatios := by
  constructor
  · intro hy
    refine ⟨fun i => ?_,fun i j hij => ?_⟩
    · apply div_ne_zero _ (a i).ne_zero
      intro hz
      exact hy (Or.inl ⟨i,hz⟩)
    · by_contra hne
      apply hy
      refine Or.inr ⟨i,j,hne,?_⟩
      have hc := (div_eq_div_iff (a i).ne_zero (a j).ne_zero).mp hij
      simpa [mul_comm] using hc
  · rintro ⟨hne,hinj⟩ (hz|he)
    · obtain ⟨i,hi⟩ := hz
      exact hne i (by simp [lotzStellarRatios,hi])
    · obtain ⟨i,j,hij,he⟩ := he
      apply hij
      apply hinj
      apply (div_eq_div_iff (a i).ne_zero (a j).ne_zero).mpr
      simpa [mul_comm] using he

omit [DecidableEq ι] [Nonempty ι] in
/-- Original-cone membership is the signed orthant condition on ratios. -/
theorem lotzBasisCone_ratio_iff (b : Basis ι ℝ E) (a : ι → ℝˣ) (y : E) :
    y ∈ lotzBasisCone b ↔ lotzSignedOrthant (lotzStellarSign a) (lotzStellarRatios b a y) := by
  rw [lotzBasisCone_mem]
  apply forall_congr'
  intro i
  by_cases ha : 0 < (a i : ℝ)
  · simp [lotzStellarSign,lotzStellarRatios,ha,le_div_iff₀ ha]
  · have hn : (a i : ℝ)<0 := (lt_or_gt_of_ne (a i).ne_zero).resolve_right ha
    simp [lotzStellarSign,lotzStellarRatios,ha,div_le_iff_of_neg hn]

omit [Nonempty ι] in
/-- Every replacement cone has exactly the scalar endpoint criterion. -/
theorem lotzStellarCone_ratio_iff (b : Basis ι ℝ E) (a : ι → ℝˣ) (j : ι) (y : E) :
    y ∈ lotzBasisCone (lotzStellarBasis b a j) ↔
      lotzCut (lotzStellarSign a) (lotzStellarRatios b a y) j := by
  have hc (k : ι) :
      0 ≤ b.equivFun y k-lotzStellarRatios b a y j*(a k : ℝ) ↔
        if lotzStellarSign a k then lotzStellarRatios b a y j ≤ lotzStellarRatios b a y k
        else lotzStellarRatios b a y k ≤ lotzStellarRatios b a y j := by
    have he : b.equivFun y k-lotzStellarRatios b a y j*(a k : ℝ) =
        (a k : ℝ)*(lotzStellarRatios b a y k-lotzStellarRatios b a y j) := by
      unfold lotzStellarRatios
      field_simp
    rw [he]
    by_cases ha : 0 < (a k : ℝ)
    · simp [lotzStellarSign,ha,sub_nonneg]
    · have hn : (a k : ℝ)<0 := (lt_or_gt_of_ne (a k).ne_zero).resolve_right ha
      simp [lotzStellarSign,ha,mul_nonneg_iff,hn.le,not_le_of_gt hn]
  rw [lotzBasisCone_mem]
  constructor
  · intro hy
    refine ⟨?_,fun k => ?_⟩
    · simpa only [lotzStellarBasis_equivFun,if_true,lotzStellarRatios] using hy j
    · by_cases hk : k=j
      · subst k
        split_ifs <;> exact le_rfl
      · apply (hc k).mp
        simpa only [lotzStellarBasis_equivFun,hk,if_false,lotzStellarRatios] using hy k
  · rintro ⟨hj,hall⟩ k
    rw [lotzStellarBasis_equivFun]
    by_cases hk : k=j
    · simpa only [hk,if_true,lotzStellarRatios] using hj
    · simp only [hk,if_false]
      exact (hc k).mpr (hall k)

/-- Indicator of a genuine geometric cone. -/
def lotzConeIndicator (C : PointedCone ℝ E) (y : E) : ℝ := if y ∈ C then 1 else 0

/-- Signed stellar subdivision, valid off its explicitly described exceptional hyperplanes. -/
theorem lotz_signed_stellar_subdivision (b : Basis ι ℝ E) (a : ι → ℝˣ) :
    Set.EqOn (fun y => lotzConeIndicator (lotzBasisCone b) y-
      ∑ j, (if 0 < (a j : ℝ) then (1 : ℝ) else -1)*
        lotzConeIndicator (lotzBasisCone (lotzStellarBasis b a j)) y)
      (fun _ => if ∀ j, (a j : ℝ)<0 then (1 : ℝ) else 0)
      (lotzStellarExceptional b a)ᶜ := by
  intro y hy
  dsimp only
  have h := lotz_signedCuts_eqOn (lotzStellarSign a)
    ((lotzStellar_generic_iff b a y).mp hy)
  have hneg : (∀ i,lotzStellarSign a i=false) ↔ ∀ i,(a i : ℝ)<0 := by
    apply forall_congr'
    intro i
    by_cases hp : 0 < (a i : ℝ)
    · simp [lotzStellarSign,hp,not_lt_of_gt hp]
    · have hn : (a i : ℝ) < 0 := (lt_or_gt_of_ne (a i).ne_zero).resolve_right hp
      simp [lotzStellarSign,hp,hn]
  dsimp only at h
  simp only [hneg] at h
  simpa [lotzSignedCutTotal,lotzConeIndicator,lotzBasisCone_ratio_iff b a y,
    lotzStellarCone_ratio_iff,lotzStellarSign,Bool.decide_eq_true,mul_ite,mul_one,mul_zero] using h

end GaloisForLFunctions.HTGeometry
