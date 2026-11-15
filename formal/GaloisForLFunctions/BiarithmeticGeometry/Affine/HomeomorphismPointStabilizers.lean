import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Atoms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Maximal stabilizers on affine coordinate lines

Bardyla--Elliott--Péresse, arXiv:2608.28211, show that double transitivity
makes point stabilizers maximal. On a topological field, affine maps supply
double transitivity explicitly. Thus the rational, real, and complex coordinate
lines all have maximal homeomorphism stabilizers, with no transitivity premise.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

/-- An affine coordinate change with invertible slope is a homeomorphism. -/
def affineLineHomeomorph (u : Kˣ) (b : K) : K ≃ₜ K :=
  (Homeomorph.mulLeft₀ (u : K) u.ne_zero).trans (Homeomorph.addRight b)

theorem affineLineHomeomorph_apply (u : Kˣ) (b x : K) :
    affineLineHomeomorph u b x = (u : K)*x+b := rfl

/-- The subgroup fixing one affine coordinate. -/
def homeomorphPointStabilizer (a : K) : Subgroup (K ≃ₜ K) where
  carrier := {f | f a = a}
  one_mem' := rfl
  mul_mem' hf hg := by
    change _ (_ a) = a
    rw [hg, hf]
  inv_mem' {f} hf := by
    change f.symm a = a
    rw [← hf, f.symm_apply_apply]

private theorem exists_affine_pair {a b c d : K} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ f : K ≃ₜ K, f a = c ∧ f b = d := by
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdc : d-c ≠ 0 := sub_ne_zero.mpr hcd.symm
  let u : Kˣ := Units.mk0 ((d-c)/(b-a)) (div_ne_zero hdc hba)
  refine ⟨affineLineHomeomorph u (c-(u:K)*a), ?_, ?_⟩
  · rw [affineLineHomeomorph_apply]
    ring
  · rw [affineLineHomeomorph_apply]
    change (d-c)/(b-a)*b+(c-(d-c)/(b-a)*a)=d
    field_simp
    ring

/-- Adding any homeomorphism that moves the fixed point generates the full group. -/
theorem homeomorphPointStabilizer_isCoatom (a : K) :
    IsCoatom (homeomorphPointStabilizer a) := by
  constructor
  · intro htop
    have hmem : affineLineHomeomorph (1 : Kˣ) 1 ∈ homeomorphPointStabilizer a := by
      rw [htop]
      trivial
    change (1 : K)*a+1=a at hmem
    have : (1 : K) = 0 := by linear_combination hmem
    exact one_ne_zero this
  · intro H hH
    obtain ⟨h, hh, hn⟩ := SetLike.exists_of_lt hH
    have hmove : a ≠ h a := fun e => hn e.symm
    apply top_unique
    intro f _
    by_cases hf : f a = a
    · exact hH.le hf
    · obtain ⟨k, hka, hkh⟩ := exists_affine_pair hmove (Ne.symm hf)
      have hk : k ∈ H := hH.le hka
      have hr : (k*h)⁻¹*f ∈ homeomorphPointStabilizer a := by
        change (k*h).symm (f a) = a
        rw [← hkh]
        exact (k*h).symm_apply_apply a
      have hprod := H.mul_mem (H.mul_mem hk hh) (hH.le hr)
      simpa only [mul_inv_cancel_left] using hprod

/-- Rational affine coordinates yield maximal subgroups of `Homeo(ℚ)`. -/
theorem rational_homeomorph_point_maximal (a : ℚ) :
    IsCoatom (homeomorphPointStabilizer a) := homeomorphPointStabilizer_isCoatom a

/-- Real affine coordinates yield maximal subgroups of `Homeo(ℝ)`. -/
theorem real_homeomorph_point_maximal (a : ℝ) :
    IsCoatom (homeomorphPointStabilizer a) := homeomorphPointStabilizer_isCoatom a

/-- Complex affine coordinates yield maximal subgroups of `Homeo(ℂ)`. -/
theorem complex_homeomorph_point_maximal (a : ℂ) :
    IsCoatom (homeomorphPointStabilizer a) := homeomorphPointStabilizer_isCoatom a

/-- Reflections distinguish the stabilizers of different affine coordinates. -/
theorem homeomorphPointStabilizer_injective [CharZero K] :
    Function.Injective (homeomorphPointStabilizer (K := K)) := by
  intro a b hab
  have ha : affineLineHomeomorph (-1 : Kˣ) (2*a) ∈ homeomorphPointStabilizer a := by
    change (-1 : K)*a+2*a=a
    ring
  have hb : affineLineHomeomorph (-1 : Kˣ) (2*a) ∈ homeomorphPointStabilizer b := hab ▸ ha
  change (-1 : K)*b+2*a=b at hb
  have htwo : (2 : K)*(a-b)=0 := by linear_combination hb
  exact sub_eq_zero.mp ((mul_eq_zero.mp htwo).resolve_left two_ne_zero)

/-- Each coordinate gives a different maximal subgroup, explicitly and uniformly. -/
def coordinateMaximalSubgroupEmbedding [CharZero K] :
    K ↪ {H : Subgroup (K ≃ₜ K) // IsCoatom H} where
  toFun a := ⟨homeomorphPointStabilizer a, homeomorphPointStabilizer_isCoatom a⟩
  inj' _ _ h := homeomorphPointStabilizer_injective (congrArg Subtype.val h)

end GaloisForLFunctions.BiarithmeticGeometry
