import GaloisForLFunctions.RHTower.XiCubicDiscriminant
import GaloisForLFunctions.RHTower.XiSignedFactorSquareClasses
import Mathlib.Algebra.CharP.Algebra

/-!
# Independent square classes of the actual marked cubic discriminants

Each discriminant is a nonzero square times Xi and its positive marked
companion. The existing signed-factor theorem therefore excludes every
nonempty finite discriminant packet from being a square. All exponential
marks and constants are transported in the actual meromorphic plane field.
-/

open GaloisForLFunctions.HTGeometry Filter Topology
noncomputable section
namespace RHTower
open XiGlobalKummer

local instance : CharZero MeromorphicPlane :=
  charZero_of_injective_ringHom constPlane_injective

/-- The actual cubic parameter agrees with the existing signed-factor source. -/
theorem xiCubicParameterElement_integer_eq (n : ℕ) :
    xiCubicParameterElement (Real.log (n + 2)) = 1 - factorElement (n + 2) := by
  apply MeromorphicPlane.germ_injective
  change ((xiCubicParameter (Real.log (n + 2))) : Germ planeCodiscrete ℂ) =
    ((fun z => 1 - deletionFactor (n + 2) z) : Germ planeCodiscrete ℂ)
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    dsimp [xiCubicParameter, deletionFactor]
    have he : -(Real.log ((n : ℝ) + 2) : ℂ) * z =
        -z * (Real.log (n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [he]
    ring

/-- The cubic parameter plus one is exactly the existing positive companion. -/
theorem xiCubicParameterElement_add_one (n : ℕ) :
    xiCubicParameterElement (Real.log (n + 2)) + 1 = augmentationElement (n + 2) := by
  rw [xiCubicParameterElement_integer_eq, augmentationElement_eq_two_sub_factor]
  ring

/-- An explicit nonzero square multiplier relating cubic discriminants to signed Xi factors. -/
def xiCubicDiscriminantUnit (n : ℕ) : MeromorphicPlane :=
  constPlane ((Real.sqrt 432 : ℂ) * Complex.I) * betaElement n

theorem xiCubicDiscriminantUnit_sq (n : ℕ) :
    xiCubicDiscriminantUnit n ^ 2 = -432 * betaElement n ^ 2 := by
  have hc : ((Real.sqrt 432 : ℂ) * Complex.I) ^ 2 = (-432 : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [xiCubicDiscriminantUnit, mul_pow, ← map_pow, hc]
  norm_num only [map_neg, map_ofNat]

theorem xiCubicDiscriminantUnit_ne_zero (n : ℕ) : xiCubicDiscriminantUnit n ≠ 0 := by
  intro h
  have hh := xiCubicDiscriminantUnit_sq n
  rw [h, zero_pow (by norm_num)] at hh
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 (betaElement_ne_zero n))) hh.symm

/-- The exact square-class factorization for every actual integer-marked cubic discriminant. -/
theorem xiCubicDiscriminant_integer_factorization (n : ℕ) :
    xiCubicDiscriminant (Real.log (n + 2)) =
      xiCubicDiscriminantUnit n ^ 2 * (xiElement * augmentationElement (n + 2)) := by
  rw [xiCubicDiscriminant_eq, xiCubicParameterElement_add_one,
    xiCubicParameterElement_integer_eq, ← betaElement_sq_mul_xi, xiCubicDiscriminantUnit_sq]
  ring

/-- Every nonempty finite packet of actual cubic discriminants is nonsquare. -/
theorem xiCubicDiscriminant_packet_not_isSquare (S : Finset ℕ) (hne : S.Nonempty) :
    ¬ IsSquare (∏ n ∈ S, xiCubicDiscriminant (Real.log (n + 2))) := by
  classical
  have hns := signed_factor_packet_not_isSquare ∅ (S.image (fun n => n + 2)) S.card
    (hne.image _) (by intro n hn; obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hn; omega)
  rw [Finset.prod_image] at hns
  swap
  · intro m _ n _ h
    dsimp at h
    omega
  simp only [Finset.prod_empty, mul_one] at hns
  have hprod : (∏ n ∈ S, xiCubicDiscriminant (Real.log (n + 2))) =
      (∏ n ∈ S, xiCubicDiscriminantUnit n) ^ 2 *
        (xiElement ^ S.card * ∏ n ∈ S, augmentationElement (n + 2)) := by
    simp only [xiCubicDiscriminant_integer_factorization, Finset.prod_mul_distrib,
      Finset.prod_pow, Finset.prod_const]
  intro hs
  rw [hprod] at hs
  have hu : (∏ n ∈ S, xiCubicDiscriminantUnit n) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun n _ => xiCubicDiscriminantUnit_ne_zero n)
  have hd := hs.div (IsSquare.sq (∏ n ∈ S, xiCubicDiscriminantUnit n))
  apply hns
  simpa only [mul_div_cancel_left₀ _ hu] using hd

/-- Exact finite-packet square criterion for the actual cubic discriminants. -/
theorem xiCubicDiscriminant_packet_isSquare_iff (S : Finset ℕ) :
    IsSquare (∏ n ∈ S, xiCubicDiscriminant (Real.log (n + 2))) ↔ S = ∅ := by
  constructor
  · intro hs
    by_contra hne
    exact xiCubicDiscriminant_packet_not_isSquare S (Finset.nonempty_iff_ne_empty.mpr hne) hs
  · rintro rfl
    simp

end RHTower
