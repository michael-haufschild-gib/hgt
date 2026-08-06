import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Noetherian
import GaloisForLFunctions.HTGeometry.DivisorSupportFinite

/-!
# The divisor of a rational function on a scheme has finite support

The order of vanishing of an element of the function field of an integral locally Noetherian
scheme vanishes wherever the element is a unit in the local ring, and on an affine open it can
therefore be nonzero only at the points whose prime ideal contains a numerator or a denominator.
Krull's height theorem bounds those points by the minimal primes over a principal ideal, so on an
affine open the divisorial support of a rational function is finite.

mathlib defines the order of vanishing at a codimension-one point but provides no divisor of a
rational function and no finiteness statement for its support; the algebraic cycle file has no
principal divisor at all.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

section Dictionary

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

include hU in
/-- The codimension of a point of an affine open is the height of the corresponding prime. -/
theorem coheight_eq_height_primeIdealOf (x : U) :
    coheight (x.1 : X) = (hU.primeIdealOf x).asIdeal.height := by
  haveI := hU.isLocalization_stalk x
  have h1 : ringKrullDim (X.presheaf.stalk x.1) = coheight x.1 := ringKrullDim_stalk_eq_coheight _
  have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf x).asIdeal
    (X.presheaf.stalk x.1)
  rw [h1] at h2
  exact_mod_cast h2

include hU in
/-- A section is a unit at a point of an affine open exactly when it avoids the corresponding
prime. -/
theorem isUnit_germ_iff_notMem_primeIdealOf (x : U) (a : Γ(X, U)) :
    IsUnit (X.presheaf.germ U x.1 x.2 a) ↔ a ∉ (hU.primeIdealOf x).asIdeal := by
  haveI := hU.isLocalization_stalk x
  exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x.1)
    (hU.primeIdealOf x).asIdeal a

include hU in
theorem primeIdealOf_injective : Function.Injective hU.primeIdealOf := by
  intro x y h
  have hx := hU.fromSpec_primeIdealOf x
  have hy := hU.fromSpec_primeIdealOf y
  rw [h, hy] at hx
  exact Subtype.ext hx.symm

end Dictionary

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **A unit of the local ring has order of vanishing zero.** -/
theorem ord_algebraMap_stalk_eq_zero {z : X} {s : X.presheaf.stalk z} (hs : IsUnit s) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField s) z = 0 := by
  by_cases hz : coheight z = 1
  · haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz]
    have h : X.ordHom z hz (algebraMap (X.presheaf.stalk z) X.functionField s) = 1 :=
      Ring.ordFrac_of_isUnit hs
    rw [h]
    simp
  · simp [hz]

/-- A section whose germ at a point is a unit has order of vanishing zero there. -/
theorem ord_germToFunctionField_eq_zero_of_isUnit_germ {U : X.Opens} [Nonempty U]
    (a : Γ(X, U)) {z : X} (hzU : z ∈ U) (hz : IsUnit (X.presheaf.germ U z hzU a)) :
    Scheme.ord (X.germToFunctionField U a) z = 0 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hzU a]
  exact ord_algebraMap_stalk_eq_zero hz

/-- **The divisorial support of a rational function is finite on an affine open.**  Writing the
function as a quotient of two sections, its order can be nonzero only at the points whose prime
contains the numerator or the denominator, and there are finitely many such points of
codimension one. -/
theorem finite_ord_support_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {a b : Γ(X, U)} (ha : a ≠ 0) (hb : b ≠ 0)
    {f : X.functionField} (hf : f * X.germToFunctionField U b = X.germToFunctionField U a) :
    {x : U | Scheme.ord f x.1 ≠ 0}.Finite := by
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hsub : hU.primeIdealOf '' {x : U | Scheme.ord f x.1 ≠ 0} ⊆
      {p : PrimeSpectrum Γ(X, U) | p.asIdeal.height = 1 ∧ (a ∈ p.asIdeal ∨ b ∈ p.asIdeal)} := by
    rintro p ⟨x, hx, rfl⟩
    have hxne : Scheme.ord f x.1 ≠ 0 := hx
    have hcoh : coheight (x.1 : X) = 1 := by
      by_contra hcon
      exact hxne (Scheme.ord_eq_zero_of_coheight_neq_one hcon f)
    refine ⟨(coheight_eq_height_primeIdealOf hU x).symm.trans hcoh, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hna, hnb⟩ := hcon
    have hfa : Scheme.ord (X.germToFunctionField U a) x.1 = 0 :=
      ord_germToFunctionField_eq_zero_of_isUnit_germ a x.2
        ((isUnit_germ_iff_notMem_primeIdealOf hU x a).mpr hna)
    have hfb : Scheme.ord (X.germToFunctionField U b) x.1 = 0 :=
      ord_germToFunctionField_eq_zero_of_isUnit_germ b x.2
        ((isUnit_germ_iff_notMem_primeIdealOf hU x b).mpr hnb)
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hxne (by simp)
    have hb0 : X.germToFunctionField U b ≠ 0 := by
      intro h
      exact hb (Scheme.germToFunctionField_injective X U (by rw [h, map_zero]))
    have hmul := Scheme.ord_mul (x := x.1) hf0 hb0
    rw [hf, hfa, hfb, add_zero] at hmul
    exact hxne hmul.symm
  have hfin : {p : PrimeSpectrum Γ(X, U) |
      p.asIdeal.height = 1 ∧ (a ∈ p.asIdeal ∨ b ∈ p.asIdeal)}.Finite := by
    refine Set.Finite.of_finite_image (f := fun p => p.asIdeal) ?_ ?_
    · refine Set.Finite.subset (finite_heightOneSupport_frac ha hb) ?_
      rintro q ⟨p, ⟨hh, hm⟩, rfl⟩
      exact ⟨p.2, hh, hm⟩
    · intro p _ q _ h
      exact PrimeSpectrum.ext h
  exact Set.Finite.of_finite_image (Set.Finite.subset hfin hsub)
    (Function.Injective.injOn (primeIdealOf_injective hU))

omit [IsLocallyNoetherian X] in
/-- On an affine open a rational function is a quotient of two sections. -/
theorem exists_num_den_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) :
    ∃ a b : Γ(X, U), b ≠ 0 ∧ f * X.germToFunctionField U b = X.germToFunctionField U a := by
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) f
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hbne : X.germToFunctionField U b ≠ 0 := fun h =>
    hb0 (Scheme.germToFunctionField_injective X U (by rw [h, map_zero]))
  have halga : X.germToFunctionField U a = algebraMap Γ(X, U) X.functionField a := rfl
  have halgb : X.germToFunctionField U b = algebraMap Γ(X, U) X.functionField b := rfl
  refine ⟨a, b, hb0, ?_⟩
  rw [halga, halgb, ← hab]
  exact div_mul_cancel₀ _ (by rw [← halgb]; exact hbne)

/-- The support of the order of vanishing inside an affine open is finite. -/
theorem finite_ord_support_inter_affineOpen {U : X.Opens} (hU : IsAffineOpen U)
    (f : X.functionField) :
    {z : X | z ∈ U ∧ Scheme.ord f z ≠ 0}.Finite := by
  by_cases hne : Nonempty U
  · haveI := hne
    by_cases hf0 : f = 0
    · subst hf0
      simp
    obtain ⟨a, b, hb0, hab⟩ := exists_num_den_of_isAffineOpen hU f
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hab
      rcases mul_eq_zero.mp hab with h | h
      · exact hf0 h
      · exact hb0 (Scheme.germToFunctionField_injective X U (by rw [h, map_zero]))
    refine Set.Finite.subset
      ((finite_ord_support_of_isAffineOpen hU ha0 hb0 hab).image Subtype.val) ?_
    rintro z ⟨hzU, hz⟩
    exact ⟨⟨z, hzU⟩, hz, rfl⟩
  · convert Set.finite_empty
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hzU
    exact absurd (⟨⟨z, hzU⟩⟩ : Nonempty U) hne

/-- **The divisorial support of a rational function on a Noetherian integral scheme is finite.**
Covering the scheme by finitely many affine opens reduces this to the affine case, where Krull's
height theorem bounds the support by the minimal primes over the numerator and the denominator. -/
theorem finite_ord_support [CompactSpace X] (f : X.functionField) :
    {z : X | Scheme.ord f z ≠ 0}.Finite := by
  have hopen : ∀ U : X.affineOpens, IsOpen (((U : X.Opens) : Set X)) := fun U =>
    (U : X.Opens).isOpen
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := by
    intro x _
    refine Set.mem_iUnion.mpr ⟨⟨(X.affineCover.f (X.affineCover.idx x)).opensRange,
      isAffineOpen_opensRange _⟩, ?_⟩
    exact X.affineCover.covers x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    (fun U _ => finite_ord_support_inter_affineOpen U.2 f)) ?_
  intro z hz
  have hmem := hs (Set.mem_univ z)
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨U, hUs, hzU⟩ := hmem
  exact Set.mem_biUnion hUs ⟨hzU, hz⟩

end GaloisForLFunctions.HTGeometry
