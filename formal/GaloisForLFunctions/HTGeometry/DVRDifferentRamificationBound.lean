import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# A sharp DVR ramification bound from the different

If an irreducible element of an upper discrete valuation ring lies in the different, then the
ramification exponent at that maximal ideal is at most two.  Combined with genuine ramification,
this forces simple ramification index two.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- An irreducible element contained in the different bounds any corresponding ramification
exponent by two. -/
theorem ramificationExponent_le_two_of_irreducible_mem_different
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [IsDedekindDomain A] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal]
    (δ : B) (hδ : Irreducible δ) (hδD : δ ∈ differentIdeal A B)
    (e : ℕ) (hp : p ≠ ⊥)
    (he : maximalIdeal B ^ e ∣ p.map (algebraMap A B)) :
    e ≤ 2 := by
  have hdvd : maximalIdeal B ^ (e - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal A (maximalIdeal B) e hp he
  have hmem : δ ∈ maximalIdeal B ^ (e - 1) :=
    (Ideal.dvd_iff_le.mp hdvd) hδD
  rw [hδ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hmem
  have hpow : δ ^ (e - 1) ∣ δ ^ (1 : ℕ) := by simpa using hmem
  have hsub : e - 1 ≤ 1 :=
    (pow_dvd_pow_iff hδ.ne_zero hδ.not_isUnit).mp hpow
  omega

/-- The actual ramification index at an upper DVR maximal ideal is at most two when an
irreducible element lies in the different. -/
theorem ramificationIdx_le_two_of_irreducible_mem_different
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [IsDedekindDomain A] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal]
    (δ : B) (hδ : Irreducible δ) (hδD : δ ∈ differentIdeal A B)
    (hp : p ≠ ⊥) :
    p.ramificationIdx' (maximalIdeal B) ≤ 2 := by
  apply ramificationExponent_le_two_of_irreducible_mem_different δ hδ hδD _ hp
  exact Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'

/-- If the ramification index is nonzero and nontrivial, the preceding bound is sharp: it equals
two. -/
theorem ramificationIdx_eq_two_of_irreducible_mem_different
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [IsDedekindDomain A] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal]
    (δ : B) (hδ : Irreducible δ) (hδD : δ ∈ differentIdeal A B)
    (hp : p ≠ ⊥)
    (hzero : p.ramificationIdx' (maximalIdeal B) ≠ 0)
    (hone : p.ramificationIdx' (maximalIdeal B) ≠ 1) :
    p.ramificationIdx' (maximalIdeal B) = 2 := by
  have hle := ramificationIdx_le_two_of_irreducible_mem_different δ hδ hδD hp
  omega

end

end GaloisForLFunctions.HTGeometry
