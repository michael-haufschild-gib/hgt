import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianPackingMinimum
import GaloisForLFunctions.HTGeometry.Lattices.IntegralFourEnergy
import Mathlib.Data.Int.Interval

/-!
# Minimum vectors and abelian parallelograms

The norm-four vectors in an abelian augmentation square are exactly the signed
four-point configurations `e_a + e_b - e_c - e_d` with distinct labels and
`a*b=c*d`. Choosing one positive and one negative coordinate gives four frames
per vector; a frame determines the ordered parallelogram uniquely.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.IntegralZeroSum
variable (G : Type) [CommGroup G] [Fintype G]

/-- Ordered four-point parallelograms in a finite abelian group. -/
@[ext] structure AbelianParallelogram where
  a : G
  b : G
  c : G
  d : G
  hab : a ≠ b
  hac : a ≠ c
  had : a ≠ d
  hbc : b ≠ c
  hbd : b ≠ d
  hcd : c ≠ d
  product_eq : a*b = c*d

instance : Finite (AbelianParallelogram G) :=
  Finite.of_injective (fun q : AbelianParallelogram G => (q.a, q.b, q.c, q.d)) (by
    intro q r h
    have ha := congrArg (fun z : G × G × G × G => z.1) h
    have hb := congrArg (fun z : G × G × G × G => z.2.1) h
    have hc := congrArg (fun z : G × G × G × G => z.2.2.1) h
    have hd := congrArg (fun z : G × G × G × G => z.2.2.2) h
    exact AbelianParallelogram.ext ha hb hc hd)

/-- Energy-four vectors in the actual integral augmentation square. -/
abbrev AbelianMinimalVector :=
  {v : AbelianAugmentationLattice G // cyclicMovingEnergy G v = 4}

private theorem root_sum_moment_zero_iff (a b c d : G) :
    cyclicMovingFirstMoment G (cyclicRootVector G a c + cyclicRootVector G b d) = 0 ↔
      a*b = c*d := by
  rw [map_add, cyclicMovingFirstMoment_root, cyclicMovingFirstMoment_root]
  have h : Additive.ofMul a - Additive.ofMul c +
      (Additive.ofMul b - Additive.ofMul d) =
      (Additive.ofMul a + Additive.ofMul b) -
        (Additive.ofMul c + Additive.ofMul d) := by abel
  rw [h, sub_eq_zero]
  exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

/-- An ordered parallelogram gives an actual minimum vector. -/
def AbelianParallelogram.vector (q : AbelianParallelogram G) : AbelianMinimalVector G :=
  ⟨⟨cyclicRootVector G q.a q.c + cyclicRootVector G q.b q.d,
      (root_sum_moment_zero_iff G _ _ _ _).mpr q.product_eq⟩, by
    change energy (cyclicMovingProfile G (_ + _)) = 4
    rw [map_add, cyclicMovingProfile_root, cyclicMovingProfile_root]
    exact energy_two_disjoint_roots q.hab q.hac q.had q.hbc q.hbd q.hcd⟩

@[simp] theorem AbelianParallelogram.vector_profile (q : AbelianParallelogram G) :
    cyclicMovingProfile G q.vector.val = root q.a q.c + root q.b q.d := by
  change cyclicMovingProfile G (_ + _) = _
  rw [map_add, cyclicMovingProfile_root, cyclicMovingProfile_root]

/-- Every minimum vector comes from an ordered abelian parallelogram. -/
theorem abelianParallelogram_vector_surjective :
    Function.Surjective (AbelianParallelogram.vector G) := by
  intro v
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hx⟩ :=
    energy_four_decomposition (cyclicMovingProfile_sum G v.val) v.property
  have hv : v.val.val = cyclicRootVector G a c + cyclicRootVector G b d := by
    apply cyclicMovingProfile_injective G
    simpa only [map_add, cyclicMovingProfile_root] using hx
  have hp : a*b = c*d := (root_sum_moment_zero_iff G a b c d).mp (hv ▸ v.val.property)
  refine ⟨⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hp⟩, ?_⟩
  apply Subtype.ext
  exact Subtype.ext hv.symm

instance : Finite (AbelianMinimalVector G) :=
  Finite.of_surjective _ (abelianParallelogram_vector_surjective G)

/-- A minimum vector with one chosen positive and one chosen negative label. -/
abbrev AbelianMinimalFrame := Σ v : AbelianMinimalVector G,
  {a : G // cyclicMovingProfile G v.val a = 1} ×
  {c : G // cyclicMovingProfile G v.val c = -1}

/-- The first positive and negative labels frame the corresponding minimum vector. -/
def AbelianParallelogram.frame (q : AbelianParallelogram G) : AbelianMinimalFrame G :=
  ⟨q.vector, ⟨⟨q.a, by
    rw [q.vector_profile]
    exact (two_roots_eq_one_iff q.hab q.hac q.had q.hbc q.hbd q.hcd).mpr (Or.inl rfl)⟩,
    ⟨q.c, by
      rw [q.vector_profile]
      exact (two_roots_eq_neg_one_iff q.hab q.hac q.had q.hbc q.hbd q.hcd).mpr
        (Or.inl rfl)⟩⟩⟩

theorem abelianParallelogram_frame_injective :
    Function.Injective (AbelianParallelogram.frame G) := by
  intro q r h
  have ha : q.a = r.a := congrArg (fun f : AbelianMinimalFrame G => f.2.1.val) h
  have hc : q.c = r.c := congrArg (fun f : AbelianMinimalFrame G => f.2.2.val) h
  have hx := congrArg (fun f : AbelianMinimalFrame G => cyclicMovingProfile G f.1.val) h
  change cyclicMovingProfile G q.vector.val = cyclicMovingProfile G r.vector.val at hx
  rw [q.vector_profile, r.vector_profile, ha, hc] at hx
  have hbd := root_injective q.hbd r.hbd (add_left_cancel hx)
  exact AbelianParallelogram.ext ha hbd.1 hc hbd.2

theorem abelianParallelogram_frame_surjective :
    Function.Surjective (AbelianParallelogram.frame G) := by
  rintro ⟨v, ⟨a, ha⟩, ⟨c, hc⟩⟩
  obtain ⟨b, d, hab, hac, had, hbc, hbd, hcd, hx⟩ :=
    energy_four_decomposition_at (cyclicMovingProfile_sum G v.val) v.property ha hc
  have hv : v.val.val = cyclicRootVector G a c + cyclicRootVector G b d := by
    apply cyclicMovingProfile_injective G
    simpa only [map_add, cyclicMovingProfile_root] using hx
  have hp : a*b = c*d := (root_sum_moment_zero_iff G a b c d).mp (hv ▸ v.val.property)
  let q : AbelianParallelogram G := ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hp⟩
  have hq : q.vector = v := Subtype.ext (Subtype.ext hv.symm)
  refine ⟨q, ?_⟩
  apply Sigma.ext hq
  cases hq
  rfl

/-- A minimum vector has exactly four ordered parallelogram presentations. -/
def abelianParallelogramFrameEquiv : AbelianParallelogram G ≃ AbelianMinimalFrame G :=
  Equiv.ofBijective _ ⟨abelianParallelogram_frame_injective G,
    abelianParallelogram_frame_surjective G⟩

theorem abelianParallelogram_card :
    Nat.card (AbelianParallelogram G) = 4 * Nat.card (AbelianMinimalVector G) := by
  classical
  letI := Fintype.ofFinite (AbelianMinimalVector G)
  rw [Nat.card_congr (abelianParallelogramFrameEquiv G), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  have hframe (v : AbelianMinimalVector G) :
      Fintype.card ({a : G // cyclicMovingProfile G v.val a = 1} ×
        {c : G // cyclicMovingProfile G v.val c = -1}) = 4 := by
    rw [Fintype.card_prod, card_positive_of_energy_four
      (cyclicMovingProfile_sum G v.val) v.property, card_negative_of_energy_four
      (cyclicMovingProfile_sum G v.val) v.property]
  simp only [hframe, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]
  exact mul_comm _ _

#print axioms abelianParallelogramFrameEquiv
#print axioms abelianParallelogram_card
end GaloisForLFunctions.RepresentationLifting
