import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.HyperplaneTateTrace
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.ReciprocalProjectiveBoundary
import GaloisForLFunctions.HTGeometry.FiniteSupportCounting

/-!
# The explicit coordinate-boundary trace

Restriction to a prescribed support identifies the coordinate boundary with
torus hyperplanes. Their count polynomials give the boundary contribution over
every finite extension.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

/-- Sum-zero vectors with a prescribed support. -/
def supportZeroSum (S : Finset ι) : Finset (ι → F) :=
  univ.filter (fun x => HTGeometry.configSupport 0 x = S ∧ ∑ i, x i = 0)

/-- Restriction and reindexing identify an exact support with a coordinate torus. -/
def supportTorusEquiv (S : Finset ι) :
    {x : ι → F // HTGeometry.configSupport 0 x = S} ≃ MomentTorus F (Fintype.card S) :=
  (HTGeometry.configSupportFiberEquiv 0 S).trans
    (Equiv.arrowCongr (Fintype.equivFin S) (Equiv.refl _))

omit [Fintype F] in
private theorem supportTorusEquiv_apply (S : Finset ι)
    (x : {x : ι → F // HTGeometry.configSupport 0 x = S}) (j : Fin (Fintype.card S)) :
    (supportTorusEquiv S x j : F) = x.val ((Fintype.equivFin S).symm j) := rfl

omit [Fintype F] in
/-- Restriction to the support preserves the coordinate sum. -/
theorem supportTorusEquiv_sum (S : Finset ι)
    (x : {x : ι → F // HTGeometry.configSupport 0 x = S}) :
    (∑ j, (supportTorusEquiv S x j : F)) = ∑ i, x.val i := by
  simp only [supportTorusEquiv_apply]
  calc (∑ j, x.val ((Fintype.equivFin S).symm j)) = ∑ i : S, x.val i :=
      (Fintype.equivFin S).symm.sum_comp (fun i : S => x.val i)
    _ = ∑ i ∈ S, x.val i := sum_coe_sort S x.val
    _ = ∑ i, x.val i := by
      apply sum_subset (subset_univ S)
      intro i _ hi
      by_contra h
      apply hi
      rw [← x.property]
      exact HTGeometry.mem_configSupport.mpr h

/-- The exact-support sum-zero count is the corresponding torus hyperplane count. -/
theorem supportZeroSum_card (S : Finset ι) :
    (supportZeroSum (F := F) S).card = (coordinateZeroTorus (F := F) S.card).card := by
  let e₀ : {x : ι → F // HTGeometry.configSupport 0 x = S ∧ ∑ i, x i = 0} ≃
      {x : {x : ι → F // HTGeometry.configSupport 0 x = S} // ∑ i, x.val i = 0} :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := e₀.trans ((supportTorusEquiv (F := F) S).subtypeEquiv
    (p := fun x => ∑ i, x.val i = 0)
    (q := fun y => ∑ j, (y j : F) = 0)
    (fun x => by rw [supportTorusEquiv_sum]))
  rw [supportZeroSum, ← Fintype.card_subtype, coordinateZeroTorus, ← Fintype.card_subtype]
  have hcard : Fintype.card S = S.card := Fintype.card_coe S
  simpa only [hcard] using Fintype.card_congr e

/-- Sum-zero vectors with prescribed support size. -/
def supportSizeZeroSum (r : ℕ) : Finset (ι → F) :=
  univ.filter (fun x => (HTGeometry.configSupport 0 x).card = r ∧ ∑ i, x i = 0)

/-- Choosing the support gives the binomial factor in each stratum. -/
theorem supportSizeZeroSum_card (r : ℕ) :
    (supportSizeZeroSum (F := F) (ι := ι) r).card =
      (Fintype.card ι).choose r * (coordinateZeroTorus (F := F) r).card := by
  have hsplit : supportSizeZeroSum (F := F) (ι := ι) r =
      (univ.powersetCard r).biUnion (supportZeroSum (F := F)) := by
    ext x
    simp only [supportSizeZeroSum, supportZeroSum, mem_filter, mem_univ, true_and,
      mem_biUnion, mem_powersetCard]
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨HTGeometry.configSupport 0 x, ⟨subset_univ _, hc⟩, rfl, hs⟩
    · rintro ⟨S, ⟨_, hc⟩, hS, hs⟩
      exact ⟨by rw [hS, hc], hs⟩
  rw [hsplit, card_biUnion]
  · have hterm : ∀ S ∈ univ.powersetCard (α := ι) r,
        (supportZeroSum (F := F) S).card = (coordinateZeroTorus (F := F) r).card := by
      intro S hS
      rw [supportZeroSum_card, (mem_powersetCard.mp hS).2]
    rw [sum_congr rfl hterm, sum_const, card_powersetCard, card_univ, nsmul_eq_mul,
      Nat.cast_id]
  · intro S _ T _ hST
    apply disjoint_left.mpr
    intro x hx hy
    exact hST ((mem_filter.mp hx).2.1.symm.trans (mem_filter.mp hy).2.1)

/-- Nonzero sum-zero vectors supported on at most `r` coordinates. -/
def boundedSupportZeroSum (r : ℕ) : Finset (ι → F) :=
  univ.filter (fun x => 0 < (HTGeometry.configSupport 0 x).card ∧
    (HTGeometry.configSupport 0 x).card ≤ r ∧ ∑ i, x i = 0)

/-- Summing the disjoint support-size strata gives the bounded-support count. -/
theorem boundedSupportZeroSum_card (r : ℕ) :
    (boundedSupportZeroSum (F := F) (ι := ι) r).card =
      ∑ k ∈ Icc 1 r, (Fintype.card ι).choose k * (coordinateZeroTorus (F := F) k).card := by
  have hsplit : boundedSupportZeroSum (F := F) (ι := ι) r =
      (Icc 1 r).biUnion (supportSizeZeroSum (F := F) (ι := ι)) := by
    ext x
    simp only [boundedSupportZeroSum, supportSizeZeroSum, mem_filter, mem_univ,
      true_and, mem_biUnion, mem_Icc]
    constructor
    · rintro ⟨hpos, hle, hs⟩
      exact ⟨(HTGeometry.configSupport 0 x).card, ⟨hpos, hle⟩, rfl, hs⟩
    · rintro ⟨k, ⟨hpos, hle⟩, hk, hs⟩
      exact ⟨by omega, by omega, hs⟩
  rw [hsplit, card_biUnion]
  · exact sum_congr rfl (fun k _ => supportSizeZeroSum_card k)
  · intro k _ l _ hkl
    apply disjoint_left.mpr
    intro x hx hy
    exact hkl ((mem_filter.mp hx).2.1.symm.trans (mem_filter.mp hy).2.1)

/-- Each nonempty support stratum has a free factor given by scalar multiplication. -/
theorem boundedSupportZeroSum_card_scale (r : ℕ) :
    (boundedSupportZeroSum (F := F) (ι := ι) r).card =
      (Fintype.card F - 1) * ∑ k ∈ Icc 1 r,
        (Fintype.card ι).choose k * (normalizedCoordinateZeroTorus (F := F) (k - 1)).card := by
  rw [boundedSupportZeroSum_card, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hcount : (coordinateZeroTorus (F := F) k).card =
      (Fintype.card F - 1) * (normalizedCoordinateZeroTorus (F := F) (k - 1)).card := by
    have h := coordinateZeroTorus_card (F := F) (k - 1)
    rwa [Nat.sub_add_cancel (mem_Icc.mp hk).1] at h
  rw [hcount]
  ring

omit [Fintype F] in
/-- Two zero coordinates are exactly a deficit of at least two in the support size. -/
theorem two_zero_coordinates_iff (x : ι → F) :
    (∃ a b, a ≠ b ∧ x a = 0 ∧ x b = 0) ↔
      (HTGeometry.configSupport 0 x).card + 2 ≤ Fintype.card ι := by
  have hm : ∀ i, i ∈ (HTGeometry.configSupport 0 x)ᶜ ↔ x i = 0 := by
    intro i
    simp only [mem_compl, HTGeometry.mem_configSupport, not_not]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hc := one_lt_card_iff.mpr ⟨a, b, (hm a).mpr ha, (hm b).mpr hb, hab⟩
    rw [card_compl] at hc
    omega
  · intro h
    have hc : 1 < (HTGeometry.configSupport 0 x)ᶜ.card := by
      rw [card_compl]
      omega
    obtain ⟨a, b, ha, hb, hab⟩ := one_lt_card_iff.mp hc
    exact ⟨a, b, hab, (hm a).mp ha, (hm b).mp hb⟩

/-- The nonzero affine cone over the coordinate boundary. -/
def coordinateBoundaryCone : Finset (ι → F) :=
  boundedSupportZeroSum (Fintype.card ι - 2)

/-- The support description is equivalent to the actual homogeneous equations
and the requirement that at least one coordinate vanish. -/
theorem mem_coordinateBoundaryCone_iff (x : ι → F) :
    x ∈ coordinateBoundaryCone (F := F) (ι := ι) ↔
      (∑ i, x i) = 0 ∧ (∃ c, x c ≠ 0) ∧ (∃ a, x a = 0) ∧
        reciprocalClearedValue x = 0 := by
  change x ∈ boundedSupportZeroSum (Fintype.card ι - 2) ↔ _
  simp only [boundedSupportZeroSum, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hpos, hbound, hs⟩
    obtain ⟨c, hc⟩ := card_pos.mp hpos
    have hpair : (HTGeometry.configSupport 0 x).card + 2 ≤ Fintype.card ι := by omega
    obtain ⟨a, b, hab, ha, hb⟩ := (two_zero_coordinates_iff x).mpr hpair
    exact ⟨hs, ⟨c, HTGeometry.mem_configSupport.mp hc⟩, ⟨a, ha⟩,
      reciprocalClearedValue_of_two_zeros x hab ha hb⟩
  · rintro ⟨hs, ⟨c, hc⟩, ⟨a, ha⟩, hvalue⟩
    have hpos : 0 < (HTGeometry.configSupport 0 x).card :=
      card_pos.mpr ⟨c, HTGeometry.mem_configSupport.mpr hc⟩
    have hb : ∃ b, b ≠ a ∧ x b = 0 := by
      by_contra h
      apply reciprocalClearedValue_ne_zero_of_one_zero x ha _ hvalue
      intro i hia hi
      exact h ⟨i, hia, hi⟩
    obtain ⟨b, hba, hb⟩ := hb
    have hbound := (two_zero_coordinates_iff x).mp ⟨a, b, hba.symm, ha, hb⟩
    exact ⟨hpos, by omega, hs⟩

private theorem support_scale (u : Fˣ) (x : ι → F) :
    HTGeometry.configSupport 0 (fun i => (u : F) * x i) = HTGeometry.configSupport 0 x := by
  ext i
  simp only [HTGeometry.mem_configSupport, mul_ne_zero_iff, Units.ne_zero, true_and]

/-- Scalar multiplication preserves each bounded-support sum-zero cone. -/
def boundedScale (r : ℕ) (u : Fˣ) (x : ↥(boundedSupportZeroSum (F := F) (ι := ι) r)) :
    ↥(boundedSupportZeroSum (F := F) (ι := ι) r) :=
  ⟨fun i => (u : F) * x.val i, by
    have hx := (mem_filter.mp x.property).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [support_scale]
    refine ⟨hx.1, hx.2.1, ?_⟩
    rw [← mul_sum, hx.2.2, mul_zero]⟩

private theorem boundedScale_apply (r : ℕ) (u : Fˣ)
    (x : ↥(boundedSupportZeroSum (F := F) (ι := ι) r)) (i : ι) :
    (boundedScale r u x).val i = (u : F) * x.val i := rfl

private theorem bounded_point_nonzero (r : ℕ)
    (x : ↥(boundedSupportZeroSum (F := F) (ι := ι) r)) : ∃ i, x.val i ≠ 0 := by
  obtain ⟨i, hi⟩ := card_pos.mp (mem_filter.mp x.property).2.1
  exact ⟨i, HTGeometry.mem_configSupport.mp hi⟩

/-- Projective equivalence is simultaneous multiplication by a nonzero scalar. -/
def supportScalarSetoid (r : ℕ) : Setoid ↥(boundedSupportZeroSum (F := F) (ι := ι) r) where
  r x y := ∃ u : Fˣ, ∀ i, x.val i = (u : F) * y.val i
  iseqv :=
    { refl := fun x => ⟨1, by intro i; simp⟩
      symm := by
        rintro x y ⟨u, hu⟩
        refine ⟨u⁻¹, fun i => ?_⟩
        rw [hu i, ← mul_assoc]
        simp
      trans := by
        rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
        refine ⟨u * v, fun i => ?_⟩
        rw [hu i, hv i, Units.val_mul, mul_assoc] }

/-- Actual scalar orbits of nonzero sum-zero vectors with bounded support. -/
def ProjectiveSupportZeroSum (r : ℕ) := Quotient (supportScalarSetoid (F := F) (ι := ι) r)

instance (r : ℕ) : Fintype (ProjectiveSupportZeroSum (F := F) (ι := ι) r) :=
  Fintype.ofFinite _

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
