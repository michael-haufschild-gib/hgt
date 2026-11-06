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

/-- A support indexed by its cardinality. -/
def supportIndexEquiv (S : Finset ι) : S ≃ Fin S.card :=
  (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))

/-- Restriction and reindexing identify an exact support with a coordinate torus. -/
def supportTorusEquiv (S : Finset ι) :
    {x : ι → F // HTGeometry.configSupport 0 x = S} ≃ MomentTorus F S.card :=
  (HTGeometry.configSupportFiberEquiv 0 S).trans
    (Equiv.arrowCongr (supportIndexEquiv S) (Equiv.refl _))

omit [Fintype F] in
private theorem supportTorusEquiv_apply (S : Finset ι)
    (x : {x : ι → F // HTGeometry.configSupport 0 x = S}) (j : Fin S.card) :
    (supportTorusEquiv S x j : F) = x.val ((supportIndexEquiv S).symm j) := rfl

omit [Fintype F] in
/-- Restriction to the support preserves the coordinate sum. -/
theorem supportTorusEquiv_sum (S : Finset ι)
    (x : {x : ι → F // HTGeometry.configSupport 0 x = S}) :
    (∑ j, (supportTorusEquiv S x j : F)) = ∑ i, x.val i := by
  simp only [supportTorusEquiv_apply]
  calc (∑ j, x.val ((supportIndexEquiv S).symm j)) = ∑ i : S, x.val i :=
      (supportIndexEquiv S).symm.sum_comp (fun i : S => x.val i)
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
  exact Fintype.card_congr e

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

omit [Fintype F] [DecidableEq ι] in
private theorem support_scale (u : Fˣ) (x : ι → F) :
    HTGeometry.configSupport 0 (fun i => (u : F) * x i) = HTGeometry.configSupport 0 x := by
  ext i
  simp only [HTGeometry.mem_configSupport, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨u.ne_zero, h⟩⟩

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

instance (r : ℕ) : Fintype (ProjectiveSupportZeroSum (F := F) (ι := ι) r) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk (supportScalarSetoid r)) (fun q => Quotient.exists_rep q)

private theorem orbit_scalar_exists (r : ℕ)
    (q : ProjectiveSupportZeroSum (F := F) (ι := ι) r)
    (x : {x : ↥(boundedSupportZeroSum (F := F) (ι := ι) r) //
      Quotient.mk (supportScalarSetoid r) x = q}) :
    ∃ u : Fˣ, ∀ i, x.val.val i = (u : F) * q.out.val i :=
  Quotient.exact (x.property.trans (Quotient.out_eq q).symm)

/-- The representatives of a projective point are in bijection with the nonzero scalars. -/
def projectiveSupportFiberEquiv (r : ℕ)
    (q : ProjectiveSupportZeroSum (F := F) (ι := ι) r) :
    Fˣ ≃ {x : ↥(boundedSupportZeroSum (F := F) (ι := ι) r) //
      Quotient.mk (supportScalarSetoid r) x = q} where
  toFun u := ⟨boundedScale r u q.out,
    (Quotient.sound (s := supportScalarSetoid r)
      (a := boundedScale r u q.out) (b := q.out) ⟨u, fun _ => rfl⟩).trans (Quotient.out_eq q)⟩
  invFun x := Classical.choose (orbit_scalar_exists r q x)
  left_inv u := by
    apply Units.ext
    obtain ⟨i, hi⟩ := bounded_point_nonzero r q.out
    apply mul_right_cancel₀ hi
    exact (Classical.choose_spec (orbit_scalar_exists r q _) i).symm
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact (Classical.choose_spec (orbit_scalar_exists r q x) i).symm

/-- Counting representatives gives the free scalar factor in the projective quotient. -/
theorem boundedSupportZeroSum_card_orbits (r : ℕ) :
    (boundedSupportZeroSum (F := F) (ι := ι) r).card =
      Fintype.card (ProjectiveSupportZeroSum (F := F) (ι := ι) r) * (Fintype.card F - 1) := by
  classical
  let π : ↥(boundedSupportZeroSum (F := F) (ι := ι) r) →
      ProjectiveSupportZeroSum (F := F) (ι := ι) r := Quotient.mk (supportScalarSetoid r)
  have hf : ∀ q : ProjectiveSupportZeroSum (F := F) (ι := ι) r,
      Fintype.card {x // π x = q} = Fintype.card Fˣ := by
    intro q
    convert (Fintype.card_congr (projectiveSupportFiberEquiv r q)).symm <;> rfl
  calc (boundedSupportZeroSum (F := F) (ι := ι) r).card =
      Fintype.card ↥(boundedSupportZeroSum (F := F) (ι := ι) r) := (Fintype.card_coe _).symm
    _ = Fintype.card (Σ q, {x // π x = q}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = _ := by
      rw [Fintype.card_sigma, sum_congr rfl (fun q _ => hf q), sum_const,
        card_univ, nsmul_eq_mul, Fintype.card_units, Nat.cast_id]

/-- The projective support strata have their expected normalized torus counts. -/
theorem projectiveSupportZeroSum_card (r : ℕ) :
    Fintype.card (ProjectiveSupportZeroSum (F := F) (ι := ι) r) =
      ∑ k ∈ Icc 1 r, (Fintype.card ι).choose k *
        (normalizedCoordinateZeroTorus (F := F) (k - 1)).card := by
  have hq : Fintype.card F - 1 ≠ 0 := by
    have h := Fintype.one_lt_card (α := F)
    omega
  apply mul_right_cancel₀ hq
  rw [← boundedSupportZeroSum_card_orbits, boundedSupportZeroSum_card_scale, mul_comm]

/-- The coordinate boundary as actual projective scalar orbits. -/
abbrev ProjectiveCoordinateBoundary :=
  ProjectiveSupportZeroSum (F := F) (ι := ι) (Fintype.card ι - 2)

/-- Every projective boundary point is counted by its support and normalized torus coordinates. -/
theorem projectiveCoordinateBoundary_card :
    Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := ι)) =
      ∑ k ∈ Icc 1 (Fintype.card ι - 2), (Fintype.card ι).choose k *
        (normalizedCoordinateZeroTorus (F := F) (k - 1)).card :=
  projectiveSupportZeroSum_card _

/-- The affine coordinate-sum hyperplane. -/
def affineZeroSum (m : ℕ) : Finset (Fin m → F) := univ.filter (fun x => ∑ i, x i = 0)

/-- Deleting one coordinate freely parametrizes the affine hyperplane. -/
theorem affineZeroSum_card (m : ℕ) :
    (affineZeroSum (F := F) (m + 1)).card = Fintype.card F ^ m := by
  have hc : (affineZeroSum (F := F) (m + 1)).card =
      (univ : Finset (Fin m → F)).card := by
    apply card_bij (fun (x : Fin (m + 1) → F) _ => Fin.tail x)
    · intro _ _
      exact mem_univ _
    · intro x hx y hy htail
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      have hs := congrArg (fun t : Fin m → F => ∑ j, t j) htail
      rw [Fin.sum_univ_succ] at hx' hy'
      change (∑ j : Fin m, x j.succ) = ∑ j : Fin m, y j.succ at hs
      have h₀ : x 0 = y 0 := by linear_combination hx' - hy' - hs
      funext i
      exact Fin.cases h₀ (fun j => congrFun htail j) i
    · intro y _
      refine ⟨Fin.cons (-(∑ j, y j)) y, ?_, rfl⟩
      simp [affineZeroSum, Fin.sum_univ_succ]
  simpa only [card_univ, Fintype.card_fun, Fintype.card_fin] using hc

omit [Fintype F] [DecidableEq ι] in
private theorem support_pos_iff (x : ι → F) :
    0 < (HTGeometry.configSupport 0 x).card ↔ x ≠ 0 := by
  constructor
  · intro hpos hz
    obtain ⟨i, hi⟩ := card_pos.mp hpos
    exact (HTGeometry.mem_configSupport.mp hi) (congrFun hz i)
  · intro hx
    apply card_pos.mpr
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, HTGeometry.mem_configSupport.mpr hi⟩

/-- Allowing every support removes only the origin from the affine hyperplane. -/
theorem boundedSupportZeroSum_card_top (m : ℕ) :
    (boundedSupportZeroSum (F := F) (ι := Fin (m + 1)) (m + 1)).card =
      Fintype.card F ^ m - 1 := by
  have heq : boundedSupportZeroSum (F := F) (ι := Fin (m + 1)) (m + 1) =
      (affineZeroSum (F := F) (m + 1)).erase 0 := by
    ext x
    simp only [boundedSupportZeroSum, affineZeroSum, mem_filter, mem_univ, true_and,
      mem_erase, support_pos_iff]
    constructor
    · rintro ⟨hne, _, hs⟩
      exact ⟨hne, hs⟩
    · rintro ⟨hne, hs⟩
      refine ⟨hne, ?_, hs⟩
      have hc := card_le_card (subset_univ (HTGeometry.configSupport 0 x))
      simpa only [card_univ, Fintype.card_fin] using hc
  rw [heq, card_erase_of_mem (show (0 : Fin (m + 1) → F) ∈ affineZeroSum (m + 1) by
    simp [affineZeroSum]), affineZeroSum_card]

/-- The projective coordinate-sum hyperplane has the usual geometric-series count. -/
theorem projectiveSupportZeroSum_card_top (m : ℕ) :
    Fintype.card (ProjectiveSupportZeroSum (F := F) (ι := Fin (m + 1)) (m + 1)) =
      ∑ j ∈ range m, Fintype.card F ^ j := by
  have hq : Fintype.card F - 1 ≠ 0 := by
    have h := Fintype.one_lt_card (α := F)
    omega
  have hc := boundedSupportZeroSum_card_orbits (F := F) (ι := Fin (m + 1)) (m + 1)
  rw [boundedSupportZeroSum_card_top] at hc
  have hg : (∑ j ∈ range m, Fintype.card F ^ j) * (Fintype.card F - 1) + 1 =
      Fintype.card F ^ m := by
    have hqone : Fintype.card F - 1 + 1 = Fintype.card F := by omega
    simpa only [hqone] using geom_sum_mul_add (R := ℕ) (Fintype.card F - 1) m
  have hp : 0 < Fintype.card F ^ m := pow_pos Fintype.card_pos _
  apply mul_right_cancel₀ hq
  omega

/-- Adding one support size adds exactly its normalized torus stratum. -/
theorem projectiveSupportZeroSum_card_succ (r : ℕ) :
    Fintype.card (ProjectiveSupportZeroSum (F := F) (ι := ι) (r + 1)) =
      Fintype.card (ProjectiveSupportZeroSum (F := F) (ι := ι) r) +
        (Fintype.card ι).choose (r + 1) * (normalizedCoordinateZeroTorus (F := F) r).card := by
  have hs : Icc 1 (r + 1) = insert (r + 1) (Icc 1 r) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [projectiveSupportZeroSum_card, hs, sum_insert (by simp)]
  rw [← projectiveSupportZeroSum_card]
  exact add_comm _ _

/-- Removing the torus and the one-zero strata gives the closed projective boundary count. -/
theorem projectiveCoordinateBoundary_card_closed (m : ℕ) :
    Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (m + 2))) +
        (normalizedCoordinateZeroTorus (F := F) (m + 1)).card +
        (m + 2) * (normalizedCoordinateZeroTorus (F := F) m).card =
      ∑ j ∈ range (m + 1), Fintype.card F ^ j := by
  have h₁ := projectiveSupportZeroSum_card_succ (F := F) (ι := Fin (m + 2)) m
  have h₂ := projectiveSupportZeroSum_card_succ (F := F) (ι := Fin (m + 2)) (m + 1)
  have ht := projectiveSupportZeroSum_card_top (F := F) (m + 1)
  simp only [Fintype.card_fin, Nat.choose_self, Nat.choose_succ_self_right, one_mul] at h₁ h₂
  rw [h₂, h₁] at ht
  simpa only [ProjectiveCoordinateBoundary, Fintype.card_fin, Nat.add_sub_cancel,
    add_assoc, add_comm, add_left_comm] using ht

/-- The finite signed Tate trace of the coordinate boundary in `n` homogeneous coordinates. -/
def boundaryTateTrace (n : ℕ) (q : ℂ) (e : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 (n - 2), (n.choose k : ℂ) * hyperplaneTateTrace (k - 1) q e

omit [DecidableEq F] in
/-- The boundary trace counts actual projective scalar orbits over every finite extension. -/
theorem boundaryTateTrace_extension_count (E : Type*) [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] :
    boundaryTateTrace (Fintype.card ι) (Fintype.card F : ℂ) (Module.finrank F E) =
      (Fintype.card (ProjectiveCoordinateBoundary (F := E) (ι := ι)) : ℂ) := by
  rw [projectiveCoordinateBoundary_card]
  simp only [boundaryTateTrace, Nat.cast_sum, Nat.cast_mul,
    hyperplaneTateTrace_extension_count (F := F) _ E]

omit [DecidableEq F] [DecidableEq ι] in
/-- Every Tate eigenvalue in the coordinate boundary has exponent at most `n−4`. -/
theorem boundaryTateTrace_weight_bound {k j : ℕ} (hk : k ∈ Icc 1 (Fintype.card ι - 2))
    (hj : j ∈ (hyperplanePolynomial (k - 1)).support) :
    ‖(Fintype.card F : ℂ) ^ j‖ ≤ (Fintype.card F : ℝ) ^ (Fintype.card ι - 4) := by
  rw [norm_pow, Complex.norm_natCast]
  have hjk := hyperplanePolynomial_support_lt hj
  have hkn := (mem_Icc.mp hk).2
  exact pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := F)) (by omega)

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
