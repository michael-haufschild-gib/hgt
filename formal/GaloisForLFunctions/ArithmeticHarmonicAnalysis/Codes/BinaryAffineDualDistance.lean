import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.BinaryCSSCodes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.TriplyEvenOrthogonality

/-!
# Weight four in affine-code homology

Orthogonality to constants forces even weight. A binary word of weight
two cannot be orthogonal to every coordinate function: its two support
points would have to coincide. Thus nonzero words in the dual affine
code have weight at least four.

Indicators of subgroups whose orders are divisible by four are
orthogonal to all affine words. A coordinate plane supplies a word of
weight four; in cubes of dimension at least four, the minimum weight of
the affine check code is at least eight, so this plane is not a boundary.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

variable {ν : Type} [Fintype ν] [DecidableEq ν]

/-- Every nonzero word orthogonal to all affine binary functions has weight at least four. -/
theorem binaryAffineDual_weight_ge_four (c : (ν → ZMod 2) → ZMod 2) (hc : c ≠ 0)
    (horth : ∀ d ∈ binaryAffineCode (ν → ZMod 2), twistedPair (RingHom.id _) c d = 0) :
    4 ≤ weight c := by
  classical
  have h1 : (fun _ : ν → ZMod 2 => (1 : ZMod 2)) ∈ binaryAffineCode (ν → ZMod 2) :=
    ⟨1, 0, fun _ => (add_zero _).symm⟩
  have hsum : (∑ x, c x) = 0 := by
    simpa only [twistedPair, RingHom.id_apply, mul_one] using horth _ h1
  rw [binary_sum_eq_weight] at hsum
  have heven := (CharP.cast_eq_zero_iff (ZMod 2) 2 (weight c)).mp hsum
  have hpos : 0 < weight c := by
    obtain ⟨x, hx⟩ : ∃ x, c x ≠ 0 := by
      by_contra! h
      exact hc (funext h)
    apply Finset.card_pos.mpr
    refine ⟨x, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  by_contra hbound
  have hw : weight c = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  let s := Finset.univ.filter (fun x => c x ≠ 0)
  have hs_card : s.card = 2 := by
    calc
      s.card = weight c := by
        unfold weight
        dsimp only [s]
        apply congrArg Finset.card
        ext x
        simp only [Finset.mem_filter]
      _ = 2 := hw
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hs_card
  have hca : c a = 1 := (binary_eq_zero_or_one (c a)).resolve_left
    (Finset.mem_filter.mp (show a ∈ s by rw [hs]; simp)).2
  have hcb : c b = 1 := (binary_eq_zero_or_one (c b)).resolve_left
    (Finset.mem_filter.mp (show b ∈ s by rw [hs]; simp)).2
  have hsummem (f : (ν → ZMod 2) → ZMod 2) :
      (∑ x, c x * f x) = ∑ x ∈ s, c x * f x := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hxs
    have hz : c x = 0 := by
      by_contra h
      exact hxs (Finset.mem_filter.mpr ⟨hx, h⟩)
    rw [hz, zero_mul]
  apply hab
  funext j
  let f : (ν → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => x j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hmem : (fun x : ν → ZMod 2 => x j) ∈ binaryAffineCode (ν → ZMod 2) :=
    ⟨0, f, fun _ => (zero_add _).symm⟩
  have hj := horth _ hmem
  change (∑ x, c x * x j) = 0 at hj
  rw [hsummem, hs, Finset.sum_pair hab, hca, hcb, one_mul, one_mul] at hj
  calc
    a j = (a j + b j) + b j := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = b j := by rw [hj, zero_add]

/-- Every nonzero homology class of an affine-cube complex requires at least four coordinates. -/
theorem binaryAffineHomologicalCode_nonboundary_weight_ge_four (n : ℕ)
    (c : (Fin (n + 3) → ZMod 2) → ZMod 2)
    (hc : c ∈ (binaryAffineHomologicalCode n).cycles)
    (hb : c ∉ (binaryAffineHomologicalCode n).boundaries) : 4 ≤ weight c := by
  apply binaryAffineDual_weight_ge_four c
  · intro hzero
    apply hb
    rw [hzero]
    exact Submodule.zero_mem _
  · exact (binaryCheckSyndrome_eq_zero_iff (binaryCubeAffineCode n) c).mp hc

#print axioms binaryAffineDual_weight_ge_four
#print axioms binaryAffineHomologicalCode_nonboundary_weight_ge_four

section Subgroup
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The binary word supported on an additive subgroup. -/
def binarySubgroupIndicator (H : AddSubgroup G) : G → ZMod 2 :=
  fun x => if x ∈ H then 1 else 0

/-- A subgroup indicator has exactly the subgroup's cardinality as its weight. -/
theorem weight_binarySubgroupIndicator (H : AddSubgroup G) :
    weight (binarySubgroupIndicator H) = Nat.card H := by
  letI : Fintype H := Fintype.ofFinite _
  simp [weight, binarySubgroupIndicator, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Four-divisible subgroup order makes its indicator orthogonal to every affine binary word. -/
theorem binarySubgroupIndicator_orthogonal (H : AddSubgroup G) (hH : 4 ∣ Nat.card H)
    (d : G → ZMod 2) (hd : d ∈ binaryAffineCode G) :
    twistedPair (RingHom.id _) (binarySubgroupIndicator H) d = 0 := by
  letI : Fintype H := Fintype.ofFinite _
  obtain ⟨b, f, hf⟩ := hd
  have hrestrict : (fun x : H => d x) ∈ binaryAffineCode H :=
    ⟨b, f.comp H.subtype, fun x => hf x⟩
  have hw : 2 ∣ weight (fun x : H => d x) :=
    binaryAffineCode_divisible_of_twice_dvd 2
      (by simpa only [Nat.card_eq_fintype_card] using hH) _ hrestrict
  have hz : (∑ x : H, d x) = 0 := by
    rw [binary_sum_eq_weight]
    exact (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr hw
  calc
    twistedPair (RingHom.id _) (binarySubgroupIndicator H) d =
        ∑ x ∈ Finset.univ.filter (fun x => x ∈ H), d x := by
      simp only [twistedPair, RingHom.id_apply, binarySubgroupIndicator, ite_mul,
        one_mul, zero_mul, Finset.sum_filter]
    _ = ∑ x : H, d x := Finset.sum_subtype _
      (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
    _ = 0 := hz

end Subgroup

private def planeFirst (n : ℕ) : Fin (n + 4) := ⟨0, by omega⟩
private def planeSecond (n : ℕ) : Fin (n + 4) := ⟨1, by omega⟩

private theorem planeFirst_ne_second (n : ℕ) : planeFirst n ≠ planeSecond n :=
  fun h => Nat.zero_ne_one (congrArg Fin.val h)

/-- Embed a binary plane by allowing its first two coordinates to vary. -/
def binaryCoordinatePlaneMap (n : ℕ) :
    (ZMod 2 × ZMod 2) →+ (Fin (n + 4) → ZMod 2) where
  toFun v i := if i = planeFirst n then v.1 else if i = planeSecond n then v.2 else 0
  map_zero' := by
    funext i
    simp only [Prod.fst_zero, Prod.snd_zero, ite_self, Pi.zero_apply]
  map_add' v w := by
    funext i
    by_cases h0 : i = planeFirst n <;> by_cases h1 : i = planeSecond n <;>
      simp [h0, h1, (planeFirst_ne_second n).symm]

/-- The two free coordinates recover the original plane point. -/
theorem binaryCoordinatePlaneMap_injective (n : ℕ) :
    Function.Injective (binaryCoordinatePlaneMap n) := by
  intro v w h
  apply Prod.ext
  · have h0 := congrFun h (planeFirst n)
    simpa [binaryCoordinatePlaneMap] using h0
  · have h1 := congrFun h (planeSecond n)
    simpa [binaryCoordinatePlaneMap, (planeFirst_ne_second n).symm] using h1

/-- The coordinate plane has exactly four points. -/
theorem binaryCoordinatePlane_card (n : ℕ) : Nat.card (binaryCoordinatePlaneMap n).range = 4 := by
  let e : (ZMod 2 × ZMod 2) ≃ (binaryCoordinatePlaneMap n).range :=
    Equiv.ofBijective (fun v => ⟨binaryCoordinatePlaneMap n v, ⟨v, rfl⟩⟩)
      ⟨fun v w h => binaryCoordinatePlaneMap_injective n (congrArg Subtype.val h),
        fun x => by obtain ⟨v, hv⟩ := x.property; exact ⟨v, Subtype.ext hv⟩⟩
  calc
    Nat.card (binaryCoordinatePlaneMap n).range = Nat.card (ZMod 2 × ZMod 2) :=
      Nat.card_congr e.symm
    _ = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

/-- A four-point plane represents a nonzero homology class in every cube of dimension at least four. -/
theorem binaryAffineHomologicalCode_exists_weight_four (n : ℕ) :
    ∃ c : (Fin (n + 4) → ZMod 2) → ZMod 2,
      c ∈ (binaryAffineHomologicalCode (n + 1)).cycles ∧
      c ∉ (binaryAffineHomologicalCode (n + 1)).boundaries ∧ weight c = 4 := by
  let H := (binaryCoordinatePlaneMap n).range
  let c := binarySubgroupIndicator H
  have hw : weight c = 4 := (weight_binarySubgroupIndicator H).trans (binaryCoordinatePlane_card n)
  have hc0 : c ≠ 0 := by
    intro hzero
    have h := hw
    rw [hzero] at h
    simp only [weight, Pi.zero_apply, ne_eq, not_true_eq_false, Finset.filter_false,
      Finset.card_empty] at h
    omega
  refine ⟨c, ?_, ?_, hw⟩
  · apply (binaryCheckSyndrome_eq_zero_iff (binaryCubeAffineCode (n + 1)) c).mpr
    exact binarySubgroupIndicator_orthogonal H (by rw [binaryCoordinatePlane_card])
  · intro hmem
    have hc : c ∈ binaryCubeAffineCode (n + 1) := by
      change c ∈ (selfOrthogonalHomologicalCode (binaryCubeAffineCode (n + 1))
        (binaryCubeAffineCode_selfOrthogonal (n + 1))).boundaries at hmem
      rwa [selfOrthogonalHomologicalCode_boundaries] at hmem
    have hd := (binaryCubeAffineCode_distance (n + 1)).1 c hc hc0
    have hdiv : 8 ∣ 2 ^ (n + 1 + 2) := by
      refine ⟨2 ^ n, ?_⟩
      rw [show n + 1 + 2 = n + 3 by omega, pow_add]
      ring
    have hlarge : 8 ≤ 2 ^ (n + 1 + 2) :=
      Nat.le_of_dvd (pow_pos (Nat.succ_pos 1) (n + 1 + 2)) hdiv
    rw [hw] at hd
    have hbad : 8 ≤ 4 := hlarge.trans hd
    omega

#print axioms binarySubgroupIndicator_orthogonal
#print axioms binaryAffineHomologicalCode_exists_weight_four
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
