import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.EllipticFrobeniusOrbits
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.EllipticSquarefreeCounts
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FibrePermutationSigns

/-!
# Actual elliptic point configurations and orientation cancellation

Frobenius-stable point subsets are unions of entire closed-place fibres.
Residue degrees give their cardinalities, so a factorial-degree extension
identifies n-point configurations with every squarefree divisor of degree n.
The actual Frobenius permutation has sign (-1)^(points + closed places).
Its signed configuration count inherits the proved curve square-root bound.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset IsDedekindDomain
open GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
variable (E : Type*) [Field E] [Algebra Constants E] [Fintype E]

/-- The actual geometric points over a closed place. -/
def ellipticPointFibre (v : EllipticPlace) : Finset (Points E) :=
  univ.filter fun p => ellipticPointPlace E p = v

/-- Full point support of a finite squarefree divisor. -/
def ellipticDivisorPoints (S : Finset EllipticPlace) : Finset (Points E) :=
  univ.filter fun p => ellipticPointPlace E p ∈ S

/-- Closed places occurring in an actual finite set of points. -/
def ellipticPointSupport (T : Finset (Points E)) : Finset EllipticPlace :=
  T.image (ellipticPointPlace E)

/-- Frobenius-stable subsets of the actual projective point set. -/
def EllipticPointStable (T : Finset (Points E)) : Prop :=
  ∀ p ∈ T, ellipticPointFrobeniusPower E 1 p ∈ T

/-- One-step arithmetic stability gives stability under every Frobenius power. -/
theorem ellipticPointStable_pow {T : Finset (Points E)} (hT : EllipticPointStable E T)
    (n : ℕ) {p : Points E} (hp : p ∈ T) : ellipticPointFrobeniusPower E n p ∈ T := by
  induction n with
  | zero => simpa only [ellipticPointFrobeniusPower_zero] using hp
  | succ n ih =>
    rw [show n + 1 = 1 + n by omega, ellipticPointFrobeniusPower_add]
    exact hT _ ih

/-- Arithmetic stability fills every closed-place fibre that is met. -/
theorem ellipticPointStable_saturated {T : Finset (Points E)} (hT : EllipticPointStable E T)
    {p q : Points E} (hp : p ∈ T) (hq : ellipticPointPlace E p = ellipticPointPlace E q) :
    q ∈ T := by
  obtain ⟨n, rfl⟩ := (ellipticPoint_same_place_iff_frobenius E p q).mp hq
  exact ellipticPointStable_pow E hT n hp

/-- A stable point set is exactly the full support of its closed-place divisor. -/
theorem ellipticDivisorPoints_pointSupport {T : Finset (Points E)}
    (hT : EllipticPointStable E T) :
    ellipticDivisorPoints E (ellipticPointSupport E T) = T := by
  ext q
  simp only [ellipticDivisorPoints, mem_filter, mem_univ, true_and,
    ellipticPointSupport, mem_image]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ellipticPointStable_saturated E hT hp he
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- Full supports of closed-place divisors are arithmetic stable. -/
theorem ellipticDivisorPoints_stable (S : Finset EllipticPlace) :
    EllipticPointStable E (ellipticDivisorPoints E S) := by
  intro p hp
  have he := (ellipticPoint_same_place_iff_frobenius E p
    (ellipticPointFrobeniusPower E 1 p)).mpr ⟨1, rfl⟩
  simpa only [ellipticDivisorPoints, mem_filter, mem_univ, true_and, ← he] using hp

private def optionMapSomeFibreEquiv {X Y : Type*} (f : X → Y) (y : Y) :
    {x : Option X // x.map f = some y} ≃ {x : X // f x = y} where
  toFun
    | ⟨none, h⟩ => by cases h
    | ⟨some x, h⟩ => ⟨x, Option.some.inj h⟩
  invFun x := ⟨some x.val, congrArg some x.property⟩
  left_inv x := by
    rcases x with ⟨x, h⟩
    cases x with
    | none => cases h
    | some x => rfl
  right_inv _ := rfl

/-- Every supported geometric fibre has exactly its residue degree in points. -/
theorem ellipticPointFibre_card (v : EllipticPlace)
    (hd : ellipticPlaceDegree v ∣ Module.finrank Constants E) :
    (ellipticPointFibre E v).card = ellipticPlaceDegree v := by
  rw [ellipticPointFibre, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let e : {p : Points E // ellipticPointPlace E p = v} ≃
      {x : Option (A →ₐ[Constants] E) // x.map (affinePointPlace E) = v} :=
    (pointsAlgHomEquiv E).subtypeEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr e]
  cases v with
  | none =>
    let e₀ : {x : Option (A →ₐ[Constants] E) // x.map (affinePointPlace E) = none} ≃
        {x : Option (A →ₐ[Constants] E) // x = none} :=
      Equiv.subtypeEquivRight (fun x => by cases x <;> simp)
    rw [Nat.card_congr e₀]
    simp only [ellipticPlaceDegree, Nat.card_unique]
  | some v =>
    rw [Nat.card_congr ((optionMapSomeFibreEquiv (affinePointPlace E) v).trans
      (affinePointFiberEquiv E v))]
    exact FiniteField.natCard_algHom_of_finrank_dvd
      (F := Constants) (K := A ⧸ v.asIdeal) (L := E) hd

/-- A place supports an actual point exactly when its residue degree divides the extension degree. -/
theorem ellipticPlace_supported_iff (v : EllipticPlace) :
    (∃ p : Points E, ellipticPointPlace E p = v) ↔
      ellipticPlaceDegree v ∣ Module.finrank Constants E := by
  cases v with
  | none =>
    constructor
    · intro _
      exact one_dvd _
    · intro _
      exact ⟨(pointsAlgHomEquiv E).symm none, by
        simp only [ellipticPointPlace, Equiv.apply_symm_apply, Option.map_none]⟩
  | some v =>
    change (∃ p : Points E, ellipticPointPlace E p = some v) ↔
      affinePlaceDegree v ∣ Module.finrank Constants E
    rw [← mem_affinePlacesOver_iff E v]
    simp only [affinePlacesOver, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨p, hp⟩
      have h : (pointsAlgHomEquiv E p).map (affinePointPlace E) = some v := hp
      cases he : pointsAlgHomEquiv E p with
      | none => simp only [he, Option.map_none, reduceCtorEq] at h
      | some f =>
        rw [he, Option.map_some] at h
        exact ⟨f, Option.some.inj h⟩
    · rintro ⟨f, hf⟩
      refine ⟨(pointsAlgHomEquiv E).symm (some f), ?_⟩
      simp only [ellipticPointPlace, Equiv.apply_symm_apply, Option.map_some, hf]

/-- Passing from a supported divisor to its points loses no closed place. -/
theorem ellipticPointSupport_divisorPoints (S : Finset EllipticPlace)
    (hS : ∀ v ∈ S, ellipticPlaceDegree v ∣ Module.finrank Constants E) :
    ellipticPointSupport E (ellipticDivisorPoints E S) = S := by
  ext v
  simp only [ellipticPointSupport, mem_image, ellipticDivisorPoints,
    mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hv
    obtain ⟨p, hp⟩ := (ellipticPlace_supported_iff E v).mpr (hS v hv)
    exact ⟨p, hp.symm ▸ hv, hp⟩

/-- Disjoint closed-place fibres add their residue degrees. -/
theorem ellipticDivisorPoints_card (S : Finset EllipticPlace)
    (hS : ∀ v ∈ S, ellipticPlaceDegree v ∣ Module.finrank Constants E) :
    (ellipticDivisorPoints E S).card = ∑ v ∈ S, ellipticPlaceDegree v := by
  have he : ellipticDivisorPoints E S = S.biUnion (ellipticPointFibre E) := by
    ext p
    simp only [ellipticDivisorPoints, mem_filter, mem_univ, true_and,
      mem_biUnion, ellipticPointFibre]
    constructor
    · intro hp
      exact ⟨ellipticPointPlace E p, hp, rfl⟩
    · rintro ⟨v, hv, hp⟩
      exact hp.symm ▸ hv
  rw [he, card_biUnion]
  · exact sum_congr rfl fun v hv => ellipticPointFibre_card E v (hS v hv)
  · intro v _ w _ hvw
    apply disjoint_left.mpr
    intro p hpv hpw
    simp only [ellipticPointFibre, mem_filter, mem_univ, true_and] at hpv hpw
    exact hvw (hpv.symm.trans hpw)

/-- The degree of the support divisor is exactly the number of stable geometric points. -/
theorem ellipticPointStable_card {T : Finset (Points E)} (hT : EllipticPointStable E T) :
    T.card = ∑ v ∈ ellipticPointSupport E T, ellipticPlaceDegree v := by
  calc
    T.card = (ellipticDivisorPoints E (ellipticPointSupport E T)).card := by
      rw [ellipticDivisorPoints_pointSupport E hT]
    _ = _ := ellipticDivisorPoints_card E _ (by
      intro v hv
      obtain ⟨p, _, hp⟩ := mem_image.mp hv
      exact (ellipticPlace_supported_iff E v).mp ⟨p, hp⟩)

omit [Fintype E] in
private theorem elliptic_divisor_supported (n : ℕ)
    (hd : n.factorial ∣ Module.finrank Constants E)
    (S : squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n) :
    ∀ v ∈ S.val, ellipticPlaceDegree v ∣ Module.finrank Constants E := by
  intro v hv
  have hs := (mem_ellipticDegreeSubsets_iff S.val n).mp S.property
  have hvn : ellipticPlaceDegree v ≤ n :=
    (single_le_sum (fun w _ => Nat.zero_le (ellipticPlaceDegree w)) hv).trans_eq hs
  cases v with
  | none => exact one_dvd _
  | some v => exact (Nat.dvd_factorial (affinePlaceDegree_pos v) hvn).trans hd

/-- Stable n-point subsets and actual squarefree divisors of degree n are the same finite objects. -/
def ellipticStableSubsetDivisorEquiv (n : ℕ)
    (hd : n.factorial ∣ Module.finrank Constants E) :
    {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n} ≃
      squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n where
  toFun T := ⟨ellipticPointSupport E T.val,
    (mem_ellipticDegreeSubsets_iff _ n).mpr
      ((ellipticPointStable_card E T.property.1).symm.trans T.property.2)⟩
  invFun S := ⟨ellipticDivisorPoints E S.val, ellipticDivisorPoints_stable E S.val,
    (ellipticDivisorPoints_card E S.val (elliptic_divisor_supported E n hd S)).trans
      ((mem_ellipticDegreeSubsets_iff S.val n).mp S.property)⟩
  left_inv T := Subtype.ext (ellipticDivisorPoints_pointSupport E T.property.1)
  right_inv S := Subtype.ext
    (ellipticPointSupport_divisorPoints E S.val (elliptic_divisor_supported E n hd S))

/-- Stable geometric point subsets in the actual common finite extension. -/
def arithmeticEllipticStableSubsets (n : ℕ) : Type :=
  let E := FiniteField.Extension Constants 3 (Fintype.card (Equiv.Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n}

/-- The canonical arithmetic extension discharges the entire splitting-degree condition. -/
def arithmeticEllipticSubsetDivisorEquiv (n : ℕ) :
    arithmeticEllipticStableSubsets n ≃
      squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n := by
  let E := FiniteField.Extension Constants 3 (Fintype.card (Equiv.Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  exact ellipticStableSubsetDivisorEquiv E n (by
    have he : Module.finrank Constants E = Fintype.card (Equiv.Perm (Fin n)) := by
      simpa only [Module.finrank_self, one_mul] using
        (FiniteField.finrank_zmod_extension Constants 3 (Fintype.card (Equiv.Perm (Fin n))))
    rw [he, Fintype.card_perm, Fintype.card_fin])

#print axioms ellipticDivisorPoints_card
#print axioms ellipticPointStable_card
#print axioms ellipticStableSubsetDivisorEquiv
#print axioms arithmeticEllipticSubsetDivisorEquiv
#print axioms ellipticPointFibre_card
#print axioms ellipticPlace_supported_iff
#print axioms ellipticPointSupport_divisorPoints
#print axioms ellipticPointStable_pow
#print axioms ellipticPointStable_saturated
#print axioms ellipticDivisorPoints_pointSupport
#print axioms ellipticDivisorPoints_stable
/-- Arithmetic Frobenius as a permutation of the actual projective point set. -/
def ellipticPointFrobenius : Equiv.Perm (Points E) :=
  (pointsAlgHomEquiv E).trans
    ((Equiv.optionCongr (ellipticAffineFrobenius E)).trans (pointsAlgHomEquiv E).symm)

/-- The permutation and the constructed arithmetic power have the same point map. -/
theorem ellipticPointFrobenius_apply (p : Points E) :
    ellipticPointFrobenius E p = ellipticPointFrobeniusPower E 1 p := by
  change (pointsAlgHomEquiv E).symm ((pointsAlgHomEquiv E p).map (ellipticAffineFrobenius E)) = _
  simp only [ellipticPointFrobeniusPower, pow_one]

/-- Permutation powers are the actual arithmetic Frobenius powers. -/
theorem ellipticPointFrobenius_pow (n : ℕ) (p : Points E) :
    (ellipticPointFrobenius E ^ n) p = ellipticPointFrobeniusPower E n p := by
  induction n with
  | zero => exact (ellipticPointFrobeniusPower_zero E p).symm
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ellipticPointFrobenius_apply, ih,
      ← ellipticPointFrobeniusPower_add, Nat.add_comm 1 n]

/-- The arithmetic permutation preserves every actual closed-place label. -/
theorem ellipticPointFrobenius_place (p : Points E) :
    ellipticPointPlace E (ellipticPointFrobenius E p) = ellipticPointPlace E p :=
  ((ellipticPoint_same_place_iff_frobenius E p _).mpr
    ⟨1, (ellipticPointFrobenius_apply E p).symm⟩).symm

/-- Forward-stable finite point sets are invariant under the actual Frobenius permutation. -/
theorem ellipticPointStable_mem_iff {T : Finset (Points E)} (hT : EllipticPointStable E T)
    (p : Points E) : ellipticPointFrobenius E p ∈ T ↔ p ∈ T := by
  constructor
  · intro hp
    exact ellipticPointStable_saturated E hT hp (ellipticPointFrobenius_place E p)
  · intro hp
    rw [ellipticPointFrobenius_apply]
    exact hT p hp

/-- The actual permutation on a finite stable geometric point set. -/
def ellipticStablePointPerm (T : Finset (Points E)) (hT : EllipticPointStable E T) :
    Equiv.Perm T :=
  (ellipticPointFrobenius E).subtypePerm (ellipticPointStable_mem_iff E hT)

/-- Closed-place labels of a stable point set retain their actual support. -/
def ellipticStablePlace (T : Finset (Points E)) (p : T) : ellipticPointSupport E T :=
  ⟨ellipticPointPlace E p, Finset.mem_image.mpr ⟨p, p.property, rfl⟩⟩

/-- Every closed place in the point support occurs as an actual point label. -/
theorem ellipticStablePlace_surjective (T : Finset (Points E)) :
    Function.Surjective (ellipticStablePlace E T) := by
  intro v
  obtain ⟨p, hp, hv⟩ := Finset.mem_image.mp v.property
  exact ⟨⟨p, hp⟩, Subtype.ext hv⟩

/-- Restricting to a stable set preserves its arithmetic closed-place partition. -/
theorem ellipticStablePlace_invariant (T : Finset (Points E)) (hT : EllipticPointStable E T)
    (p : T) :
    ellipticStablePlace E T (ellipticStablePointPerm E T hT p) = ellipticStablePlace E T p :=
  Subtype.ext (ellipticPointFrobenius_place E p)

/-- The restricted point permutation keeps the original arithmetic iterates. -/
theorem ellipticStablePointPerm_pow_val (T : Finset (Points E))
    (hT : EllipticPointStable E T) (n : ℕ) (p : T) :
    ((ellipticStablePointPerm E T hT ^ n) p).val = ellipticPointFrobeniusPower E n p := by
  induction n with
  | zero => exact (ellipticPointFrobeniusPower_zero E p).symm
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change ellipticPointFrobenius E (((ellipticStablePointPerm E T hT ^ n) p).val) = _
    rw [ellipticPointFrobenius_apply, ih, ← ellipticPointFrobeniusPower_add, Nat.add_comm 1 n]

/-- Every closed-place fibre inside a stable point set is one full arithmetic cycle. -/
theorem ellipticStablePlace_cycle (T : Finset (Points E)) (hT : EllipticPointStable E T)
    (v : ellipticPointSupport E T) :
    (labelledFibrePerm (ellipticStablePointPerm E T hT) (ellipticStablePlace E T)
      (ellipticStablePlace_invariant E T hT) v).IsCycleOn Set.univ := by
  let f := labelledFibrePerm (ellipticStablePointPerm E T hT) (ellipticStablePlace E T)
    (ellipticStablePlace_invariant E T hT) v
  refine ⟨⟨fun _ _ => Set.mem_univ _, f.injective.injOn,
    fun y _ => ⟨f.symm y, Set.mem_univ _, f.apply_symm_apply y⟩⟩, ?_⟩
  intro p _ q _
  have he : ellipticPointPlace E p.val.val = ellipticPointPlace E q.val.val :=
    congrArg Subtype.val (p.property.trans q.property.symm)
  obtain ⟨n, hn⟩ := (ellipticPoint_same_place_iff_frobenius E p.val.val q.val.val).mp he
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  apply Subtype.ext
  rw [labelledFibrePerm_pow_val]
  apply Subtype.ext
  rw [ellipticStablePointPerm_pow_val]
  exact hn

/-- Frobenius orientation is determined by the actual number of points and closed-place fibres. -/
theorem ellipticStablePointPerm_sign (T : Finset (Points E)) (hT : EllipticPointStable E T) :
    Equiv.Perm.sign (ellipticStablePointPerm E T hT) =
      (-1 : ℤˣ) ^ (T.card + (ellipticPointSupport E T).card) := by
  have h := sign_eq_pow_card_add_card (ellipticStablePointPerm E T hT) (ellipticStablePlace E T)
    (ellipticStablePlace_invariant E T hT) (ellipticStablePlace_surjective E T)
    (ellipticStablePlace_cycle E T hT)
  simp only [Fintype.card_coe] at h
  convert! h using 1
  congr 2
  exact Subsingleton.elim _ _

/-- Sum of actual Frobenius orientation indices on stable geometric n-point subsets. -/
def arithmeticEllipticStableOrientationSum (n : ℕ) : ℤ :=
  let E := FiniteField.Extension Constants 3 (Fintype.card (Equiv.Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  ∑ T : {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n},
    (Equiv.Perm.sign (ellipticStablePointPerm E T.val T.property.1) : ℤ)

/-- Actual geometric orientation indices recover the signed divisor count with its precise degree sign. -/
theorem arithmeticEllipticStableOrientationSum_eq (n : ℕ) :
    arithmeticEllipticStableOrientationSum n =
      (-1 : ℤ) ^ n * ((ellipticEvenDivisorCount n : ℤ) - ellipticOddDivisorCount n) := by
  let E := FiniteField.Extension Constants 3 (Fintype.card (Equiv.Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  change (∑ T : {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n},
    (Equiv.Perm.sign (ellipticStablePointPerm E T.val T.property.1) : ℤ)) = _
  have hs (T : {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n}) :
      (Equiv.Perm.sign (ellipticStablePointPerm E T.val T.property.1) : ℤ) =
        (-1 : ℤ) ^ n * (-1 : ℤ) ^ (ellipticPointSupport E T.val).card := by
    rw [ellipticStablePointPerm_sign, T.property.2]
    calc
      _ = (-1 : ℤ) ^ (n + (ellipticPointSupport E T.val).card) :=
        Units.val_pow_eq_pow_val (-1 : ℤˣ) _
      _ = _ := pow_add (-1 : ℤ) n _
  simp_rw [hs]
  rw [← mul_sum]
  congr 1
  calc
    _ = ∑ S : squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n,
        (-1 : ℤ) ^ S.val.card :=
      Fintype.sum_equiv
        (show {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n} ≃
          squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n from
            arithmeticEllipticSubsetDivisorEquiv n) _ _ (fun _ => rfl)
    _ = ∑ S ∈ squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n,
        (-1 : ℤ) ^ S.card :=
      Finset.sum_coe_sort
        (squarefreeDegreeSubsets (ellipticPlaceCutoff n) ellipticPlaceDegree n)
        (fun S : Finset EllipticPlace => (-1 : ℤ) ^ S.card)
    _ = _ := by
      simp only [neg_one_pow_eq_ite, sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_neg,
        ellipticEvenDivisorCount, ellipticOddDivisorCount,
        evenSquarefreeDivisorCount, oddSquarefreeDivisorCount, sub_eq_add_neg]

/-- The independently defined geometric orientation indices satisfy the actual curve's square-root bound. -/
theorem arithmeticEllipticStableOrientationSum_bound (n : ℕ) :
    |(arithmeticEllipticStableOrientationSum n : ℝ)| ≤
      8 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ n := by
  rw [arithmeticEllipticStableOrientationSum_eq]
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact elliptic_signed_divisor_count_bound n

#print axioms ellipticPointFrobenius_pow
#print axioms ellipticStablePlace_cycle
#print axioms ellipticStablePointPerm_sign
#print axioms arithmeticEllipticStableOrientationSum_eq
#print axioms arithmeticEllipticStableOrientationSum_bound

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
