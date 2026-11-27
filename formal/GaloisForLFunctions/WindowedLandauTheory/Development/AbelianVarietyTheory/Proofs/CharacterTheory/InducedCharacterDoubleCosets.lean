import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.DoubleCosetNormalizedSum
import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionInduction

/-! The pairing of two induced characters splits over double cosets,
with each contribution given by the character pairing on the overlap. -/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions

variable {G : Type*} [Group G] [Fintype G] (H K : Subgroup G)

omit [Fintype G] in
private theorem conj_mem (b : K) (z : G) :
    b.val⁻¹ * z * b.val ∈ K ↔ z ∈ K := by
  constructor
  · intro hz
    have he : b.val * (b.val⁻¹ * z * b.val) * b.val⁻¹ = z := by group
    exact he ▸ K.mul_mem (K.mul_mem b.property hz) (K.inv_mem b.property)
  · intro hz
    exact K.mul_mem (K.mul_mem (K.inv_mem b.property) hz) b.property

omit [Fintype G] in
private theorem conjugate_product (x : G) (a : H) (b : K) (u : H) :
    (a.val * x * b.val)⁻¹ * ((MulAut.conj a u : H) : G) * (a.val * x * b.val) =
      b.val⁻¹ * (x⁻¹ * u.val * x) * b.val := by
  change (a.val * x * b.val)⁻¹ * (a.val * u.val * a.val⁻¹) * (a.val * x * b.val) = _
  group

omit [Fintype G] in
private theorem card_overlap_mul (x : G) (a : H) (b : K) :
    Nat.card (doubleCosetOverlap H K (a.val * x * b.val)) = Nat.card (doubleCosetOverlap H K x) := by
  let e := (MulAut.conj a).toEquiv
  have h (u : H) : u ∈ doubleCosetOverlap H K x ↔
      e u ∈ doubleCosetOverlap H K (a.val * x * b.val) := by
    rw [mem_doubleCosetOverlap, mem_doubleCosetOverlap]
    change x⁻¹ * u.val * x ∈ K ↔
      (a.val * x * b.val)⁻¹ * ((MulAut.conj a u : H) : G) * (a.val * x * b.val) ∈ K
    rw [conjugate_product H K x a b u, conj_mem K b]
  exact Nat.card_congr (e.subtypeEquiv h).symm

private def overlapSum (α : H → ℂ) (β : K → ℂ) (x : G) : ℂ :=
  ∑ u : H, α u⁻¹ * extendByZero K β (x⁻¹ * u.val * x)

private theorem overlapSum_mul (α : H → ℂ) (β : K → ℂ)
    (hα : ∀ u a : H, α (a * u * a⁻¹) = α u)
    (hβ : ∀ u b : K, β (b * u * b⁻¹) = β u) (x : G) (a : H) (b : K) :
    overlapSum H K α β (a.val * x * b.val) = overlapSum H K α β x := by
  let y := a.val * x * b.val
  let F (u : H) := α u⁻¹ * extendByZero K β (y⁻¹ * u.val * y)
  calc
    _ = ∑ u : H, F (MulAut.conj a u) := (Equiv.sum_comp (MulAut.conj a).toEquiv F).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun u _ => ?_
      change α (MulAut.conj a u)⁻¹ * extendByZero K β (y⁻¹ * ((MulAut.conj a u : H) : G) * y) =
        α u⁻¹ * extendByZero K β (x⁻¹ * u.val * x)
      have he : (MulAut.conj a u)⁻¹ = a * u⁻¹ * a⁻¹ := by rw [MulAut.conj_apply]; group
      have hz : extendByZero K β (b.val⁻¹ * (x⁻¹ * u.val * x) * b.val) =
          extendByZero K β (x⁻¹ * u.val * x) := by
        simpa only [Subgroup.coe_inv, inv_inv] using
          extendByZero_conj K (fun k t => hβ t k) b⁻¹ (x⁻¹ * u.val * x)
      rw [he, hα, conjugate_product H K x a b u, hz]

/-- The normalized character contribution from the overlap of the two subgroups. -/
def doubleCosetPairing (α : H → ℂ) (β : K → ℂ) (x : G) : ℂ :=
  (Nat.card (doubleCosetOverlap H K x) : ℂ)⁻¹ * overlapSum H K α β x

/-- Conjugation maps the overlap of the left subgroup into the right subgroup. -/
def doubleCosetOverlapConj (x : G) : doubleCosetOverlap H K x →* K where
  toFun u := ⟨x⁻¹ * u.val.val * x, (mem_doubleCosetOverlap H K x u.val).mp u.property⟩
  map_one' := Subtype.ext (by
    change x⁻¹ * 1 * x = 1
    group)
  map_mul' u v := Subtype.ext (by
    change x⁻¹ * (u.val.val * v.val.val) * x = (x⁻¹ * u.val.val * x) * (x⁻¹ * v.val.val * x)
    group)

/-- The normalized contribution is the ordinary pairing of the two pulled-back functions. -/
theorem doubleCosetPairing_eq_pairing (α : H → ℂ) (β : K → ℂ) (x : G)
    [Fintype (doubleCosetOverlap H K x)] :
    doubleCosetPairing H K α β x =
      characterPairing (doubleCosetOverlap H K x) (fun u => α u.val)
        (fun u => β (doubleCosetOverlapConj H K x u)) := by
  let O := doubleCosetOverlap H K x
  let F (u : H) := α u⁻¹ * extendByZero K β (x⁻¹ * u.val * x)
  unfold doubleCosetPairing characterPairing
  apply congrArg (((Nat.card O : ℂ)⁻¹) * ·)
  change (∑ u : H, F u) = _
  calc
    _ = ∑ u ∈ Finset.univ.filter (fun u : H => u ∈ O), F u := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u ∈ O
      · rw [if_pos hu]
      · rw [if_neg hu]
        dsimp only [F]
        rw [extendByZero_of_notMem K β (mt (mem_doubleCosetOverlap H K x u).mpr hu), mul_zero]
    _ = ∑ u : O, F u.val :=
      Finset.sum_subtype _ (fun u => by simp [O]) F
    _ = _ := by
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [F]
      rw [extendByZero_of_mem K β ((mem_doubleCosetOverlap H K x u.val).mp u.property)]
      exact mul_comm _ _

/-- The overlap pairing is invariant under the choice of double-coset representative. -/
theorem doubleCosetPairing_eq_of_mk_eq (α : H → ℂ) (β : K → ℂ)
    (hα : ∀ u a : H, α (a * u * a⁻¹) = α u)
    (hβ : ∀ u b : K, β (b * u * b⁻¹) = β u)
    {x y : G} (h : DoubleCoset.mk H K x = DoubleCoset.mk H K y) :
    doubleCosetPairing H K α β x = doubleCosetPairing H K α β y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (DoubleCoset.eq H K x y).mp h
  simp only [doubleCosetPairing, card_overlap_mul H K x ⟨a, ha⟩ ⟨b, hb⟩,
    overlapSum_mul H K α β hα hβ x ⟨a, ha⟩ ⟨b, hb⟩]

/-- The restricted induction pairing is the sum of the normalized overlap pairings. -/
theorem characterPairing_restrict_induced_doubleCosets (α : H → ℂ) (β : K → ℂ)
    (hα : ∀ u a : H, α (a * u * a⁻¹) = α u)
    (hβ : ∀ u b : K, β (b * u * b⁻¹) = β u) :
    letI := mixedDoubleCosetFintype H K
    characterPairing H α (fun u => inducedFunction K β (u : G)) =
      ∑ q : DoubleCoset.Quotient (H : Set G) K, doubleCosetPairing H K α β q.out := by
  let Q := DoubleCoset.Quotient (H : Set G) K
  letI : Fintype Q := mixedDoubleCosetFintype H K
  let F (q : Q) := doubleCosetPairing H K α β q.out
  let h : ℂ := Nat.card H
  let k : ℂ := Nat.card K
  have hu (u : H) : inducedFunction K β (u : G) * α u⁻¹ =
      k⁻¹ * ∑ x : G, α u⁻¹ * extendByZero K β (x⁻¹ * u.val * x) := by
    rw [mul_comm (_ : ℂ) (α u⁻¹)]
    unfold inducedFunction
    rw [← Equiv.sum_comp (Equiv.inv G), mul_left_comm, Finset.mul_sum]
    simp only [Equiv.inv_apply, inv_inv, k]
  have hx (x : G) : overlapSum H K α β x =
      (Nat.card (doubleCosetOverlap H K x) : ℂ) * F (DoubleCoset.mk H K x) := by
    let c : ℂ := Nat.card (doubleCosetOverlap H K x)
    have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    calc
      _ = c * doubleCosetPairing H K α β x := by
        change overlapSum H K α β x = c * (c⁻¹ * overlapSum H K α β x)
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ = _ := congrArg (c * ·)
        (doubleCosetPairing_eq_of_mk_eq H K α β hα hβ (DoubleCoset.out_eq' H K (DoubleCoset.mk H K x)).symm)
  calc
    _ = h⁻¹ * (k⁻¹ * ∑ x : G, overlapSum H K α β x) := by
      change h⁻¹ * (∑ u : H, inducedFunction K β (u : G) * α u⁻¹) =
        h⁻¹ * (k⁻¹ * ∑ x : G, ∑ u : H, α u⁻¹ * extendByZero K β (x⁻¹ * u.val * x))
      simp_rw [hu]
      rw [← Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset H)) (t := (Finset.univ : Finset G))]
    _ = _ := by
      simp only [hx]
      exact sum_over_doubleCosets H K F

/-- Frobenius reciprocity and the double-coset decomposition compute the pairing
of two induced representation characters. -/
theorem characterPairing_induced_doubleCosets
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ K W) :
    letI := mixedDoubleCosetFintype H K
    characterPairing G (inducedFunction H ρ.character) (inducedFunction K σ.character) =
      ∑ q : DoubleCoset.Quotient (H : Set G) K, doubleCosetPairing H K ρ.character σ.character q.out := by
  have h := characterPairing_induced_restricted H.subtype ρ (Representation.ind K.subtype σ)
  have e : (Representation.ind K.subtype σ).character = inducedFunction K σ.character :=
    induced_character_eq_inducedFunction K σ
  have er : Representation.character ((Representation.ind K.subtype σ).comp H.subtype) =
      (fun u : H => inducedFunction K σ.character u.val) := funext fun u => congrFun e u.val
  rw [induced_character_eq_inducedFunction H ρ, e, er] at h
  exact h.trans (characterPairing_restrict_induced_doubleCosets H K ρ.character σ.character
    (fun u a => ρ.char_conj u a) (fun u a => σ.char_conj u a))

end GaloisForLFunctions
