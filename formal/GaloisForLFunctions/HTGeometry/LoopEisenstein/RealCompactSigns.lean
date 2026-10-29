import GaloisForLFunctions.HTGeometry.LoopEisenstein.SimpleCompactBorel
import GaloisForLFunctions.HTGeometry.LoopEisenstein.ExtendedCartanConjugation

/-!
# Central signs and the two enlarged rotation groups

Adjoining the central sign to either simple rotation group gives the same
four-element sign torus in its Borel intersection. These enlarged groups
generate the rotation subgroup used by real Iwasawa decomposition.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

open GaloisForLFunctions.RHTower

noncomputable section

/-- The two signs among the real field units. -/
def realSignUnits : Subgroup ℝˣ where
  carrier := {a | a = 1 ∨ a = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by
    rintro a (rfl | rfl) <;> simp

namespace LoopSL2

/-- Both central and finite-coroot coordinates are signs. -/
def signTorus : Subgroup (LoopSL2 ℝ) :=
  (realSignUnits.prod realSignUnits).map (cartanEmbedding ℝ)

theorem central_sign_mem_signTorus (c : realSignUnits) :
    centralEmbedding ℝ c ∈ signTorus := by
  refine ⟨((c : ℝˣ), 1), ⟨c.property, Or.inl rfl⟩, ?_⟩
  change centralEmbedding ℝ c * finiteCoroot ℝ 1 = centralEmbedding ℝ c
  rw [map_one, mul_one]

theorem finite_sign_mem_signTorus (a : realSignUnits) :
    finiteCoroot ℝ a ∈ signTorus := by
  refine ⟨(1, (a : ℝˣ)), ⟨Or.inl rfl, a.property⟩, ?_⟩
  change centralEmbedding ℝ 1 * finiteCoroot ℝ a = finiteCoroot ℝ a
  rw [map_one, one_mul]

theorem signTorus_le_positiveBorel : signTorus ≤ positiveBorel ℝ := by
  rintro g ⟨⟨c, a⟩, _, rfl⟩
  change centralEmbedding ℝ c * finiteCoroot ℝ a ∈ positiveBorel ℝ
  apply (positiveBorel ℝ).mul_mem (centralEmbedding_mem_positiveBorel ℝ c)
  rw [← finiteSL2Embedding_diagonal]
  exact finiteSL2Embedding_upperTriangular ℝ _ rfl

/-- The two actual simple embeddings restricted to real rotations. -/
def simpleRotationHom (i : Bool) : upperHalfPlaneStabilizer →* LoopSL2 ℝ :=
  if i then (affineSimpleSL2Embedding ℝ).comp upperHalfPlaneStabilizer.subtype
  else (finiteSL2Embedding ℝ).comp upperHalfPlaneStabilizer.subtype

@[simp] theorem simpleRotationHom_false (k : upperHalfPlaneStabilizer) :
    simpleRotationHom false k = finiteSL2Embedding ℝ k := rfl

@[simp] theorem simpleRotationHom_true (k : upperHalfPlaneStabilizer) :
    simpleRotationHom true k = affineSimpleSL2Embedding ℝ k := rfl

/-- Central signs commute with rotations, so their product is a homomorphism. -/
def signRotationHom (i : Bool) : realSignUnits × upperHalfPlaneStabilizer →* LoopSL2 ℝ where
  toFun p := centralEmbedding ℝ p.1 * simpleRotationHom i p.2
  map_one' := by
    change centralEmbedding ℝ 1 * simpleRotationHom i 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' p q := by
    change centralEmbedding ℝ ((p.1 : ℝˣ) * q.1) * simpleRotationHom i (p.2 * q.2) =
      (centralEmbedding ℝ p.1 * simpleRotationHom i p.2) *
        (centralEmbedding ℝ q.1 * simpleRotationHom i q.2)
    rw [map_mul, map_mul]
    calc
      _ = centralEmbedding ℝ p.1 *
          (centralEmbedding ℝ q.1 * simpleRotationHom i p.2) * simpleRotationHom i q.2 := by
        simp only [mul_assoc]
      _ = centralEmbedding ℝ p.1 *
          (simpleRotationHom i p.2 * centralEmbedding ℝ q.1) * simpleRotationHom i q.2 := by
        rw [centralEmbedding_mul_comm ℝ (q.1 : ℝˣ) (simpleRotationHom i p.2)]
      _ = _ := by simp only [mul_assoc]

/-- A simple rotation group enlarged by the central sign. -/
def enlargedSimpleCompact (i : Bool) : Subgroup (LoopSL2 ℝ) := (signRotationHom i).range

theorem central_sign_mem_enlargedSimpleCompact (i : Bool) (c : realSignUnits) :
    centralEmbedding ℝ c ∈ enlargedSimpleCompact i := by
  refine ⟨(c, 1), ?_⟩
  change centralEmbedding ℝ c * simpleRotationHom i 1 = centralEmbedding ℝ c
  rw [map_one, mul_one]

theorem rotation_mem_enlargedSimpleCompact (i : Bool) (k : upperHalfPlaneStabilizer) :
    simpleRotationHom i k ∈ enlargedSimpleCompact i := by
  refine ⟨(1, k), ?_⟩
  change centralEmbedding ℝ 1 * simpleRotationHom i k = simpleRotationHom i k
  rw [map_one, one_mul]

theorem finite_neg_one_mem_enlargedSimpleCompact (i : Bool) :
    finiteCoroot ℝ (-1) ∈ enlargedSimpleCompact i := by
  let k : upperHalfPlaneStabilizer := ⟨sl2Diagonal (-1), sl2Diagonal_neg_one_mem_rotation⟩
  cases i with
  | false =>
    have h := rotation_mem_enlargedSimpleCompact false k
    change finiteSL2Embedding ℝ (sl2Diagonal (-1)) ∈ enlargedSimpleCompact false at h
    rwa [finiteSL2Embedding_diagonal] at h
  | true =>
    refine ⟨(⟨-1, Or.inr rfl⟩, k), ?_⟩
    change centralEmbedding ℝ (-1) * affineSimpleSL2Embedding ℝ (sl2Diagonal (-1)) = _
    rw [affineSimpleSL2Embedding_diagonal, affineCoroot_eq_central_finite, ← mul_assoc, ← map_mul]
    simp

/-- Both enlarged simple groups contain the same central/finite sign torus. -/
theorem signTorus_le_enlargedSimpleCompact (i : Bool) : signTorus ≤ enlargedSimpleCompact i := by
  rintro g ⟨⟨c, a⟩, ⟨hc, ha⟩, rfl⟩
  change centralEmbedding ℝ c * finiteCoroot ℝ a ∈ enlargedSimpleCompact i
  apply (enlargedSimpleCompact i).mul_mem
    (central_sign_mem_enlargedSimpleCompact i ⟨c, hc⟩)
  rcases ha with rfl | rfl
  · rw [map_one]
    exact (enlargedSimpleCompact i).one_mem
  · exact finite_neg_one_mem_enlargedSimpleCompact i

/-- Triangular source rotations contribute only signs, including the affine central correction. -/
theorem signRotationHom_mem_signTorus_of_triangular (i : Bool)
    (c : realSignUnits) (k : upperHalfPlaneStabilizer) (hc : (k : SL2 ℝ) 1 0 = 0) :
    signRotationHom i (c, k) ∈ signTorus := by
  have hs := rotation_upperTriangular_eq_sign (k : SL2 ℝ) k.property hc
  change centralEmbedding ℝ c * simpleRotationHom i k ∈ signTorus
  apply signTorus.mul_mem (central_sign_mem_signTorus c)
  cases i with
  | false =>
    rw [simpleRotationHom_false]
    rcases hs with he | he
    · rw [he, map_one]
      exact signTorus.one_mem
    · rw [he, finiteSL2Embedding_diagonal]
      exact finite_sign_mem_signTorus ⟨-1, Or.inr rfl⟩
  | true =>
    rw [simpleRotationHom_true]
    rcases hs with he | he
    · rw [he, map_one]
      exact signTorus.one_mem
    · rw [he, affineSimpleSL2Embedding_diagonal, affineCoroot_eq_central_finite]
      apply signTorus.mul_mem (central_sign_mem_signTorus ⟨-1, Or.inr rfl⟩)
      simpa using finite_sign_mem_signTorus ⟨-1, Or.inr rfl⟩

theorem enlargedSimpleCompact_borel_le_signTorus (i : Bool) :
    enlargedSimpleCompact i ⊓ positiveBorel ℝ ≤ signTorus := by
  rintro g ⟨⟨⟨c, k⟩, rfl⟩, hb⟩
  apply signRotationHom_mem_signTorus_of_triangular i c k
  have hk : simpleRotationHom i k ∈ positiveBorel ℝ := by
    have h := (positiveBorel ℝ).mul_mem
      ((positiveBorel ℝ).inv_mem (centralEmbedding_mem_positiveBorel ℝ c)) hb
    change (centralEmbedding ℝ c)⁻¹ * (centralEmbedding ℝ c * simpleRotationHom i k)
      ∈ positiveBorel ℝ at h
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
  cases i with
  | false => exact (finiteSL2Embedding_mem_borel_iff ℝ k).1 hk
  | true => exact (affineSimpleSL2Embedding_mem_borel_iff ℝ k).1 hk

theorem enlargedSimpleCompact_inf_borel (i : Bool) :
    enlargedSimpleCompact i ⊓ positiveBorel ℝ = signTorus :=
  le_antisymm (enlargedSimpleCompact_borel_le_signTorus i)
    (le_inf (signTorus_le_enlargedSimpleCompact i) signTorus_le_positiveBorel)

theorem central_sign_mem_realCompact (c : realSignUnits) :
    centralEmbedding ℝ c ∈ realCompact := by
  rcases c.property with hc | hc
  · rw [hc, map_one]
    exact realCompact.one_mem
  · rw [hc]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

theorem enlargedSimpleCompact_le_realCompact (i : Bool) : enlargedSimpleCompact i ≤ realCompact := by
  rintro g ⟨⟨c, k⟩, rfl⟩
  apply realCompact.mul_mem (central_sign_mem_realCompact c)
  cases i with
  | false => exact finiteCompact_le_realCompact ⟨k, k.property, rfl⟩
  | true => exact affineCompact_le_realCompact ⟨k, k.property, rfl⟩

/-- The enlarged simple groups generate precisely the subgroup in real Iwasawa decomposition. -/
theorem enlargedSimpleCompact_sup : enlargedSimpleCompact false ⊔ enlargedSimpleCompact true =
    realCompact := by
  apply le_antisymm (sup_le (enlargedSimpleCompact_le_realCompact false)
    (enlargedSimpleCompact_le_realCompact true))
  apply sup_le
  · apply sup_le
    · rintro g ⟨k, hk, rfl⟩
      exact Subgroup.mem_sup_left (rotation_mem_enlargedSimpleCompact false ⟨k, hk⟩)
    · rintro g ⟨k, hk, rfl⟩
      exact Subgroup.mem_sup_right (rotation_mem_enlargedSimpleCompact true ⟨k, hk⟩)
  · apply Subgroup.closure_le.2
    intro g hg
    have he : g = centralEmbedding ℝ (-1) := Set.mem_singleton_iff.1 hg
    rw [he]
    exact Subgroup.mem_sup_left (central_sign_mem_enlargedSimpleCompact false ⟨-1, Or.inr rfl⟩)

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
