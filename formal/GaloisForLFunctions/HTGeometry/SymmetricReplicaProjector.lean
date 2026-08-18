import GaloisForLFunctions.HTGeometry.SymmetricReplicaRankLaw
import GaloisForLFunctions.HTGeometry.PureConjugationChannel
import GaloisForLFunctions.HTGeometry.PurityRankBarrier
import GaloisForLFunctions.HTGeometry.SymmetricProjectionPurityBarrier

/-!
# The symmetric replica projector and the moment of a finitely supported target law

An ordered replica coordinate `x : Fin r → α` carries an unordered content, and a pure replica
tensor is constant on each content class.  The matrix that averages over a content class is
therefore the orthogonal projection onto the symmetric replica power: it is self-adjoint,
idempotent, fixes every pure replica tensor, and its trace counts the content classes, which is the
stars-and-bars number `binom(d + r - 1, r)`.

The moment of a finitely supported law on unit targets is the corresponding convex combination of
replica projectors.  It is Hermitian, has trace one, is carried by the symmetric projector, and its
purity is at least the reciprocal of the number of supported targets, because every cross term in
the purity is a squared replica overlap and hence non-negative.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Content

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The ordered replica coordinates sharing a content. -/
def symClass (r : ℕ) (x : Fin r → α) : Finset (Fin r → α) :=
  Finset.univ.filter fun z => symTupleIndex r z = symTupleIndex r x

theorem mem_symClass_iff (r : ℕ) (x z : Fin r → α) :
    z ∈ symClass r x ↔ symTupleIndex r z = symTupleIndex r x := by
  simp [symClass]

theorem symClass_eq_of_index_eq (r : ℕ) {x y : Fin r → α}
    (h : symTupleIndex r x = symTupleIndex r y) : symClass r x = symClass r y := by
  ext z
  simp [symClass, h]

theorem self_mem_symClass (r : ℕ) (x : Fin r → α) : x ∈ symClass r x := by
  simp [symClass]

theorem symClass_card_pos (r : ℕ) (x : Fin r → α) : 0 < (symClass r x).card :=
  Finset.card_pos.mpr ⟨x, self_mem_symClass r x⟩

/-- A replica tensor coordinate depends only on the content of the ordered coordinate. -/
theorem finitePureTensorPower_congr (r : ℕ) (psi : α → ℂ) {x y : Fin r → α}
    (h : symTupleIndex r x = symTupleIndex r y) :
    finitePureTensorPower r psi x = finitePureTensorPower r psi y := by
  have hm : ((List.ofFn x : List α) : Multiset α) = ((List.ofFn y : List α) : Multiset α) :=
    congrArg Subtype.val h
  have hprod : (((List.ofFn x : List α) : Multiset α).map psi).prod
      = (((List.ofFn y : List α) : Multiset α).map psi).prod := by rw [hm]
  simpa [finitePureTensorPower, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
    List.prod_ofFn, Function.comp] using hprod

theorem symTupleIndex_surjective (r : ℕ) :
    Function.Surjective (symTupleIndex (α := α) r) := by
  intro s
  obtain ⟨l, hl⟩ : ∃ l : List α, (l : Multiset α) = s.val := ⟨s.val.toList, s.val.coe_toList⟩
  have hlen : l.length = r := by
    have hcard : Multiset.card s.val = r := s.2
    rw [← hl] at hcard
    simpa using hcard
  subst hlen
  refine ⟨l.get, Sym.coe_injective ?_⟩
  show ((List.ofFn l.get : List α) : Multiset α) = (s : Multiset α)
  rw [List.ofFn_get]
  exact hl

end Content

section Projector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **`(19)`.**  The orthogonal projection onto the symmetric replica power: averaging over a
content class. -/
def symReplicaProjection (r : ℕ) : Matrix (Fin r → α) (Fin r → α) ℂ :=
  Matrix.of fun x y =>
    if symTupleIndex r x = symTupleIndex r y then (((symClass r x).card : ℂ))⁻¹ else 0

theorem symReplicaProjection_apply (r : ℕ) (x y : Fin r → α) :
    symReplicaProjection r x y =
      if symTupleIndex r x = symTupleIndex r y then (((symClass r x).card : ℂ))⁻¹ else 0 := rfl

theorem symClass_card_ne_zero (r : ℕ) (x : Fin r → α) :
    (((symClass r x).card : ℂ)) ≠ 0 := by
  have h := symClass_card_pos r x
  simp only [ne_eq, Nat.cast_eq_zero]
  omega

theorem symReplicaProjection_conjTranspose (r : ℕ) :
    (symReplicaProjection (α := α) r)ᴴ = symReplicaProjection r := by
  funext x y
  rw [Matrix.conjTranspose_apply, symReplicaProjection_apply, symReplicaProjection_apply]
  by_cases h : symTupleIndex r x = symTupleIndex r y
  · rw [if_pos h, if_pos h.symm, symClass_eq_of_index_eq r h]
    simp
  · rw [if_neg h, if_neg fun hh => h hh.symm]
    simp

theorem symReplicaProjection_mul_self (r : ℕ) :
    symReplicaProjection (α := α) r * symReplicaProjection r = symReplicaProjection r := by
  funext x y
  rw [Matrix.mul_apply, symReplicaProjection_apply]
  by_cases h : symTupleIndex r x = symTupleIndex r y
  · rw [if_pos h]
    have hterm : ∀ z : Fin r → α,
        symReplicaProjection r x z * symReplicaProjection r z y =
          if symTupleIndex r z = symTupleIndex r x then (((symClass r x).card : ℂ))⁻¹ *
            (((symClass r x).card : ℂ))⁻¹ else 0 := by
      intro z
      rw [symReplicaProjection_apply, symReplicaProjection_apply]
      by_cases hz : symTupleIndex r z = symTupleIndex r x
      · rw [if_pos hz.symm, if_pos (hz.trans h), if_pos hz, symClass_eq_of_index_eq r hz]
      · rw [if_neg fun hh => hz hh.symm, if_neg hz, zero_mul]
    rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.sum_filter]
    show (∑ _z ∈ symClass r x, (((symClass r x).card : ℂ))⁻¹ *
      (((symClass r x).card : ℂ))⁻¹) = _
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (symClass_card_ne_zero r x),
      one_mul]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [symReplicaProjection_apply, symReplicaProjection_apply]
    by_cases hz : symTupleIndex r x = symTupleIndex r z
    · rw [if_neg fun hh => h (hz.trans hh), mul_zero]
    · rw [if_neg hz, zero_mul]

/-- **`(19)`.**  The trace of the symmetric projector counts the content classes, which is the
stars-and-bars dimension `binom(d + r - 1, r)`. -/
theorem symReplicaProjection_trace (r : ℕ) :
    (symReplicaProjection (α := α) r).trace
      = (((Fintype.card α + r - 1).choose r : ℕ) : ℂ) := by
  classical
  have hdiag : ∀ x : Fin r → α,
      symReplicaProjection (α := α) r x x = (((symClass r x).card : ℂ))⁻¹ := by
    intro x
    rw [symReplicaProjection_apply, if_pos rfl]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun x _ => hdiag x]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin r → α)) (symTupleIndex r)
    (fun x => (((symClass r x).card : ℂ))⁻¹)]
  have hfib : ∀ s : Sym α r,
      (∑ x ∈ Finset.univ with symTupleIndex r x = s, (((symClass r x).card : ℂ))⁻¹) = 1 := by
    intro s
    obtain ⟨x0, hx0⟩ := symTupleIndex_surjective (α := α) r s
    have hset : (Finset.univ.filter fun x : Fin r → α => symTupleIndex r x = s)
        = symClass r x0 := by
      ext z
      simp [symClass, hx0]
    rw [hset]
    have hval : ∀ z ∈ symClass r x0,
        (((symClass r z).card : ℂ))⁻¹ = (((symClass r x0).card : ℂ))⁻¹ := by
      intro z hz
      rw [symClass_eq_of_index_eq r ((mem_symClass_iff r x0 z).mp hz)]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ (symClass_card_ne_zero r x0)]
  rw [Finset.sum_congr rfl fun s _ => hfib s, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Sym.card_sym_eq_choose (α := α) r]

/-- The symmetric projector fixes every pure replica tensor. -/
theorem symReplicaProjection_mulVec_pure (r : ℕ) (psi : α → ℂ) :
    (symReplicaProjection (α := α) r).mulVec (finitePureTensorPower r psi)
      = finitePureTensorPower r psi := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  have hterm : ∀ z : Fin r → α,
      symReplicaProjection (α := α) r x z * finitePureTensorPower r psi z =
        if symTupleIndex r z = symTupleIndex r x then (((symClass r x).card : ℂ))⁻¹ *
          finitePureTensorPower r psi x else 0 := by
    intro z
    rw [symReplicaProjection_apply]
    by_cases hz : symTupleIndex r z = symTupleIndex r x
    · rw [if_pos hz.symm, if_pos hz, finitePureTensorPower_congr r psi hz]
    · rw [if_neg fun hh => hz hh.symm, if_neg hz, zero_mul]
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.sum_filter]
  show (∑ _z ∈ symClass r x, (((symClass r x).card : ℂ))⁻¹ *
    finitePureTensorPower r psi x) = _
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (symClass_card_ne_zero r x),
    one_mul]

end Projector

end

end GaloisForLFunctions.HTGeometry
