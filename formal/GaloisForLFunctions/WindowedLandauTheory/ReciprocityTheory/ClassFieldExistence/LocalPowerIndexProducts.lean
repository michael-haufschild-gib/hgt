import Mathlib.GroupTheory.Index

/-! The index of an n-th power subgroup in a finite product is the
product of the local indices, also for varying coordinate groups. -/

namespace GlobalTheory.Reciprocity

private theorem pow_range_pi {ι : Type*} {G : ι → Type*} [∀ i, CommGroup (G i)] (n : ℕ) :
    (powMonoidHom n : (∀ i, G i) →* (∀ i, G i)).range =
      ⨅ i, ((powMonoidHom n : G i →* G i).range).comap (Pi.evalMonoidHom G i) := by
  ext x
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Pi.evalMonoidHom_apply, MonoidHom.mem_range,
    powMonoidHom_apply]
  exact ⟨fun ⟨y, hy⟩ i => ⟨y i, congrFun hy i⟩, fun hx => ⟨fun i => (hx i).choose,
    funext fun i => (hx i).choose_spec⟩⟩

theorem index_power_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, CommGroup (G i)] (n : ℕ) :
    (powMonoidHom n : (∀ i, G i) →* (∀ i, G i)).range.index =
      ∏ i, (powMonoidHom n : G i →* G i).range.index := by
  rw [pow_range_pi]
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv
      (fun i => QuotientGroup.leftRel ((powMonoidHom n : G i →* G i).range))).symm)
  change _ ↔ ∀ i, QuotientGroup.leftRel ((powMonoidHom n : G i →* G i).range) (x i) (y i)
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_iInf, Subgroup.mem_comap,
    Pi.evalMonoidHom_apply, Pi.mul_apply, Pi.inv_apply]

theorem index_power_prod {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range.index =
      (powMonoidHom n : G →* G).range.index * (powMonoidHom n : H →* H).range.index := by
  rw [← Subgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [Subgroup.mem_prod, MonoidHom.mem_range, powMonoidHom_apply]
  exact ⟨fun ⟨x, hx⟩ => ⟨⟨x.1, congrArg Prod.fst hx⟩, ⟨x.2, congrArg Prod.snd hx⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ⟨(x, y), Prod.ext hx hy⟩⟩

theorem index_power_congr {A B : Type*} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (n : ℕ) :
    (powMonoidHom n : A →* A).range.index = (powMonoidHom n : B →* B).range.index := by
  have hmap : (powMonoidHom n : A →* A).range.map e.toMonoidHom =
      (powMonoidHom n : B →* B).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨e a, (map_pow e a n).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨e.symm b ^ n, ⟨e.symm b, rfl⟩, by simp⟩
  refine (Subgroup.index_map_equiv ((powMonoidHom n : A →* A).range) e).symm.trans ?_
  exact congrArg Subgroup.index hmap

end GlobalTheory.Reciprocity
