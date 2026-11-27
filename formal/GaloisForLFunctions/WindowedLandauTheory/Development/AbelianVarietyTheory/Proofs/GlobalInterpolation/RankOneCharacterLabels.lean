import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenBridge

/-! A character on the prime-field units is labelled by the residue element
whose Teichmüller lift is its value at the first coupled generator. -/

noncomputable section

open WindowedLandauTheory.CyclotomicNorms GlobalTheory.GreenBridge

namespace GlobalTheory.GLq

variable {p : ℕ} [Fact p.Prime]

/-- The degree-one generator is the image of a primitive prime-field unit. -/
theorem exists_primeField_generator (L : LabelDatum p) :
    ∃ u : (ZMod p)ˣ, algebraMap (ZMod p) (Fbar p) (u : ZMod p) = L.gen 1 ∧
      orderOf u = p - 1 := by
  obtain ⟨u, hu, -⟩ := exists_unit_gen L (d := 1) one_pos
  let j := algebraMap (ZMod p) (KK p 1)
  have hj : Function.Surjective j :=
    (Function.Injective.bijective_of_nat_card_le j.injective
      (by rw [GaloisField.card p 1 one_ne_zero, Nat.card_zmod, pow_one])).2
  obtain ⟨c, hc⟩ := hj (u : KK p 1)
  have hc₀ : c ≠ 0 := fun h => u.ne_zero (by rw [← hc, h, map_zero])
  let a := Units.mk0 c hc₀
  have ha : algebraMap (ZMod p) (Fbar p) (a : ZMod p) = L.gen 1 := by
    change algebraMap (ZMod p) (Fbar p) c = _
    rw [← (emb p 1).commutes c, hc, hu]
  refine ⟨a, ha, ?_⟩
  rw [← orderOf_units (y := a), ← orderOf_injective
    (algebraMap (ZMod p) (Fbar p)).toMonoidHom (algebraMap (ZMod p) (Fbar p)).injective]
  change orderOf (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) = _
  rw [ha, L.gen_order 1 one_pos, pow_one]

/-- The prime-field label is unique. It is primitive for an injective character. -/
theorem existsUnique_rankOneCharacterLabel (L : LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) :
    ∃! c : (ZMod p)ˣ,
      (∀ u : (ZMod p)ˣ, algebraMap (ZMod p) (Fbar p) (u : ZMod p) = L.gen 1 →
        (χ u : ℂ) = L.teich (algebraMap (ZMod p) (Fbar p) (c : ZMod p))) ∧
      (Function.Injective χ → orderOf c = p - 1) := by
  obtain ⟨u, hu, ho⟩ := exists_primeField_generator L
  have hn : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  letI : NeZero (p - 1) := ⟨hn.ne'⟩
  let t : (ZMod p)ˣ →* ℂ := L.teich.comp
    ((algebraMap (ZMod p) (Fbar p)).toMonoidHom.comp (Units.coeHom _))
  have ht : Function.Injective t := by
    intro a b h
    exact Units.ext ((algebraMap (ZMod p) (Fbar p)).injective
      (L.teich_inj _ _ (by simp) (by simp) h))
  have hprim : IsPrimitiveRoot (t u) (p - 1) := by
    rw [← ho, ← orderOf_injective t ht u]
    exact IsPrimitiveRoot.orderOf _
  have hχ : (χ u : ℂ) ^ (p - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ho, pow_orderOf_eq_one, map_one, Units.val_one]
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one hχ
  have htχ : t (u ^ m) = (χ u : ℂ) := by rw [map_pow, hm]
  refine ⟨u ^ m, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    have he : a = u := Units.ext ((algebraMap (ZMod p) (Fbar p)).injective (ha.trans hu.symm))
    subst a
    exact htχ.symm
  · intro hχinj
    rw [← orderOf_injective t ht (u ^ m), htχ, orderOf_units, orderOf_injective χ hχinj, ho]
  · intro c hc
    exact ht ((hc.1 u hu).symm.trans htχ.symm)

end GlobalTheory.GLq
