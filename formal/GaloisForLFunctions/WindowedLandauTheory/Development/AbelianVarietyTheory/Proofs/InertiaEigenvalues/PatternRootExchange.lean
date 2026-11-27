import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PatternCharacterGroups
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootExchangeTrace

/-! Moving a row of roots to a column of roots leaves the weighted trace
unchanged when the commutator pairs the two sets through a single character root. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem inPattern_of_ne_zero {Φ : Fin n → Fin n → Prop} {M : Mt g n}
    (hM : InPattern Φ M) {i j : Fin n} (h : M i j ≠ 0) : i = j ∨ Φ i j := by
  by_contra! hn
  exact h ((hM i j hn.2).trans (Matrix.one_apply_ne hn.1))

private theorem mul_single_mul_apply (A B : Mt g n) (u v : Fin n) (t : ZMod g) (i j : Fin n) :
    (A * Matrix.single u v t * B) i j = A i u * t * B v j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single v]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem pattern_conj_entrySum {Φ Ψ E : Fin n → Fin n → Prop}
    (hE : ∀ i, ¬ E i i) {u v p q : Fin n} (hpq : E p q)
    (h : ∀ i j, (i = u ∨ Φ i u) → (v = j ∨ Φ v j) → Ψ i j ∧ (E i j → i = p ∧ j = q))
    {A B : Mt g n} (hA : InPattern Φ A) (hB : InPattern Φ B) (t : ZMod g) :
    InPattern Ψ (1 + A * Matrix.single u v t * B) ∧
      patternEntrySum E (1 + A * Matrix.single u v t * B) = A p u * t * B v q := by
  let C := A * Matrix.single u v t * B
  have hc (i j : Fin n) : C i j = A i u * t * B v j :=
    mul_single_mul_apply A B u v t i j
  have hsupport (i j : Fin n) (hn : C i j ≠ 0) :
      Ψ i j ∧ (E i j → i = p ∧ j = q) := by
    rw [hc] at hn
    exact h i j (inPattern_of_ne_zero hA (left_ne_zero_of_mul (left_ne_zero_of_mul hn)))
      (inPattern_of_ne_zero hB (right_ne_zero_of_mul hn))
  constructor
  · intro i j hij
    change (1 + C) i j = (1 : Mt g n) i j
    rw [Matrix.add_apply, show C i j = 0 from of_not_not (fun hn => hij (hsupport i j hn).1),
      add_zero]
  · have hz (i j : Fin n) (hne : i ≠ p ∨ j ≠ q) :
        (if E i j then (1 + C) i j else 0) = 0 := by
      split_ifs with he
      · have hne' : i ≠ j := by
          rintro rfl
          exact hE i he
        rw [Matrix.add_apply, Matrix.one_apply_ne hne', zero_add]
        by_contra hval
        obtain ⟨hi, hj⟩ := (hsupport i j hval).2 he
        exact hne.elim (fun h' => h' hi) (fun h' => h' hj)
      · rfl
    have hpq' : p ≠ q := by
      rintro rfl
      exact hE p hpq
    change patternEntrySum E (1 + C) = _
    unfold patternEntrySum
    rw [Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero fun j _ => hz i j (Or.inl hi))
      (by simp), Finset.sum_eq_single q (fun j _ hj => hz p j (Or.inr hj)) (by simp),
      if_pos hpq, Matrix.add_apply, Matrix.one_apply_ne hpq', zero_add, hc]

private theorem exists_pattern_mismatch (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    {Φ Ψ E : Fin n → Fin n → Prop}
    (htrans : ∀ i j k, Ψ i j → Ψ j k → Ψ i k) (hirr : ∀ i, ¬ Ψ i i)
    (hE : ∀ i, ¬ E i i) (hpath : ∀ i j k, Ψ i j → Ψ j k → ¬ E i k)
    {u v p q : Fin n} (hpq : E p q) (huv : p ≠ u ∨ v ≠ q)
    (h : ∀ i j, (i = u ∨ Φ i u) → (v = j ∨ Φ v j) → Ψ i j ∧ (E i j → i = p ∧ j = q))
    (z : Gn g n) (hA : InPattern Φ (z⁻¹).val) (hB : InPattern Φ z.val)
    (hn : (z⁻¹).val p u * z.val v q ≠ 0) :
    let H := patternGroup (g := g) Ψ htrans
    let χH := patternCharacter Ψ E htrans hirr hE hpath ψ
    ∃ x y : H, y.val = z⁻¹ * x.val * z ∧ χH y ≠ χH x := by
  obtain ⟨c, hc⟩ := AddChar.ne_one_iff.mp hψ
  let t := ((z⁻¹).val p u * z.val v q)⁻¹ * c
  have ht : (z⁻¹).val p u * t * z.val v q = c := by
    dsimp only [t]
    rw [show ∀ a b d e : ZMod g, a * (d * e) * b = a * b * d * e from fun _ _ _ _ => by ring,
      mul_inv_cancel₀ hn, one_mul]
  have h1 : InPattern Φ (1 : Mt g n) := fun _ _ _ => rfl
  obtain ⟨hx, hxval⟩ := pattern_conj_entrySum hE hpq h h1 h1 t
  rw [one_mul, mul_one] at hx hxval
  have hxzero : patternEntrySum E (1 + Matrix.single u v t) = 0 := by
    rw [hxval]
    obtain hpu | hvq := huv
    · rw [Matrix.one_apply_ne hpu, zero_mul, zero_mul]
    · rw [Matrix.one_apply_ne hvq, mul_zero]
  obtain ⟨hy, hyval⟩ := pattern_conj_entrySum hE hpq h hA hB t
  let x : Gn g n := (isUnit_of_inPattern hirr htrans hx).unit
  have hval : x.val = 1 + Matrix.single u v t := IsUnit.unit_spec _
  have hconj : (z⁻¹ * x * z).val = 1 + (z⁻¹).val * Matrix.single u v t * z.val := by
    rw [Units.val_mul, Units.val_mul, hval, mul_add, add_mul, mul_one, Units.inv_mul]
  have hxH : InPattern Ψ x.val := by rwa [hval]
  have hyH : InPattern Ψ (z⁻¹ * x * z).val := by rwa [hconj]
  refine ⟨⟨x, hxH⟩, ⟨z⁻¹ * x * z, hyH⟩, rfl, fun he => hc ?_⟩
  have he' := congrArg (fun w : ℂˣ => (w : ℂ)) he
  change ψ (patternEntrySum E (z⁻¹ * x * z).val) = ψ (patternEntrySum E x.val) at he'
  rwa [hconj, hyval, ht, hval, hxzero, AddChar.map_zero_eq_one] at he'

private theorem card_patterns_eq_of_exchange {Φ Ψ : Fin n → Fin n → Prop}
    (W : Fin n → Prop) (p q : Fin n)
    (hΦ : ∀ i j, (Φ i j ∧ ¬ Ψ i j) ↔ i = p ∧ W j)
    (hΨ : ∀ i j, (Ψ i j ∧ ¬ Φ i j) ↔ W i ∧ j = q) :
    (Finset.univ.filter fun r : Fin n × Fin n => Φ r.1 r.2).card =
      (Finset.univ.filter fun r : Fin n × Fin n => Ψ r.1 r.2).card := by
  have hsplit (A B : Fin n → Fin n → Prop) :
      (Finset.univ.filter fun r : Fin n × Fin n => A r.1 r.2).card =
        (Finset.univ.filter fun r : Fin n × Fin n => A r.1 r.2 ∧ B r.1 r.2).card +
        (Finset.univ.filter fun r : Fin n × Fin n => A r.1 r.2 ∧ ¬ B r.1 r.2).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      fun r : Fin n × Fin n => A r.1 r.2) (fun r => B r.1 r.2), Finset.filter_filter,
      Finset.filter_filter]
  have hd :
      (Finset.univ.filter fun r : Fin n × Fin n => Φ r.1 r.2 ∧ ¬ Ψ r.1 r.2).card =
      (Finset.univ.filter fun r : Fin n × Fin n => Ψ r.1 r.2 ∧ ¬ Φ r.1 r.2).card := by
    refine Finset.card_bij' (fun r _ => (r.2, q)) (fun r _ => (p, r.1)) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦ] at hr
      simp [Finset.mem_filter, hΨ, hr.2]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΨ] at hr
      simp [Finset.mem_filter, hΦ, hr.1]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦ] at hr
      exact Prod.ext hr.1.symm rfl
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΨ] at hr
      exact Prod.ext rfl hr.2.symm
  rw [hsplit Φ Ψ, hsplit Ψ Φ, hd]
  congr 1
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- Exchange an allowed row with an allowed column through a selected root. -/
theorem tr_pattern_eq_of_rootExchange (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (Φ Ψ E : Fin n → Fin n → Prop) (W : Fin n → Prop) (p q : Fin n)
    (hE : ∀ i, ¬ E i i) (hpq : E p q) (hp : ¬ W p) (hq : ¬ W q)
    (hiΦ : ∀ i, ¬ Φ i i) (hiΨ : ∀ i, ¬ Ψ i i)
    (htΦ : ∀ i j k, Φ i j → Φ j k → Φ i k)
    (htΨ : ∀ i j k, Ψ i j → Ψ j k → Ψ i k)
    (ht : ∀ i j k, (Φ i j ∨ Ψ i j) → (Φ j k ∨ Ψ j k) → (Φ i k ∨ Ψ i k))
    (heΦ : ∀ i j k, Φ i j → Φ j k → ¬ E i k)
    (heΨ : ∀ i j k, Ψ i j → Ψ j k → ¬ E i k)
    (hdΦ : ∀ i j, (Φ i j ∧ ¬ Ψ i j) ↔ i = p ∧ W j)
    (hdΨ : ∀ i j, (Ψ i j ∧ ¬ Φ i j) ↔ W i ∧ j = q)
    (hcΦ : ∀ w, W w → ∀ i j, (i = p ∨ (Φ i p ∨ Ψ i p)) →
      (w = j ∨ (Φ w j ∨ Ψ w j)) → Φ i j ∧ (E i j → i = p ∧ j = q))
    (hcΨ : ∀ w, W w → ∀ i j, (i = w ∨ (Φ i w ∨ Ψ i w)) →
      (q = j ∨ (Φ q j ∨ Ψ q j)) → Ψ i j ∧ (E i j → i = p ∧ j = q))
    (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    tr (eDat g n (InPattern Φ) (patternEntrySum E) ψ) χ =
      tr (eDat g n (InPattern Ψ) (patternEntrySum E) ψ) χ := by
  let H := patternGroup (g := g) Φ htΦ
  let K := patternGroup (g := g) Ψ htΨ
  let L := patternGroup (g := g) (fun i j => Φ i j ∨ Ψ i j) ht
  let χH := patternCharacter Φ E htΦ hiΦ hE heΦ ψ
  let χK := patternCharacter Ψ E htΨ hiΨ hE heΨ ψ
  have hH : H ≤ L := fun u hu i j h => hu i j (fun h' => h (Or.inl h'))
  have hK : K ≤ L := fun u hu i j h => hu i j (fun h' => h (Or.inr h'))
  have hcard : Nat.card H = Nat.card K := by
    change Nat.card (patternGroup (g := g) Φ htΦ) = Nat.card (patternGroup (g := g) Ψ htΨ)
    rw [card_patternGroup Φ hiΦ, card_patternGroup Ψ hiΨ,
      card_patterns_eq_of_exchange W p q hdΦ hdΨ]
  have hagree (a : H) (b : K) (e : a.val = b.val) : χH a = χK b :=
    Units.ext (congrArg (fun x : Gn g n => ψ (patternEntrySum E x.val)) e)
  have hright (b : K) (hb : b.val ∉ H) : ∃ x y : H,
      y.val = b.val⁻¹ * x.val * b.val ∧ χH y ≠ χH x := by
    let z := b.val
    have hB : InPattern (fun i j => Φ i j ∨ Ψ i j) z.val := hK b.property
    have hA : InPattern (fun i j => Φ i j ∨ Ψ i j) (z⁻¹).val := L.inv_mem (hK b.property)
    obtain ⟨w, hw, hval⟩ : ∃ w, W w ∧ z.val w q ≠ 0 := by
      by_contra! hnone
      apply hb
      change InPattern Φ z.val
      intro i j hij
      by_cases h : Ψ i j
      · obtain ⟨hi, hj⟩ := (hdΨ i j).mp ⟨h, hij⟩
        subst j
        have hne : i ≠ q := by
          rintro rfl
          exact hq hi
        rw [hnone i hi, Matrix.one_apply_ne hne]
      · exact hB i j (fun he => he.elim hij h)
    have hpp : (z⁻¹).val p p = 1 := by
      rw [hA p p (fun h => h.elim (hiΦ p) (hiΨ p)), Matrix.one_apply_eq]
    exact exists_pattern_mismatch ψ hψ htΦ hiΦ hE heΦ hpq
      (Or.inr fun e => hq (e ▸ hw)) (hcΦ w hw) z hA hB (by simpa only [hpp, one_mul] using hval)
  have hleft (a : H) (ha : a.val ∉ K) : ∃ x y : K,
      y.val = a.val⁻¹ * x.val * a.val ∧ χK y ≠ χK x := by
    let z := a.val
    have hB : InPattern (fun i j => Φ i j ∨ Ψ i j) z.val := hH a.property
    have hA : InPattern (fun i j => Φ i j ∨ Ψ i j) (z⁻¹).val := L.inv_mem (hH a.property)
    obtain ⟨w, hw, hval⟩ : ∃ w, W w ∧ (z⁻¹).val p w ≠ 0 := by
      by_contra! hnone
      apply ha
      rw [← inv_mem_iff]
      change InPattern Ψ (z⁻¹).val
      intro i j hij
      by_cases h : Φ i j
      · obtain ⟨hi, hj⟩ := (hdΦ i j).mp ⟨h, hij⟩
        subst i
        have hne : p ≠ j := by
          rintro rfl
          exact hp hj
        rw [hnone j hj, Matrix.one_apply_ne hne]
      · exact hA i j (fun he => he.elim h hij)
    have hqq : z.val q q = 1 := by
      rw [hB q q (fun h => h.elim (hiΦ q) (hiΨ q)), Matrix.one_apply_eq]
    exact exists_pattern_mismatch ψ hψ htΨ hiΨ hE heΨ hpq
      (Or.inl fun e => hp (e.symm ▸ hw)) (hcΨ w hw) z hA hB
      (by simpa only [hqq, mul_one] using hval)
  rw [tr_eDat_of_subgroup _ _ ψ H (fun _ => Iff.rfl),
    tr_eDat_of_subgroup _ _ ψ K (fun _ => Iff.rfl)]
  have hHval (u : H) : (χH u : ℂ) = ψ (patternEntrySum E u.val.val) := rfl
  have hKval (u : K) : (χK u : ℂ) = ψ (patternEntrySum E u.val.val) := rfl
  simpa only [map_inv, Units.val_inv_eq_inv_val, hHval, hKval] using
    (weighted_trace_eq_of_exchange H K χH χK hcard hagree hright hleft hχ)

end GlobalTheory.GLq
