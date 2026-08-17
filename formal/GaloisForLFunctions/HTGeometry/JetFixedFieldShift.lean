import GaloisForLFunctions.HTGeometry.JetShiftTopCoefficient

/-!
# Normalizing shifts are exactly nonconstant fixed elements

The two conditions the orbifold-tail question is phrased in are the same condition.

A normalizing shift `t` at jet level `M` linearizes the substitution on the top coordinate, so
`y_M + t` is scaled by `R'`; dividing by `y₁`, which is scaled by `R'` as well, gives an element
*fixed* by the substitution, and its `M`-th partial is `1/y₁`, so it has order exactly `M`.
Conversely a fixed element of order exactly `M` is an eigen-relation of weight zero and eigenvalue
one, which the normalization dichotomy turns into a shift at level `M` because its order does not
drop.

Hence, for a map with no nonconstant fixed element of jet order at most one, the whole tail is
trivial exactly when no jet level of order at least two admits a normalizing shift.  That is the
single remaining obligation of the orbifold-tail classification for a given map.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **A normalizing shift at level `M ≥ 2` is a fixed element of order exactly `M`.** -/
theorem hasNormalizingShift_iff_exists_fixed (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {M : ℕ} (hM : 2 ≤ M) :
    HasNormalizingShift R hR (le_trans one_le_two hM) ↔
      ∃ g : JetField C Unit, (∀ j : ℕ, M < j → JetField.pd ((), j) g = 0) ∧
        JetField.pd ((), M) g ≠ 0 ∧ jetSubstitution R hR g = g := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  constructor
  · rintro ⟨t, ht⟩
    set v : JetField C Unit := (JetField.jet ((), M) : JetField C Unit)
      + algebraMap ↥(jetPrefixField C M) (JetField C Unit) t with hvdef
    have hv : jetSubstitution R hR v = substitutionDeriv R * v :=
      jetSubstitution_jet_add R hR (le_trans one_le_two hM) ht
    refine ⟨v / (JetField.jet ((), 1) : JetField C Unit), ?_, ?_, ?_⟩
    · intro j hj
      have hleib := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (v / (JetField.jet ((), 1) : JetField C Unit))
          (JetField.jet ((), 1) : JetField C Unit)
      simp only [smul_eq_mul] at hleib
      have hmul : v / (JetField.jet ((), 1) : JetField C Unit)
          * (JetField.jet ((), 1) : JetField C Unit) = v := div_mul_cancel₀ v hy1
      rw [hmul] at hleib
      have hjet : JetField.pd ((), j) (JetField.jet ((), 1) : JetField C Unit) = 0 :=
        JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
      have hvj : JetField.pd ((), j) v = 0 := by
        rw [hvdef, map_add]
        have h1 : JetField.pd ((), j) (JetField.jet ((), M) : JetField C Unit) = 0 :=
          JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
        have h2 : JetField.pd ((), j)
            (algebraMap ↥(jetPrefixField C M) (JetField C Unit) t) = 0 :=
          (mem_jetPrefixField_iff M _).mp t.2 j (by omega)
        rw [h1, h2, add_zero]
      rw [hvj, hjet, mul_zero, add_zero] at hleib
      exact (mul_eq_zero.mp hleib.symm).resolve_right hy1
    · have hleib := (JetField.pd ((), M) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (v / (JetField.jet ((), 1) : JetField C Unit))
          (JetField.jet ((), 1) : JetField C Unit)
      simp only [smul_eq_mul] at hleib
      have hmul : v / (JetField.jet ((), 1) : JetField C Unit)
          * (JetField.jet ((), 1) : JetField C Unit) = v := div_mul_cancel₀ v hy1
      rw [hmul] at hleib
      have hjet : JetField.pd ((), M) (JetField.jet ((), 1) : JetField C Unit) = 0 :=
        JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
      have hvM : JetField.pd ((), M) v = 1 := by
        rw [hvdef, map_add]
        have h1 : JetField.pd ((), M) (JetField.jet ((), M) : JetField C Unit) = 1 :=
          JetField.pd_jet_self _
        have h2 : JetField.pd ((), M)
            (algebraMap ↥(jetPrefixField C M) (JetField C Unit) t) = 0 :=
          (mem_jetPrefixField_iff M _).mp t.2 M (le_refl _)
        rw [h1, h2, add_zero]
      rw [hvM, hjet, mul_zero, add_zero] at hleib
      intro hzero
      rw [hzero, zero_mul] at hleib
      exact one_ne_zero hleib
    · have hone := jetSubstitution_jet_one R hR
      rw [map_div₀, hv, hone]
      have hρ : substitutionDeriv R ≠ 0 := hR
      field_simp
      ring
  · rintro ⟨g, hord, hpd, hfix⟩
    have hg0 : g ≠ 0 := by
      intro hh
      rw [hh, map_zero] at hpd
      exact hpd rfl
    have heigen : SubstitutionEigen R hR M 0 g 1 := by
      refine ⟨hg0, hord, ?_⟩
      rw [zpow_zero, mul_one, hfix, map_one, one_mul]
    rcases lowerOrder_or_hasNormalizingShift R hR (le_trans one_le_two hM) one_ne_zero heigen
      with hlow | hshift
    · exact absurd (hlow M (by omega)) hpd
    · exact hshift

/-- **The tail is trivial exactly when no jet level of order at least two admits a normalizing
shift**, for a map whose fixed elements of jet order at most one are already constant. -/
theorem forall_fixed_isConst_iff (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (h1 : ∀ g : JetField C Unit, (∀ j : ℕ, 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e) :
    (∀ g : JetField C Unit, jetSubstitution R hR g = g →
        ∃ e : C, g = algebraMap C (JetField C Unit) e)
      ↔ ∀ M : ℕ, ∀ hM : 2 ≤ M, ¬ HasNormalizingShift R hR (le_trans one_le_two hM) := by
  constructor
  · intro hfix M hM hshift
    obtain ⟨g, hord, hpd, hgfix⟩ := (hasNormalizingShift_iff_exists_fixed R hR hM).mp hshift
    obtain ⟨e, he⟩ := hfix g hgfix
    refine hpd ?_
    rw [he]
    exact Derivation.map_algebraMap _ e
  · intro hno g hgfix
    -- every fixed element has some finite order; descend on it
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j : ℕ, M < j → JetField.pd ((), j) g = 0 := by
      obtain ⟨s, hs⟩ := exists_finite_order g
      exact ⟨s, hs⟩
    induction M with
    | zero =>
        refine h1 g (fun j hj => hM j (by omega)) hgfix
    | succ M ih =>
        rcases Nat.lt_or_ge M 1 with hlt | hge
        · refine h1 g (fun j hj => hM j (by omega)) hgfix
        · by_cases hpd : JetField.pd ((), M + 1) g = 0
          · exact ih (fun j hj => by
              rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with heq | hgt
              · rw [← heq]; exact hpd
              · exact hM j (by omega))
          · exact absurd ((hasNormalizingShift_iff_exists_fixed R hR (by omega)).mpr
              ⟨g, hM, hpd, hgfix⟩) (hno (M + 1) (by omega))

end

end GaloisForLFunctions.HTGeometry
