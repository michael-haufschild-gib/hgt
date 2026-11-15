import GaloisForLFunctions.HTGeometry.Lattices.SmallZeroSumEnergy

/-!
# Integral vectors of squared norm four

Zero-sum integer vectors of energy four are precisely sums of two roots with
disjoint endpoints. Prescribing one positive and one negative endpoint uniquely
determines the remaining root.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.IntegralZeroSum
variable {ι : Type*} [Fintype ι]

theorem sum_root (a b : ι) : ∑ i, root a b i = 0 := by
  classical
  simp [root, Pi.single_apply, Finset.sum_sub_distrib]

omit [Fintype ι] in
theorem root_eq_one_iff {a b i : ι} (hab : a ≠ b) : root a b i = 1 ↔ i = a := by
  classical
  by_cases hia : i = a
  · subst i; simp [root, hab]
  · by_cases hib : i = b
    · subst i; simp [root, hia]
    · simp [root, hia, hib]

omit [Fintype ι] in
theorem root_eq_neg_one_iff {a b i : ι} (hab : a ≠ b) : root a b i = -1 ↔ i = b := by
  classical
  by_cases hib : i = b
  · subst i; simp [root, Ne.symm hab]
  · by_cases hia : i = a
    · subst i; simp [root, hib]
    · simp [root, hia, hib]

omit [Fintype ι] in
theorem root_injective {a b c d : ι} (hab : a ≠ b) (hcd : c ≠ d)
    (h : root a b = root c d) : a = c ∧ b = d := by
  constructor
  · apply (root_eq_one_iff hcd).mp
    rw [← h]
    exact (root_eq_one_iff hab).mpr rfl
  · apply (root_eq_neg_one_iff hcd).mp
    rw [← h]
    exact (root_eq_neg_one_iff hab).mpr rfl

/-- Removing any chosen positive and negative coordinates from an energy-four
vector leaves one root, with disjoint endpoints. -/
theorem energy_four_decomposition_at {x : ι → ℤ} (hs : ∑ i, x i = 0)
    (he : energy x = 4) {a c : ι} (ha : x a = 1) (hc : x c = -1) :
    ∃ b d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      x = root a c + root b d := by
  classical
  have hac : a ≠ c := by intro h; subst c; omega
  have hy : ∑ i, (x - root a c) i = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hs, sum_root, sub_self]
  have hey : energy (x - root a c) = 2 := by
    rw [energy_sub, he, energy_root, if_neg hac, pairing_root_right, ha, hc]
    norm_num
  obtain ⟨b, d, hbd, hroot⟩ := exists_root_of_energy_two hy hey
  have hya : root b d a = 0 := by
    rw [← hroot]
    simp [root, ha, hac]
  have hyc : root b d c = 0 := by
    rw [← hroot]
    simp [root, hc, Ne.symm hac]
  have hab : a ≠ b := by
    intro h
    have := (root_eq_one_iff hbd).mpr h
    omega
  have had : a ≠ d := by
    intro h
    have := (root_eq_neg_one_iff hbd).mpr h
    omega
  have hcb : c ≠ b := by
    intro h
    have := (root_eq_one_iff hbd).mpr h
    omega
  have hcd : c ≠ d := by
    intro h
    have := (root_eq_neg_one_iff hbd).mpr h
    omega
  exact ⟨b, d, hab, hac, had, hcb.symm, hbd, hcd, sub_eq_iff_eq_add'.mp hroot⟩

/-- Every integral zero-sum vector of energy four has exactly two positive and
 two negative unit coordinates. -/
theorem energy_four_decomposition {x : ι → ℤ} (hs : ∑ i, x i = 0)
    (he : energy x = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      x = root a c + root b d := by
  have hpos : ∃ a, 0 < x a := by
    by_contra! h
    have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => h i)).mp hs
    have hx : x = 0 := funext fun i => hz i (Finset.mem_univ i)
    rw [(energy_eq_zero_iff x).mpr hx] at he
    omega
  have hneg : ∃ c, x c < 0 := by
    by_contra! h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).mp hs
    have hx : x = 0 := funext fun i => hz i (Finset.mem_univ i)
    rw [(energy_eq_zero_iff x).mpr hx] at he
    omega
  obtain ⟨a, ha⟩ := hpos
  obtain ⟨c, hc⟩ := hneg
  have ha1 : x a = 1 := by
    have := coordinate_abs_le_one_of_energy_le_four hs he.le a
    omega
  have hc1 : x c = -1 := by
    have := coordinate_abs_le_one_of_energy_le_four hs he.le c
    omega
  obtain ⟨b, d, h⟩ := energy_four_decomposition_at hs he ha1 hc1
  exact ⟨a, b, c, d, h⟩

/-- Four distinct endpoints give energy four. -/
theorem energy_two_disjoint_roots {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    energy (root a c + root b d) = 4 := by
  classical
  have h : root a c + root b d = root a c - root d b := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, root]
    ring
  rw [h, energy_sub, energy_root, energy_root, if_neg hac, if_neg hbd.symm,
    pairing_root_left]
  simp [root, hab, had, hbc, hcd, eq_comm]

omit [Fintype ι] in
/-- The positive coordinates of two disjoint roots are exactly their initial endpoints. -/
theorem two_roots_eq_one_iff {a b c d i : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (root a c + root b d) i = 1 ↔ i = a ∨ i = b := by
  classical
  by_cases hia : i = a
  · subst i; simp [root, hab, hac, had]
  by_cases hib : i = b
  · subst i; simp [root, hab, hbc, hbd]
  by_cases hic : i = c
  · subst i; simp [root, hac, hbc, hcd, eq_comm]
  by_cases hid : i = d
  · subst i; simp [root, had, hbd, hcd, eq_comm]
  simp [root, hia, hib, hic, hid]

omit [Fintype ι] in
/-- The negative coordinates of two disjoint roots are exactly their final endpoints. -/
theorem two_roots_eq_neg_one_iff {a b c d i : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (root a c + root b d) i = -1 ↔ i = c ∨ i = d := by
  classical
  by_cases hia : i = a
  · subst i; simp [root, hab, hac, had]
  by_cases hib : i = b
  · subst i; simp [root, hab, hbc, hbd]
  by_cases hic : i = c
  · subst i; simp [root, hac, hbc, hcd, eq_comm]
  by_cases hid : i = d
  · subst i; simp [root, had, hbd, hcd, eq_comm]
  simp [root, hia, hib, hic, hid]

/-- Exactly two coordinates of an energy-four zero-sum vector are positive units. -/
theorem card_positive_of_energy_four {x : ι → ℤ} (hs : ∑ i, x i = 0)
    (he : energy x = 4) : Fintype.card {i // x i = 1} = 2 := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    energy_four_decomposition hs he
  rw [Fintype.card_subtype]
  have hset : Finset.univ.filter (fun i => (root a c + root b d) i = 1) = {a, b} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      two_roots_eq_one_iff hab hac had hbc hbd hcd, Finset.mem_insert,
      Finset.mem_singleton]
  rw [hset]
  simp [hab]

/-- Exactly two coordinates of an energy-four zero-sum vector are negative units. -/
theorem card_negative_of_energy_four {x : ι → ℤ} (hs : ∑ i, x i = 0)
    (he : energy x = 4) : Fintype.card {i // x i = -1} = 2 := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    energy_four_decomposition hs he
  rw [Fintype.card_subtype]
  have hset : Finset.univ.filter (fun i => (root a c + root b d) i = -1) = {c, d} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      two_roots_eq_neg_one_iff hab hac had hbc hbd hcd, Finset.mem_insert,
      Finset.mem_singleton]
  rw [hset]
  simp [hcd]

#print axioms energy_four_decomposition_at
#print axioms energy_four_decomposition
#print axioms energy_two_disjoint_roots
end GaloisForLFunctions.HTGeometry.IntegralZeroSum
