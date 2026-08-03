import GaloisForLFunctions.HTGeometry.BarnesSourceSeries

/-!
# The atoms of the Barnes source and the ladder shift

Naming the rational atom of the source makes the ladder visible.  Shifting the argument by a period
moves the denominator of an atom to the denominator of the atom at the shifted exponent vector,
because the cone value of the shifted vector is the shifted cone value.  What is left over is the
difference of the two numerators divided by that common denominator.

The reindexing itself is a bijection: adding the unit vector in one direction identifies the whole
cone with the slice on which that exponent is positive.  The complementary slice, where the exponent
vanishes, is the cone of the frame with that period deleted, which is the lower step of the Barnes
hierarchy.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## The atom -/

/-- The rational atom of the Barnes source at one exponent vector. -/
def barnesAtom (ω : ι → ℂ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0
  else (-(z / conePeriod ω n)) ^ Fintype.card ι / (conePeriod ω n + z)

theorem logDeriv_barnesConeFactor_eq_barnesAtom (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    {z : ℂ} (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) (n : ι → ℕ) :
    logDeriv (barnesConeFactor ω n) z = barnesAtom ω n z := by
  by_cases h : n = 0
  · subst h
    have hconst : barnesConeFactor ω (0 : ι → ℕ) = fun _ : ℂ => 1 := by
      funext y
      rw [barnesConeFactor, if_pos rfl]
    rw [hconst, barnesAtom, if_pos rfl]
    simp [logDeriv]
  · rw [barnesAtom, if_neg h, logDeriv_barnesConeFactor ω hω h z (hpole n h)]

/-- **The Barnes source is the atom series.** -/
theorem logDeriv_barnesConeProduct_eq_tsum_barnesAtom (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    {z : ℂ} (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) :
    logDeriv (barnesConeProduct ω) z = ∑' n : ι → ℕ, barnesAtom ω n z := by
  rw [logDeriv_barnesConeProduct_eq_tsum ω hω hpole]
  exact tsum_congr fun n => logDeriv_barnesConeFactor_eq_barnesAtom ω hω hpole n

/-! ## The ladder shift of one atom -/

omit [Nonempty ι] in
theorem conePeriod_shift_denom [DecidableEq ι] (ω : ι → ℂ) (n : ι → ℕ) (j : ι) (z : ℂ) :
    conePeriod ω n + (z + ω j) = conePeriod ω (n + Pi.single j 1) + z := by
  rw [conePeriod_add_single]
  ring

omit [Fintype ι] [Nonempty ι] in
theorem add_single_ne_zero [DecidableEq ι] (n : ι → ℕ) (j : ι) : n + Pi.single j 1 ≠ 0 := by
  intro hcon
  have hj := congrFun hcon j
  rw [Pi.add_apply, Pi.single_eq_same] at hj
  simp at hj

omit [Nonempty ι] in
/-- **The ladder shift of one atom.**  Shifting the argument by a period moves the atom onto the
denominator of the shifted exponent vector, leaving the difference of the numerators. -/
theorem barnesAtom_shift_sub [DecidableEq ι] (ω : ι → ℂ) {n : ι → ℕ} (hn : n ≠ 0) (j : ι)
    (z : ℂ) :
    barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z =
      ((-((z + ω j) / conePeriod ω n)) ^ Fintype.card ι -
          (-(z / conePeriod ω (n + Pi.single j 1))) ^ Fintype.card ι) /
        (conePeriod ω (n + Pi.single j 1) + z) := by
  rw [barnesAtom, if_neg hn, barnesAtom, if_neg (add_single_ne_zero n j),
    conePeriod_shift_denom ω n j z, div_sub_div_same]

/-! ## The ladder reindexing as a bijection -/

/-- **Adding one unit in a direction is a bijection onto the slice where that exponent is
positive.** -/
def addSingleEquiv [DecidableEq ι] (j : ι) : (ι → ℕ) ≃ {n : ι → ℕ // 1 ≤ n j} where
  toFun n := ⟨n + Pi.single j 1, by rw [Pi.add_apply, Pi.single_eq_same]; omega⟩
  invFun m := m.1 - Pi.single j 1
  left_inv n := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  right_inv m := by
    refine Subtype.ext ?_
    funext i
    by_cases h : i = j
    · subst h
      have := m.2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp [Pi.single_eq_of_ne h]

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem addSingleEquiv_apply [DecidableEq ι] (j : ι) (n : ι → ℕ) :
    (addSingleEquiv j n : ι → ℕ) = n + Pi.single j 1 := rfl

omit [Nonempty ι] in
/-- The complementary slice is the deleted-frame cone. -/
theorem conePeriod_of_not_one_le [DecidableEq ι] (ω : ι → ℂ) {n : ι → ℕ} {j : ι}
    (hj : ¬ 1 ≤ n j) :
    conePeriod ω n = ∑ i ∈ Finset.univ.erase j, (n i : ℂ) * ω i :=
  conePeriod_eq_sum_erase_of_eq_zero ω (by omega)

end

end GaloisForLFunctions
