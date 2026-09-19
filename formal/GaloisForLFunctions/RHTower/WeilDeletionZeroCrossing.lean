import GaloisForLFunctions.RHTower.CCMApertureRemainderFamilyContinuity
import GaloisForLFunctions.RHTower.WeilInsertionCCMCrossing

/-!
# Certified zero crossings of the deleted and inserted restricted Weil operators

The prime-deleted and prime-inserted bounded remainders are aperture-compatible families: the
extra block at a larger aperture, restricted to a form vector supported in a smaller aperture,
either coincides with the block at the smaller aperture or pairs to zero because its translation
exceeds the support diameter.  Hence their ground energies are continuous in the aperture, and the
sign changes of `WeilDeletionCCMCrossing` and `WeilInsertionCCMCrossing` become genuine zero
crossings: for every prime `p ≥ e^{18}` there is an aperture `a ≤ log p + 1` at which the
`p`-deleted restricted Weil operator has a nonzero kernel element, and likewise for the operator
with a fictitious prime power inserted at any scale `x ≥ e^{18}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-! ## The literal remainder is aperture-compatible -/

theorem literal_diagonal_eq_of_val_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    (inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b v))
        (ccmArchimedeanFormToAperture b v)).re =
      (inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  have hsrc := ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hvu
  have hb := ccmRestrictedWeilForm_self_re_eq_source b v
  have ha := ccmRestrictedWeilForm_self_re_eq_source a u
  unfold ccmRestrictedWeilForm at hb ha
  rw [Complex.add_re, CCMRemainderFamily.re_inner_self] at hb ha
  have hnorm : ‖v‖ = ‖u‖ := by
    change ‖v.1‖ = ‖u.1‖
    rw [hvu]
  have hnorm2 : ‖v‖ ^ 2 = ‖u‖ ^ 2 := by rw [hnorm]
  linarith

/-- Visibility thresholds are monotone in the aperture. -/
theorem mem_Icc_floor_of_le {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) {p : ℕ}
    (hp : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1))) := by
  rw [Finset.mem_Icc] at hp ⊢
  refine ⟨hp.1, hp.2.trans ?_⟩
  apply Nat.floor_mono
  exact Real.exp_le_exp.mpr (by linarith)

theorem two_mul_lt_log_of_notMem {a : SuzukiPositiveAperture} {p : ℕ} (hp2 : 2 ≤ p)
    (h : p ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) : 2 * a.1 < Real.log p := by
  have hfloor : Nat.floor (Real.exp (2 * a.1)) < p := by
    by_contra hnot
    exact h (Finset.mem_Icc.mpr ⟨hp2, Nat.le_of_not_gt hnot⟩)
  have hexpN : Real.exp (2 * a.1) < (p : ℝ) := Nat.lt_of_floor_lt hfloor
  have hppos : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp2)
  have hstrict := Real.strictMonoOn_log (Set.mem_Ioi.mpr (Real.exp_pos (2 * a.1)))
    (Set.mem_Ioi.mpr hppos) hexpN
  rwa [Real.log_exp] at hstrict

/-! ## The deleted family -/

theorem re_inner_visiblePrimeBlock_eq (a : SuzukiPositiveAperture) (p : ℕ)
    (f : suzukiApertureHilbert a) (hvis : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    (inner ℂ (ccmVisiblePrimeBlock a p f) f).re =
      (ArithmeticFunction.vonMangoldt p : ℝ) * (1 / Real.sqrt p) *
        (inner ℂ (logTranslationCLM (Real.log p) f.1) f.1 +
          inner ℂ (logTranslationCLM (-Real.log p) f.1) f.1).re := by
  unfold ccmVisiblePrimeBlock
  rw [if_pos hvis, smul_apply, inner_smul_left, Complex.conj_ofReal, inner_ccmPrimeTransportOperator,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem deleted_diagonal_eq_of_val_eq (p : ℕ) {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    (inner ℂ (ccmVisiblePrimeBlock b p (ccmArchimedeanFormToAperture b v))
        (ccmArchimedeanFormToAperture b v)).re =
      (inner ℂ (ccmVisiblePrimeBlock a p (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  set fa := ccmArchimedeanFormToAperture a u with hfa
  set fb := ccmArchimedeanFormToAperture b v with hfb
  have hcoe : (fb : SoninL2) = (fa : SoninL2) := ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu
  by_cases hvb : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1)))
  · by_cases hva : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
    · rw [re_inner_visiblePrimeBlock_eq b p fb hvb, re_inner_visiblePrimeBlock_eq a p fa hva, hcoe]
    · rw [re_inner_visiblePrimeBlock_eq b p fb hvb, ccmVisiblePrimeBlock_of_invisible a hva]
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hvb).1
      have hlog := two_mul_lt_log_of_notMem hp2 hva
      have hzero := inner_symmetric_logTranslations_eq_zero_of_aperture a fa hlog
      rw [hcoe, hzero]
      simp
  · have hva : p ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := fun h =>
      hvb (mem_Icc_floor_of_le hab h)
    rw [ccmVisiblePrimeBlock_of_invisible b hvb, ccmVisiblePrimeBlock_of_invisible a hva]
    simp

/-- The prime-deleted remainders form an aperture-compatible family. -/
def deletedFamily (p : ℕ) : CCMRemainderFamily where
  B a := ccmDeletedRemainder a p
  selfAdjoint a := ccmDeletedRemainder_isSelfAdjoint a p
  compat := by
    intro a b hab u v hvu
    unfold ccmDeletedRemainder
    rw [add_apply, add_apply, inner_add_left, inner_add_left, Complex.add_re, Complex.add_re,
      literal_diagonal_eq_of_val_eq hab hvu, deleted_diagonal_eq_of_val_eq p hab hvu]

theorem deletedFamily_energy (p : ℕ) (a : SuzukiPositiveAperture) :
    (deletedFamily p).energy a = ccmDeletedGroundEnergy a p := rfl

/-- **Certified zero crossing of the prime-deleted restricted Weil operator.**  For every prime
`p ≥ e^{18}` there is an aperture `a ≤ log p + 1` at which the ground energy of the `p`-deleted
operator vanishes and the operator has a nonzero kernel element. -/
theorem exists_deleted_zero_crossing {p : ℕ} (hp : p.Prime) (hp18 : Real.exp 18 ≤ p) :
    ∃ a : SuzukiPositiveAperture, a.1 ≤ Real.log p + 1 ∧ ccmDeletedGroundEnergy a p = 0 ∧
      ∃ x : ((deletedFamily p).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧ (deletedFamily p).operator a x = 0 := by
  obtain ⟨⟨δ, hδ, hpos⟩, ⟨a₁, ha₁, hneg⟩⟩ := ccmDeletedGroundEnergy_sign_change hp hp18
  let a₀ : SuzukiPositiveAperture := ⟨min (δ / 2) a₁.1, lt_min (by linarith) a₁.2⟩
  have h01 : a₀.1 ≤ a₁.1 := min_le_right _ _
  have h0 : 0 < (deletedFamily p).energy a₀ := by
    rw [deletedFamily_energy]
    exact hpos a₀ (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h1 : (deletedFamily p).energy a₁ < 0 := by
    rw [deletedFamily_energy]
    exact hneg
  obtain ⟨a, -, ha₁', hzero⟩ := (deletedFamily p).exists_energy_eq_zero h01 h0 h1
  refine ⟨a, ha₁'.trans ha₁, by rw [← deletedFamily_energy]; exact hzero, ?_⟩
  exact (deletedFamily p).exists_kernel_of_energy_eq_zero hzero

/-! ## The inserted family -/

theorem re_inner_insertedBlock_eq (a : SuzukiPositiveAperture) (x w : ℝ)
    (f : suzukiApertureHilbert a) (hvis : x ≤ Real.exp (2 * a.1)) :
    (inner ℂ (ccmInsertedBlock a x w f) f).re =
      w * (1 / Real.sqrt x) *
        (inner ℂ (logTranslationCLM (Real.log x) f.1) f.1 +
          inner ℂ (logTranslationCLM (-Real.log x) f.1) f.1).re := by
  unfold ccmInsertedBlock
  rw [if_pos hvis, smul_apply, inner_smul_left, Complex.conj_ofReal, inner_ccmScaleTransportOperator,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem inserted_diagonal_eq_of_val_eq (x w : ℝ) {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    (inner ℂ (ccmInsertedBlock b x w (ccmArchimedeanFormToAperture b v))
        (ccmArchimedeanFormToAperture b v)).re =
      (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  set fa := ccmArchimedeanFormToAperture a u with hfa
  set fb := ccmArchimedeanFormToAperture b v with hfb
  have hcoe : (fb : SoninL2) = (fa : SoninL2) := ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu
  by_cases hvb : x ≤ Real.exp (2 * b.1)
  · by_cases hva : x ≤ Real.exp (2 * a.1)
    · rw [re_inner_insertedBlock_eq b x w fb hvb, re_inner_insertedBlock_eq a x w fa hva, hcoe]
    · rw [re_inner_insertedBlock_eq b x w fb hvb, ccmInsertedBlock_of_invisible a w hva]
      have hxa : Real.exp (2 * a.1) < x := lt_of_not_ge hva
      have hlog : 2 * a.1 < Real.log x := by
        rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hxa)]
        exact hxa
      have hzero := inner_symmetric_logTranslations_eq_zero_of_aperture a fa hlog
      rw [hcoe, hzero]
      simp
  · have hva : ¬ x ≤ Real.exp (2 * a.1) := fun h =>
      hvb (h.trans (Real.exp_le_exp.mpr (by linarith)))
    rw [ccmInsertedBlock_of_invisible b w hvb, ccmInsertedBlock_of_invisible a w hva]
    simp

/-- The prime-inserted remainders form an aperture-compatible family. -/
def insertedFamily (x w : ℝ) : CCMRemainderFamily where
  B a := ccmInsertedRemainder a x w
  selfAdjoint a := ccmInsertedRemainder_isSelfAdjoint a x w
  compat := by
    intro a b hab u v hvu
    unfold ccmInsertedRemainder
    rw [sub_apply, sub_apply, inner_sub_left, inner_sub_left, Complex.sub_re, Complex.sub_re,
      literal_diagonal_eq_of_val_eq hab hvu, inserted_diagonal_eq_of_val_eq x w hab hvu]

theorem insertedFamily_energy (x w : ℝ) (a : SuzukiPositiveAperture) :
    (insertedFamily x w).energy a = ccmInsertedGroundEnergy a x w := rfl

/-- **Certified zero crossing of the prime-inserted restricted Weil operator.**  For every real
scale `x ≥ e^{18}` and weight `w ≥ log x` there is an aperture `a ≤ log x + 1` at which the ground
energy of the operator with the fictitious prime power inserted vanishes and the operator has a
nonzero kernel element. -/
theorem exists_inserted_zero_crossing {x : ℝ} (hx18 : Real.exp 18 ≤ x) {w : ℝ}
    (hw : Real.log x ≤ w) :
    ∃ a : SuzukiPositiveAperture, a.1 ≤ Real.log x + 1 ∧ ccmInsertedGroundEnergy a x w = 0 ∧
      ∃ y : ((insertedFamily x w).operator a).domain,
        (y : suzukiApertureHilbert a) ≠ 0 ∧ (insertedFamily x w).operator a y = 0 := by
  obtain ⟨⟨δ, hδ, hpos⟩, ⟨a₁, ha₁, hneg⟩⟩ := ccmInsertedGroundEnergy_sign_change hx18 hw
  let a₀ : SuzukiPositiveAperture := ⟨min (δ / 2) a₁.1, lt_min (by linarith) a₁.2⟩
  have h01 : a₀.1 ≤ a₁.1 := min_le_right _ _
  have h0 : 0 < (insertedFamily x w).energy a₀ := by
    rw [insertedFamily_energy]
    exact hpos a₀ (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h1 : (insertedFamily x w).energy a₁ < 0 := by
    rw [insertedFamily_energy]
    exact hneg
  obtain ⟨a, -, ha₁', hzero⟩ := (insertedFamily x w).exists_energy_eq_zero h01 h0 h1
  refine ⟨a, ha₁'.trans ha₁, by rw [← insertedFamily_energy]; exact hzero, ?_⟩
  exact (insertedFamily x w).exists_kernel_of_energy_eq_zero hzero

end RHTower.WeilDeletion

end
