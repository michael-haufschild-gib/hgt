import GaloisForLFunctions.ArithmeticIndexDescent.TheIndexIsPaidByTransverseEnergy
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# The transverse energy strictly exceeds each positive index witness

An off-line zero has two different reflected neighbours. Its horizontal partner
contributes one angular unit; the zero `1 - rho` contributes a strictly positive
diagonal angle. Consequently a nonempty right packet costs more energy than its
cardinality, and every positive finite Weil negative index is strictly below the
total energy. Conjugation strengthens the global energy gap to the closed threshold
two. The extra diagonal angle has no asserted uniform positive lower bound.
-/

open Finset RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- The extra angle from a zero to its functional-equation reflection `1 - rho`. -/
def reflectionDiagonalAngle (j : XiDivisorSupport) : ℝ :=
  (2 * (j : ℂ).re - 1) ^ 2 /
    ((2 * (j : ℂ).re - 1) ^ 2 + (2 * (j : ℂ).im) ^ 2)

theorem reflectionDiagonalAngle_pos {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    0 < reflectionDiagonalAngle j := by
  have h : 2 * (j : ℂ).re - 1 ≠ 0 := fun he => hj (by linarith only [he])
  exact div_pos (sq_pos_of_ne_zero h)
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _))

theorem angularEnergyTerm_reflect {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    angularEnergyTerm j (xiZeroReflectEquiv j) = reflectionDiagonalAngle j := by
  have hne : xiZeroReflectEquiv j ≠ j := by
    intro h
    have hr := congrArg (fun k : XiDivisorSupport => (k : ℂ).re) h
    rw [xiZeroReflectEquiv_apply] at hr
    simp only [Complex.sub_re, Complex.one_re] at hr
    exact hj (by linarith only [hr])
  rw [angularEnergyTerm, if_neg hne, xiZeroReflectEquiv_apply]
  simp only [reflectionDiagonalAngle, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im]
  congr 1 <;> ring

/-- The horizontal quantum and the second reflected angle both belong to the full row. -/
theorem one_add_diagonalAngle_le_angularEnergy {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) : 1 + reflectionDiagonalAngle j ≤ angularEnergy j := by
  classical
  have hne : supportPartner j ≠ xiZeroReflectEquiv j := by
    intro h
    have hi := congrArg (fun k : XiDivisorSupport => (k : ℂ).im) h
    rw [supportPartner_coe, xiZeroReflectEquiv_apply] at hi
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg] at hi
    exact xiSupport_im_ne_zero j (by linarith only [hi])
  have hsum := (summable_angularEnergyTerm j).sum_le_tsum
    {supportPartner j, xiZeroReflectEquiv j} (fun k _ => angularEnergyTerm_nonneg j k)
  simpa only [Finset.sum_pair hne, angularEnergyTerm_supportPartner hj,
    angularEnergyTerm_reflect hj] using hsum

/-- An actual off-line Xi zero carries strictly more than its horizontal unit quantum. -/
theorem one_lt_angularEnergy {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    1 < angularEnergy j := by
  have h := one_add_diagonalAngle_le_angularEnergy hj
  linarith only [h, reflectionDiagonalAngle_pos hj]

theorem card_offPacket_lt_two_mul_divisorTransverseEnergy (s : Finset XiDivisorSupport)
    (hne : s.Nonempty) (hs : ∀ j ∈ s, (j : ℂ).re ≠ 1 / 2) :
    (s.card : ℝ≥0∞) < 2 * divisorTransverseEnergy := by
  rw [two_mul_divisorTransverseEnergy]
  calc
    (s.card : ℝ≥0∞) = ∑ _j ∈ s, (1 : ℝ≥0∞) := by simp
    _ < ∑ j ∈ s, ENNReal.ofReal (angularEnergy j) :=
      ENNReal.sum_lt_sum_of_nonempty hne fun j hj => by
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
            (one_lt_angularEnergy (hs j hj))
    _ ≤ _ := ENNReal.sum_le_tsum s

/-- Every nonempty right packet has a strictly positive energy surplus over its cardinality. -/
theorem card_rightPacket_lt_divisorTransverseEnergy (s : Finset XiDivisorSupport)
    (hne : s.Nonempty) (hs : ∀ j ∈ s, 1 / 2 < (j : ℂ).re) :
    (s.card : ℝ≥0∞) < divisorTransverseEnergy := by
  classical
  have hd : Disjoint s (s.image supportPartner) := by
    refine Finset.disjoint_left.mpr fun j hj hjp => ?_
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hjp
    have hright := hs (supportPartner k) hj
    rw [supportPartner_re] at hright
    linarith only [hright, hs k hk]
  have hcard : (s ∪ s.image supportPartner).card = 2 * s.card := by
    rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective s supportPartner.injective]
    omega
  have hquantum := card_offPacket_lt_two_mul_divisorTransverseEnergy
    (s ∪ s.image supportPartner) (by
      obtain ⟨j, hj⟩ := hne
      exact ⟨j, Finset.mem_union.mpr (Or.inl hj)⟩) (by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (hs j hj).ne'
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        rw [supportPartner_re]
        linarith only [hs k hk])
  rw [hcard, Nat.cast_mul, Nat.cast_ofNat, two_mul_divisorTransverseEnergy] at hquantum
  rw [divisorTransverseEnergy, ENNReal.lt_div_iff_mul_lt (Or.inl two_ne_zero)
    (Or.inl ENNReal.ofNat_ne_top)]
  simpa only [mul_comm] using hquantum

theorem card_rightZeros_lt_divisorTransverseEnergy (s : Finset ℂ) (hne : s.Nonempty)
    (hs : ∀ ρ ∈ s, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re) :
    (s.card : ℝ≥0∞) < divisorTransverseEnergy := by
  classical
  let j : s → XiDivisorSupport := fun ρ =>
    xiDivisorZetaCarrierEquiv.symm ⟨ρ, (hs ρ ρ.property).1⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : XiDivisorSupport => (z : ℂ)) hab)
  have hpacket : (s.attach.image j).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨j ⟨a, ha⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩⟩
  have hbound := card_rightPacket_lt_divisorTransverseEnergy (s.attach.image j) hpacket (by
    intro ρ hρ
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hρ
    exact (hs a a.property).2)
  simpa only [Finset.card_image_of_injective _ hj, Finset.card_attach] using hbound

/-- A finite Weil index is zero or is strictly less than the transverse energy it forces. -/
theorem negIndex_eq_zero_or_lt_divisorTransverseEnergy {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 0 ∨
      (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)
        < divisorTransverseEnergy := by
  classical
  let k := hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)
  by_cases hk0 : k = 0
  · exact Or.inl hk0
  right
  let R : Set ℂ := {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}
  have hk : (k : ℕ∞) ≤ R.encard := negIndex_weilGram_le_offLineCount f hf hfc
  have hpacket : ∃ s : Finset ℂ, (↑s : Set ℂ) ⊆ R ∧ s.card = k := by
    rcases R.finite_or_infinite with hR | hR
    · rw [hR.encard_eq_coe_toFinset_card] at hk
      obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (ENat.coe_le_coe.mp hk)
      exact ⟨s, fun ρ hρ => hR.mem_toFinset.mp (hs hρ), hcard⟩
    · exact hR.exists_subset_card_eq k
  obtain ⟨s, hs, hcard⟩ := hpacket
  have hne : s.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.pos_of_ne_zero hk0)
  have hbound := card_rightZeros_lt_divisorTransverseEnergy s hne (fun ρ hρ => hs hρ)
  simpa only [hcard] using hbound

theorem two_lt_divisorTransverseEnergy_of_right {j : XiDivisorSupport}
    (hj : 1 / 2 < (j : ℂ).re) : 2 < divisorTransverseEnergy := by
  classical
  have hne : j ≠ xiSupportConj j := by
    intro h
    have hi := congrArg (fun k : XiDivisorSupport => (k : ℂ).im) h
    rw [xiSupportConj_coe, Complex.conj_im] at hi
    exact xiSupport_im_ne_zero j (by linarith only [hi])
  have hbound := card_rightPacket_lt_divisorTransverseEnergy {j, xiSupportConj j}
    (by simp) (by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hj
      · have heq := Finset.mem_singleton.mp hk
        rw [heq, xiSupportConj_coe, Complex.conj_re]
        exact hj)
  simpa only [Finset.card_pair hne, Nat.cast_ofNat] using hbound

/-- The closed global energy threshold two excludes every off-line quartet. -/
theorem riemannHypothesis_iff_divisorTransverseEnergy_le_two :
    RiemannHypothesis ↔ divisorTransverseEnergy ≤ 2 := by
  constructor
  · intro h
    rw [divisorTransverseEnergy_eq_zero_iff.mpr h]
    exact zero_le
  · intro h
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun j => ?_
    by_contra hj
    rcases lt_or_gt_of_ne hj with hleft | hright
    · have hright : 1 / 2 < (supportPartner j : ℂ).re := by
        rw [supportPartner_re]
        linarith only [hleft]
      exact (not_lt_of_ge h) (two_lt_divisorTransverseEnergy_of_right hright)
    · exact (not_lt_of_ge h) (two_lt_divisorTransverseEnergy_of_right hright)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.negIndex_eq_zero_or_lt_divisorTransverseEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_iff_divisorTransverseEnergy_le_two
