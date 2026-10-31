import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupGramLimit
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialCorrection

/-!
# Classification of continuous-dilation subgroup successors

The zero-axis polynomial correction removes integer period defects. Dilation
conjugation then reduces every nonzero proper rational subgroup to one containing
the integers, where the prime-power Gram limit forces infinite negative index.
The zero and full subgroups both admit positive carriers with constant dilations.
-/

open Filter Topology Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Subgroup indicators are integer-periodic when the subgroup contains one. -/
theorem hasSubgroupSuccessor_translation_periodic {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ} (hs : HasSubgroupSuccessor H k) (b : ℚ) :
    k (translation (b + 1)) = k (translation b) := by
  classical
  have hmem : b + 1 ∈ H ↔ b ∈ H := by
    constructor
    · intro hb
      simpa only [add_sub_cancel_right] using H.sub_mem hb h1
    · intro hb
      exact H.add_mem hb h1
  rw [hs (b + 1), hs b]
  by_cases hb : b ∈ H
  · rw [if_pos (hmem.mpr hb), if_pos hb]
  · rw [if_neg (fun h => hb (hmem.mp h)), if_neg hb]

/-- Polynomial correction removes the integer-invariance restriction from the subgroup obstruction. -/
theorem negIndex_eq_top_of_subgroup_containing_one_continuous_dilation
    {H : AddSubgroup ℚ} (h1 : (1 : ℚ) ∈ H) (hproper : H ≠ ⊤)
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) (hs : HasSubgroupSuccessor H k)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) : negIndex k = ⊤ := by
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    obtain ⟨q, _, _, _, hqt, hqd, hrem, hindex, hperiod, _⟩ :=
      exists_zero_axis_polynomial_correction hk hi (hasSubgroupSuccessor_translation_periodic h1 hs)
    have hsrem : HasSubgroupSuccessor H (fun g => k g - q g) := by
      intro b
      change k (translation b) - q (translation b) = _
      rw [hqt, sub_zero]
      exact hs b
    have hdrem (u : ℚˣ) (hu : 0 < (u : ℚ)) : k (dilation u) - q (dilation u) = f (u : ℚ) := by
      rw [hqd, sub_zero, hdil u hu]
    have htop := negIndex_eq_top_of_integer_invariant_subgroup_continuous_dilation
      h1 hproper hrem hsrem hperiod hf hdrem
    rw [htop] at hindex
    simp at hindex
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

private def conjugateByDilation (u : ℚˣ) : AffineGroupQ →* AffineGroupQ where
  toFun g := dilation u * g * (dilation u)⁻¹
  map_one' := by rw [mul_one, mul_inv_cancel]
  map_mul' g h := by simp only [mul_assoc, inv_mul_cancel_left]

private theorem conjugateByDilation_translation (u : ℚˣ) (b : ℚ) :
    conjugateByDilation u (translation b) = translation ((u : ℚ) * b) := by
  have harith : (u : ℚ) * b / (u : ℚ) = b := by field_simp [u.ne_zero]
  have he : translation ((u : ℚ) * b) * dilation u = dilation u * translation b := by
    rw [translation_mul_affine_eq, affSlope_dilation, harith]
  change (dilation u * translation b) * (dilation u)⁻¹ = _
  rw [← he, mul_assoc, mul_inv_cancel, mul_one]

private theorem conjugateByDilation_dilation (u a : ℚˣ) :
    conjugateByDilation u (dilation a) = dilation a := by
  change (dilation u * dilation a) * (dilation u)⁻¹ = dilation a
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_comm u a, mul_assoc, mul_inv_cancel, mul_one]

/-- Every nonzero proper subgroup successor has infinite index when dilations are continuous. -/
theorem negIndex_eq_top_of_nontrivial_subgroup_continuous_dilation
    {H : AddSubgroup ℚ} (hnonzero : H ≠ ⊥) (hproper : H ≠ ⊤)
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) (hs : HasSubgroupSuccessor H k)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) : negIndex k = ⊤ := by
  classical
  have hex : ∃ a : ℚ, a ∈ H ∧ a ≠ 0 := by
    by_contra h
    push Not at h
    apply hnonzero
    apply le_antisymm _ bot_le
    intro a ha
    exact AddSubgroup.mem_bot.mpr (h a ha)
  obtain ⟨a, haH, ha⟩ := hex
  let u := Units.mk0 a ha
  let S : ℚ →+ ℚ :=
    { toFun := fun b => a * b
      map_zero' := mul_zero a
      map_add' := mul_add a }
  let H' := H.comap S
  have h1 : (1 : ℚ) ∈ H' := by
    change a * 1 ∈ H
    rwa [mul_one]
  have hproper' : H' ≠ ⊤ := by
    intro he
    apply hproper
    apply top_unique
    intro q _
    have hmem : q / a ∈ H' := by rw [he]; exact AddSubgroup.mem_top _
    change a * (q / a) ∈ H at hmem
    have hmul : a * (q / a) = q := by field_simp [ha]
    rwa [hmul] at hmem
  let F := conjugateByDilation u
  have hs' : HasSubgroupSuccessor H' (k ∘ F) := by
    intro b
    change k (conjugateByDilation u (translation b)) = _
    rw [conjugateByDilation_translation]
    have hmem : b ∈ H' ↔ a * b ∈ H := Iff.rfl
    simpa only [u, Units.val_mk0, hmem] using hs (a * b)
  have hdil' (v : ℚˣ) (hv : 0 < (v : ℚ)) : (k ∘ F) (dilation v) = f (v : ℚ) := by
    change k (conjugateByDilation u (dilation v)) = _
    rw [conjugateByDilation_dilation, hdil v hv]
  have htop := negIndex_eq_top_of_subgroup_containing_one_continuous_dilation
    h1 hproper' (hk.comp F) hs' hf hdil'
  apply top_unique
  rw [← htop]
  exact negIndex_comp_le k F

/-- Exactly the zero and full rational subgroups admit finite-index continuous-dilation carriers. -/
theorem exists_finite_index_continuous_subgroup_successor_iff (H : AddSubgroup ℚ) :
    (∃ k : AffineGroupQ → ℂ, IsHermKernel k ∧ HasSubgroupSuccessor H k ∧ negIndex k < ⊤ ∧
      ∃ f : ℝ → ℂ, ContinuousAt f 1 ∧
        ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) ↔ H = ⊥ ∨ H = ⊤ := by
  constructor
  · rintro ⟨k, hk, hs, hi, f, hf, hdil⟩
    by_cases hzero : H = ⊥
    · exact Or.inl hzero
    · by_cases hfull : H = ⊤
      · exact Or.inr hfull
      · have he := negIndex_eq_top_of_nontrivial_subgroup_continuous_dilation hzero hfull hk hs hf hdil
        rw [he] at hi
        exact (lt_irrefl _ hi).elim
  · intro hH
    obtain ⟨k, hk, hs, hi, hdil⟩ := exists_positive_subgroup_successor_endpoints H hH
    refine ⟨k, hk.1, hs, ?_, fun _ => 1, continuousAt_const, fun u _ => hdil u⟩
    rw [hi]
    exact bot_lt_top

#print axioms negIndex_eq_top_of_nontrivial_subgroup_continuous_dilation
#print axioms exists_finite_index_continuous_subgroup_successor_iff
end GaloisForLFunctions.AdelicKreinGeometry
