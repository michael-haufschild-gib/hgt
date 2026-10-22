import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSmoothModularPeriodization

/-!
Actual modular periodization of compact chart tests has compact quotient support.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- Every projective modular orbit has height bounded by the starting height or its reciprocal. -/
theorem modular_orbit_height_le (γ : PSL2Z) (z : UpperHalfPlane) :
    (γ • z).im ≤ max z.im (1/z.im) := by
  induction γ using QuotientGroup.induction_on with
  | H A =>
    rw [PSL2Z_mk_smul,ModularGroup.im_smul_eq_div_normSq,denom_apply]
    by_cases hc : A 1 0 = 0
    · have hd : A 1 1 ≠ 0 := fun hd => zero_ne_one <| by
        simpa only [Matrix.det_fin_two,hc,hd,mul_zero,sub_zero] using A.det_coe
      have hs : (1 : ℝ) ≤ (A 1 1 : ℝ)^(2 : ℕ) := by
        exact_mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hd)
      apply le_trans _ (le_max_left _ _)
      rw [show Complex.normSq ((A 1 0)*z+(A 1 1)) = (A 1 1 : ℝ)^(2 : ℕ) by simp [hc,sq]]
      exact div_le_self z.im_pos.le hs
    · apply le_trans _ (le_max_right _ _)
      rw [show 1/z.im = z.im/z.im^(2 : ℕ) by field_simp]
      gcongr
      rw [show Complex.normSq ((A 1 0)*z+(A 1 1)) =
        ((A 1 0 : ℝ)*z.re+(A 1 1 : ℝ))^(2 : ℕ)+(A 1 0 : ℝ)^(2 : ℕ)*z.im^(2 : ℕ) by
          simp [Complex.normSq_apply]; ring]
      have hs : (1 : ℝ) ≤ (A 1 0 : ℝ)^(2 : ℕ) := by
        exact_mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hc)
      nlinarith [sq_nonneg ((A 1 0 : ℝ)*z.re+(A 1 1 : ℝ))]

/-- Truncating the original closed modular cell at any finite height gives a compact set. -/
theorem truncated_cell_compact (M : ℝ) : IsCompact {z : UpperHalfPlane | z ∈ fd ∧ z.im ≤ M} := by
  let K : Set ℂ := {z | z.re ∈ Icc (-1/2) (1/2) ∧ z.im ∈ Icc (1/2) M}
  have hK : IsCompact K := by
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hKr : K ⊆ Set.range UpperHalfPlane.coe := by
    intro z hz
    rw [UpperHalfPlane.range_coe]
    have hy : (1/2 : ℝ) ≤ z.im := hz.2.1
    change 0 < z.im
    linarith
  have hc : IsCompact (UpperHalfPlane.coe ⁻¹' K) :=
    UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage' hK hKr
  apply hc.of_isClosed_subset
  · exact isClosed_fd.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)
  · intro z hz
    have hb := three_le_four_mul_im_sq_of_mem_fd hz.1
    change z.re ∈ Icc (-1/2) (1/2) ∧ z.im ∈ Icc (1/2) M
    refine ⟨?_,⟨by nlinarith [z.im_pos],hz.2⟩⟩
    simpa only [neg_div,Set.mem_Icc] using abs_le.mp hz.1.2

/-- The modular translates of a compact set can meet the closed cell only inside
a single compact height truncation, including both joined sides and elliptic points. -/
theorem compact_orbit_cell_bound (K : Set UpperHalfPlane) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ z : UpperHalfPlane, (∃ γ : PSL2Z, γ • z ∈ K) → z.im ≤ M := by
  have hcont : Continuous (fun z : UpperHalfPlane => max z.im (1/z.im)) :=
    UpperHalfPlane.continuous_im.max (continuous_const.div UpperHalfPlane.continuous_im
      (fun z => z.im_ne_zero))
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨M,?_⟩
  rintro z ⟨γ,hγ⟩
  have he := modular_orbit_height_le γ⁻¹ (γ • z)
  simpa only [inv_smul_smul] using he.trans ((le_abs_self _).trans (hM _ hγ))

/-- General compact tests, including seam-crossing tests, have compact quotient
support after their actual full modular periodization. -/
theorem periodize_cellCompact (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ z ∈ fd, z ∉ K → periodize f z = 0 := by
  obtain ⟨M,hM⟩ := compact_orbit_cell_bound (tsupport f) hf
  refine ⟨{z : UpperHalfPlane | z ∈ fd ∧ z.im ≤ M},truncated_cell_compact M,?_⟩
  intro z hz hn
  have he (γ : PSL2Z) : f (γ • z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hn ⟨hz,hM z ⟨γ,hs⟩⟩
  simp [periodize,he]

end
end RHTower.D4BMModularCore
