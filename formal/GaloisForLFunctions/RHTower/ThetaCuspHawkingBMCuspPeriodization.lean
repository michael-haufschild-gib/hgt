import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalCuspCutoff

/-!
Exact modular periodization of high-cusp profiles, including the compact smooth translation partition and every nonparabolic term.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- A compact smooth partition window for the integer translation action. -/
def cuspWindow (x : ℝ) : ℝ := Real.smoothTransition (x+1)-Real.smoothTransition x

theorem cuspWindow_smooth : ContDiff ℝ ∞ cuspWindow :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem cuspWindow_zero_left {x : ℝ} (hx : x ≤ -1) : cuspWindow x = 0 := by
  rw [cuspWindow,Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]

theorem cuspWindow_zero_right {x : ℝ} (hx : 1 ≤ x) : cuspWindow x = 0 := by
  rw [cuspWindow,Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le hx,sub_self]

theorem cuspWindow_support : tsupport cuspWindow ⊆ Icc (-1) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (cuspWindow_zero_left (le_of_not_ge hn))
  · by_contra hn
    exact hx (cuspWindow_zero_right (le_of_not_ge hn))

/-- All integer translates of the actual smooth window sum to one on the
entire closed modular strip, including the joined sides. -/
theorem cuspWindow_partition (x : ℝ) (hx : |x| ≤ 1/2) :
    (∑' n : ℤ, cuspWindow (x+n)) = 1 := by
  classical
  have h := abs_le.mp hx
  rw [tsum_eq_sum (f := fun n : ℤ => cuspWindow (x+n)) (s := {-1,0,1})]
  · rw [Finset.sum_insert (by norm_num : (-1:ℤ) ∉ ({0,1}:Finset ℤ)),
      Finset.sum_insert (by norm_num : (0:ℤ) ∉ ({1}:Finset ℤ)),Finset.sum_singleton]
    simp only [Int.cast_neg,Int.cast_one,Int.cast_zero,add_zero]
    simp only [cuspWindow]
    rw [Real.smoothTransition.zero_of_nonpos (x := x + -1) (by linarith),
      Real.smoothTransition.one_of_one_le (x := x+1+1) (by linarith)]
    rw [show x + -1 + 1 = x by ring]
    ring
  · intro n hn
    have hn' : n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 := by simpa using hn
    have hc : n ≤ -2 ∨ 2 ≤ n := by omega
    rcases hc with hl | hr
    · apply cuspWindow_zero_left
      have hl' : (n:ℝ) ≤ -2 := by exact_mod_cast hl
      linarith
    · apply cuspWindow_zero_right
      have hr' : (2:ℝ) ≤ n := by exact_mod_cast hr
      linarith

private theorem projective_eq_of_smul_eq (a b : PSL2Z)
    (h : ∀ z : UpperHalfPlane, a • z = b • z) : a = b := by
  induction a using QuotientGroup.induction_on with
  | H A =>
    induction b using QuotientGroup.induction_on with
    | H B =>
      rw [QuotientGroup.eq,MonoidHom.mem_ker]
      apply Equiv.ext
      intro z
      change (A⁻¹ * B) • z = z
      rw [mul_smul,← show A • z = B • z from h z,inv_smul_smul]

/-- The actual projective modular translations are indexed without multiplicity by integers. -/
def cuspTranslation (n : ℤ) : PSL2Z := QuotientGroup.mk (T^n)

theorem cuspTranslation_injective : Function.Injective cuspTranslation := by
  intro n m he
  have hh := congrArg (fun γ : PSL2Z => (γ • UpperHalfPlane.I).re) he
  simp only [cuspTranslation,PSL2Z_mk_smul,ModularGroup.re_T_zpow_smul] at hh
  exact_mod_cast (add_left_cancel hh)

/-- Full projective modular periodization of a high-cusp field reduces exactly
to integer translates on the original closed cell; no nonparabolic term is discarded. -/
theorem periodize_high_cusp (f : UpperHalfPlane → ℂ)
    (hf : ∀ z : UpperHalfPlane, z.im ≤ 2 → f z = 0) (z : UpperHalfPlane) (hz : z ∈ fd) :
    periodize f z = ∑' n : ℤ, f (T^n • z) := by
  have hs : Function.support (fun γ : PSL2Z => f (γ • z)) ⊆ Set.range cuspTranslation := by
    intro γ hγ
    induction γ using QuotientGroup.induction_on with
    | H A =>
      by_cases hc : A 1 0 = 0
      · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
        exact ⟨n,projective_eq_of_smul_eq _ _ (fun w => (hn w).symm)⟩
      · have hy : 1/2 < z.im := by
          nlinarith [three_le_four_mul_im_sq_of_mem_fd hz,z.im_pos]
        have hb : (A • z).im ≤ 2 := (nonparabolic_height_le A hc z).trans
          ((div_le_iff₀ z.im_pos).mpr (by linarith))
        exact False.elim (hγ (hf _ hb))
  simpa only [periodize,cuspTranslation,PSL2Z_mk_smul] using
    (cuspTranslation_injective.tsum_eq hs).symm

/-- The full modular periodization realizes an exactly horizontal-constant cusp
profile on the closed cell, rather than a test with an artificial horizontal cutoff error. -/
theorem periodize_cuspWindow (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    periodize (fun w : UpperHalfPlane => (cuspWindow w.re : ℂ)*h w.im) z = h z.im := by
  rw [periodize_high_cusp _ (fun w hw => by rw [hh _ hw,mul_zero]) z hz]
  simp only [ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul]
  rw [tsum_mul_right,← Complex.ofReal_tsum,cuspWindow_partition z.re hz.2]
  simp

end
end RHTower.D4BMModularCore
