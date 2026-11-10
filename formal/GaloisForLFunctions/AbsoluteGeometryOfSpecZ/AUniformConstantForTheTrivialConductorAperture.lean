import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTrivialApertureAndTheExceptionalSquare

/-!
# A uniform constant in the trivial conductor aperture

The sharpened prime mass is asymptotic to `2 exp a`. Monotonicity controls
the remaining bounded range. Consequently every coefficient above two
admits one additive constant, independent of conductor and character.
In particular `4 exp a + C ≤ log q` forces the twisted zero form to be
nonnegative on every packet of aperture `a`.
-/

open Filter Topology MeasureTheory
noncomputable section
namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower.FreeLagTrace

/-- A single additive constant bounds the prime and archimedean costs for every conductor. -/
theorem exists_uniform_conductor_aperture_cost {κ : ℝ} (hκ : 2 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℝ),
      primeMass a + primeMass (a / 2) + archConstant χ ≤ κ * Real.exp a + C := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (tendsto_sharpened_primeMass_div_exp.eventually_le_const hκ)
  let B : ℝ := |Real.log (4 * Real.pi)| + |Real.log (128 * Real.pi)|
  let M : ℝ := primeMass A + primeMass (A / 2)
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨B + |M|, add_nonneg hB (abs_nonneg _), fun q χ a => ?_⟩
  have harch : archConstant χ ≤ B := by
    unfold archConstant
    split_ifs
    · exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    · exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  by_cases ha : A ≤ a
  · have hm := (div_le_iff₀ (Real.exp_pos a)).mp (hA a ha)
    linarith only [hm, harch, abs_nonneg M]
  · have ha' : a ≤ A := (lt_of_not_ge ha).le
    have h1 := monotone_primeMass_half (show 2 * a ≤ 2 * A by linarith only [ha'])
    rw [show 2 * a / 2 = a by ring, show 2 * A / 2 = A by ring] at h1
    have h2 := monotone_primeMass_half ha'
    have hm : primeMass a + primeMass (a / 2) ≤ M := add_le_add h1 h2
    have hκ0 : 0 ≤ κ * Real.exp a := mul_nonneg (by linarith only [hκ]) (Real.exp_pos a).le
    linarith only [hm, harch, le_abs_self M, hκ0]

/-- Uniform quantitative lower bound for the twisted form at any aperture. -/
theorem exists_uniform_twistedZeroSum_aperture_margin {κ : ℝ} (hκ : 2 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (hq : 1 < q)
      (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (a c : ℝ)
      (f : ℝ → ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ u, a < |u - c| → f u = 0) →
      (Real.log q - κ * Real.exp a - C) * (∫ u, f u ^ 2) ≤ twistedZeroSum hq hprim f := by
  obtain ⟨C, hC, hcost⟩ := exists_uniform_conductor_aperture_cost hκ
  refine ⟨C, hC, fun q _ hq χ hprim a c f hf hfc hsupp => ?_⟩
  apply le_trans _ (twistedZeroSum_ge_of_aperture_sharpened hq hprim hf hfc hsupp)
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun u => sq_nonneg (f u))
  linarith only [hcost q χ a]

/-- The coefficient-four trivial aperture uses an absolute constant, uniform in the conductor. -/
theorem exists_uniform_trivial_conductor_aperture :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (hq : 1 < q)
      (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (a c : ℝ),
      4 * Real.exp a + C ≤ Real.log q → ∀ f : ℝ → ℝ,
      ContDiff ℝ 2 f → HasCompactSupport f → (∀ u, a < |u - c| → f u = 0) →
      0 ≤ twistedZeroSum hq hprim f := by
  obtain ⟨C, hC, hmargin⟩ := exists_uniform_twistedZeroSum_aperture_margin (by norm_num : (2 : ℝ) < 4)
  refine ⟨C, hC, fun q _ hq χ hprim a c hcost f hf hfc hsupp => ?_⟩
  exact (mul_nonneg (by linarith only [hcost]) (integral_nonneg fun u => sq_nonneg (f u))).trans
    (hmargin q hq χ hprim a c f hf hfc hsupp)

#print axioms exists_uniform_twistedZeroSum_aperture_margin
#print axioms exists_uniform_trivial_conductor_aperture

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
