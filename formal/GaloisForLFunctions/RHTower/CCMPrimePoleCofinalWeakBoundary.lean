import GaloisForLFunctions.RHTower.CCMPrimePoleProjectionCoherence

/-!
# Cofinal weak boundary of the CCM prime-pole family

At a fixed positive local scale, the normalized CCM pole vectors are unit
vectors whose individual coordinates vanish as the positive pole index tends
to infinity.  Density of the canonical ell-square basis upgrades coordinate
decay to weak convergence against every continuous linear functional.

This supplies the weakly-null cofinal carrier required for compact-operator and
essential-boundary consequences.
-/

open Filter Topology

noncomputable section

namespace RHTower

theorem tendsto_norm_ccmPrimePoleCoefficient_nat_succ_zero
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => ‖ccmPrimePoleCoefficient L ((n + 1 : ℕ) : ℤ)‖)
      atTop (𝓝 0) := by
  let C : ℝ := 2 * Real.sqrt 2 * Real.sqrt L
  have hC : 0 ≤ C := by positivity
  have hdenpos : 0 < 4 * Real.pi := by positivity
  have hbound : ∀ n : ℕ,
      ‖ccmPrimePoleCoefficient L ((n + 1 : ℕ) : ℤ)‖ ≤
        C / (4 * Real.pi * (n + 1 : ℕ)) := by
    intro n
    let D : ℂ :=
      ((4 * Real.pi * (((n + 1 : ℕ) : ℤ) : ℝ) : ℝ) : ℂ) +
        3 * Complex.I * L
    have hDlower : 4 * Real.pi * (n + 1 : ℕ) ≤ ‖D‖ := by
      have hre := Complex.abs_re_le_norm D
      norm_num [D, abs_of_pos (mul_pos hdenpos (by positivity))] at hre ⊢
      have hnnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
      simpa [abs_of_pos Real.pi_pos, abs_of_nonneg hnnonneg] using hre
    rw [ccmPrimePoleCoefficient, norm_div]
    have hnum : ‖((2 * Real.sqrt 2 * Real.sqrt L : ℝ) : ℂ)‖ = C := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [hnum]
    exact div_le_div_of_nonneg_left hC (mul_pos hdenpos (by positivity)) hDlower
  have hdenT : Tendsto (fun n : ℕ => 4 * Real.pi * ((n + 1 : ℕ) : ℝ))
      atTop atTop := by
    apply (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop
    exact hdenpos
  have hupper : Tendsto (fun n : ℕ => C / (4 * Real.pi * (n + 1 : ℕ)))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_const_nhds.div_atTop hdenT
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hupper

theorem tendsto_ccmNormalizedPrimePoleSequence_coordinate_nat_succ_zero
    {L : ℝ} (hL : 0 < L) (k : ℕ) :
    Tendsto (fun n : ℕ =>
      ccmNormalizedPrimePoleSequence L ((n + 1 : ℕ) : ℤ) k)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hcoeff := tendsto_norm_ccmPrimePoleCoefficient_nat_succ_zero hL
  have hupper : Tendsto (fun n : ℕ =>
      Real.sqrt L * ‖ccmPrimePoleCoefficient L ((n + 1 : ℕ) : ℤ)‖)
      atTop (𝓝 0) := by
    simpa using hcoeff.const_mul (Real.sqrt L)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hupper
  intro n
  rw [ccmNormalizedPrimePoleSequence, ccmPrimePoleSequence, norm_mul,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpole := ccmPrimePolePoint_norm_lt_one hL (((n + 1 : ℕ) : ℤ))
  have hpownonneg : 0 ≤ ‖ccmPrimePolePoint L ((n + 1 : ℕ) : ℤ)‖ ^ k := by positivity
  have hpowle : ‖ccmPrimePolePoint L ((n + 1 : ℕ) : ℤ)‖ ^ k ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg _) hpole.le
  gcongr
  exact mul_le_of_le_one_right
    (norm_nonneg (ccmPrimePoleCoefficient L ((n + 1 : ℕ) : ℤ))) hpowle

theorem ccmNormalizedPrimePoleVector_nat_succ_weakly_tendsto_zero
    {L : ℝ} (hL : 0 < L) :
    ∀ ℓ : CCMPrimePoleHilbert →L[ℂ] ℂ,
      Tendsto (fun n : ℕ =>
        ℓ (ccmNormalizedPrimePoleVector L hL ((n + 1 : ℕ) : ℤ)))
        atTop (𝓝 0) := by
  let v : ℕ → CCMPrimePoleHilbert := fun n =>
    ccmNormalizedPrimePoleVector L hL ((n + 1 : ℕ) : ℤ)
  have hbasis (k : ℕ) :
      Tendsto (fun n : ℕ => inner ℂ (HilbertSchmidt.lpBasis ℕ k) (v n))
        atTop (𝓝 0) := by
    rw [HilbertSchmidt.lpBasis_apply]
    simpa only [v, lp.inner_single_left, RCLike.inner_apply, map_one, one_mul,
      mul_one, ccmNormalizedPrimePoleVector_apply] using
      tendsto_ccmNormalizedPrimePoleSequence_coordinate_nat_succ_zero hL k
  have hspan : ∀ z ∈ Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)),
      Tendsto (fun n : ℕ => inner ℂ z (v n)) atTop (𝓝 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact hbasis k
    | zero => simp
    | add x y hx hy hxt hyt =>
        simpa only [inner_add_left, zero_add] using hxt.add hyt
    | smul a x hx hxt =>
        simpa only [inner_smul_left, mul_zero] using
          hxt.const_mul (starRingEnd ℂ a)
  have hdense : Dense (Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)) :
      Set CCMPrimePoleHilbert) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis ℕ).dense_span
  have hinner : ∀ y : CCMPrimePoleHilbert,
      Tendsto (fun n : ℕ => inner ℂ y (v n)) atTop (𝓝 0) := by
    intro y
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨z, hz, hyz⟩ := hdense.exists_dist_lt y (half_pos hε)
    have hz0 := hspan z hz
    rw [NormedAddGroup.tendsto_nhds_zero] at hz0
    filter_upwards [hz0 (ε / 2) (half_pos hε)] with n hn
    have hvnorm : ‖v n‖ = 1 :=
      norm_ccmNormalizedPrimePoleVector hL ((n + 1 : ℕ) : ℤ)
    calc
      ‖inner ℂ y (v n)‖ = ‖inner ℂ (y - z) (v n) + inner ℂ z (v n)‖ := by
        rw [← inner_add_left, sub_add_cancel]
      _ ≤ ‖inner ℂ (y - z) (v n)‖ + ‖inner ℂ z (v n)‖ := norm_add_le _ _
      _ ≤ ‖y - z‖ * ‖v n‖ + ‖inner ℂ z (v n)‖ := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = dist y z + ‖inner ℂ z (v n)‖ := by
        rw [hvnorm, mul_one, dist_eq_norm]
      _ < ε / 2 + ε / 2 := add_lt_add hyz hn
      _ = ε := by ring
  intro ℓ
  let y : CCMPrimePoleHilbert := (InnerProductSpace.toDual ℂ CCMPrimePoleHilbert).symm ℓ
  simpa [v, y, InnerProductSpace.toDual_symm_apply] using hinner y

/-- The full nonnegative-index family is weakly null; deleting or inserting a
finite prefix does not affect the limit. -/
theorem ccmNormalizedPrimePoleVector_nat_weakly_tendsto_zero
    {L : ℝ} (hL : 0 < L) :
    ∀ ℓ : CCMPrimePoleHilbert →L[ℂ] ℂ,
      Tendsto (fun n : ℕ => ℓ (ccmNormalizedPrimePoleVector L hL (n : ℤ)))
        atTop (𝓝 0) := by
  intro ℓ
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using
    ccmNormalizedPrimePoleVector_nat_succ_weakly_tendsto_zero hL ℓ

/-- Every cofinal subsequence of normalized CCM pole vectors remains weakly
null. -/
theorem ccmNormalizedPrimePoleVector_nat_comp_weakly_tendsto_zero
    {L : ℝ} (hL : 0 < L) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    ∀ ℓ : CCMPrimePoleHilbert →L[ℂ] ℂ,
      Tendsto (fun n : ℕ => ℓ (ccmNormalizedPrimePoleVector L hL (φ n : ℤ)))
        atTop (𝓝 0) := by
  intro ℓ
  simpa only [Function.comp_apply] using
    (ccmNormalizedPrimePoleVector_nat_weakly_tendsto_zero hL ℓ).comp hφ

end RHTower
