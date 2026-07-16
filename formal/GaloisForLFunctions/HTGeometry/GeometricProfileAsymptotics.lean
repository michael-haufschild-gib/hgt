import GaloisForLFunctions.HTGeometry.GeometricActiveAtomConfinement

/-!
# Elementary asymptotics for an exact geometric profile
-/

namespace GaloisForLFunctions

open Filter Topology

noncomputable section

/-- Every convergent real sequence is little-`o` of a geometric sequence of ratio greater than
one. -/
theorem isLittleO_constPow_of_tendsto
    {lam c₀ : ℝ} (hlam : 1 < lam) {c : ℕ → ℝ}
    (hc : Tendsto c atTop (nhds c₀)) :
    c =o[atTop] fun t : ℕ => lam ^ t := by
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 ?_
  · exact Filter.Eventually.of_forall fun t hzero =>
      ((pow_ne_zero t (zero_lt_one.trans hlam).ne') hzero).elim
  · exact hc.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hlam)

/-- A convergent additive correction cannot remove more than half of a positive geometric leading
term, uniformly after any fixed forward shift. -/
theorem eventually_geometricProfile_half_lower
    {A lam c₀ : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds c₀)) (C : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      A / 2 * lam ^ t ≤ A * lam ^ (t + C) + c (t + C) := by
  have hcshift := hc.comp (tendsto_add_atTop_nat C)
  have hclower : ∀ᶠ t : ℕ in atTop, c₀ - 1 < c (t + C) :=
    (tendsto_order.1 hcshift).1 (c₀ - 1) (by linarith)
  have hpow : Tendsto (fun t : ℕ => lam ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam
  have hlarge : ∀ᶠ t : ℕ in atTop,
      2 * (|c₀| + 1) / A < lam ^ t :=
    hpow.eventually_gt_atTop (2 * (|c₀| + 1) / A)
  filter_upwards [hclower, hlarge] with t hct ht
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hpowC : 1 ≤ lam ^ C := one_le_pow₀ hlam.le
  have hpowt : 0 < lam ^ t := pow_pos hlam0 t
  have hlead : A * lam ^ t ≤ A * lam ^ (t + C) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowC hpowt.le) hA.le
  have hcabs : c₀ - 1 ≥ -(|c₀| + 1) := by
    have := neg_abs_le c₀
    linarith
  have hscale : 2 * (|c₀| + 1) < A * lam ^ t := by
    simpa [mul_comm] using (div_lt_iff₀ hA).mp ht
  linarith

/-- Every positive multiple of a geometric sequence eventually exceeds one. -/
theorem eventually_one_le_mul_geometric
    {lam γ : ℝ} (hlam : 1 < lam) (hγ : 0 < γ) :
    ∀ᶠ t : ℕ in atTop, 1 ≤ γ * lam ^ t := by
  have hpow : Tendsto (fun t : ℕ => lam ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam
  have hlarge := hpow.eventually_ge_atTop (1 / γ)
  filter_upwards [hlarge] with t ht
  simpa [mul_comm] using (div_le_iff₀ hγ).mp ht

/-- A geometric exponential in the exponent beats every fixed polynomial in a translated natural
parameter. -/
theorem tendsto_natAdd_pow_mul_exp_neg_geometric
    {lam γ : ℝ} (hlam : 1 < lam) (hγ : 0 < γ) (K P : ℕ) :
    Tendsto (fun t : ℕ =>
      (((t + K : ℕ) : ℝ) ^ P) * Real.exp (-γ * lam ^ t))
      atTop (nhds 0) := by
  have hpowTop : Tendsto (fun t : ℕ => lam ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam
  have hcoreReal :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (P : ℝ) γ hγ
  have hcore : Tendsto (fun t : ℕ =>
      (lam ^ t) ^ P * Real.exp (-γ * lam ^ t)) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using hcoreReal.comp hpowTop
  obtain ⟨T, hT⟩ := exists_const_mul_pow_lt_of_geometric_lower
    (b := fun t : ℕ => lam ^ t)
    (fun t => pow_pos (zero_lt_one.trans hlam) t) hlam (N := 0)
    (fun t _ => by simp [pow_succ, mul_comm]) 2 (by norm_num) 1 1 (by omega)
  have hbound : ∀ᶠ t : ℕ in atTop,
      (((t + K : ℕ) : ℝ) ^ P) * Real.exp (-γ * lam ^ t) ≤
        (lam ^ t) ^ P * Real.exp (-γ * lam ^ t) := by
    filter_upwards [eventually_ge_atTop (max T (max K 1))] with t ht
    have htT : T ≤ t := (le_max_left _ _).trans ht
    have htK : K ≤ t := (le_trans (le_max_left _ _) (le_max_right T _)).trans ht
    have ht1 : 1 ≤ t := (le_trans (le_max_right _ _) (le_max_right T _)).trans ht
    have hadd : t + K ≤ 2 * (t + 1) := by omega
    have hcast : ((t + K : ℕ) : ℝ) ≤ lam ^ t := by
      have haddR : ((t + K : ℕ) : ℝ) ≤ 2 * ((t + 1 : ℕ) : ℝ) := by
        exact_mod_cast hadd
      have hTR : 2 * ((t + 1 : ℕ) : ℝ) < lam ^ t := by
        simpa using hT t htT
      exact (haddR.trans_lt hTR).le
    have hpowLe : (((t + K : ℕ) : ℝ) ^ P) ≤ (lam ^ t) ^ P := by
      gcongr
    exact mul_le_mul_of_nonneg_right hpowLe (Real.exp_nonneg _)
  apply squeeze_zero' (f := fun t : ℕ =>
    (((t + K : ℕ) : ℝ) ^ P) * Real.exp (-γ * lam ^ t))
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (pow_nonneg (by positivity) P) (Real.exp_nonneg _)
  · exact hbound
  · exact hcore

end

end GaloisForLFunctions
