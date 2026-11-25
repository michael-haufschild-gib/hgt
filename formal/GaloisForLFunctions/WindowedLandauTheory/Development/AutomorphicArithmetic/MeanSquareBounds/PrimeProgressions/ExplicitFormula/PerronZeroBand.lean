import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroWindow

/-! Moving the truncated zero sum by at most one in height costs only a logarithmic window. -/

open Complex DirichletCharacter Finset

noncomputable section

namespace QH.PrimeProgressions

theorem primitive_perron_zero_band :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u T U : ℝ, 2 ≤ T → T ≤ u → T ≤ U → U ≤ T + 1 →
        ‖(∑ᶠ ρ ∈ primitiveInteriorZeros χ U, (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
          (∑ᶠ ρ ∈ primitiveInteriorZeros χ T, (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ))‖ ≤
          C * (u * Real.log ((N : ℝ) * u * T) ^ 2 / T) := by
  obtain ⟨C, hC, H⟩ := primitive_zero_window
  refine ⟨2 * C, by positivity, ?_⟩
  intro N _ χ hχ u T U hT hu hTU hU
  classical
  let L := Real.log ((N : ℝ) * u * T)
  let a := primitiveInteriorZeros_finite hχ T
  let b := primitiveInteriorZeros_finite hχ U
  let B := b.toFinset \ a.toFinset
  have hsub : a.toFinset ⊆ b.toFinset := fun ρ h => by
    obtain ⟨h₀, h₁, h₂⟩ := a.mem_toFinset.mp h
    exact b.mem_toFinset.mpr ⟨h₀, h₁, h₂.trans_le hTU⟩
  have hmem (ρ : ℂ) (h : ρ ∈ B) : χ.LFunction ρ = 0 ∧ ρ.re ∈ Set.Ioo 0 1 ∧
      T ≤ |ρ.im| ∧ |ρ.im| < U := by
    obtain ⟨h₀, h₁⟩ := mem_sdiff.mp h
    obtain ⟨hz, hr, ht⟩ := b.mem_toFinset.mp h₀
    exact ⟨hz, hr, le_of_not_gt fun hlt => h₁ (a.mem_toFinset.mpr ⟨hz, hr, hlt⟩), ht⟩
  let V (ρ : ℂ) := (analyticOrderNatAt χ.LFunction ρ : ℝ)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have ht₀ : 0 < T := by linarith only [hT]
  have hu₀ : 0 < u := ht₀.trans_le hu
  have hu₁ : (2 : ℝ) ≤ u := hT.trans hu
  have hlog : Real.log ((N : ℝ) * (|T| + 2)) ≤ L := by
    apply Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) (by positivity))
    rw [abs_of_pos ht₀, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((by linarith only [hT] : T + 2 ≤ 2 * T).trans (mul_le_mul_of_nonneg_right hu₁ ht₀.le))
      (Nat.cast_nonneg _)
  have Hparts (t : ℝ) (ht : |t| = |T|) (E : Finset ℂ)
      (hE : ∀ ρ ∈ E, ρ ∈ primitiveZerosNear χ t) : (∑ ρ ∈ E, V ρ) ≤ C * L := by
    obtain ⟨S, hS⟩ := H N χ hχ t
    rw [finsum_mem_eq_finite_toFinset_sum _ S, ht] at hS
    have hf := sum_le_sum_of_subset_of_nonneg (fun ρ hρ => S.mem_toFinset.mpr (hE ρ hρ))
      (f := V) (fun _ _ _ => by positivity)
    exact (hf.trans hS).trans (mul_le_mul_of_nonneg_left hlog hC.le)
  let pos := B.filter fun ρ => 0 ≤ ρ.im
  let neg := B.filter fun ρ => ¬ 0 ≤ ρ.im
  have hpos := Hparts T rfl pos (by
    intro ρ hρ
    obtain ⟨hρ, hi⟩ := mem_filter.mp hρ
    obtain ⟨hz, hr, ht, ht'⟩ := hmem ρ hρ
    rw [abs_of_nonneg hi] at ht ht'
    exact ⟨hz, hr, abs_le.mpr ⟨by linarith only [ht], by linarith only [ht', hU]⟩⟩)
  have hneg := Hparts (-T) (abs_neg _) neg (by
    intro ρ hρ
    obtain ⟨hρ, hi⟩ := mem_filter.mp hρ
    obtain ⟨hz, hr, ht, ht'⟩ := hmem ρ hρ
    rw [abs_of_neg (lt_of_not_ge hi)] at ht ht'
    exact ⟨hz, hr, abs_le.mpr ⟨by linarith only [ht', hU], by linarith only [ht]⟩⟩)
  have hsum : (∑ ρ ∈ B, V ρ) ≤ 2 * C * L := by
    rw [← sum_filter_add_sum_filter_not B (fun ρ => 0 ≤ ρ.im)]
    exact (add_le_add hpos hneg).trans_eq (by ring)
  let F (ρ : ℂ) : ℂ := (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)
  simp only [finsum_mem_eq_finite_toFinset_sum _ (primitiveInteriorZeros_finite hχ _)]
  change ‖(∑ ρ ∈ b.toFinset, F ρ) - ∑ ρ ∈ a.toFinset, F ρ‖ ≤ _
  rw [← sum_sdiff hsub, add_sub_cancel_right]
  have hbound : ‖∑ ρ ∈ B, F ρ‖ ≤ (u / T) * ∑ ρ ∈ B, V ρ := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro ρ hρ
    obtain ⟨_, hre, ht, _⟩ := hmem ρ hρ
    have hρd := ht.trans (abs_im_le_norm ρ)
    have huρ : u ^ ρ.re ≤ u :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith only [hu₁]) hre.2.le).trans_eq (Real.rpow_one _)
    dsimp only [F, V]
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_cpow_eq_rpow_re_of_pos hu₀, mul_comm (u / T)]
    exact mul_le_mul_of_nonneg_left
      ((div_le_div_of_nonneg_right huρ (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left hu₀.le ht₀ hρd)) (Nat.cast_nonneg _)
  have hX : (4 : ℝ) ≤ (N : ℝ) * u * T := by
    have hNu := hu₁.trans (le_mul_of_one_le_left hu₀.le hn)
    exact (by norm_num : (4 : ℝ) ≤ 2 * 2).trans
      (mul_le_mul hNu hT (by norm_num) (by positivity))
  have hL : 1 ≤ L := (Real.le_log_iff_exp_le (by linarith only [hX])).mpr
    ((by linarith only [Real.exp_one_lt_d9] : Real.exp 1 ≤ 4).trans hX)
  have hL₂ : L ≤ L ^ 2 := by nlinarith only [mul_nonneg (show 0 ≤ L by linarith only [hL]) (sub_nonneg.mpr hL)]
  refine hbound.trans ((mul_le_mul_of_nonneg_left
    (hsum.trans (mul_le_mul_of_nonneg_left hL₂ (by positivity))) (by positivity)).trans_eq ?_)
  dsimp only [L]
  ring

end QH.PrimeProgressions
