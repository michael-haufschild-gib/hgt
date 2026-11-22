import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExceptionalZeroInSharpSum

/-! At low conductor, the logarithmic zero-free region bounds the nonexceptional zero sum. -/

open Finset Complex Classical
open WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

private theorem total_zero_multiplicity {M : ℕ} [NeZero M] (Z : Finset ℂ) (m : ℂ → ℕ)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hZ : ∀ ρ ∈ Z, |ρ.im| ≤ T + 1)
    (hunit : ∀ t : ℝ, ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), m ρ : ℕ) : ℝ) ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) :
    ∑ ρ ∈ Z, (m ρ : ℝ) ≤ 2 * C * (T + 2) * Real.log ((M : ℝ) * (T + 3)) := by
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  let b (ρ : ℂ) := ⌊|ρ.im|⌋₊
  let N := ⌊T + 1⌋₊ + 1
  let L := Real.log ((M : ℝ) * (T + 3))
  have hL : 0 ≤ L := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hM₁ (by linarith))
  have hb (ρ : ℂ) (hρ : ρ ∈ Z) : b ρ ∈ range N := by
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hZ ρ hρ)))
  have hbin (n : ℕ) (hn : n ∈ range N) :
      (∑ ρ ∈ Z.filter (fun ρ => b ρ = n), (m ρ : ℝ)) ≤ 2 * C * L := by
    let F := Z.filter (fun ρ => b ρ = n)
    have hN : (n : ℝ) ≤ T + 1 :=
      (Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp hn))).trans (Nat.floor_le (by linarith))
    have hsubsetPos : F.filter (fun ρ => 0 ≤ ρ.im) ⊆ Z.filter (fun ρ => |ρ.im - n| ≤ 1) := by
      intro ρ hρ
      obtain ⟨hρF, hi⟩ := mem_filter.mp hρ
      obtain ⟨hρZ, hf⟩ := mem_filter.mp hρF
      have hinterval := (Nat.floor_eq_iff (abs_nonneg ρ.im)).mp hf
      rw [abs_of_nonneg hi] at hinterval
      exact mem_filter.mpr ⟨hρZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hsubsetNeg : F.filter (fun ρ => ¬0 ≤ ρ.im) ⊆ Z.filter (fun ρ => |ρ.im - (-(n : ℝ))| ≤ 1) := by
      intro ρ hρ
      obtain ⟨hρF, hi⟩ := mem_filter.mp hρ
      obtain ⟨hρZ, hf⟩ := mem_filter.mp hρF
      have hinterval := (Nat.floor_eq_iff (abs_nonneg ρ.im)).mp hf
      rw [abs_of_neg (lt_of_not_ge hi)] at hinterval
      exact mem_filter.mpr ⟨hρZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hp := hunit n
    have hq := hunit (-(n : ℝ))
    push_cast at hp hq
    rw [abs_of_nonneg (Nat.cast_nonneg n)] at hp
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)] at hq
    have hlog : C * Real.log ((M : ℝ) * ((n : ℝ) + 2)) ≤ C * L :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith only [hN]) (Nat.cast_nonneg M))) hC
    have hpos := (sum_le_sum_of_subset_of_nonneg hsubsetPos (fun ρ _ _ => Nat.cast_nonneg (α := ℝ) (m ρ))).trans (hp.trans hlog)
    have hneg := (sum_le_sum_of_subset_of_nonneg hsubsetNeg (fun ρ _ _ => Nat.cast_nonneg (α := ℝ) (m ρ))).trans (hq.trans hlog)
    change ∑ ρ ∈ F, (m ρ : ℝ) ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not F (fun ρ => 0 ≤ ρ.im) (fun ρ => (m ρ : ℝ))]
    linarith only [hpos, hneg]
  rw [← sum_fiberwise_of_maps_to hb]
  refine (sum_le_sum hbin).trans ?_
  have hfloor : (N : ℝ) ≤ T + 2 := by
    dsimp [N]; push_cast; linarith only [Nat.floor_le (show 0 ≤ T + 1 by linarith)]
  rw [sum_const, card_range, nsmul_eq_mul]
  calc (N : ℝ) * (2 * C * L) ≤ (T + 2) * (2 * C * L) :=
        mul_le_mul_of_nonneg_right hfloor (by positivity)
    _ = _ := by dsimp only [L]; ring

/-- Every zero in the logarithmic region is the selected simple exception. Bounding the
remaining zeros by their gap from one yields an exponential bound for the weighted sum. -/
theorem near_range_zero_sum {M : ℕ} [NeZero M] (hM : 3 ≤ M)
    (Z : DirichletCharacter ℂ M → Finset ℂ) (m : DirichletCharacter ℂ M → ℂ → ℕ)
    {C T y : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hy : 1 ≤ y)
    (hz : ∀ χ, ∀ ρ ∈ Z χ, IsLZero χ ρ ∧ |ρ.im| ≤ T + 1)
    (hsimple : ∀ χ, ∀ ρ ∈ Z χ, deriv χ.LFunction ρ ≠ 0 → m χ ρ = 1)
    (hunit : ∀ χ t, ((∑ ρ ∈ (Z χ).filter (fun ρ => |ρ.im - t| ≤ 1), m χ ρ : ℕ) : ℝ) ≤
      C * Real.log ((M : ℝ) * (|t| + 2))) :
    (∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ,
      ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1)) ≤
      (M : ℝ) * (2 * C * (T + 2) * Real.log ((M : ℝ) * (T + 3))) *
        Real.exp (-(cZ * Real.log y / Real.log ((M : ℝ) * (T + 3)))) := by
  let L := Real.log ((M : ℝ) * (T + 3))
  let U := Real.exp (-(cZ * Real.log y / L))
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hL : 0 < L := Real.log_pos ((show (1 : ℝ) < T + 3 by linarith).trans_le
    (le_mul_of_one_le_left (by positivity) hM₁))
  have hterm (χ : DirichletCharacter ℂ M) (ρ : ℂ) (hρ : ρ ∈ Z χ) :
      ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤ (m χ ρ : ℝ) * U := by
    by_cases hreg : InRegion cZ M ρ
    · obtain ⟨β, he, hr, hd⟩ := zero_in_region M (by omega) χ ρ hreg (hz χ ρ hρ).1
      rw [hsimple χ ρ hρ hd, he]
      simp [excW, hr, U] <;> positivity
    · have hlog : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) :=
        Real.log_pos ((show (1 : ℝ) < |ρ.im| + 2 by linarith [abs_nonneg ρ.im]).trans_le
          (le_mul_of_one_le_left (by positivity) hM₁))
      have hlog' : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ L :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left
          (by linarith only [(hz χ ρ hρ).2]) (Nat.cast_nonneg M))
      have hd := div_le_div_of_nonneg_left cZ_pos.le hlog hlog'
      have hre := lt_of_not_ge hreg
      change ρ.re < 1 - cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) at hre
      have hexp : y ^ (ρ.re - 1) ≤ U := by
        change y ^ (ρ.re - 1) ≤ Real.exp (-(cZ * Real.log y / L))
        rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hy)]
        apply Real.exp_le_exp.mpr
        rw [show -(cZ * Real.log y / L) = Real.log y * (-(cZ / L)) by ring]
        exact mul_le_mul_of_nonneg_left (by linarith only [hre, hd]) (Real.log_nonneg hy)
      exact (mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _))
  have hc (χ : DirichletCharacter ℂ M) :
      (∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1)) ≤
          (2 * C * (T + 2) * L) * U := by
    refine (sum_le_sum (hterm χ)).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right
      (total_zero_multiplicity (M := M) (Z χ) (m χ) hC hT (fun ρ hρ => (hz χ ρ hρ).2) (hunit χ))
      (by positivity)
  refine (sum_le_sum (fun χ _ => hc χ)).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (card_char_le M) (by positivity)).trans_eq (by ring)

end QH.PrimeProgressions
