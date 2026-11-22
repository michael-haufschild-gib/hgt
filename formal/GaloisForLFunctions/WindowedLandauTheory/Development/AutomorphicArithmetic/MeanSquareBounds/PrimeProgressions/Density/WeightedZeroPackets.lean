import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.LogFreeDensity

/-! Weight the finite zero divisor by powers using the log-free density estimate. -/

open Finset Complex WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

theorem weighted_zero_packets :
    ∃ d C κ : ℝ, 0 < d ∧ 0 < C ∧ 0 < κ ∧
      ∀ (M : ℕ) [NeZero M] (T y η : ℝ) (Z : DirichletCharacter ℂ M → Finset ℂ),
        2 ≤ T → 0 < y → d * Real.log ((M : ℝ) * T) ≤ Real.log y →
        0 ≤ η → (∀ χ, ∀ ρ ∈ Z χ, 1 - κ ≤ ρ.re ∧ ρ.re ≤ 1 - η ∧ |ρ.im| ≤ T ∧ IsLZero χ ρ) →
        ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ,
          (analyticOrderNatAt χ.LFunction ρ : ℝ) * y ^ (ρ.re - 1) ≤ C * y ^ (-η / 2) := by
  obtain ⟨A, B, κ, hA, hB, hκ, hcount⟩ := log_free_zero_density
  let g := Real.exp (-1)
  have hg : 0 < g := Real.exp_pos _
  have hg₁ : g < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeom := summable_geometric_of_lt_one hg.le hg₁
  let K := ∑' j : ℕ, g ^ j
  have hK : 0 < K := by
    have h := hgeom.sum_le_tsum ({0} : Finset ℕ) (fun _ _ => by positivity)
    simp only [sum_singleton, pow_zero] at h
    exact zero_lt_one.trans_le h
  refine ⟨2 * (A + 1), B * Real.exp A * K, κ, by positivity, by positivity, hκ, ?_⟩
  intro M _ T y η Z hT hy hscale hη hZ
  let ℓ := Real.log ((M : ℝ) * T)
  let Y := Real.log y
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hMT : (1 : ℝ) < (M : ℝ) * T :=
    (show (1 : ℝ) < T by linarith only [hT]).trans_le (le_mul_of_one_le_left (by linarith only [hT]) hM)
  have hℓ : 0 < ℓ := Real.log_pos hMT
  have hY : 0 ≤ Y := (by positivity : 0 ≤ 2 * (A + 1) * ℓ).trans hscale
  let J := ⌊ℓ * κ⌋₊ + 1
  let slot (ρ : ℂ) := ⌊ℓ * (1 - ρ.re)⌋₊
  let Zj (χ : DirichletCharacter ℂ M) (j : ℕ) := (Z χ).filter (fun ρ => slot ρ = j)
  have hslot (χ : DirichletCharacter ℂ M) (ρ : ℂ) (hρ : ρ ∈ Z χ) : slot ρ ∈ range J := by
    have hs : 1 - ρ.re ≤ κ := by linarith only [(hZ χ ρ hρ).1]
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left hs hℓ.le)))
  have hweight (χ : DirichletCharacter ℂ M) (j : ℕ) (ρ : ℂ) (hρ : ρ ∈ Zj χ j) :
      y ^ (ρ.re - 1) ≤ y ^ (-η / 2) * Real.exp (-((A + 1) * j)) := by
    obtain ⟨hρZ, hj⟩ := mem_filter.mp hρ
    have hgap : η ≤ 1 - ρ.re := by linarith only [(hZ χ ρ hρZ).2.1]
    have hj' : (j : ℝ) ≤ ℓ * (1 - ρ.re) := by
      rw [← hj]
      exact Nat.floor_le (mul_nonneg hℓ.le (hη.trans hgap))
    rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hy, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hgap (show 0 ≤ Y / 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hj' (show 0 ≤ A + 1 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hscale (hη.trans hgap)
    change Y * (ρ.re - 1) ≤ Y * (-η / 2) + -((A + 1) * j)
    linarith only [h1, h2, h3]
  have hmass (j : ℕ) : ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Zj χ j,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤ B * Real.exp (A * (j + 1)) := by
    let x := min κ ((j + 1) / ℓ)
    have hx : 0 ≤ x := le_min hκ.le (by positivity)
    have h := hcount M T (1 - x) hT (sub_le_sub_left (min_le_left κ ((j + 1) / ℓ)) 1)
      (by linarith only [hx]) (fun χ => Zj χ j) (by
        intro χ ρ hρ
        obtain ⟨hρZ, hj⟩ := mem_filter.mp hρ
        obtain ⟨hre, -, him, hz⟩ := hZ χ ρ hρZ
        refine ⟨?_, him, hz⟩
        have he : 1 - ρ.re ≤ x := by
          apply le_min (by linarith only [hre])
          rw [le_div_iff₀ hℓ, mul_comm]
          have hf := Nat.lt_floor_add_one (ℓ * (1 - ρ.re))
          change ℓ * (1 - ρ.re) < (slot ρ : ℝ) + 1 at hf
          exact (hj ▸ hf).le
        linarith only [he])
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB.le)
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hMT)]
    apply Real.exp_le_exp.mpr
    have he := (le_div_iff₀ hℓ).mp (min_le_right κ ((j + 1) / ℓ))
    have he' := mul_le_mul_of_nonneg_left he hA.le
    change ℓ * (A * (1 - (1 - x))) ≤ A * (j + 1)
    linarith only [he']
  have hsum (j : ℕ) : ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Zj χ j,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * y ^ (ρ.re - 1) ≤
        B * Real.exp A * y ^ (-η / 2) * g ^ j := by
    let c := y ^ (-η / 2) * Real.exp (-((A + 1) * j))
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Zj χ j, c * (analyticOrderNatAt χ.LFunction ρ : ℝ) := by
        refine sum_le_sum fun χ _ => sum_le_sum fun ρ hρ => ?_
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left (hweight χ j ρ hρ) (Nat.cast_nonneg _)
      _ = c * ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Zj χ j,
          (analyticOrderNatAt χ.LFunction ρ : ℝ) := by simp_rw [mul_sum]
      _ ≤ c * (B * Real.exp (A * (j + 1))) :=
        mul_le_mul_of_nonneg_left (hmass j) (by dsimp only [c]; positivity)
      _ = _ := by
        have he : -((A + 1) * j) + A * (j + 1) = A + -(j : ℝ) := by ring
        have hex : Real.exp (-((A + 1) * j)) * Real.exp (A * (j + 1)) =
            Real.exp A * g ^ j := by
          rw [← Real.exp_add, he, Real.exp_add]
          dsimp only [g]
          rw [← Real.exp_nat_mul]
          congr 2
          ring
        dsimp only [c]
        calc
          _ = B * y ^ (-η / 2) * (Real.exp (-((A + 1) * j)) * Real.exp (A * (j + 1))) := by ring
          _ = _ := by rw [hex]; ring
  calc
    _ = ∑ j ∈ range J, ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Zj χ j,
        (analyticOrderNatAt χ.LFunction ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [sum_comm]
      exact sum_congr rfl fun χ _ => (sum_fiberwise_of_maps_to (hslot χ) _).symm
    _ ≤ ∑ j ∈ range J, B * Real.exp A * y ^ (-η / 2) * g ^ j := sum_le_sum fun j _ => hsum j
    _ ≤ B * Real.exp A * y ^ (-η / 2) * K := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (hgeom.sum_le_tsum (range J) (fun _ _ => by positivity)) (by positivity)
    _ = _ := by ring

end QH.PrimeProgressions
