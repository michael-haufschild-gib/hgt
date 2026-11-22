import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CharacterLocalMoments
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.FejerRepulsion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.FullLocalMoments

/-! A real exceptional zero repels zeros of every character at its level. -/

open Complex Finset

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

private theorem denominator_repulsion :
    ∃ A : ℝ, 0 < A ∧ ∀ {C ℓ δ e : ℝ}, 1 ≤ C → 1 ≤ ℓ →
      0 ≤ δ → δ ≤ 1 / 100 → 0 < e → ∀ S : Multiset ℂ,
      ((1 / 50 + δ : ℝ) : ℂ) ∈ S → (S.card : ℝ) ≤ C * ℓ →
      (∀ j : ℕ, 1 ≤ j → ((S.map (fun w => 1 / w ^ j)).sum).re ≤
        2 * j * e / (1 / 50 : ℝ) ^ (j + 1) + C * ℓ * 25 ^ j) →
      Real.log ((1 / 50 : ℝ) / ((A * C) * ℓ * e)) / ((A * C) * ℓ) ≤ 50 * δ := by
  obtain ⟨A, hA, hpower⟩ := powerSum_repulsion
  refine ⟨A, hA, ?_⟩
  intro C ℓ δ e hC hℓ hδ hδ' he S hS hcard hm
  let η : ℝ := 1 / 50
  let L := C * ℓ
  have hη : 0 < η := by norm_num [η]
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hC hℓ
  obtain ⟨N, w, hw⟩ := dhFlat S
  let z (i : Fin N) : ℂ := (η : ℂ) / w i
  have hcard' : (N : ℝ) ≤ L := by
    have h := congrArg Multiset.card hw
    simp only [Multiset.card_map, Finset.card_val, card_univ, Fintype.card_fin] at h
    rwa [h]
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp (hw.symm ▸ hS)
  have hiNorm : 1 / (1 + δ / η) ≤ ‖z i‖ := by
    change _ ≤ ‖(η : ℂ) / w i‖
    rw [hi, norm_div, norm_real, norm_real,
      Real.norm_of_nonneg hη.le, Real.norm_of_nonneg (add_nonneg hη.le hδ)]
    apply le_of_eq
    change 1 / (1 + δ / η) = η / (η + δ)
    have hηδ : 0 < η + δ := add_pos_of_pos_of_nonneg hη hδ
    field_simp
    <;> ring
  have hs (j : ℕ) (hj : 1 ≤ j) :
      (∑ i : Fin N, z i ^ j).re ≤ 2 * j * (e / η) + L / (2 : ℝ) ^ j := by
    have heq : (∑ i : Fin N, z i ^ j).re =
        η ^ j * ((S.map (fun w => 1 / w ^ j)).sum).re := by
      simp only [z, div_pow]
      simp only [div_eq_mul_inv, one_mul]
      rw [← mul_sum, ← ofReal_pow, re_ofReal_mul, dhFlat_sum w S hw (fun u => (u ^ j)⁻¹)]
    rw [heq]
    refine (mul_le_mul_of_nonneg_left (hm j hj) (pow_nonneg hη.le _)).trans_eq ?_
    change η ^ j * (2 * j * e / η ^ (j + 1) + L * 25 ^ j) = _
    rw [mul_add, pow_succ η j]
    have hfirst : η ^ j * (2 * j * e / (η ^ j * η)) = 2 * j * (e / η) := by
      field_simp
      <;> ring
    rw [hfirst]
    congr 1
    calc η ^ j * (L * 25 ^ j) = L * (η * 25) ^ j := by rw [mul_pow]; ring
      _ = L / (2 : ℝ) ^ j := by
        rw [show η * 25 = (1 : ℝ) / 2 by norm_num [η], div_pow, one_pow, mul_one_div]
  have h := hpower (Fin N) univ z (fun _ => 1) i L (e / η) (δ / η)
    (mem_univ _) le_rfl hL (div_pos he hη) (div_nonneg hδ hη.le)
    (by norm_num [η]; linarith only [hδ']) hiNorm
    (by simpa only [Nat.cast_one, sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin] using hcard')
    (fun j hj => by simpa only [Nat.cast_one, one_mul] using hs j hj)
  have harg : 1 / (A * L * (e / η)) = η / ((A * C) * ℓ * e) := by
    dsimp only [L]
    field_simp
    <;> ring
  have hδeq : δ / η = 50 * δ := by dsimp only [η]; ring
  rw [harg, hδeq] at h
  simpa only [η, L, mul_assoc] using h

/-- Repulsion at a fixed modulus with one power of the logarithmic conductor in the
exceptional-zero parameter. -/
theorem deuring_heilbronn_sharp :
    ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β T : ℝ) (ρ : ℂ),
        3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → χ₁.LFunction (β : ℂ) = 0 →
        1 - c₁ / Real.log ((M : ℝ) * T) < β → β < 1 → IsLZero χ ρ →
        1 - c₀ ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β : ℂ)) →
        c₂ * Real.log (c₁ / ((1 - β) * Real.log ((M : ℝ) * T))) /
          Real.log ((M : ℝ) * T) ≤ 1 - ρ.re := by
  obtain ⟨C, hC, hfull⟩ := deuring_heilbronn_full_moments deuring_heilbronn_positivity
    deuring_heilbronn_local
  obtain ⟨A, hA, hrep⟩ := denominator_repulsion
  let B := A * C
  have hB : 0 < B := by dsimp only [B]; exact mul_pos hA (zero_lt_one.trans_le hC)
  let c₂ : ℝ := (1 / 50) / B
  have hc₂ : 0 < c₂ := div_pos (by norm_num) hB
  let c₁ := min (1 / 20) c₂
  have hc₁ : 0 < c₁ := lt_min (by norm_num) hc₂
  refine ⟨1 / 100, c₁, c₂, by norm_num, hc₁, hc₂, ?_⟩
  intro M _ χ₁ χ β T ρ hM hT hχ₁ hnon hzβ hclose hβ hρ hnear him hne
  let ℓ := Real.log ((M : ℝ) * T)
  have hℓ : 1 ≤ ℓ := dhLogOne M T hM hT
  have hℓ₀ : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hβnear : 19 / 20 ≤ β := by
    have hsmall : c₁ / ℓ ≤ 1 / 20 := (div_le_self hc₁.le hℓ).trans (min_le_left _ _)
    linarith only [hclose, hsmall]
  have hre : ρ.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hρ.1 h hρ.2
  let δ := 1 - ρ.re
  let e := 1 - β
  have hδ : 0 ≤ δ := sub_nonneg.mpr hre.le
  have hδ' : δ ≤ 1 / 100 := by dsimp only [δ]; linarith only [hnear]
  have he : 0 < e := sub_pos.mpr hβ
  obtain ⟨S, hS, hcard, hm⟩ := hfull M χ₁ χ β T (1 / 50) ρ hM hT hχ₁ hnon hzβ
    hβnear hβ hρ (by linarith only [hnear]) him hne (by norm_num) (by norm_num)
  have hd := hrep hC hℓ hδ hδ' he S hS hcard hm
  have harg : c₂ / (e * ℓ) = (1 / 50 : ℝ) / (B * ℓ * e) := by
    dsimp only [c₂]
    rw [div_div]
    congr 1
    ring
  have hlog : Real.log (c₁ / (e * ℓ)) ≤ Real.log (c₂ / (e * ℓ)) :=
    Real.log_le_log (div_pos hc₁ (mul_pos he hℓ₀))
      (div_le_div_of_nonneg_right (min_le_right _ _) (mul_pos he hℓ₀).le)
  change c₂ * Real.log (c₁ / (e * ℓ)) / ℓ ≤ δ
  calc
    _ ≤ c₂ * Real.log (c₂ / (e * ℓ)) / ℓ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hc₂.le) hℓ₀.le
    _ = (Real.log ((1 / 50 : ℝ) / (B * ℓ * e)) / (B * ℓ)) / 50 := by
      rw [harg]
      dsimp only [c₂]
      ring
    _ ≤ δ := (div_le_iff₀ (by norm_num)).2 (by simpa only [mul_comm δ] using hd)

end QH.PrimeProgressions
