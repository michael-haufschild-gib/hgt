import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimitiveZeroCells
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroWindow

/-! Analytic-multiplicity density for primitive Dirichlet zeros near the one-line. -/

open Finset Complex

namespace QH.PrimeProgressions

private theorem zero_cell_log_bound {Q N t : ℝ} (hQ : 3 ≤ Q) (hN₀ : 0 < N)
    (hN : N ≤ Q) (ht : |t| ≤ Q + 1) :
    Real.log (N * (|t| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
  have h₁ : N * (|t| + 2) ≤ Q * (Q + 3) :=
    mul_le_mul hN (by linarith only [ht]) (by positivity) (by linarith only [hQ])
  have h₂ : Q + 3 ≤ Q ^ 2 := by
    have hQ₂ := mul_nonneg (show 0 ≤ Q - 3 by linarith only [hQ])
      (show 0 ≤ Q + 2 by linarith only [hQ])
    nlinarith only [hQ₂]
  have h₃ : N * (|t| + 2) ≤ Q ^ 3 := h₁.trans
    ((mul_le_mul_of_nonneg_left h₂ (by linarith only [hQ])).trans_eq (by ring))
  have hlog := Real.log_le_log (by positivity) h₃
  rw [Real.log_pow] at hlog
  have h := Real.log_le_rpow_div (x := Q) (ε := (1 : ℝ) / 8) (by linarith only [hQ]) (by norm_num)
  have h₄ : Real.log Q ≤ 8 * Q ^ ((1 : ℝ) / 8) := h.trans_eq (by ring)
  calc
    _ ≤ 3 * Real.log Q := by simpa only [Nat.cast_ofNat] using hlog
    _ ≤ 3 * (8 * Q ^ ((1 : ℝ) / 8)) := mul_le_mul_of_nonneg_left h₄ (by norm_num)
    _ = _ := by ring

/-- Primitive zeros with real part at least 399/400 and modulus and height at most Q
have total analytic multiplicity O(Q^(1/4)). -/
theorem primitive_near_one_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      ∀ U : Finset ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ),
      (∀ p ∈ U, ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧
        p.1.2.LFunction p.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.re ∧ |p.2.im| ≤ Q) →
      ((∑ p ∈ U, analyticOrderNatAt (DirichletCharacter.LFunction p.1.2) p.2 : ℕ) : ℝ) ≤
        C * Q ^ ((1 : ℝ) / 4) := by
  classical
  obtain ⟨C₁, hC₁, hw⟩ := primitive_zero_window
  obtain ⟨C₂, hC₂, hc⟩ := primitive_zero_cells_bound
  refine ⟨C₂ * (C₁ * 24), by positivity, ?_⟩
  intro Q hQ U hU
  have hQ₀ : 0 < Q := by linarith only [hQ]
  let w (p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) :=
    (analyticOrderNatAt (DirichletCharacter.LFunction p.1.2) p.2 : ℝ)
  let B := C₁ * (24 * Q ^ ((1 : ℝ) / 8))
  let T := U.image primitiveZeroCell
  have hcell (v : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℤ) (hv : v ∈ T) :
      ∑ p ∈ U.filter (fun p => primitiveZeroCell p = v), w p ≤ B := by
    obtain ⟨⟨x, z⟩, hz, rfl⟩ := mem_image.mp hv
    obtain ⟨hq, hχ, _, _, hzim⟩ := hU (x, z) hz
    let j := ⌊z.im⌋
    obtain ⟨hf, hw'⟩ := hw (x.1 + 1) x.2 hχ (j : ℝ)
    rw [finsum_mem_eq_finite_toFinset_sum _ hf] at hw'
    have hj : |(j : ℝ)| ≤ Q + 1 := by
      have hz' := abs_le.mp hzim
      exact abs_le.mpr ⟨by linarith only [hz'.1, Int.lt_floor_add_one z.im],
        by linarith only [hz'.2, Int.floor_le z.im]⟩
    have hl := zero_cell_log_bound hQ (by positivity) hq hj
    let g (ρ : ℂ) := (x, ρ)
    have hg : Function.Injective g := fun ρ ρ' h => congrArg Prod.snd h
    have hsub : U.filter (fun p => primitiveZeroCell p = primitiveZeroCell (x, z)) ⊆
        hf.toFinset.image g := by
      rintro ⟨x', ρ⟩ hp
      obtain ⟨hpU, he⟩ := mem_filter.mp hp
      obtain ⟨_, hpχ, hpz, hpre, _⟩ := hU (x', ρ) hpU
      change (x', ⌊ρ.im⌋) = (x, j) at he
      obtain ⟨hx, hfloor⟩ := Prod.mk.inj he
      subst x'
      refine mem_image.mpr ⟨ρ, hf.mem_toFinset.mpr ?_, rfl⟩
      refine ⟨hpz, ⟨by linarith only [hpre], primitive_zero_re_lt_one hpχ hpz⟩, ?_⟩
      have h₁ := Int.floor_le ρ.im
      have h₂ := Int.lt_floor_add_one ρ.im
      rw [hfloor] at h₁ h₂
      exact abs_le.mpr ⟨by linarith only [h₁], by linarith only [h₂]⟩
    calc
      _ ≤ ∑ p ∈ hf.toFinset.image g, w p :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
      _ = ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt x.2.LFunction ρ : ℝ) := sum_image hg.injOn
      _ ≤ _ := hw'.trans (mul_le_mul_of_nonneg_left hl hC₁.le)
  push_cast
  change (∑ p ∈ U, w p) ≤ _
  rw [← sum_fiberwise_of_maps_to (s := U) (t := T) (g := primitiveZeroCell)
    (fun p hp => mem_image_of_mem _ hp)]
  have hcard : (T.card : ℝ) ≤ C₂ * Q ^ ((1 : ℝ) / 8) := hc Q hQ U hU
  calc
    _ ≤ (T.card : ℝ) * B := by simpa only [nsmul_eq_mul] using sum_le_card_nsmul _ _ _ hcell
    _ ≤ (C₂ * Q ^ ((1 : ℝ) / 8)) * B := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [show Q ^ ((1 : ℝ) / 4) = Q ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) by
        rw [← Real.rpow_add hQ₀]; norm_num]
      dsimp [B]
      ring

end QH.PrimeProgressions
