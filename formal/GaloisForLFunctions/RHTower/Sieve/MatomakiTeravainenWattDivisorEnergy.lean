import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattProductMeanSquare
import GaloisForLFunctions.RHTower.Sieve.ProdIdxFibreDivisorBound

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

theorem sum_norm_sq_mtWattUnitCoeff_le_inv
    {N N' : ℕ} (hN : 1 ≤ N) (hN' : N' ≤ 2 * N) :
    (∑ j : Fin N', ‖mtWattUnitCoeff N N' j‖ ^ 2) ≤ 1 / (N : ℝ) := by
  let F : ℕ → ℂ := fun n => mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n
  have hbridge :
      (∑ j : Fin N', ‖mtWattUnitCoeff N N' j‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 N',
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 := by
    rw [← sum_fin_eq_sum_Icc N'
      (fun n => ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mtWattUnitCoeff, twistedTruncCoeff]
    dsimp only [F]
    push_cast
    rfl
  rw [hbridge]
  have hsub : Finset.Ioc N N' ⊆ Finset.Icc 1 N' := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  have hrestrict :
      (∑ n ∈ Finset.Icc 1 N',
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2) =
        ∑ n ∈ Finset.Ioc N N',
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnmem
    have hnpos : 0 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [show F n = 0 by
      dsimp only [F]
      rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
      apply if_neg
      intro hinside
      apply hnmem
      simp only [Finset.mem_Ioc]
      exact_mod_cast hinside]
    simp
  rw [hrestrict]
  have hterm : ∀ n ∈ Finset.Ioc N N',
      ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 ≤
        1 / (N : ℝ) ^ 2 := by
    intro n hn
    have hnNat : N < n ∧ n ≤ N' := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hinside : (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N' : ℝ) := by
      exact_mod_cast hnNat
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat.1.le
    have hinv : (n : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hNpos hNn
    have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnRpos.le
    have hinvSq : (n : ℝ)⁻¹ ^ 2 ≤ (N : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_left₀ hinv0 hinv 2
    dsimp only [F]
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos, if_pos hinside,
      Real.rpow_neg_one]
    simp only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hnRpos, one_div]
    simpa [inv_pow] using hinvSq
  calc
    (∑ n ∈ Finset.Ioc N N',
        ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2) ≤
        ∑ _n ∈ Finset.Ioc N N', 1 / (N : ℝ) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = ((N' - N : ℕ) : ℝ) * (1 / (N : ℝ) ^ 2) := by simp
    _ ≤ (N : ℝ) * (1 / (N : ℝ) ^ 2) := by
      have hdiff : N' - N ≤ N := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdiff) (by positivity)
    _ = 1 / (N : ℝ) := by field_simp

/-- Both reciprocal unit blocks retain their `N⁻²` energy after multiplicative convolution,
up to the standard arbitrarily-small divisor power. -/
theorem exists_sum_norm_sq_mtWattProductDirCoeff_le_divisor
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      (∑ r : Fin ((2 * A) * (N' * N')),
          ‖mtWattProductDirCoeff a A N N' r‖ ^ 2) ≤
        C ^ 2 * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
          ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) ^ 2 := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨C, hC, hconv⟩ := exists_sum_norm_sq_dirConv_le_rpow hhalf
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN'
  let u := mtWattUnitCoeff N N'
  let b := mtWattDataCoeff a A
  let uu := mtWattUnitSquareCoeff N N'
  let E := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  have hu := sum_norm_sq_mtWattUnitCoeff_le_inv hN hN'
  have hu0 : 0 ≤ ∑ j : Fin N', ‖u j‖ ^ 2 := by positivity
  have hinvN0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hpowNN0 : 0 ≤ (((N' * N' : ℕ) : ℝ) : ℝ) ^ (ε / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have huuBase := hconv N' N' u u
  have huu :
      (∑ r : Fin (N' * N'), ‖uu r‖ ^ 2) ≤
        C * ((N' * N' : ℕ) : ℝ) ^ (ε / 2) * (1 / (N : ℝ)) ^ 2 := by
    calc
      (∑ r : Fin (N' * N'), ‖uu r‖ ^ 2) ≤
          C * ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
            ((∑ j : Fin N', ‖u j‖ ^ 2) *
              (∑ j : Fin N', ‖u j‖ ^ 2)) := by
        simpa only [uu, mtWattUnitSquareCoeff] using huuBase
      _ ≤ C * ((N' * N' : ℕ) : ℝ) ^ (ε / 2) * (1 / (N : ℝ)) ^ 2 := by
        have hu' : (∑ j : Fin N', ‖u j‖ ^ 2) ≤ 1 / (N : ℝ) := by
          simpa only [u] using hu
        have hsq : (∑ j : Fin N', ‖u j‖ ^ 2) *
              (∑ j : Fin N', ‖u j‖ ^ 2) ≤ (1 / (N : ℝ)) ^ 2 := by
          nlinarith
        exact mul_le_mul_of_nonneg_left hsq
          (mul_nonneg hC.le hpowNN0)
  have hb := sum_norm_sq_mtWattDataCoeff_le_energy a hA
  have hb0 : 0 ≤ ∑ j : Fin (2 * A), ‖b j‖ ^ 2 := by positivity
  have huu0 : 0 ≤ ∑ r : Fin (N' * N'), ‖uu r‖ ^ 2 := by positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hpowM0 : 0 ≤ ((((2 * A) * (N' * N') : ℕ) : ℝ) : ℝ) ^ (ε / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hproduct := hconv (2 * A) (N' * N') b uu
  calc
    (∑ r : Fin ((2 * A) * (N' * N')),
        ‖mtWattProductDirCoeff a A N N' r‖ ^ 2) ≤
        C * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
          ((∑ j : Fin (2 * A), ‖b j‖ ^ 2) *
            (∑ r : Fin (N' * N'), ‖uu r‖ ^ 2)) := by
      simpa only [mtWattProductDirCoeff, b, uu] using hproduct
    _ ≤ C * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
        (((1 / (A : ℝ) ^ 2) * E) *
          (C * ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
            (1 / (N : ℝ)) ^ 2)) := by
      have hb' : (∑ j : Fin (2 * A), ‖b j‖ ^ 2) ≤
          (1 / (A : ℝ) ^ 2) * E := by
        simpa only [b, E] using hb
      gcongr
    _ = C ^ 2 * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
          ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
          (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2 := by ring

/-- Ordinary affine mean square plus divisor-fibre energy recovers both reciprocal unit-block
energies.  This is the elementary middle-range envelope before comparison with the sharper
Watt--Deshouillers--Iwaniec terms. -/
theorem exists_integral_mtWatt_divisorEnergy
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 1 ≤ T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
          ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
          (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) ^ 2 := by
  obtain ⟨C₀, hC₀, henergy⟩ :=
    exists_sum_norm_sq_mtWattProductDirCoeff_le_divisor hε
  let Caff : ℝ := 5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2
  refine ⟨Caff * C₀ ^ 2, mul_pos (by dsimp [Caff]; positivity) (sq_pos_of_pos hC₀), ?_⟩
  intro a A N N' hA hN hN' T hT
  let M := (2 * A) * (N' * N')
  let c := mtWattProductDirCoeff a A N N'
  let Ec := ∑ r : Fin M, ‖c r‖ ^ 2
  let E := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  let P := (((M : ℕ) : ℝ) ^ (ε / 2)) *
    (((N' * N' : ℕ) : ℝ) ^ (ε / 2))
  have hT0 : 0 ≤ T := by linarith
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEc0 : 0 ≤ Ec := by dsimp [Ec]; positivity
  have hweight :
      (∑ r : Fin M, (((r : ℕ) : ℝ) + 1) * ‖c r‖ ^ 2) ≤ (M : ℝ) * Ec := by
    dsimp only [Ec]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => by
      have hrM : (r : ℕ) + 1 ≤ M := by omega
      have hrMR : (((r : ℕ) : ℝ) + 1) ≤ (M : ℝ) := by
        exact_mod_cast hrM
      exact mul_le_mul_of_nonneg_right hrMR (sq_nonneg _)
  have haff := integral_Icc_normSq_dirPoly_le_affine c hT
  have hfull :
      (∫ t in Set.Icc (-T) T, ‖dirPoly M c t‖ ^ 2) ≤
        Caff * (T + (M : ℝ)) * Ec := by
    calc
      _ ≤ 5 * Real.pi * Real.exp 1 *
            (∑ r : Fin M, (((r : ℕ) : ℝ) + 1) * ‖c r‖ ^ 2) +
          (5 * Real.pi / 2) * Ec * T := by
        simpa only [M, c, Ec] using haff
      _ ≤ 5 * Real.pi * Real.exp 1 * ((M : ℝ) * Ec) +
          (5 * Real.pi / 2) * Ec * T := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hweight (by positivity)) le_rfl
      _ ≤ Caff * (T + (M : ℝ)) * Ec := by
        let c₁ : ℝ := 5 * Real.pi * Real.exp 1
        let c₂ : ℝ := 5 * Real.pi / 2
        have hc₁0 : 0 ≤ c₁ := by dsimp [c₁]; positivity
        have hc₂0 : 0 ≤ c₂ := by dsimp [c₂]; positivity
        have hcross : 0 ≤ c₁ * T * Ec + c₂ * (M : ℝ) * Ec := by positivity
        change c₁ * ((M : ℝ) * Ec) + c₂ * Ec * T ≤
          (c₁ + c₂) * (T + (M : ℝ)) * Ec
        calc
          c₁ * ((M : ℝ) * Ec) + c₂ * Ec * T ≤
              c₁ * ((M : ℝ) * Ec) + c₂ * Ec * T +
                (c₁ * T * Ec + c₂ * (M : ℝ) * Ec) :=
            le_add_of_nonneg_right hcross
          _ = (c₁ + c₂) * (T + (M : ℝ)) * Ec := by ring
  have hreflect :
      (∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2) =
        ∫ t in Set.Icc (-T) T, ‖dirPoly M c t‖ ^ 2 := by
    exact GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg
      (fun t : ℝ => dirPoly M c t) hT0
  have hcont : Continuous (fun t : ℝ => ‖dirPoly M c (-t)‖ ^ 2) :=
    ((continuous_dirPoly M c).comp continuous_neg).norm.pow 2
  have hsubset : Set.Ioc (T / 2) T ⊆ Set.Icc (-T) T := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hmono :
      (∫ t in Set.Ioc (T / 2) T, ‖dirPoly M c (-t)‖ ^ 2) ≤
        ∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2 := by
    exact MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun _ ht => hsubset ht)
  have henergy' : Ec ≤ C₀ ^ 2 * P * (1 / (A : ℝ) ^ 2) * E *
      (1 / (N : ℝ)) ^ 2 := by
    simpa only [Ec, E, P, M, c, mul_assoc] using henergy a A N N' hA hN hN'
  have hfactor0 : 0 ≤ Caff * (T + (M : ℝ)) := by
    dsimp [Caff]
    positivity
  calc
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock a A t‖ ^ 2) =
        ∫ t in (T / 2)..T, ‖dirPoly M c (-t)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 =
        ‖dirPoly M c (-t)‖ ^ 2
      rw [show dirPoly M c (-t) =
          mtWattUnitBlock N N' t * mtWattUnitBlock N N' t *
            mtWattCoefficientBlock a A t by
        simpa only [M, c] using (mtWattProduct_eq_dirPoly a A N N' t).symm]
      simp only [norm_mul]
      ring
    _ = ∫ t in Set.Ioc (T / 2) T, ‖dirPoly M c (-t)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ ≤ ∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2 := hmono
    _ ≤ Caff * (T + (M : ℝ)) * Ec := by rw [hreflect]; exact hfull
    _ ≤ Caff * (T + (M : ℝ)) *
        (C₀ ^ 2 * P * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left henergy' hfactor0
    _ = (Caff * C₀ ^ 2) * ((M : ℝ) ^ (ε / 2)) *
          ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
          (T + (M : ℝ)) * (1 / (A : ℝ) ^ 2) * E *
          (1 / (N : ℝ)) ^ 2 := by
      dsimp only [P]
      ring



end

end RHTower.Sieve
