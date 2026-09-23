import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceLocalization

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

/-- An outer signed defect of the literal physical slice reaches the same additive-length
large-value receiver, with the exact quadratic Mellin-decay cost. -/
theorem physicalSlice_base_or_exists_dyadic_superlevel_energy_of_adjacent_defect_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {A B : ℕ}, 1 ≤ A → 2 ≤ B → A ≤ B →
      ∀ {N H R U a Δ D v T : ℝ} {Q n : ℕ},
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 < U → 0 < Δ → 0 < D → 0 < v → 0 < Q →
        (∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ), U ≤ |y|) →
        D ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * Δ),
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ →
        (B : ℝ) * (Real.log B / A) ≤ (((2 ^ Q : ℕ) : ℝ) * v) →
        Δ / 2 ≤ a →
        a + ((2 * n : ℕ) : ℝ) * Δ + Δ / 2 ≤ T →
        let M := 65 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ)
        D / (4 * Δ * M) ≤ (n : ℝ) * v ∨
          ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
            (∀ i, lam i + Δ ≤ lam (i + 1)) ∧
            S ⊆ Finset.range n ∧ q < Q ∧
            (∀ j < n,
              lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
                  (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) ∨
              lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
                  (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
            (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤
              ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (lam r)‖) ∧
            D / (4 * Δ * M * (Q : ℝ)) ≤
              (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) ∧
            (S.card : ℝ) * ((((2 ^ q : ℕ) : ℝ) * v) ^ (2 : ℕ)) ≤
              (T + 4 * (B : ℝ) * (1 + Real.log B)) *
                (1 / Δ + 2 * Real.log B) *
                  (((B - A : ℕ) : ℝ) * (Real.log B / A) ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hquad⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_one_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro A B hA hB hAB N H R U a Δ D v T Q n hN hH hR hHR hRH hRN hU hΔ
    hD hv hQ haway hdefect hP ha hT
  let F : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  let M : ℝ := 65 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ)
  change D / (4 * Δ * M) ≤ (n : ℝ) * v ∨ _
  have hFc : Continuous F :=
    (continuous_dirPoly B (routeTVonMangoldtSliceCoeff A B)).comp continuous_neg
  have hKc : Continuous K :=
    (continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num))
  have hHleN : H ≤ N := hHR.trans hRN
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK : ∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ), ‖K y‖ ≤ M := by
    intro y hy
    have hyU := haway y hy
    have hy2 : U ^ (2 : ℕ) ≤ |y| ^ (2 : ℕ) := by nlinarith [sq_nonneg (|y| - U)]
    have hqR := hquad N R y hN hR hRN
    have hqH := hquad N H y hN hH hHleN
    have hKR : ‖routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I)‖ ≤
        13 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ) := by
      rw [le_div_iff₀ (sq_pos_of_pos hU)]
      calc
        ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I)‖ * U ^ (2 : ℕ) =
            U ^ (2 : ℕ) * ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I)‖ := by ring
        _ ≤ |y| ^ (2 : ℕ) * ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I)‖ :=
          mul_le_mul_of_nonneg_right hy2 (norm_nonneg _)
        _ ≤ 13 * C * (N / R) ^ (2 : ℕ) := hqR
    have hratio : R / H ≤ 2 := (div_le_iff₀ hH).2 hRH
    have hratioSq : (R / H) ^ (2 : ℕ) ≤ 4 := by
      have hratio0 : 0 ≤ R / H := by positivity
      nlinarith
    have hNH : (N / H) ^ (2 : ℕ) ≤ 4 * (N / R) ^ (2 : ℕ) := by
      have hre : N / H = (N / R) * (R / H) := by field_simp
      rw [hre, mul_pow]
      calc
        (N / R) ^ (2 : ℕ) * (R / H) ^ (2 : ℕ) ≤ (N / R) ^ (2 : ℕ) * 4 :=
          mul_le_mul_of_nonneg_left hratioSq (sq_nonneg (N / R))
        _ = 4 * (N / R) ^ (2 : ℕ) := by ring
    have hKH : ‖routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)‖ ≤
        52 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ) := by
      rw [le_div_iff₀ (sq_pos_of_pos hU)]
      calc
        ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ * U ^ (2 : ℕ) =
            U ^ (2 : ℕ) * ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ := by ring
        _ ≤ |y| ^ (2 : ℕ) * ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ :=
          mul_le_mul_of_nonneg_right hy2 (norm_nonneg _)
        _ ≤ 13 * C * (N / H) ^ (2 : ℕ) := hqH
        _ ≤ 13 * C * (4 * (N / R) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hNH (mul_nonneg (by norm_num) hC0)
        _ = 52 * C * (N / R) ^ (2 : ℕ) := by ring
    dsimp only [K, M]
    calc
      ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * I)‖ ≤
          ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * I)‖ +
            ‖routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * I)‖ :=
        norm_sub_le _ _
      _ ≤ 13 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ) +
          52 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ) := add_le_add hKR hKH
      _ = 65 * C * (N / R) ^ (2 : ℕ) / U ^ (2 : ℕ) := by ring
  obtain ⟨c, hc, hcellUpper⟩ :=
    exists_cell_max_norm_intervalIntegral_mul_le hFc hKc hΔ (2 * n) hK
  have hM : 0 < M := by
    dsimp only [M]
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    positivity
  have hcell : D ≤ ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖F (c j)‖) := by
    exact hdefect.trans (by simpa only [F, K, M] using hcellUpper)
  have hF : ∀ y : ℝ, ‖F y‖ ≤ (B : ℝ) * (Real.log B / A) := by
    intro y
    exact norm_dirPoly_routeTVonMangoldtSliceCoeff_le hA (-y)
  rcases base_layer_or_exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hΔ hM hD hv hQ hc hcell hF hP with hbase | hhigh
  · exact Or.inl hbase
  · right
    obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlargeNeg, hmass⟩ := hhigh
    have hlarge : ∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤
        ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (lam r)‖ := by
      intro r hr
      rw [← norm_dirPoly_routeTVonMangoldtSliceCoeff_neg_eq A B (lam r)]
      simpa only [F] using hlargeNeg r hr
    have hband : ∀ r ∈ S, Δ / 2 ≤ lam r ∧ lam r + Δ / 2 ≤ T := by
      intro r hr
      have hrn : r < n := Finset.mem_range.mp (hS hr)
      rcases hmem r hrn with heven | hodd
      · constructor
        · have har : a ≤ lam r := by
            have hr0 : (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by positivity
            nlinarith [heven.1]
          exact ha.trans har
        · have hcast : ((2 * r : ℕ) : ℝ) + 1 ≤ (2 * n : ℕ) := by
            norm_cast
            omega
          nlinarith [heven.2]
      · constructor
        · have har : a ≤ lam r := by
            have hr0 : (0 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by positivity
            nlinarith [hodd.1]
          exact ha.trans har
        · have hcast : ((2 * r + 1 : ℕ) : ℝ) + 1 ≤ (2 * n : ℕ) := by
            norm_cast
            omega
          nlinarith [hodd.2]
    have hT0 : 0 ≤ T := by
      have hn0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by positivity
      nlinarith
    have hV : 0 < (((2 ^ q : ℕ) : ℝ) * v) := by positivity
    have henergy := card_largeValues_routeTVonMangoldtSlice_finset
      hA hB hAB hΔ hT0 hV hgap hband hlarge
    refine ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass, henergy⟩

end RHTower.Sieve
