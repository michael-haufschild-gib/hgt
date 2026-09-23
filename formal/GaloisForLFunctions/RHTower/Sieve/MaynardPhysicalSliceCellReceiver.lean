import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSlicePerronRecut
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeLayerExtraction

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

@[simp] theorem conj_routeTVonMangoldtSliceCoeff
    (A B : ℕ) (m : Fin B) :
    (starRingEnd ℂ) (routeTVonMangoldtSliceCoeff A B m) =
      routeTVonMangoldtSliceCoeff A B m := by
  rw [routeTVonMangoldtSliceCoeff]
  split_ifs
  · exact Complex.conj_ofReal _
  · simp

theorem norm_dirPoly_routeTVonMangoldtSliceCoeff_neg_eq
    (A B : ℕ) (y : ℝ) :
    ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y)‖ =
      ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) y‖ := by
  have h := dirPoly_conj_neg B (routeTVonMangoldtSliceCoeff A B) y
  simp only [conj_routeTVonMangoldtSliceCoeff] at h
  rw [h, RCLike.norm_conj]

theorem norm_dirPoly_routeTVonMangoldtSliceCoeff_le
    {A B : ℕ} (hA : 1 ≤ A) (y : ℝ) :
    ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) y‖ ≤
      (B : ℝ) * (Real.log B / A) := by
  calc
    ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) y‖ ≤
        ∑ m : Fin B, ‖routeTVonMangoldtSliceCoeff A B m‖ :=
      norm_dirPoly_le_sum_norm B (routeTVonMangoldtSliceCoeff A B) y
    _ ≤ ∑ _m : Fin B, Real.log B / A :=
      Finset.sum_le_sum fun _m _hm => norm_routeTVonMangoldtSliceCoeff_le hA
    _ = (B : ℝ) * (Real.log B / A) := by simp

/-- A central signed defect of the literal physical slice reaches its local-energy receiver.
Either the base layer already carries the defect, or one separated dyadic superlevel has both
the first-moment lower bound and the additive-length Montgomery upper bound. -/
theorem physicalSlice_base_or_exists_dyadic_superlevel_energy_of_adjacent_defect_central
    {A B : ℕ} (hA : 1 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B)
    {N H R a Δ D v T : ℝ} {Q n : ℕ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hΔ : 0 < Δ) (hD : 0 < D) (hv : 0 < v) (hQ : 0 < Q)
    (hcentral : ∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ),
      |y| ≤ N / (2 * R))
    (hdefect : D ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * Δ),
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖)
    (hP : (B : ℝ) * (Real.log B / A) ≤ (((2 ^ Q : ℕ) : ℝ) * v))
    (ha : Δ / 2 ≤ a)
    (hT : a + ((2 * n : ℕ) : ℝ) * Δ + Δ / 2 ≤ T) :
    D / (16 * Δ) ≤ (n : ℝ) * v ∨
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
        D / (16 * Δ * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) ∧
        (S.card : ℝ) * ((((2 ^ q : ℕ) : ℝ) * v) ^ (2 : ℕ)) ≤
          (T + 4 * (B : ℝ) * (1 + Real.log B)) *
            (1 / Δ + 2 * Real.log B) *
              (((B - A : ℕ) : ℝ) * (Real.log B / A) ^ (2 : ℕ)) := by
  let F : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hFc : Continuous F := by
    exact (continuous_dirPoly B (routeTVonMangoldtSliceCoeff A B)).comp
      continuous_neg
  have hKc : Continuous K :=
    (continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num))
  have hK : ∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ), ‖K y‖ ≤ 4 := by
    intro y hy
    have hyabs := hcentral y hy
    let s : ℂ := (1 : ℂ) + (y : ℝ) * I
    have hsre : s.re = 1 := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by simp [s, Real.norm_eq_abs]
    have hsmall : ‖s - 1‖ * (2 * R / N) ≤ 1 := by
      rw [hsnorm]
      calc
        |y| * (2 * R / N) ≤ (N / (2 * R)) * (2 * R / N) :=
          mul_le_mul_of_nonneg_right hyabs (by positivity)
        _ = 1 := by field_simp
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR (by simpa [hsre]) hsmall
    norm_num [hsre, hsnorm] at hkernel
    dsimp only [K, s] at hkernel ⊢
    calc
      ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * I)‖ ≤
          8 * |y| * (R / N) := hkernel
      _ ≤ 8 * (N / (2 * R)) * (R / N) := by gcongr
      _ = 4 := by field_simp; norm_num
  obtain ⟨c, hc, hcellUpper⟩ :=
    exists_cell_max_norm_intervalIntegral_mul_le hFc hKc hΔ (2 * n) hK
  have hcell : D ≤ ∑ j ∈ Finset.range (2 * n), Δ * (4 * ‖F (c j)‖) := by
    exact hdefect.trans (by simpa only [F, K] using hcellUpper)
  have hF : ∀ y : ℝ, ‖F y‖ ≤ (B : ℝ) * (Real.log B / A) := by
    intro y
    dsimp only [F]
    exact norm_dirPoly_routeTVonMangoldtSliceCoeff_le hA (-y)
  rcases base_layer_or_exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hΔ (by norm_num : (0 : ℝ) < 4) hD hv hQ hc hcell hF hP with hbase | hhigh
  · left
    convert hbase using 1 <;> ring
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
    refine ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, ?_, henergy⟩
    convert hmass using 1 <;> ring

end RHTower.Sieve
