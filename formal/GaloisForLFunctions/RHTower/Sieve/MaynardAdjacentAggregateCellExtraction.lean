import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentKernelLocalization
import GaloisForLFunctions.HTGeometry.CellMaxDiscretisation

/-!
# Cancellation-preserving cell extraction for adjacent Route-T kernels

The multiscale signed defect must reach the existing Maynard selected-cell counts without replacing
the signed integral by a global supremum.  This module discretises a vertical interval at maxima of
the full integrand.  On the natural central band, exact pole cancellation bounds the adjacent
kernel by `4`; on a tail block its second-order Mellin decay gives the explicit scale
`65 C (N/R)^2/U^2`.  The produced maxima remain in their literal cells, so parity splitting yields
two separated ordinate families with no loss of cancellation before extraction.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- A normalized adjacent-window Mellin kernel is continuous on every positive vertical line. -/
theorem continuous_routeTNormalizedSmoothWindowMellin_line
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Continuous (fun y : ℝ => routeTNormalizedSmoothWindowMellin N H
      ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hplus := continuous_mellin_smoothWeight_line
    (N := N + H) hH hsigma
  have hbase := continuous_mellin_smoothWeight_line
    (N := N) hH hsigma
  have hsub := hplus.sub hbase
  have heq : (fun y : ℝ => routeTNormalizedSmoothWindowMellin N H
        ((sigma : ℂ) + (y : ℝ) * I)) =
      fun y : ℝ => (H : ℂ)⁻¹ *
        (mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) -
          mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) := by
    funext y
    rw [routeTNormalizedSmoothWindowMellin,
      mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by simpa using hsigma)]
  rw [heq]
  exact continuous_const.mul hsub

/-- The literal finite window-relevant Heath--Brown aggregate is continuous on every vertical
line. -/
theorem continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
    (L X k : ℕ) (T0 t N sigma : ℝ) :
    Continuous (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * I)) := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t N
  let M : ℕ := 2 ^ (2 * k) * X
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro h
      apply hn
      simp [complexCoeff_apply, h]
    exact upperSupported_heathBrownWindowRelevantEligiblePacket L X k T0 t N n hnF
  have hcont := continuous_LSeries_line_of_support hzero hsupp sigma
  refine hcont.congr (fun y => ?_)
  exact LSeries_heathBrownWindowRelevantEligiblePacket L X k T0 t N _

/-- Generic signed-integral cell extraction.  No triangle inequality is applied before the norm of
the integral; only then is the integral discretised at full-integrand maxima. -/
theorem exists_cell_max_norm_intervalIntegral_mul_le
    {A K : ℝ → ℂ} (hA : Continuous A) (hK : Continuous K)
    {a Δ M : ℝ} (hΔ : 0 < Δ) (m : ℕ)
    (hM : ∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ), ‖K y‖ ≤ M) :
    ∃ c : ℕ → ℝ,
      (∀ j, j < m → c j ∈
        Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ)) ∧
      ‖∫ y in a..(a + (m : ℝ) * Δ), A y * K y‖ ≤
        ∑ j ∈ Finset.range m, Δ * (M * ‖A (c j)‖) := by
  let F : ℝ → ℝ := fun y => ‖A y * K y‖
  have hF : Continuous F := (hA.mul hK).norm
  obtain ⟨c, hc, hint⟩ := exists_cell_max_integral_le hF a Δ hΔ m
  refine ⟨c, hc, ?_⟩
  have hend : a ≤ a + (m : ℝ) * Δ :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg m) hΔ.le)
  have hnorm : ‖∫ y in a..(a + (m : ℝ) * Δ), A y * K y‖ ≤
      ∫ y in a..(a + (m : ℝ) * Δ), F y :=
    intervalIntegral.norm_integral_le_integral_norm hend
  have hpoint : ∀ j ∈ Finset.range m, F (c j) ≤ M * ‖A (c j)‖ := by
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hcj := hc j hjlt
    have hcglobal : c j ∈ Set.Icc a (a + (m : ℝ) * Δ) := by
      constructor
      · exact (le_add_of_nonneg_right
          (mul_nonneg (Nat.cast_nonneg j) hΔ.le)).trans hcj.1
      · have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by
          exact_mod_cast (show j + 1 ≤ m by omega)
        exact hcj.2.trans (by nlinarith [hΔ.le])
    dsimp only [F]
    rw [norm_mul]
    calc
      ‖A (c j)‖ * ‖K (c j)‖ ≤ ‖A (c j)‖ * M :=
        mul_le_mul_of_nonneg_left (hM (c j) hcglobal) (norm_nonneg _)
      _ = M * ‖A (c j)‖ := by ring
  exact hnorm.trans (hint.trans (Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (hpoint j hj) hΔ.le))

/-- On the common natural band, exact pole cancellation bounds the adjacent kernel by `4`, so a
signed interval defect is controlled by literal full-aggregate cell maxima. -/
theorem exists_cell_max_norm_intervalIntegral_adjacent_defect_central_le
    (L X k : ℕ) (T0 t : ℝ) {N H R a Δ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hΔ : 0 < Δ) (m : ℕ)
    (hband : ∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ), |y| ≤ N / (2 * R)) :
    ∃ c : ℕ → ℝ,
      (∀ j, j < m → c j ∈
        Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ)) ∧
      ‖∫ y in a..(a + (m : ℝ) * Δ),
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((1 : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖ ≤
        ∑ j ∈ Finset.range m, Δ *
          (4 * ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((1 : ℂ) + (c j : ℝ) * I)‖) := by
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
      ((1 : ℂ) + (y : ℝ) * I)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hA : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line L X k T0 t N 1
  have hK : Continuous K :=
    (continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num))
  have hM : ∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ), ‖K y‖ ≤ 4 := by
    intro y hy
    have hyabs := hband y hy
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
  exact exists_cell_max_norm_intervalIntegral_mul_le hA hK hΔ m hM

/-- On any block staying outside ordinate `U`, quadratic Mellin decay bounds the adjacent kernel
by `65 C (N/R)^2/U^2`.  Comparable widths are the only scale hypothesis. -/
theorem exists_cell_max_norm_intervalIntegral_adjacent_defect_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {N H R U a Δ : ℝ},
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 < U → 0 < Δ → ∀ (m : ℕ),
        (∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ), U ≤ |y|) →
        ∃ c : ℕ → ℝ,
          (∀ j, j < m → c j ∈
            Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ)) ∧
          ‖∫ y in a..(a + (m : ℝ) * Δ),
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                ((1 : ℂ) + (y : ℝ) * I) *
              (routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I))‖ ≤
            ∑ j ∈ Finset.range m, Δ *
              ((65 * C * (N / R) ^ 2 / U ^ 2) *
                ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                  ((1 : ℂ) + (c j : ℝ) * I)‖) := by
  obtain ⟨C, hC, hquad⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_one_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro L X k T0 t N H R U a Δ hN hH hR hHR hRH hRN hU hΔ m haway
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
      ((1 : ℂ) + (y : ℝ) * I)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hA : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line L X k T0 t N 1
  have hK : Continuous K :=
    (continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num))
  have hHleN : H ≤ N := hHR.trans hRN
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hM : ∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ),
      ‖K y‖ ≤ 65 * C * (N / R) ^ 2 / U ^ 2 := by
    intro y hy
    have hyU := haway y hy
    have hy2 : U ^ 2 ≤ |y| ^ 2 := by nlinarith [sq_nonneg (|y| - U)]
    have hqR := hquad N R y hN hR hRN
    have hqH := hquad N H y hN hH hHleN
    have hKR : ‖routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I)‖ ≤
        13 * C * (N / R) ^ 2 / U ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hU)]
      calc
        ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I)‖ * U ^ 2 =
            U ^ 2 * ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I)‖ := by ring
        _ ≤ |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I)‖ :=
          mul_le_mul_of_nonneg_right hy2 (norm_nonneg _)
        _ ≤ 13 * C * (N / R) ^ 2 := hqR
    have hratio : R / H ≤ 2 := (div_le_iff₀ hH).2 hRH
    have hratio0 : 0 ≤ R / H := by positivity
    have hratioSq : (R / H) ^ 2 ≤ 4 := by nlinarith
    have hNH : (N / H) ^ 2 ≤ 4 * (N / R) ^ 2 := by
      have hre : N / H = (N / R) * (R / H) := by field_simp
      rw [hre, mul_pow]
      calc
        (N / R) ^ 2 * (R / H) ^ 2 ≤ (N / R) ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left hratioSq (sq_nonneg (N / R))
        _ = 4 * (N / R) ^ 2 := by ring
    have hKH : ‖routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)‖ ≤
        52 * C * (N / R) ^ 2 / U ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hU)]
      calc
        ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ * U ^ 2 =
            U ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ := by ring
        _ ≤ |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ :=
          mul_le_mul_of_nonneg_right hy2 (norm_nonneg _)
        _ ≤ 13 * C * (N / H) ^ 2 := hqH
        _ ≤ 13 * C * (4 * (N / R) ^ 2) :=
          mul_le_mul_of_nonneg_left hNH (mul_nonneg (by norm_num) hC0)
        _ = 52 * C * (N / R) ^ 2 := by ring
    dsimp only [K]
    calc
      ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * I)‖ ≤
          ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * I)‖ +
            ‖routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * I)‖ :=
        norm_sub_le _ _
      _ ≤ 13 * C * (N / R) ^ 2 / U ^ 2 +
          52 * C * (N / R) ^ 2 / U ^ 2 := add_le_add hKR hKH
      _ = 65 * C * (N / R) ^ 2 / U ^ 2 := by ring
  exact exists_cell_max_norm_intervalIntegral_mul_le hA hK hΔ m hM

/-- Every even collection of cell maxima splits into two globally defined `Δ`-spaced sequences.
Each selected value retains its literal source-cell certificate, and the full cell sum is preserved
exactly.  This is the sequence interface consumed by the selected-cell Route-T receiver. -/
theorem exists_two_gap_sequences_of_cell_sum_bound
    {A : ℝ → ℂ} {a Δ M B : ℝ} (hΔ : 0 < Δ) (n : ℕ)
    {c : ℕ → ℝ}
    (hc : ∀ j, j < 2 * n → c j ∈
      Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ))
    (hB : B ≤ ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖A (c j)‖)) :
    ∃ lam0 lam1 : ℕ → ℝ,
      (∀ i, lam0 i + Δ ≤ lam0 (i + 1)) ∧
      (∀ i, lam1 i + Δ ≤ lam1 (i + 1)) ∧
      (∀ j < n, lam0 j ∈
        Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
          (a + (((2 * j : ℕ) : ℝ) + 1) * Δ)) ∧
      (∀ j < n, lam1 j ∈
        Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
          (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
      B ≤ (∑ j ∈ Finset.range n, Δ * (M * ‖A (lam0 j)‖)) +
        ∑ j ∈ Finset.range n, Δ * (M * ‖A (lam1 j)‖) := by
  obtain ⟨lam0, hgap0, hval0⟩ :=
    exists_gap_sequence_of_cells hΔ hc 0
  obtain ⟨lam1, hgap1, hval1⟩ :=
    exists_gap_sequence_of_cells hΔ hc 1
  have hmem0 : ∀ j < n, lam0 j ∈
      Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
        (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) := by
    intro j hj
    rw [hval0 j (by omega)]
    exact hc (2 * j) (by omega)
  have hmem1 : ∀ j < n, lam1 j ∈
      Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
        (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ) := by
    intro j hj
    rw [hval1 j (by omega)]
    exact hc (2 * j + 1) (by omega)
  refine ⟨lam0, lam1, hgap0, hgap1, hmem0, hmem1, hB.trans_eq ?_⟩
  let g : ℕ → ℝ := fun j => Δ * (M * ‖A (c j)‖)
  calc
    ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖A (c j)‖) =
        ∑ j ∈ Finset.range (2 * n), g j := by rfl
    _ = (∑ j ∈ {j ∈ Finset.range (2 * n) | j % 2 = 0}, g j) +
        ∑ j ∈ {j ∈ Finset.range (2 * n) | ¬(j % 2 = 0)}, g j :=
      (Finset.sum_filter_add_sum_filter_not
        (Finset.range (2 * n)) (fun j => j % 2 = 0) g).symm
    _ = (∑ j ∈ Finset.range n, g (2 * j)) +
        ∑ j ∈ Finset.range n, g (2 * j + 1) := by
      rw [sum_filter_even_eq_sum_range, sum_filter_odd_eq_sum_range]
      have heven : (2 * n + 1) / 2 = n := by omega
      have hodd : (2 * n) / 2 = n := by omega
      rw [heven, hodd]
    _ = (∑ j ∈ Finset.range n, Δ * (M * ‖A (lam0 j)‖)) +
        ∑ j ∈ Finset.range n, Δ * (M * ‖A (lam1 j)‖) := by
      apply congrArg₂ (fun x y : ℝ => x + y)
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hval0 j (by omega)]
        rfl
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hval1 j (by omega)]

/-- The fixed-polylog aggregate envelope upgrades the arbitrary-cutoff adjacent-kernel tail bound
to the actual Route-T signed defect.  Thus defect mass beyond `U` decays like
`fixedPolylog * (N / R)^2 / U`, uniformly over the eligible dyadic aggregate. -/
theorem exists_integral_norm_windowRelevantAggregate_mul_adjacentKernel_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {N H R U : ℝ},
        1 ≤ X → 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                ((1 : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ ≤
          heathBrownWindowRelevantFixedPolylogBound L X k N 1 *
            (130 * C * (N / R) ^ 2 / U) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTAdjacentNormalizedKernel_one_general_tail_le
  refine ⟨C, hC, ?_⟩
  intro L X k T0 t N H R U hX hN hH hR hHR hRH hRN hU
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
      ((1 : ℂ) + (y : ℝ) * I)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k N 1
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  have hA : ∀ y : ℝ, ‖A y‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t N 1 y hN (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hA 0)
  have hKR := integrable_routeTNormalizedSmoothWindowMellin_one hN hR
  have hKH := integrable_routeTNormalizedSmoothWindowMellin_one hN hH
  have hKnorm : Integrable (fun y => ‖K y‖) := by
    exact (hKR.sub hKH).norm
  have hprod : Integrable (fun y => ‖A y * K y‖) := by
    have hAKR := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hR (by norm_num : (0 : ℝ) < 1)
    have hAKH := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hH (by norm_num : (0 : ℝ) < 1)
    simpa only [A, K, mul_sub, Pi.sub_apply, ofReal_one] using (hAKR.sub hAKH).norm
  have hmono : (∫ y in tail, ‖A y * K y‖) ≤
      ∫ y in tail, P * ‖K y‖ := by
    apply setIntegral_mono_on hprod.integrableOn
      (hKnorm.const_mul P).integrableOn
        (measurableSet_le measurable_const continuous_abs.measurable)
    intro y _hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _)
  have hscale : (∫ y in tail, P * ‖K y‖) =
      P * ∫ y in tail, ‖K y‖ := by
    rw [MeasureTheory.integral_const_mul]
  have hktail := htail N H R U hN hH hR hHR hRH hRN hU
  calc
    (∫ y in {y : ℝ | U ≤ |y|},
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((1 : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖) =
        ∫ y in tail, ‖A y * K y‖ := by rfl
    _ ≤ ∫ y in tail, P * ‖K y‖ := hmono
    _ = P * ∫ y in tail, ‖K y‖ := hscale
    _ ≤ P * (130 * C * (N / R) ^ 2 / U) :=
      mul_le_mul_of_nonneg_left (by simpa [tail, K] using hktail) hP
    _ = _ := by rfl

/-- Abstract signed-mass localization: after paying a symmetric low interval and an absolute far
tail, all remaining norm is forced into the intervening two-sided annulus.  Crucially, the middle
term keeps the norm outside its signed integral. -/
theorem norm_setIntegral_annulus_ge_of_low_tail
    {f : ℝ → ℂ} (hf : Integrable f) {B U V E₀ E₁ : ℝ}
    (hU : 0 ≤ U) (hUV : U ≤ V)
    (hfull : B ≤ ‖∫ y : ℝ, f y‖)
    (hlow : ‖∫ y in (-U)..U, f y‖ ≤ E₀)
    (htail : (∫ y in {y : ℝ | V ≤ |y|}, ‖f y‖) ≤ E₁) :
    B - E₀ - E₁ ≤
      ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖ := by
  let TU : Set ℝ := {y : ℝ | U ≤ |y|}
  let TV : Set ℝ := {y : ℝ | V ≤ |y|}
  let M : Set ℝ := {y : ℝ | U ≤ |y| ∧ |y| < V}
  have hTUmeas : MeasurableSet TU := by
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hTVmeas : MeasurableSet TV := by
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hMunion : M ∪ TV = TU := by
    ext y
    simp only [M, TV, TU, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hy | hy)
      · exact hy.1
      · exact hUV.trans hy
    · intro hy
      by_cases hyv : |y| < V
      · exact Or.inl ⟨hy, hyv⟩
      · exact Or.inr (not_lt.mp hyv)
  have hdisj : Disjoint M TV := by
    rw [Set.disjoint_left]
    intro y hyM hyTV
    exact (not_lt_of_ge hyTV) hyM.2
  have htailNorm : ‖∫ y in TV, f y‖ ≤ E₁ := by
    calc
      ‖∫ y in TV, f y‖ ≤ ∫ y in TV, ‖f y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ E₁ := by simpa only [TV] using htail
  have hlowEq : (∫ y in TUᶜ, f y) = ∫ y in (-U)..U, f y := by
    have hcomp : TUᶜ = Set.Ioo (-U) U := by
      ext y
      simp [TU, Set.mem_Ioo, abs_lt]
    rw [hcomp, MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
  have htailSplit : (∫ y in TU, f y) =
      (∫ y in M, f y) + ∫ y in TV, f y := by
    rw [← hMunion]
    exact MeasureTheory.setIntegral_union hdisj hTVmeas hf.integrableOn hf.integrableOn
  have hwholeSplit : (∫ y : ℝ, f y) =
      (∫ y in M, f y) + (∫ y in TV, f y) + ∫ y in TUᶜ, f y := by
    rw [← htailSplit]
    exact (integral_add_compl hTUmeas hf).symm
  have hbound : B ≤ ‖∫ y in M, f y‖ + E₀ + E₁ := calc
    B ≤ ‖∫ y : ℝ, f y‖ := hfull
    _ = ‖(∫ y in M, f y) + (∫ y in TV, f y) + ∫ y in TUᶜ, f y‖ := by rw [hwholeSplit]
    _ ≤ ‖∫ y in M, f y‖ + ‖∫ y in TV, f y‖ + ‖∫ y in TUᶜ, f y‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖∫ y in M, f y‖ + E₁ + E₀ := by
      rw [hlowEq]
      gcongr
    _ = ‖∫ y in M, f y‖ + E₀ + E₁ := by ring
  dsimp only [M] at hbound ⊢
  linarith

/-- Quantitative Route-T annulus localization.  For any adjacent comparable widths, a full signed
defect can lose only `16 * fixedPolylog * (R/N) * U²` in the pole-cancelled low band and only
`130 * C * fixedPolylog * (N/R)² / V` beyond the far cutoff.  The residual signed norm therefore
lives between `U` and `V`. -/
theorem exists_norm_setIntegral_windowRelevantAggregate_mul_adjacentKernel_annulus_ge :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {N H R U V B : ℝ},
        1 ≤ X → 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N →
        0 ≤ U → U ≤ V → 0 < V → U * (2 * R / N) ≤ 1 →
        B ≤ ‖∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                ((1 : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ →
        B - 16 * heathBrownWindowRelevantFixedPolylogBound L X k N 1 *
              (R / N) * U ^ 2 -
            heathBrownWindowRelevantFixedPolylogBound L X k N 1 *
              (130 * C * (N / R) ^ 2 / V) ≤
          ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                  ((1 : ℂ) + (y : ℝ) * I) *
              (routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I))‖ := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_norm_windowRelevantAggregate_mul_adjacentKernel_tail_le
  refine ⟨C, hC, ?_⟩
  intro L X k T0 t N H R U V B hX hN hH hR hHR hRH hRN hU hUV hV hsmall hfull
  let f : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((1 : ℂ) + (y : ℝ) * I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I))
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k N 1
  have hf : Integrable f := by
    have hRint := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hR (by norm_num : (0 : ℝ) < 1)
    have hHint := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hH (by norm_num : (0 : ℝ) < 1)
    exact (hRint.sub hHint).congr (Filter.Eventually.of_forall fun y => by
      simp only [f, Pi.sub_apply, mul_sub, ofReal_one])
  have hlowRaw :=
    norm_intervalIntegral_windowRelevantAggregate_mul_normalizedKernelDefect_le_fixedPolylog
      L X k hX T0 t N H R 1 U hN hH hR hHR (by norm_num) hU (by simpa using hsmall)
  have hlow : ‖∫ y in (-U)..U, f y‖ ≤ 16 * P * (R / N) * U ^ 2 := by
    dsimp only [f, P]
    convert hlowRaw using 1 <;> norm_num <;> ring
  have hfar := htail L X k T0 t hX hN hH hR hHR hRH hRN hV
  have hfar' : (∫ y in {y : ℝ | V ≤ |y|}, ‖f y‖) ≤
      P * (130 * C * (N / R) ^ 2 / V) := by
    simpa only [f, P] using hfar
  exact norm_setIntegral_annulus_ge_of_low_tail hf hU hUV
    (by simpa only [f] using hfull) hlow hfar'

/-- A two-sided annular signed defect has a large signed wing.  Splitting at any intermediate
transition `T`, one of the two central or two outer intervals retains at least one quarter of the
annular norm.  No absolute value is moved inside any interval integral. -/
theorem exists_interval_norm_ge_quarter_of_annulus
    {f : ℝ → ℂ} (hf : Integrable f) {B U T V : ℝ}
    (hU : 0 ≤ U) (hUT : U ≤ T) (hTV : T ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖) :
    B / 4 ≤ ‖∫ y in (-V)..(-T), f y‖ ∨
    B / 4 ≤ ‖∫ y in (-T)..(-U), f y‖ ∨
    B / 4 ≤ ‖∫ y in U..T, f y‖ ∨
    B / 4 ≤ ‖∫ y in T..V, f y‖ := by
  let M : Set ℝ := {y : ℝ | U ≤ |y| ∧ |y| < V}
  let L : Set ℝ := Set.Ioc (-V) (-U)
  let R₀ : Set ℝ := Set.Ico U V
  let R : Set ℝ := Set.Ioc U V
  have hM : M = L ∪ R₀ := by
    ext y
    simp only [M, L, R₀, Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
    rw [abs_lt, le_abs]
    constructor
    · rintro ⟨hyU, hyV⟩
      rcases hyU with hypos | hyneg
      · exact Or.inr ⟨hypos, hyV.2⟩
      · exact Or.inl ⟨hyV.1, by linarith⟩
    · rintro (hyneg | hypos)
      · exact ⟨Or.inr (by linarith), ⟨hyneg.1, by linarith⟩⟩
      · exact ⟨Or.inl hypos.1, ⟨by linarith, hypos.2⟩⟩
  have hdisj : Disjoint L R := by
    rw [Set.disjoint_left]
    intro y hyL hyR
    rcases hyL with ⟨_hyL, hyneg⟩
    rcases hyR with ⟨hypos, _hyR⟩
    linarith
  have hsplit : (∫ y in M, f y) =
      (∫ y in (-V)..(-U), f y) + ∫ y in U..V, f y := by
    rw [hM]
    have hcongr : (∫ y in L ∪ R₀, f y) = ∫ y in L ∪ R, f y := by
      apply MeasureTheory.setIntegral_congr_set
      filter_upwards [MeasureTheory.Ico_ae_eq_Ioc (a := U) (b := V)] with y hy
      change (y ∈ L ∨ y ∈ Set.Ico U V) = (y ∈ L ∨ y ∈ Set.Ioc U V)
      exact congrArg (fun q : Prop => (y ∈ L) ∨ q) hy
    rw [hcongr, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      hf.integrableOn hf.integrableOn]
    rw [intervalIntegral.integral_of_le (by linarith : -V ≤ -U),
      intervalIntegral.integral_of_le (hUT.trans hTV)]
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (f := f) (a := -V) (b := -T) (c := -U)
    hf.intervalIntegrable hf.intervalIntegrable
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (f := f) (a := U) (b := T) (c := V)
    hf.intervalIntegrable hf.intervalIntegrable
  rw [← hleft, ← hright] at hsplit
  by_contra hall
  push Not at hall
  have hB' : B ≤ ‖∫ y in M, f y‖ := by simpa only [M] using hB
  have hnorm : B ≤
      ‖((∫ y in (-V)..(-T), f y) + ∫ y in (-T)..(-U), f y) +
        ((∫ y in U..T, f y) + ∫ y in T..V, f y)‖ := by
    rw [← hsplit]
    exact hB'
  have hsum :
      (‖∫ y in (-V)..(-T), f y‖ + ‖∫ y in (-T)..(-U), f y‖) +
          (‖∫ y in U..T, f y‖ + ‖∫ y in T..V, f y‖) < B := by
    linarith
  have hpair :
      ‖(∫ y in (-V)..(-T), f y) + ∫ y in (-T)..(-U), f y‖ +
          ‖(∫ y in U..T, f y) + ∫ y in T..V, f y‖ < B := by
    refine lt_of_le_of_lt (add_le_add (norm_add_le _ _) (norm_add_le _ _)) hsum
  exact (not_lt_of_ge (hnorm.trans (norm_add_le _ _))) hpair

end RHTower.Sieve
