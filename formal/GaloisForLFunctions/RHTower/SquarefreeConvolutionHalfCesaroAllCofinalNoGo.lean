import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroPowerScheduleNoGo
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfAnchoredCountertermNoGo
import Mathlib.Data.Nat.Sqrt

/-!
# Every cofinal Cesàro schedule is impossible

The schedule-independent gate isolated by the Cesàro source criterion is itself impossible: the
triangular Cesàro means cannot converge to zero at `s = 6/11`.

Indeed, if `C_N → 0`, then the second primitive `B_N = N C_N` is eventually bounded by `N`.
Average the raw partial sum `D_N` over a backward block of length `k^3`, where
`k = sqrt (sqrt N)`.  The primitive controls the block average, while
`‖D_N - D_j‖` is controlled by coefficient decay `n^{-6/11} ≤ n^{-1/2}`.  Since this block stays
above `(k(k-1))^2`, the resulting discrete Landau interpolation bound is
`‖D_N‖ ≤ 34 k ≤ 34 N^{1/3}`.  This contradicts the already-proved polynomial Abel obstruction,
whose threshold at `6/11` is `5/11`.

Consequently no cofinal Cayley pole-factor schedule can make the canonical Cesàro source locally
bounded.  The argument is complex-valued and uses no coefficient-reality or positivity input.
-/

open Complex Filter Metric Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem norm_squarefreeHalf_term_boundary_le_two_div_sq
    {k n : ℕ} (hk : 2 ≤ k) (hn : (k * (k - 1)) ^ 2 ≤ n) :
    ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n‖ ≤
      2 / (k : ℝ) ^ 2 := by
  have hn0 : n ≠ 0 := by
    exact Nat.ne_zero_of_lt ((pow_pos
      (Nat.mul_pos (by omega : 0 < k) (by omega : 0 < k - 1)) 2).trans_le hn)
  rw [LSeries.norm_term_eq, if_neg hn0]
  have hn1Nat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1Nat
  have hexp : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (6 / 11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hm0 : (0 : ℝ) ≤ (k * (k - 1) : ℕ) := by positivity
  have hn0r : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hm : ((k * (k - 1) : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt hm0 hn0r]
    exact_mod_cast hn
  have hden : ((k * (k - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ (6 / 11 : ℝ) := by
    calc
      ((k * (k - 1) : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := hm
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ (n : ℝ) ^ (6 / 11 : ℝ) := hexp
  have hmpos : (0 : ℝ) < ((k * (k - 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < k) (by omega : 0 < k - 1))
  have hdenpos : 0 < (n : ℝ) ^ (6 / 11 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hcoeff : ‖squarefreeConvolutionHalf n‖ ≤ 1 :=
    norm_squarefreeConvolutionHalf_le_one n
  calc
    ‖squarefreeConvolutionHalf n‖ / (n : ℝ) ^ boundaryExteriorPoint.re ≤
        1 / (n : ℝ) ^ (6 / 11 : ℝ) := by
      norm_num [boundaryExteriorPoint]
      simpa [one_div] using div_le_div_of_nonneg_right hcoeff hdenpos.le
    _ ≤ 1 / ((k * (k - 1) : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hmpos hden
    _ ≤ 2 / (k : ℝ) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hk1pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      rw [div_le_div_iff₀ (mul_pos hkpos hk1pos) (sq_pos_of_pos hkpos)]
      nlinarith only [hkreal]

private theorem norm_squarefreeHalf_partialSum_sub_boundary_le
    {k j N : ℕ} (hk : 2 ≤ k) (hbase : (k * (k - 1)) ^ 2 ≤ j)
    (hjN : j ≤ N) :
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint -
        squarefreeHalfDirichletPartialSum j boundaryExteriorPoint‖ ≤
      (N - j : ℕ) * (2 / (k : ℝ) ^ 2) := by
  rw [squarefreeHalfDirichletPartialSum, squarefreeHalfDirichletPartialSum,
    ← Finset.sum_Ico_eq_sub _ hjN]
  calc
    ‖∑ n ∈ Finset.Ico j N,
        LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n‖ ≤
        ∑ n ∈ Finset.Ico j N,
          ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico j N, (2 / (k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_squarefreeHalf_term_boundary_le_two_div_sq hk
        (hbase.trans (Finset.mem_Ico.mp hn).1)
    _ = (N - j : ℕ) * (2 / (k : ℝ) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]

private theorem fourthRootBlock_spec {Q N : ℕ} (hQ2 : 2 ≤ Q) (hN : Q ^ 4 ≤ N) :
    let r := Nat.sqrt N
    let k := Nat.sqrt r
    let L := k ^ 3
    let a := N - L
    Q ≤ k ∧ k ^ 4 ≤ N ∧ N ≤ 16 * k ^ 4 ∧ L ≤ N ∧
      (k * (k - 1)) ^ 2 ≤ a ∧ k ≤ (k * (k - 1)) ^ 2 ∧ a ≤ N := by
  dsimp only
  let r : ℕ := Nat.sqrt N
  let k : ℕ := Nat.sqrt r
  have hQ2r : Q ^ 2 ≤ r := by
    dsimp [r]
    rw [Nat.le_sqrt]
    simpa [pow_succ, pow_two, mul_assoc] using hN
  have hQk : Q ≤ k := by
    dsimp [k]
    rw [Nat.le_sqrt]
    simpa [pow_two] using hQ2r
  have hk2 : 2 ≤ k := hQ2.trans hQk
  have hkr : k * k ≤ r := by
    dsimp [k]
    exact Nat.sqrt_le r
  have hrN : r * r ≤ N := by
    dsimp [r]
    exact Nat.sqrt_le N
  have hk4N : k ^ 4 ≤ N := by
    calc
      k ^ 4 = (k * k) * (k * k) := by ring
      _ ≤ r * r := Nat.mul_le_mul hkr hkr
      _ ≤ N := hrN
  have hNupper : N ≤ 16 * k ^ 4 := by
    have hNr : N < (r + 1) * (r + 1) := by
      simpa [r] using Nat.lt_succ_sqrt N
    have hrk : r < (k + 1) * (k + 1) := by
      simpa [k] using Nat.lt_succ_sqrt r
    calc
      N ≤ (r + 1) ^ 2 := by
        simpa [pow_two] using Nat.le_of_lt hNr
      _ ≤ ((k + 1) ^ 2) ^ 2 := by
        gcongr
        simpa [pow_two] using hrk
      _ = (k + 1) ^ 4 := by ring
      _ ≤ (2 * k) ^ 4 := by
        gcongr
        omega
      _ = 16 * k ^ 4 := by ring
  have hLN : k ^ 3 ≤ N := by
    calc
      k ^ 3 = k ^ 3 * 1 := by simp
      _ ≤ k ^ 3 * k := Nat.mul_le_mul_left _ (by omega)
      _ = k ^ 4 := by ring
      _ ≤ N := hk4N
  have hpoly : (k * (k - 1)) ^ 2 + k ^ 3 ≤ k ^ 4 := by
    have hkdecomp : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    calc
      (k * (k - 1)) ^ 2 + k ^ 3 =
          k ^ 2 * (k - 1) ^ 2 + k ^ 3 := by ring
      _ ≤ k ^ 2 * ((k - 1) * k) + k ^ 3 := by
        gcongr
        simpa [pow_two] using Nat.mul_le_mul_left (k - 1) (by omega : k - 1 ≤ k)
      _ = k ^ 3 * ((k - 1) + 1) := by ring
      _ = k ^ 4 := by rw [hkdecomp]; ring
  have hbase : (k * (k - 1)) ^ 2 ≤ N - k ^ 3 :=
    Nat.le_sub_of_add_le (hpoly.trans hk4N)
  have hkbase : k ≤ (k * (k - 1)) ^ 2 := by
    have hkminus : 1 ≤ k - 1 := by omega
    have hmone : 1 ≤ k * (k - 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc
      k = k * 1 := by simp
      _ ≤ k * (k - 1) := Nat.mul_le_mul_left k hkminus
      _ = 1 * (k * (k - 1)) := by simp
      _ ≤ (k * (k - 1)) * (k * (k - 1)) := Nat.mul_le_mul_right _ hmone
      _ = (k * (k - 1)) ^ 2 := by ring
  exact ⟨hQk, hk4N, hNupper, hLN, hbase, hkbase, Nat.sub_le _ _⟩

/-- The triangular Cesàro source cannot vanish at the exterior point. -/
theorem not_tendsto_squarefreeHalfCesaroSum_boundaryExteriorPoint_zero :
    ¬ Tendsto (fun N => squarefreeHalfCesaroSum N boundaryExteriorPoint)
      atTop (𝓝 0) := by
  intro hzero
  have hsmall : ∀ᶠ N : ℕ in atTop,
      squarefreeHalfCesaroSum N boundaryExteriorPoint ∈ ball (0 : ℂ) 1 :=
    hzero.eventually (ball_mem_nhds (0 : ℂ) (by norm_num))
  rw [eventually_atTop] at hsmall
  obtain ⟨N₀, hN₀⟩ := hsmall
  have hCesaro : ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ 1 := by
    intro N hN
    have h := hN₀ N hN
    have hlt : ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using h
    exact hlt.le
  apply not_exists_eventual_poly_bound_squarefreeHalfDirichletPartialSum
    (sigma := (6 / 11 : ℝ)) (alpha := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  let Q : ℕ := max 2 N₀
  refine ⟨34, by norm_num, Q ^ 4, fun N hN => ?_⟩
  rw [show ((6 / 11 : ℝ) : ℂ) = boundaryExteriorPoint by
    norm_num [boundaryExteriorPoint]]
  let r : ℕ := Nat.sqrt N
  let k : ℕ := Nat.sqrt r
  let L : ℕ := k ^ 3
  let a : ℕ := N - L
  have hQ2 : 2 ≤ Q := le_max_left _ _
  have hQN₀ : N₀ ≤ Q := le_max_right _ _
  obtain ⟨hQk, hk4N, hNupper, hLN, hbase, hkbase, haN⟩ :=
    fourthRootBlock_spec hQ2 hN
  have hk2 : 2 ≤ k := hQ2.trans hQk
  have hkN₀ : N₀ ≤ k := hQN₀.trans hQk
  have haN₀ : N₀ ≤ a := by
    exact hkN₀.trans (hkbase.trans hbase)
  have hcard : (Finset.Ico a N).card = L := by
    rw [Nat.card_Ico]
    dsimp [a]
    exact Nat.sub_sub_self hLN
  have hkN : k ≤ N := by
    have hkk : 1 ≤ k * k := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    calc
      k = k * 1 := by simp
      _ ≤ k * (k * k) := Nat.mul_le_mul_left k hkk
      _ = k ^ 3 := by ring
      _ ≤ N := hLN
  have hNN₀ : N₀ ≤ N := hkN₀.trans hkN
  let D : ℕ → ℂ := fun m =>
    squarefreeHalfDirichletPartialSum m boundaryExteriorPoint
  let B : ℕ → ℂ := fun m =>
    (m : ℂ) * squarefreeHalfCesaroSum m boundaryExteriorPoint
  have hBN : ‖B N‖ ≤ (N : ℝ) := by
    dsimp [B]
    rw [norm_mul, Complex.norm_natCast]
    calc
      (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
          (N : ℝ) * 1 := mul_le_mul_of_nonneg_left
            (hCesaro N hNN₀) (by positivity)
      _ = N := by ring
  have hBa : ‖B a‖ ≤ (a : ℝ) := by
    dsimp [B]
    rw [norm_mul, Complex.norm_natCast]
    calc
      (a : ℝ) * ‖squarefreeHalfCesaroSum a boundaryExteriorPoint‖ ≤
          (a : ℝ) * 1 := mul_le_mul_of_nonneg_left
            (hCesaro a haN₀) (by positivity)
      _ = a := by ring
  have hsumD : ∑ j ∈ Finset.Ico a N, D j = B N - B a := by
    dsimp [D, B]
    rw [Finset.sum_Ico_eq_sub _ haN,
      ← natCast_mul_squarefreeHalfCesaroSum,
      ← natCast_mul_squarefreeHalfCesaroSum]
  have hdiff : ∀ j ∈ Finset.Ico a N, ‖D N - D j‖ ≤ 2 * (k : ℝ) := by
    intro j hj
    have hjN : j ≤ N := (Finset.mem_Ico.mp hj).2.le
    have hjbase : (k * (k - 1)) ^ 2 ≤ j :=
      hbase.trans (Finset.mem_Ico.mp hj).1
    have hraw := norm_squarefreeHalf_partialSum_sub_boundary_le hk2 hjbase hjN
    have hlength : N - j ≤ L := by
      have hja : a ≤ j := (Finset.mem_Ico.mp hj).1
      dsimp [a] at hja
      omega
    calc
      ‖D N - D j‖ ≤ (N - j : ℕ) * (2 / (k : ℝ) ^ 2) := by
        simpa [D] using hraw
      _ ≤ (L : ℕ) * (2 / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlength) (by positivity)
      _ = 2 * (k : ℝ) := by
        dsimp [L]
        push_cast
        field_simp
  have hdiffsum :
      ‖∑ j ∈ Finset.Ico a N, (D N - D j)‖ ≤ 2 * (k : ℝ) ^ 4 := by
    calc
      ‖∑ j ∈ Finset.Ico a N, (D N - D j)‖ ≤
          ∑ j ∈ Finset.Ico a N, ‖D N - D j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.Ico a N, (2 * (k : ℝ)) := by
        apply Finset.sum_le_sum
        exact hdiff
      _ = 2 * (k : ℝ) ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        dsimp [L]
        push_cast
        ring
  have hidentity :
      (L : ℂ) * D N =
        (B N - B a) + ∑ j ∈ Finset.Ico a N, (D N - D j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hsumD]
    ring
  have hmult : (L : ℝ) * ‖D N‖ ≤ 34 * (k : ℝ) ^ 4 := by
    calc
      (L : ℝ) * ‖D N‖ = ‖(L : ℂ) * D N‖ := by simp
      _ = ‖(B N - B a) + ∑ j ∈ Finset.Ico a N, (D N - D j)‖ := by
        rw [hidentity]
      _ ≤ ‖B N - B a‖ + ‖∑ j ∈ Finset.Ico a N, (D N - D j)‖ :=
        norm_add_le _ _
      _ ≤ (‖B N‖ + ‖B a‖) + 2 * (k : ℝ) ^ 4 :=
        add_le_add (norm_sub_le _ _) hdiffsum
      _ ≤ ((N : ℝ) + (a : ℝ)) + 2 * (k : ℝ) ^ 4 :=
        add_le_add (add_le_add hBN hBa) le_rfl
      _ ≤ 34 * (k : ℝ) ^ 4 := by
        have haNreal : (a : ℝ) ≤ N := by exact_mod_cast haN
        have hNupperReal : (N : ℝ) ≤ 16 * (k : ℝ) ^ 4 := by
          exact_mod_cast hNupper
        linarith only [haNreal, hNupperReal]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hDk : ‖D N‖ ≤ 34 * (k : ℝ) := by
    calc
      ‖D N‖ ≤ (34 * (k : ℝ) ^ 4) / (L : ℝ) :=
        (le_div_iff₀ (by dsimp [L]; positivity)).2 (by simpa [mul_comm] using hmult)
      _ = 34 * (k : ℝ) := by
        dsimp [L]
        push_cast
        field_simp
  have hk3N : k ^ 3 ≤ N := by
    simpa [L] using hLN
  have hkrpow : (k : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
      Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
    norm_num
    exact_mod_cast hk3N
  exact hDk.trans (mul_le_mul_of_nonneg_left hkrpow (by norm_num))

/-- Every cofinal pole-factor schedule is incompatible with local boundedness of the canonical
Cesàro source. -/
theorem no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_cofinal
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCesaroScheduledLocallyBounded kappa :=
  no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_not_tendsto_zero
    hkappa not_tendsto_squarefreeHalfCesaroSum_boundaryExteriorPoint_zero

end

end RHTower
