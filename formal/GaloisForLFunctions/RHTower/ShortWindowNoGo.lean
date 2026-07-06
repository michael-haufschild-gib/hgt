/-
Global vacuity of the sharp mean-value energy face at pinning windows.

The pinning geometry of the window certificates confines the anchor window inside a
disc of radius below `1/2`, so its length satisfies `U < 1`.  At such lengths the
sharp-carrier mean-value energy face is false for every depth `N ≥ 4`: the adjacent
pairs `(m, m+1)` alone contribute at least `N − 1` to the off-diagonal sum (each such
term is `≥ 1`, since `log(1+1/m) ≤ 1/m` and `√(m(m+1)) ≤ 2m`), while the diagonal
supply is at most `U·(1 + log N) ≤ 1 + log N < N − 1` once `N ≥ 4`.  Consequently every
window certificate that draws its carrier anchor from the sharp mean-value budget
admits witnesses only at depth `N ≤ 3`: the certificate family is globally vacuous
beyond that depth, and a carrier anchor at pinning windows must come from coefficient
designs whose off-diagonal is controlled, not from the sharp truncation.
-/
import GaloisForLFunctions.RHTower.HardyCarrier

open MeasureTheory

namespace RHTower

/-- Harmonic upper bound: `Σ_{n≤N} 1/n ≤ 1 + log N`. -/
theorem harmonic_Icc_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) ≤ 1 + Real.log N := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h0 : N = 0
    · subst h0
      simp [Finset.Icc_self]
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr h0
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hlogstep : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ≤
          Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) := by
        have hlog := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < (N : ℝ) / ((N + 1 : ℕ) : ℝ) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        have heq : (N : ℝ) / ((N + 1 : ℕ) : ℝ) - 1 = -(1 / ((N + 1 : ℕ) : ℝ)) := by
          field_simp
          push_cast
          ring
        rw [heq] at hlog
        linarith
      have hih := ih hN1
      linarith

/-- The sharp diagonal is the harmonic sum. -/
theorem sharp_diagonal_eq_harmonic (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  rw [sq, ← Real.rpow_add hpos]
  have harg : (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = -1 := by norm_num
  rw [harg, Real.rpow_neg_one, one_div]

private lemma adjacent_term_ge_one (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) ≤ 2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))| /
      |Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm10 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hx : (m : ℝ) ^ (-(1 / 2 : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      1 / (Real.sqrt m * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hm0.le, Real.rpow_neg hm10.le, Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ← mul_inv, ← one_div]
  have hL0 : 0 < Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
    have := Real.log_lt_log hm0 (show (m : ℝ) < ((m + 1 : ℕ) : ℝ) by push_cast; linarith)
    linarith
  have hLle : Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ 1 / m := by
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have heq : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by
      field_simp
      push_cast
      ring
    linarith
  have hsqrt : Real.sqrt m * Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * m := by
    rw [← Real.sqrt_mul hm0.le]
    calc Real.sqrt ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) ≤ Real.sqrt ((2 * m) ^ 2) := by
          apply Real.sqrt_le_sqrt
          push_cast
          nlinarith
      _ = 2 * m := Real.sqrt_sq (by positivity)
  have habs : |(m : ℝ) ^ (-(1 / 2 : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))| =
      1 / (Real.sqrt m * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [hx, abs_of_pos (by positivity)]
  rw [habs, abs_of_pos hL0, le_div_iff₀ hL0, one_mul]
  have hs0 : (0 : ℝ) < Real.sqrt m * Real.sqrt ((m + 1 : ℕ) : ℝ) := by positivity
  have h2 : (1 : ℝ) / m ≤ 2 * (1 / (Real.sqrt m * Real.sqrt ((m + 1 : ℕ) : ℝ))) := by
    rw [mul_one_div, div_le_div_iff₀ hm0 hs0]
    linarith
  linarith

/-- **Adjacent-pair floor for the sharp off-diagonal**: the mean-value off-diagonal sum
of the sharp coefficients is at least `N − 1`. -/
theorem sharp_offDiagonal_ge (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) - 1 ≤
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
          / |Real.log n - Real.log m| := by
  have hnn : ∀ m n : ℕ, 0 ≤ 2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
      / |Real.log n - Real.log m| := fun m n => by positivity
  have hsub : (∑ m ∈ Finset.Ico 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
          / |Real.log n - Real.log m|) ≤
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
          / |Real.log n - Real.log m| :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
      (fun i _ _ => Finset.sum_nonneg fun n _ => hnn i n)
  have hkey : ∀ m ∈ Finset.Ico 1 N, (1 : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
          / |Real.log n - Real.log m| := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Ico.mp hm
    have hmem : m + 1 ∈ (Finset.Icc 1 N).erase m := by
      rw [Finset.mem_erase]
      exact ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    exact le_trans (adjacent_term_ge_one m hm1)
      (Finset.single_le_sum (fun n _ => hnn m n) hmem)
  have hcount : (N : ℝ) - 1 ≤
      ∑ m ∈ Finset.Ico 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
          / |Real.log n - Real.log m| := by
    calc (N : ℝ) - 1 = ∑ _m ∈ Finset.Ico 1 N, (1 : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
            Nat.cast_sub hN, Nat.cast_one]
      _ ≤ _ := Finset.sum_le_sum hkey
  linarith

/-- **Global falsity of the sharp energy face at short windows.**  For every depth
`N ≥ 4` and every window of length `U ≤ 1`, the sharp mean-value energy budget is
contradictory: the adjacent-pair off-diagonal floor `N − 1` exceeds the harmonic
diagonal supply `U·(1 + log N)`. -/
theorem sharp_energy_face_false_short_window {N : ℕ} (hN : 4 ≤ N) {T U m_J : ℝ}
    (hU0 : 0 < U) (hU1 : U ≤ 1)
    (henergy : m_J ^ 2 * U +
        (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
      4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)) : False := by
  have hint : 0 ≤ ∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => by positivity)
  have hmJ : 0 ≤ m_J ^ 2 * U := mul_nonneg (sq_nonneg _) hU0.le
  have hH0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hharm := harmonic_Icc_le_one_add_log N (by omega)
  have hoff := sharp_offDiagonal_ge N (by omega)
  rw [sharp_diagonal_eq_harmonic N] at henergy
  have hX : (N : ℝ) - 1 < U * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) := by linarith
  have hUH : U * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) ≤
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by nlinarith
  have hN0 : (0 : ℝ) < N := by positivity
  have hlogN : Real.log N ≤ 2 * Real.sqrt N - 2 := by
    have hs := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < Real.sqrt N from Real.sqrt_pos.mpr hN0)
    rw [Real.log_sqrt hN0.le] at hs
    linarith
  have hsqrtN : 2 ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 from by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hNsq : (N : ℝ) = Real.sqrt N * Real.sqrt N :=
    (Real.mul_self_sqrt hN0.le).symm
  have hfinal : (N : ℝ) < 2 * Real.sqrt N := by linarith
  nlinarith [hsqrtN, hNsq, Real.sqrt_nonneg (N : ℝ)]

/-- **The pinning geometry forces short windows.**  The quadratic containment face and
the radii chain confine the anchor window to length `U < 1`. -/
theorem pinning_geometry_short_window {ρ : ℂ} {T U rz R P RJ : ℝ}
    (hrz0 : 0 < rz) (hrzR : rz < R) (hRP : R ≤ P) (hPrz : P + rz ≤ RJ)
    (hRJ12 : RJ < 1 / 2)
    (hquad : (ρ.re - 1 / 2) ^ 2 +
      (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2) :
    U < 1 := by
  have hRrz0 : 0 < R - rz := by linarith
  have hRrz : R - rz < 1 / 2 := by linarith
  have hmax0 : 0 ≤ max |ρ.im - T| |ρ.im - (T + U)| :=
    le_trans (abs_nonneg (ρ.im - T)) (le_max_left _ _)
  have hmax : max |ρ.im - T| |ρ.im - (T + U)| < R - rz := by
    nlinarith [sq_nonneg (ρ.re - 1 / 2)]
  have h1 : |ρ.im - T| < R - rz := lt_of_le_of_lt (le_max_left _ _) hmax
  have h2 : |ρ.im - (T + U)| < R - rz := lt_of_le_of_lt (le_max_right _ _) hmax
  have hU2 : U ≤ |ρ.im - T| + |ρ.im - (T + U)| := by
    have h3 : U = (ρ.im - T) - (ρ.im - (T + U)) := by ring
    calc U ≤ |(ρ.im - T) - (ρ.im - (T + U))| := by
          rw [← h3]
          exact le_abs_self U
      _ ≤ |ρ.im - T| + |ρ.im - (T + U)| := by
          rw [sub_eq_add_neg]
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_neg]
  linarith

/-- **Global depth bound for MV-anchored pinning certificates.**  Any window
certificate carrying both the pinning geometry and the sharp mean-value energy face
has depth `N ≤ 3`: the whole sharp-anchored certificate family is vacuous beyond
that depth, at every zero and every height. -/
theorem sharp_pinning_certificate_depth_lt_four {N : ℕ} {ρ : ℂ}
    {T U rz R P RJ m_J : ℝ}
    (hU0 : 0 < U) (hrz0 : 0 < rz) (hrzR : rz < R) (hRP : R ≤ P)
    (hPrz : P + rz ≤ RJ) (hRJ12 : RJ < 1 / 2)
    (hquad : (ρ.re - 1 / 2) ^ 2 +
      (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2)
    (henergy : m_J ^ 2 * U +
        (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
      4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)) : N < 4 := by
  by_contra hcon
  rw [not_lt] at hcon
  exact sharp_energy_face_false_short_window hcon hU0
    (pinning_geometry_short_window hrz0 hrzR hRP hPrz hRJ12 hquad).le henergy

end RHTower
