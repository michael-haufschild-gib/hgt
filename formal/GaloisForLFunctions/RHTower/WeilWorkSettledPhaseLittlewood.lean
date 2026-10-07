import GaloisForLFunctions.RHTower.WeilProducerLittlewoodBound

/-!
# A source-wide Littlewood bound for WP05

The coefficient bound in `exists_re_producerLogZeta_le_littlewood` is unnecessary:
absolute summability at two bounds a shorter Dirichlet polynomial. Every full-positive
system therefore has `Re log F(σ+it) = O(log |t| / log log |t|)` uniformly for
`1/2 < σ ≤ 2`. No atomicity, coefficient-growth, or settlement premise is added.

This supplies a quantitative source-growth estimate; it does not prove phase settlement.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilWorkSettledPhase

open WeilSpectral WeilHerglotz

/-- Absolute summability at two controls the short polynomial without a pointwise
coefficient bound. -/
theorem re_producerPoly_div_le_mass {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 0 ≤ s.re) :
    (producerPoly lam L s).re / L ≤
      ((∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) / Real.log 2) * Real.exp (2 * L) := by
  set w : ℕ → ℝ := fun n => |lam n| / (n : ℝ) ^ (2 : ℝ)
  have hw : Summable w := WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW
    (by norm_num : (1 : ℝ) < 2)
  have hw0 : ∀ n, 0 ≤ w n := fun n => by dsimp [w]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : ∀ n ∈ Finset.range ⌈Real.exp L⌉₊,
      ‖LSeries.term (lamC lam) s n * ((max (L - Real.log n) 0 : ℝ) : ℂ) /
        Real.log n‖ ≤ w n * (Real.exp (2 * L) * L / Real.log 2) := by
    intro n hn
    rcases lt_or_ge n 2 with hn2 | hn2
    · rw [term_lamC_eq_zero_of_lt lam s hn2]
      simp only [zero_mul, zero_div, norm_zero]
      exact mul_nonneg (hw0 n) (by positivity)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num)
      (by exact_mod_cast hn2)
    have hlog0 : 0 < Real.log n := hl2.trans_le hlog
    have hnexp : (n : ℝ) < Real.exp L := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    have hnpow : (n : ℝ) ^ (2 : ℝ) ≤ Real.exp (2 * L) := by
      rw [Real.rpow_two, show Real.exp (2 * L) = Real.exp L ^ 2 by
        rw [pow_two, ← Real.exp_add]; congr 1; ring]
      exact pow_le_pow_left₀ hn0.le hnexp.le 2
    have hterm : ‖LSeries.term (lamC lam) s n‖ ≤ |lam n| := by
      simpa using norm_term_lamC_le lam hs n
    have hmass : |lam n| ≤ w n * Real.exp (2 * L) := by
      calc |lam n| = w n * (n : ℝ) ^ (2 : ℝ) := by
              dsimp [w]; rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn0 _).ne']
        _ ≤ w n * Real.exp (2 * L) := mul_le_mul_of_nonneg_left hnpow (hw0 n)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right _ _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlog0]
    have hmax : max (L - Real.log n) 0 ≤ L := max_le (by linarith) hL.le
    calc ‖LSeries.term (lamC lam) s n‖ * max (L - Real.log n) 0 / Real.log n
        ≤ (w n * Real.exp (2 * L)) * L / Real.log 2 := by
          gcongr
          exact hterm.trans hmass
      _ = w n * (Real.exp (2 * L) * L / Real.log 2) := by ring
  have hnorm : ‖producerPoly lam L s‖ ≤
      (∑' n, w n) * (Real.exp (2 * L) * L / Real.log 2) := by
    rw [producerPoly_eq_sum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ht).trans ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hw.sum_le_tsum _ (fun n _ => hw0 n)) (by positivity)
  rw [div_le_iff₀ hL]
  exact (Complex.re_le_norm _).trans (hnorm.trans_eq (by dsimp [w]; ring))

/-- Littlewood's bound from full positivity alone. The summability used in its proof
is derived from the original source; no pointwise coefficient estimate is assumed. -/
theorem exists_re_producerLogZeta_le_littlewood_full {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C T₀ : ℝ, 0 < C ∧ ∀ σ t : ℝ, T₀ ≤ |t| → 1 / 2 < σ → σ ≤ 2 →
      (producerLogZeta hW σ t).re ≤ C * Real.log |t| / Real.log (Real.log |t|) := by
  set M : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)
  have hM : 0 ≤ M := tsum_nonneg fun n => by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ : ℝ := M / (2 * Real.log 2)
  have hκ : 0 ≤ κ := div_nonneg hM (by positivity)
  refine ⟨4 * (4 * κ + M + 9), Real.exp (Real.exp 8), by positivity,
    fun σ t ht hσ hσ2 => ?_⟩
  have he8 : (9 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp 8]
  have ht4 : 4 ≤ |t| := by
    have := Real.add_one_le_exp (Real.exp 8)
    linarith
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht4; linarith
  set y : ℝ := Real.log |t|
  have hy8 : Real.exp 8 ≤ y := by
    rw [show y = Real.log |t| from rfl, Real.le_log_iff_exp_le (by linarith)]
    exact ht
  have hy1 : 1 < y := by linarith
  set ell : ℝ := Real.log y
  have hell8 : 8 ≤ ell := by
    rw [show ell = Real.log y from rfl, Real.le_log_iff_exp_le (by linarith)]
    exact hy8
  set L : ℝ := ell / 4
  have hL2 : 2 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by linarith
  have hLell : L ≤ ell := by dsimp [L]; linarith
  have hellpos : 0 < ell := by linarith
  set σ₀ : ℝ := max σ (1 / 2 + 1 / L)
  have hσσ₀ : σ ≤ σ₀ := le_max_left _ _
  have hσ₀2 : σ₀ ≤ 2 := max_le hσ2 (by
    have : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL2
    linarith)
  have hσ₀ge : 1 / 2 + 1 / L ≤ σ₀ := le_max_right _ _
  have hlam1 : 1 ≤ (σ₀ - 1 / 2) * L := by
    have : 1 / L * L = 1 := by field_simp
    have := mul_le_mul_of_nonneg_right (by linarith : 1 / L ≤ σ₀ - 1 / 2) hLpos.le
    linarith
  have hlamb : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ (σ₀ - 1 / 2) * L := by
    have : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hmain := re_producerLogZeta_le hW hσ hσσ₀ hσ₀2 ht0 hLpos hlamb
  have hP1 : (producerPoly lam L ((σ₀ : ℂ) + t * I)).re / L ≤ 2 * κ * Real.sqrt y := by
    have h := re_producerPoly_div_le_mass hW hLpos (s := (σ₀ : ℂ) + t * I)
      (by simp; linarith)
    have hsq : Real.exp (2 * L) = Real.sqrt y := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
      congr 1
      dsimp [L, ell]; ring
    rw [hsq] at h
    exact h.trans_eq (by dsimp [κ, M]; ring)
  have hU : ∀ u : ℝ, 1 / 2 < u → u ≤ 2 → (archU ((u : ℂ) + t * I)).re ≤ y / 2 + 3 :=
    fun u hu hu2 => re_archU_le (by linarith) hu2 ht4
  have hP2 : (archU ((σ₀ : ℂ) + t * I)).re / L ≤ (y / 2 + 3) / L :=
    div_le_div_of_nonneg_right (hU σ₀ (by linarith) hσ₀2) hLpos.le
  have hdiff : σ₀ - σ ≤ 1 / L := by
    rcases le_total σ (1 / 2 + 1 / L) with h | h
    · rw [show σ₀ = max σ (1 / 2 + 1 / L) from rfl, max_eq_right h]; linarith
    · rw [show σ₀ = max σ (1 / 2 + 1 / L) from rfl, max_eq_left h]
      have : 0 < 1 / L := by positivity
      linarith
  have hP3 : (∫ u in σ..σ₀, (archU ((u : ℂ) + t * I)).re) ≤ (y / 2 + 3) / L := by
    have hc := continuousOn_archU_horizontal hW hσ (by linarith : 1 / 2 < σ₀) ht0
    have hint := (Complex.continuous_re.comp_continuousOn hc).intervalIntegrable (μ := volume)
    have h1 := intervalIntegral.integral_mono_on hσσ₀ hint
      (intervalIntegrable_const (c := y / 2 + 3)) fun u hu =>
        hU u (by linarith [hu.1]) (hu.2.trans hσ₀2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    calc _ ≤ (σ₀ - σ) * (y / 2 + 3) := h1
      _ ≤ 1 / L * (y / 2 + 3) := mul_le_mul_of_nonneg_right hdiff (by linarith)
      _ = (y / 2 + 3) / L := by ring
  have hexp : Real.exp L ≤ |t| := by
    calc Real.exp L ≤ Real.exp ell := Real.exp_le_exp.mpr hLell
      _ = y := Real.exp_log (by linarith)
      _ ≤ |t| := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hP4 := residual_div_le_littlewood hM hσ₀ge hL2 ht4 hexp
  obtain ⟨hsqrt, hyell⟩ := sqrt_le_and_one_le_littlewood hy1 (show ell = Real.log y from rfl)
  have hratio : y / ell ≤ y / L := div_le_div_of_nonneg_left (by linarith) hLpos hLell
  have hbound := littlewood_assemble hκ hM hLpos hL2
    (hsqrt.trans (by linarith)) (hyell.trans hratio) hmain hP1 hP2 hP3 hP4
  exact hbound.trans_eq (by dsimp [L, ell, y]; ring)

end RHTower.WeilWorkSettledPhase
