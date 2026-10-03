import GaloisForLFunctions.RHTower.WeilProducerSoundararajanInequality
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Littlewood's bound for every Weil-positive system

**Theorem** (`exists_re_producerLogZeta_le_littlewood`).  Let `lam` be full-cone Weil-positive with
`|lam(n)| ≤ κ log n` for `n ≥ 2`.  There are `C` and `T₀` such that

`log|F_lam(σ + it)| ≤ C log|t| / log log|t|`  for all `½ < σ ≤ 2` and `|t| ≥ T₀`.

For `ζ` this is Littlewood's consequence of RH.  On the Weil cone it holds unconditionally, uniformly
up to the critical line.

**Proof.**  Soundararajan's inequality (`re_producerLogZeta_le`) with `L = log log|t|` and
`σ₀ = max(σ, ½ + 1/L)`, so that `λ = (σ₀ − ½)L ≥ 1`.
- The Dirichlet polynomial is at most `κ Σ_{n ≤ e^L} n^{−½} ≤ 2κ e^{L/2} = 2κ√(log|t|)`.
- The archimedean terms are `≤ (2/L)(½ log|t| + 3)`, from the digamma asymptotic.
- The residual terms are `O(1)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz PerronPole

/-- `Re U(u + it) ≤ ½ log|t| + 3` for `0 < u ≤ 2` and `|t| ≥ 4`. -/
theorem re_archU_le {u t : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) (ht : 4 ≤ |t|) :
    (archU ((u : ℂ) + t * I)).re ≤ Real.log |t| / 2 + 3 := by
  set z : ℂ := (u : ℂ) + t * I with hz
  have hzre : z.re = u := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have ht0 : 0 < |t| := by linarith
  have hnz : |t| ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z; rwa [hzim] at this
  have hnz2 : ‖z‖ ≤ u + |t| := by
    have h := norm_add_le (u : ℂ) ((t : ℂ) * I)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have h2re : 0 < (z / 2).re := by
    have : (z / 2).re = u / 2 := by simp [hzre]
    rw [this]; linarith
  have h2n : ‖z / 2‖ = ‖z‖ / 2 := by rw [norm_div, Complex.norm_two]
  have h2ge : 2 ≤ ‖z / 2‖ := by rw [h2n]; linarith
  have hdig : (Complex.digamma (z / 2)).re ≤ Real.log |t| + 3 / 2 := by
    have h := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos h2re h2ge
    have h1 : (Complex.digamma (z / 2) - Complex.log (z / 2)).re ≤ 3 / ‖z / 2‖ :=
      (Complex.re_le_norm _).trans h
    rw [Complex.sub_re, Complex.log_re] at h1
    have h3 : 3 / ‖z / 2‖ ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2ge
    have h4 : Real.log ‖z / 2‖ ≤ Real.log |t| := by
      refine Real.log_le_log (by linarith) ?_
      rw [h2n]; linarith
    linarith
  have hinv : ∀ w : ℂ, |t| ≤ ‖w‖ → (1 / w).re ≤ 1 := by
    intro w hw
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hp1 := hinv z hnz
  have hp2 := hinv (z - 1) (by
    have := Complex.abs_im_le_norm (z - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero, hzim] at this
    exact this)
  have hpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hre : (archU z).re = (Complex.digamma (z / 2)).re / 2 - Real.log π / 2 + (1 / z).re +
      (1 / (z - 1)).re := by
    unfold archU zetaArchimedeanDatum
    simp only [Complex.add_re, Complex.sub_re]
    congr 2
    simp
  rw [hre]
  linarith

/-- The Dirichlet polynomial is at most `2κ e^{L/2}` after division by `L`. -/
theorem re_producerPoly_div_le {lam : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {L : ℝ} (hL : 0 < L) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    (producerPoly lam L s).re / L ≤ 2 * κ * Real.exp (L / 2) := by
  set N : ℕ := ⌈Real.exp L⌉₊ with hN
  have hterm : ∀ n ∈ Finset.range N, ‖LSeries.term (lamC lam) s n *
      ((max (L - Real.log n) 0 : ℝ) : ℂ) / Real.log n‖ ≤
        κ * L * (if n = 0 then 0 else 1 / Real.sqrt n) := by
    intro n _
    rcases lt_or_ge n 2 with hn | hn
    · rw [term_lamC_eq_zero_of_lt lam _ hn]
      simp only [zero_mul, zero_div, norm_zero]
      split_ifs <;> positivity
    · have hn0 : n ≠ 0 := by omega
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      rw [if_neg hn0, norm_div, norm_mul, LSeries.norm_term_eq, if_neg hn0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hl]
      have hlamC : ‖lamC lam n‖ ≤ κ * Real.log n := by
        unfold lamC
        rw [Complex.norm_real, Real.norm_eq_abs, if_pos hn]
        exact hlam n hn
      have hpow : Real.sqrt n ≤ (n : ℝ) ^ s.re := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hn1 hs
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
      have hmax : max (L - Real.log n) 0 ≤ L := max_le (by linarith) hL.le
      have hmax0 : 0 ≤ max (L - Real.log n) 0 := le_max_right _ _
      calc ‖lamC lam n‖ / (n : ℝ) ^ s.re * max (L - Real.log n) 0 / Real.log n
          ≤ (κ * Real.log n) / Real.sqrt n * L / Real.log n := by
            gcongr
        _ = κ * L * (1 / Real.sqrt n) := by field_simp
  have hsum : ∑ n ∈ Finset.range N, (if n = 0 then (0 : ℝ) else 1 / Real.sqrt n) ≤
      2 * Real.exp (L / 2) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp; positivity
    · have hsplit : ∑ n ∈ Finset.range N, (if n = 0 then (0 : ℝ) else 1 / Real.sqrt n) =
          ∑ n ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / Real.sqrt n := by
        rw [Finset.range_eq_Ico]
        have : Finset.Ico 0 N = insert 0 (Finset.Icc 1 (N - 1)) := by
          ext n; simp; omega
        rw [this, Finset.sum_insert (by simp), if_pos rfl, zero_add]
        exact Finset.sum_congr rfl fun n hn => by
          rw [if_neg (by simp at hn; omega)]
      rw [hsplit]
      refine (sum_one_div_sqrt_le (N - 1)).trans ?_
      have hN1 : ((N - 1 : ℕ) : ℝ) ≤ Real.exp L := by
        have h := Nat.ceil_lt_add_one (Real.exp_pos L).le
        rw [Nat.cast_sub (by omega : 1 ≤ N)]
        push_cast
        rw [← hN] at h
        linarith
      have : Real.sqrt ((N - 1 : ℕ) : ℝ) ≤ Real.exp (L / 2) := by
        rw [show Real.exp (L / 2) = Real.sqrt (Real.exp L) by
          rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf]
        exact Real.sqrt_le_sqrt hN1
      linarith
  have hnorm : ‖producerPoly lam L s‖ ≤ κ * L * (2 * Real.exp (L / 2)) := by
    rw [producerPoly_eq_sum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  rw [div_le_iff₀ hL]
  have := (Complex.re_le_norm _).trans hnorm
  linarith

theorem continuousOn_archU_horizontal {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b t : ℝ}
    (ha : 1 / 2 < a) (hb : 1 / 2 < b) (ht : t ≠ 0) :
    ContinuousOn (fun u : ℝ => archU ((u : ℂ) + t * I)) (uIcc a b) := by
  have hAc := continuousOn_horizontal (continuousOn_producerA hW) ha hb ht
  have hWc : ContinuousOn (fun u : ℝ => weilContinuation hW ((u : ℂ) + t * I)) (uIcc a b) := by
    refine (differentiableOn_weilContinuation hW).continuousOn.comp (by fun_prop) fun u hu => ?_
    have : 1 / 2 < u := by
      rcases Set.mem_uIcc.mp hu with h | h <;> linarith [h.1]
    show 1 / 2 < ((u : ℂ) + t * I).re
    simpa using this
  exact (hAc.add hWc).congr fun u _ => by simp only [Pi.add_apply]; rw [archU_eq hW]


theorem residual_div_le_littlewood {M₂ σ₀ L t : ℝ} (hM₂0 : 0 ≤ M₂) (hσ₀ : 1 / 2 + 1 / L ≤ σ₀)
    (hL2 : 2 ≤ L) (ht4 : 4 ≤ |t|) (hexp : Real.exp L ≤ |t|) :
    (2 * M₂ + (Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) *
      (1 + (1 - Real.exp (-2 * L))⁻¹)) / (L * t ^ 2)) / L ≤ M₂ + 2 := by
  have hLpos : 0 < L := by linarith
  have hL1 : 0 < 1 / L := by positivity
  have hσ₀pos : 0 < σ₀ := by linarith
  have h1 : Real.exp ((1 - σ₀) * L) ≤ |t| := by
    have : (1 - σ₀) * L ≤ L := by nlinarith
    exact (Real.exp_le_exp.mpr this).trans hexp
  have h2 : Real.exp (-σ₀ * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 : Real.exp (-2 * L) ≤ 1 / 2 := by
    have : Real.exp (-2 * L) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h := Real.exp_one_gt_d9
    have : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
    have : 1 / Real.exp 1 ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have h4 : (1 - Real.exp (-2 * L))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h5 : 0 ≤ Real.exp (-σ₀ * L) := (Real.exp_pos _).le
  have h6 : 0 ≤ (1 - Real.exp (-2 * L))⁻¹ := inv_nonneg.mpr (by linarith)
  have hnum : Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) * (1 + (1 - Real.exp (-2 * L))⁻¹) ≤
      |t| + 3 := by
    have : Real.exp (-σ₀ * L) * (1 + (1 - Real.exp (-2 * L))⁻¹) ≤ 1 * (1 + 2) :=
      mul_le_mul h2 (by linarith) (by linarith) zero_le_one
    linarith
  have ht2 : |t| ^ 2 = t ^ 2 := sq_abs t
  have hEp : (Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) * (1 + (1 - Real.exp (-2 * L))⁻¹)) /
      (L * t ^ 2) ≤ 4 := by
    have htp : 0 < t ^ 2 := by rw [← ht2]; exact pow_pos (by linarith) 2
    rw [div_le_iff₀ (mul_pos hLpos htp), ← ht2]
    nlinarith
  rw [div_le_iff₀ hLpos]
  nlinarith

theorem sqrt_le_and_one_le_littlewood {y L : ℝ} (hy1 : 1 < y) (hL : L = Real.log y) :
    Real.sqrt y ≤ 2 * (y / L) ∧ 1 ≤ y / L := by
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hy1
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  refine ⟨?_, ?_⟩
  · have hlog : L ≤ 2 * Real.sqrt y := by
      have h := Real.log_le_sub_one_of_pos hs
      rw [Real.log_sqrt (by linarith)] at h
      rw [hL]; linarith
    have e2 : 2 * (y / L) = 2 * y / L := by ring
    rw [e2, le_div_iff₀ hLpos]
    have h1 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hlog hs.le
    linarith
  · rw [le_div_iff₀ hLpos, one_mul, hL]
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)

theorem littlewood_assemble {κ M₂ y L ℓ P1 P2 P3 P4 : ℝ} (hκ : 0 ≤ κ) (hM₂0 : 0 ≤ M₂)
    (hLpos : 0 < L) (hL2 : 2 ≤ L) (hsqrt : Real.sqrt y ≤ 2 * (y / L)) (hyL : 1 ≤ y / L)
    (hℓ : ℓ ≤ P1 + P2 + P3 + P4) (hP1 : P1 ≤ 2 * κ * Real.sqrt y) (hP2 : P2 ≤ (y / 2 + 3) / L)
    (hP3 : P3 ≤ (y / 2 + 3) / L) (hP4 : P4 ≤ M₂ + 2) :
    ℓ ≤ (4 * κ + M₂ + 9) * (y / L) := by
  have h6 : 6 / L ≤ 3 * (y / L) := by
    have : 6 / L ≤ 3 := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  have hκy : 2 * κ * Real.sqrt y ≤ 4 * κ * (y / L) := by
    have h := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ 2 * κ)
    linarith
  have hM : M₂ + 2 ≤ (M₂ + 2) * (y / L) := le_mul_of_one_le_right (by linarith) hyL
  have e : (y / 2 + 3) / L + (y / 2 + 3) / L = y / L + 6 / L := by ring
  have e2 : (4 * κ + M₂ + 9) * (y / L) = 4 * κ * (y / L) + y / L + 3 * (y / L) +
      (M₂ + 2) * (y / L) + 3 * (y / L) := by ring
  linarith

/-- **Littlewood's bound on the Weil cone.**  If `|lam(n)| ≤ κ log n` for `n ≥ 2`, then
`Re log F_lam(σ + it) ≤ C log|t| / log log|t|` for `½ < σ ≤ 2` and `|t| ≥ T₀`. -/
theorem exists_re_producerLogZeta_le_littlewood {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {κ : ℝ} (hκ : 0 ≤ κ) (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) :
    ∃ C T₀ : ℝ, ∀ σ t : ℝ, T₀ ≤ |t| → 1 / 2 < σ → σ ≤ 2 →
      (producerLogZeta hW σ t).re ≤ C * Real.log |t| / Real.log (Real.log |t|) := by
  set M₂ : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) with hM₂
  have hM₂0 : 0 ≤ M₂ := tsum_nonneg fun n => by positivity
  refine ⟨4 * κ + M₂ + 9, Real.exp (Real.exp 2), fun σ t ht hσ hσ2 => ?_⟩
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2
    have h := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hT₀ : (4 : ℝ) ≤ Real.exp (Real.exp 2) := by
    have := Real.add_one_le_exp (Real.exp 2); linarith
  have ht4 : 4 ≤ |t| := hT₀.trans ht
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht4; linarith
  set y : ℝ := Real.log |t| with hy
  have hy2 : Real.exp 2 ≤ y := by
    rw [hy, Real.le_log_iff_exp_le (by linarith)]; exact ht
  have hy1 : 1 < y := by linarith
  set L : ℝ := Real.log y with hL
  have hL2 : 2 ≤ L := by rw [hL, Real.le_log_iff_exp_le (by linarith)]; exact hy2
  have hLpos : 0 < L := by linarith
  set σ₀ : ℝ := max σ (1 / 2 + 1 / L) with hσ₀
  have hσσ₀ : σ ≤ σ₀ := le_max_left _ _
  have hσ₀2 : σ₀ ≤ 2 := max_le hσ2 (by
    have : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL2
    linarith)
  have hσ₀ge : 1 / 2 + 1 / L ≤ σ₀ := le_max_right _ _
  have hlam1 : 1 ≤ (σ₀ - 1 / 2) * L := by
    have : 1 / L * L = 1 := by field_simp
    have h := mul_le_mul_of_nonneg_right (by linarith : 1 / L ≤ σ₀ - 1 / 2) hLpos.le
    linarith
  have hlamb : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ (σ₀ - 1 / 2) * L := by
    have : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hmain := re_producerLogZeta_le hW hσ hσσ₀ hσ₀2 ht0 hLpos hlamb
  -- the four pieces
  have hP1 : (producerPoly lam L ((σ₀ : ℂ) + t * I)).re / L ≤ 2 * κ * Real.sqrt y := by
    have h := re_producerPoly_div_le hκ hlam hLpos (s := (σ₀ : ℂ) + t * I)
      (by simp; linarith)
    have hsq : Real.exp (L / 2) = Real.sqrt y := by
      rw [hL, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]; ring_nf
    rwa [hsq] at h
  have hU : ∀ u : ℝ, 1 / 2 < u → u ≤ 2 → (archU ((u : ℂ) + t * I)).re ≤ y / 2 + 3 :=
    fun u hu hu2 => re_archU_le (by linarith) hu2 ht4
  have hP2 : (archU ((σ₀ : ℂ) + t * I)).re / L ≤ (y / 2 + 3) / L :=
    div_le_div_of_nonneg_right (hU σ₀ (by linarith) hσ₀2) hLpos.le
  have hdiff : σ₀ - σ ≤ 1 / L := by
    rcases le_total σ (1 / 2 + 1 / L) with h | h
    · rw [hσ₀, max_eq_right h]; linarith
    · rw [hσ₀, max_eq_left h]; have : 0 < 1 / L := by positivity
      linarith
  have hP3 : (∫ u in σ..σ₀, (archU ((u : ℂ) + t * I)).re) ≤ (y / 2 + 3) / L := by
    have hc := continuousOn_archU_horizontal hW hσ (by linarith : 1 / 2 < σ₀) ht0
    have hint := (Complex.continuous_re.comp_continuousOn hc).intervalIntegrable (μ := volume)
    have h1 := intervalIntegral.integral_mono_on hσσ₀ hint
      (intervalIntegrable_const (c := y / 2 + 3)) fun u hu =>
        hU u (by linarith [hu.1]) (hu.2.trans hσ₀2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have hy3 : 0 ≤ y / 2 + 3 := by linarith
    calc _ ≤ (σ₀ - σ) * (y / 2 + 3) := h1
      _ ≤ 1 / L * (y / 2 + 3) := mul_le_mul_of_nonneg_right hdiff hy3
      _ = (y / 2 + 3) / L := by ring
  have hP4 := residual_div_le_littlewood hM₂0 hσ₀ge hL2 ht4
    (show Real.exp L ≤ |t| by
      rw [hL, Real.exp_log (by linarith), hy]
      exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
  obtain ⟨hsqrt, hyL⟩ := sqrt_le_and_one_le_littlewood hy1 hL
  rw [mul_div_assoc]
  exact littlewood_assemble hκ hM₂0 hLpos hL2 hsqrt hyL hmain hP1 hP2 hP3 hP4

end RHTower.WeilSpectral

end
