import GaloisForLFunctions.RHTower.XiSliceSaddleArcBounds
import GaloisForLFunctions.PNTPlus.ZetaBounds

/-!
# Saddle-arc control for the slice product with the saddle near the critical strip

`XiSliceSaddleArcBounds` controls the slice product `g_t(x) = ξ(½+x+it)ξ(½−x+it)` on the saddle disc
`|w − R| ≤ R/2` for `R ≥ 5`, where both points `½ + w ± it` lie in `Re ≥ 2`.  Here the saddle radius
may be as small as `½ + 2η`: the disc has radius `η`, so both points lie in the Euler region
`Re ≥ 1 + η`, where `‖ζ'/ζ(s)‖ ≤ (Re s − 1)⁻¹ + C`.  The Stirling comparison for `ξ'/ξ` then holds
with the constant `3 + 1/η + C`, and the disc, slope and saddle-arc bounds follow as before, with
`η` in place of `R/2`.
-/

open Complex Real Metric

namespace RHTower

noncomputable section

theorem exists_norm_logDeriv_zeta_le_of_one_lt_re :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ s : ℂ, 1 < s.re →
      ‖logDeriv riemannZeta s‖ ≤ (s.re - 1)⁻¹ + C₀ := by
  obtain ⟨C, hC, h⟩ := triv_bound_zeta
  refine ⟨C, hC, fun s hs => ?_⟩
  have h1 := h s.re s.im hs
  rw [Complex.re_add_im] at h1
  rw [logDeriv_apply]
  rwa [neg_div, norm_neg] at h1

/-- A constant with `‖ζ'/ζ(s)‖ ≤ (Re s − 1)⁻¹ + C` on `Re s > 1`. -/
def zetaLogDerivEulerConstant : ℝ := Classical.choose exists_norm_logDeriv_zeta_le_of_one_lt_re

theorem zetaLogDerivEulerConstant_nonneg : 0 ≤ zetaLogDerivEulerConstant :=
  (Classical.choose_spec exists_norm_logDeriv_zeta_le_of_one_lt_re).1

theorem norm_logDeriv_zeta_le_euler {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv riemannZeta s‖ ≤ (s.re - 1)⁻¹ + zetaLogDerivEulerConstant :=
  (Classical.choose_spec exists_norm_logDeriv_zeta_le_of_one_lt_re).2 s hs

/-- The Stirling constant for `ξ'/ξ` on `Re ≥ 1 + η`. -/
def xiEulerConstant (η : ℝ) : ℝ := 3 + 1 / η + zetaLogDerivEulerConstant

theorem xiEulerConstant_pos {η : ℝ} (hη : 0 < η) : 0 < xiEulerConstant η := by
  unfold xiEulerConstant
  have := zetaLogDerivEulerConstant_nonneg
  positivity

/-- `‖ξ'/ξ(s) − ½ log(s/2)‖ ≤ 3 + 1/η + C` on `Re s ≥ 1 + η`, `‖s‖ ≥ 4`. -/
theorem norm_logDeriv_xi_sub_half_log_le_euler {η : ℝ} (hη : 0 < η) {s : ℂ} (hs : 1 + η ≤ s.re)
    (hs4 : 4 ≤ ‖s‖) :
    ‖logDeriv xi s - Complex.log (s / 2) / 2‖ ≤ xiEulerConstant η := by
  rw [logDeriv_xi_fourFactor (by linarith)]
  have e : 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2
      + logDeriv riemannZeta s - Complex.log (s / 2) / 2
      = (1 / s + 1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2
        + ((Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 + logDeriv riemannZeta s) := by
    ring
  rw [e]
  have h1 : ‖1 / s‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) hs4
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (by norm_num)
    have := norm_sub_norm_le s 1; simp only [norm_one] at this; linarith
  have h3 : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ 11 / 10 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2']
    linarith [Real.pi_lt_d2]
  have hs2re : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hs2 : 2 ≤ ‖s / 2‖ := by
    rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have h4 : ‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2‖ ≤ 3 / 4 := by
    rw [norm_div]; simp only [Complex.norm_ofNat]
    have := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hs2re hs2
    have h' : 3 / ‖s / 2‖ ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
    linarith
  have h5 : ‖logDeriv riemannZeta s‖ ≤ 1 / η + zetaLogDerivEulerConstant := by
    have := norm_logDeriv_zeta_le_euler (s := s) (by linarith)
    have hinv : (s.re - 1)⁻¹ ≤ 1 / η := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hη (by linarith)
    linarith
  calc _ ≤ ‖(1 / s + 1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2‖
        + ‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 + logDeriv riemannZeta s‖ :=
        norm_add_le _ _
    _ ≤ (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖)
        + (‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2‖ + ‖logDeriv riemannZeta s‖) := by
        gcongr
        · exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
        · exact norm_add_le _ _
    _ ≤ (1 / 4 + 1 / 3 + 11 / 10) + (3 / 4 + (1 / η + zetaLogDerivEulerConstant)) := by gcongr
    _ ≤ xiEulerConstant η := by unfold xiEulerConstant; linarith

theorem logDeriv_xi_annulus_bounds_euler {η : ℝ} (hη : 0 < η) {s : ℂ} {m₁ m₂ : ℝ}
    (hs : 1 + η ≤ s.re) (hm₁ : 4 ≤ m₁) (h₁ : m₁ ≤ ‖s‖) (h₂ : ‖s‖ ≤ m₂) :
    ‖logDeriv xi s‖ ≤ Real.log (m₂ / 2) / 2 + Real.pi / 4 + xiEulerConstant η
      ∧ Real.log (m₁ / 2) / 2 - xiEulerConstant η ≤ (logDeriv xi s).re
      ∧ (logDeriv xi s).re ≤ Real.log (m₂ / 2) / 2 + xiEulerConstant η := by
  have hs4 : 4 ≤ ‖s‖ := le_trans hm₁ h₁
  have hE := norm_logDeriv_xi_sub_half_log_le_euler hη hs hs4
  set C := xiEulerConstant η
  have hre2 : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hn2 : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; simp
  have hn1 : 1 ≤ ‖s / 2‖ := by rw [hn2]; linarith
  have hlogle : Real.log ‖s / 2‖ ≤ Real.log (m₂ / 2) := by
    rw [hn2]; exact Real.log_le_log (by linarith) (by linarith)
  have hlogge : Real.log (m₁ / 2) ≤ Real.log ‖s / 2‖ := by
    rw [hn2]; exact Real.log_le_log (by linarith) (by linarith)
  have hlog := norm_log_le_of_re_pos hre2 hn1
  have hre : (Complex.log (s / 2) / 2).re = Real.log ‖s / 2‖ / 2 := by
    rw [Complex.div_ofNat_re, Complex.log_re]
  have hEre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hE))
  rw [Complex.sub_re, hre] at hEre
  refine ⟨?_, by linarith [hEre.1], by linarith [hEre.2]⟩
  calc ‖logDeriv xi s‖ ≤ ‖Complex.log (s / 2) / 2‖ + ‖logDeriv xi s - Complex.log (s / 2) / 2‖ := by
        have := norm_add_le (Complex.log (s / 2) / 2) (logDeriv xi s - Complex.log (s / 2) / 2)
        simpa using this
    _ ≤ (Real.log (m₂ / 2) + Real.pi / 2) / 2 + C := by
        rw [norm_div]; simp only [Complex.norm_ofNat]
        gcongr
        linarith
    _ = Real.log (m₂ / 2) / 2 + Real.pi / 4 + C := by ring

theorem norm_logDeriv_xi_sub_le_annulus_euler {η : ℝ} (hη : 0 < η) {s s' : ℂ} {m₁ m₂ : ℝ}
    (hs : 1 + η ≤ s.re) (hs' : 1 + η ≤ s'.re)
    (hm₁ : 4 ≤ m₁) (h₁ : m₁ ≤ ‖s‖) (h₂ : ‖s‖ ≤ m₂) (h₁' : m₁ ≤ ‖s'‖) (h₂' : ‖s'‖ ≤ m₂) :
    ‖logDeriv xi s - logDeriv xi s'‖
      ≤ Real.log (m₂ / m₁) / 2 + Real.pi / 2 + 2 * xiEulerConstant η := by
  have hE := norm_logDeriv_xi_sub_half_log_le_euler hη hs (le_trans hm₁ h₁)
  have hE' := norm_logDeriv_xi_sub_half_log_le_euler hη hs' (le_trans hm₁ h₁')
  set C := xiEulerConstant η
  have hre : ∀ z : ℂ, 1 + η ≤ z.re → 0 < (z / 2).re := fun z hz => by
    have : (z / 2).re = z.re / 2 := by simp
    rw [this]; linarith
  have hlog := norm_log_sub_log_le_of_re_pos (hre s hs) (hre s' hs')
  have hn2 : ∀ z : ℂ, ‖z / 2‖ = ‖z‖ / 2 := fun z => by rw [norm_div]; simp
  have hm1pos : 0 < m₁ := by linarith
  have hspos : 0 < ‖s‖ := by linarith
  have hs'pos : 0 < ‖s'‖ := by linarith
  have hratio : |Real.log ‖s / 2‖ - Real.log ‖s' / 2‖| ≤ Real.log (m₂ / m₁) := by
    rw [hn2, hn2, ← Real.log_div (by positivity) (by positivity), abs_le]
    have hp : 0 < ‖s‖ / 2 / (‖s'‖ / 2) := by positivity
    constructor
    · rw [neg_le, ← Real.log_inv, inv_div]
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by linarith) hm1pos]
      nlinarith
    · apply Real.log_le_log hp
      rw [div_le_div_iff₀ (by linarith) hm1pos]
      nlinarith
  calc ‖logDeriv xi s - logDeriv xi s'‖
      ≤ ‖Complex.log (s / 2) / 2 - Complex.log (s' / 2) / 2‖
        + ‖logDeriv xi s - Complex.log (s / 2) / 2‖ + ‖logDeriv xi s' - Complex.log (s' / 2) / 2‖ := by
        have e : logDeriv xi s - logDeriv xi s' = (Complex.log (s / 2) / 2 - Complex.log (s' / 2) / 2)
            + (logDeriv xi s - Complex.log (s / 2) / 2)
            - (logDeriv xi s' - Complex.log (s' / 2) / 2) := by ring
        rw [e]
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (Real.log (m₂ / m₁) + Real.pi) / 2 + C + C := by
        gcongr
        rw [← sub_div, norm_div]; simp only [Complex.norm_ofNat]
        gcongr
        linarith
    _ = Real.log (m₂ / m₁) / 2 + Real.pi / 2 + 2 * C := by ring

/-- Geometry of `½ + w ± it` for `|w − R| ≤ η`, `½ + 2η ≤ R ≤ t/2`, `t ≥ 8`. -/
theorem slicePoint_annulus_euler {t R η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (ht : 8 ≤ t)
    (hR : 1 / 2 + 2 * η ≤ R) (hRt : R ≤ t / 2) {w : ℂ} (hw : w ∈ closedBall (R : ℂ) η)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    1 + η ≤ (1 / 2 + w + (ε * t : ℝ) * I).re ∧ 3 * t / 4 ≤ ‖1 / 2 + w + (ε * t : ℝ) * I‖
      ∧ ‖1 / 2 + w + (ε * t : ℝ) * I‖ ≤ 3 * t := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw))
  have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hw))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
  have hεt : |ε * t| = t := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_pos (by linarith : (0 : ℝ) < t)]
  have hsre : (1 / 2 + w + (ε * t : ℝ) * I).re = 1 / 2 + w.re := by simp
  have hsim : (1 / 2 + w + (ε * t : ℝ) * I).im = w.im + ε * t := by simp
  refine ⟨by rw [hsre]; linarith, ?_, ?_⟩
  · refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [hsim]
    have h1 : |ε * t| - |w.im| ≤ |w.im + ε * t| := by
      have := abs_sub_abs_le_abs_sub (ε * t) (-w.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this; linarith
    rw [hεt] at h1
    have : |w.im| ≤ η := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hsre, hsim]
    have h1 : |1 / 2 + w.re| ≤ 1 / 2 + R + η := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |w.im + ε * t| ≤ η + t := by
      refine (abs_add_le _ _).trans ?_
      rw [hεt]; have : |w.im| ≤ η := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    linarith

/-- Disc bounds for `L = ξ'/ξ(½+·+it) + ξ'/ξ(½+·−it)` on `|w − R| ≤ η`. -/
theorem xiSliceLogDeriv_disc_bounds_euler {t R η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (ht : 8 ≤ t)
    (hR : 1 / 2 + 2 * η ≤ R) (hRt : R ≤ t / 2) {w : ℂ} (hw : w ∈ closedBall (R : ℂ) η) :
    ‖xiSliceLogDeriv t w‖ ≤ Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiEulerConstant η
      ∧ ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖
        ≤ Real.log 4 + Real.pi + 4 * xiEulerConstant η := by
  have hR0 : (R : ℂ) ∈ closedBall (R : ℂ) η := mem_closedBall_self hη.le
  have ep : ∀ z : ℂ, (1 / 2 + z + ((1 : ℝ) * t : ℝ) * I) = 1 / 2 + z + (t : ℂ) * I := by
    intro z; push_cast; ring
  have em : ∀ z : ℂ, (1 / 2 + z + ((-1 : ℝ) * t : ℝ) * I) = 1 / 2 + z - (t : ℂ) * I := by
    intro z; push_cast; ring
  obtain ⟨p1, p2, p3⟩ := slicePoint_annulus_euler hη hη1 ht hR hRt hw 1 (Or.inl rfl)
  obtain ⟨m1, m2, m3⟩ := slicePoint_annulus_euler hη hη1 ht hR hRt hw (-1) (Or.inr rfl)
  obtain ⟨q1, q2, q3⟩ := slicePoint_annulus_euler hη hη1 ht hR hRt hR0 1 (Or.inl rfl)
  obtain ⟨n1, n2, n3⟩ := slicePoint_annulus_euler hη hη1 ht hR hRt hR0 (-1) (Or.inr rfl)
  rw [ep] at p1 p2 p3 q1 q2 q3
  rw [em] at m1 m2 m3 n1 n2 n3
  have hm : (4 : ℝ) ≤ 3 * t / 4 := by linarith
  have hA := (logDeriv_xi_annulus_bounds_euler hη p1 hm p2 p3).1
  have hB := (logDeriv_xi_annulus_bounds_euler hη m1 hm m2 m3).1
  have hdiv : 3 * t / (3 * t / 4) = 4 := by field_simp
  have hD1 := norm_logDeriv_xi_sub_le_annulus_euler hη p1 q1 hm p2 p3 q2 q3
  have hD2 := norm_logDeriv_xi_sub_le_annulus_euler hη m1 n1 hm m2 m3 n2 n3
  rw [hdiv] at hD1 hD2
  constructor
  · unfold xiSliceLogDeriv
    calc _ ≤ ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I)‖ + ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I)‖ :=
          norm_add_le _ _
      _ ≤ (Real.log (3 * t / 2) / 2 + Real.pi / 4 + xiEulerConstant η)
          + (Real.log (3 * t / 2) / 2 + Real.pi / 4 + xiEulerConstant η) := by
          gcongr
      _ = _ := by ring
  · unfold xiSliceLogDeriv
    have e : logDeriv xi (1 / 2 + w + (t : ℂ) * I) + logDeriv xi (1 / 2 + w - (t : ℂ) * I)
        - (logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I) + logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I))
        = (logDeriv xi (1 / 2 + w + (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I))
          + (logDeriv xi (1 / 2 + w - (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I)) := by
      ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (Real.log 4 / 2 + Real.pi / 2 + 2 * xiEulerConstant η)
          + (Real.log 4 / 2 + Real.pi / 2 + 2 * xiEulerConstant η) := add_le_add hD1 hD2
      _ = _ := by ring

/-- `L(R)` is real, with `log(t/2) − 2C_η ≤ L(R) ≤ log t + 2C_η` for `R ≥ ½ + η`. -/
theorem xiSliceLogDeriv_real_bounds_euler {t R η : ℝ} (hη : 0 < η) (ht : 8 ≤ t)
    (hR : 1 / 2 + η ≤ R) (hRt : R ≤ t / 2) :
    (xiSliceLogDeriv t R).im = 0
      ∧ Real.log (t / 2) - 2 * xiEulerConstant η ≤ (xiSliceLogDeriv t R).re
      ∧ (xiSliceLogDeriv t R).re ≤ Real.log t + 2 * xiEulerConstant η := by
  set s : ℂ := 1 / 2 + (R : ℂ) + (t : ℂ) * I with hs
  have hc : (1 / 2 : ℂ) + (R : ℂ) - (t : ℂ) * I = (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext <;> simp
  have hL : xiSliceLogDeriv t R = logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s) := by
    unfold xiSliceLogDeriv; rw [hc, logDeriv_xi_conj_xiLogDerivSymmetry]
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have h1 : t ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; rw [hsim, abs_of_pos (by linarith)] at this; exact this
  have h2 : ‖s‖ ≤ 2 * t := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsre, hsim, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  obtain ⟨-, hlo, hhi⟩ := logDeriv_xi_annulus_bounds_euler hη (s := s) (m₁ := t) (m₂ := 2 * t)
    (by rw [hsre]; linarith) (by linarith) h1 h2
  rw [hL]
  have hre : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).re = 2 * (logDeriv xi s).re := by
    simp; ring
  have him : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).im = 0 := by simp
  rw [hre, him]
  have e : 2 * t / 2 = t := by ring
  rw [e] at hhi
  refine ⟨rfl, by linarith, by linarith⟩

/-- The saddle-disc constant on the radius-`η` disc. -/
def xiSliceDiscConstantEuler (η t R : ℝ) : ℝ :=
  η * (Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiEulerConstant η)
    + R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η)

/-- **Saddle-arc control with the saddle near the strip.**  For `t ≥ 8`, `½ + 2η ≤ R ≤ t/2`,
`0 ≤ θ` and `Rθ ≤ η/2`, the bounds of `HTGeometry.saddleArc_bounds` hold with `r = η` and
`M = xiSliceDiscConstantEuler η t R`. -/
theorem xiSlice_saddleArc_bounds_euler {t R η θ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (ht : 8 ≤ t)
    (hR : 1 / 2 + 2 * η ≤ R) (hRt : R ≤ t / 2) (hθ0 : 0 ≤ θ) (hθ : R * θ ≤ η / 2) :
    ‖HTGeometry.saddleArc (xiSliceProduct t) R
        (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) + 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3)
        ≤ (HTGeometry.saddleArc (xiSliceProduct t) R
            (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ).re) := by
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hball : closedBall (R : ℂ) η ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 1 / 2 < w.re; linarith
  apply HTGeometry.saddleArc_bounds hUo (differentiable_xiSliceProduct t).differentiableOn
    (fun w hw => xiSliceProduct_ne_zero_of_re hw) (by linarith) hη hball
  · intro w hw
    have hwU : 1 / 2 < w.re := hball hw
    have hRU : 1 / 2 < (R : ℂ).re := by simp; linarith
    rw [scaledLogDeriv_xiSliceProduct hwU, scaledLogDeriv_xiSliceProduct hRU]
    obtain ⟨h1, h2⟩ := xiSliceLogDeriv_disc_bounds_euler hη hη1 ht hR hRt hw
    have hwR : ‖w - R‖ ≤ η := by rwa [mem_closedBall, dist_eq_norm] at hw
    have e : w * xiSliceLogDeriv t w - R * xiSliceLogDeriv t R
        = (w - R) * xiSliceLogDeriv t w + R * (xiSliceLogDeriv t w - xiSliceLogDeriv t R) := by ring
    rw [e]
    calc _ ≤ ‖(w - R) * xiSliceLogDeriv t w‖ + ‖(R : ℂ) * (xiSliceLogDeriv t w - xiSliceLogDeriv t R)‖ :=
          norm_add_le _ _
      _ = ‖w - R‖ * ‖xiSliceLogDeriv t w‖ + R * ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      _ ≤ η * (Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiEulerConstant η)
          + R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) := by
          gcongr
      _ = xiSliceDiscConstantEuler η t R := by unfold xiSliceDiscConstantEuler; ring
  · intro x hx
    have hx' : 1 / 2 < ((x : ℂ)).re := hx
    exact im_scaledLogDeriv_xiSliceProduct_ofReal (by simpa using hx')
  · exact hθ0
  · exact hθ

/-- **The saddle slope near the strip.**  `|F'(R) − L(R)| ≤ R(log 4 + π + 4C_η)/η`. -/
theorem xiSlice_saddleSlope_bounds_euler {t R η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (ht : 8 ≤ t)
    (hR : 1 / 2 + 2 * η ≤ R) (hRt : R ≤ t / 2) :
    Real.log (t / 2) - 2 * xiEulerConstant η
        - R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
    ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ≤ Real.log t + 2 * xiEulerConstant η
        + R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η := by
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hRU : (R : ℂ) ∈ U := by show 1 / 2 < (R : ℂ).re; simp; linarith
  have hball : closedBall (R : ℂ) η ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 1 / 2 < w.re; linarith
  have hLd := differentiableOn_xiSliceLogDeriv t
  have hev : HTGeometry.scaledLogDeriv (xiSliceProduct t) =ᶠ[nhds (R : ℂ)]
      fun w => w * xiSliceLogDeriv t w := by
    filter_upwards [hUo.mem_nhds hRU] with w hw
    exact scaledLogDeriv_xiSliceProduct hw
  have hLR : HasDerivAt (xiSliceLogDeriv t) (deriv (xiSliceLogDeriv t) R) R :=
    (hLd.differentiableAt (hUo.mem_nhds hRU)).hasDerivAt
  have hderiv : deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R
      = xiSliceLogDeriv t R + R * deriv (xiSliceLogDeriv t) R := by
    rw [hev.deriv_eq]
    have := (hasDerivAt_id' (R : ℂ)).mul hLR
    exact this.deriv.trans (by ring)
  have hcauchy : ‖deriv (xiSliceLogDeriv t) R‖
      ≤ (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η :=
    HTGeometry.norm_deriv_le_of_norm_sub_le hLd (c := (R : ℂ)) hη hball
      (fun z hz => (xiSliceLogDeriv_disc_bounds_euler hη hη1 ht hR hRt
        (sphere_subset_closedBall hz)).2)
  obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds_euler hη ht (by linarith) hRt
  have hRd : |(R * deriv (xiSliceLogDeriv t) R : ℂ).re|
      ≤ R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc R * ‖deriv (xiSliceLogDeriv t) R‖
        ≤ R * ((Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η) := by
          gcongr; linarith
      _ = R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η := by ring
  rw [hderiv, Complex.add_re]
  have := abs_le.mp hRd
  constructor <;> linarith [this.1, this.2]

end

end RHTower
