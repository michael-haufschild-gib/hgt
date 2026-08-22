import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFarLine
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Reindex the CGL complementary subtype tail as the literal series beginning
at `M+1`. -/
theorem cglLemma62_dirichletTail_eq_tsum_shift
    (χ : DirichletCharacter ℂ q) (M : ℕ) (s : CGLAbsoluteConvergencePoint) :
    cglLemma62DirichletTail χ M s =
      ∑' k : ℕ, LSeries.term (↗χ) s.1 (k + (M + 1)) := by
  have hsum : LSeriesSummable (↗χ) s.1 :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ s.2
  have hsplit := hsum.sum_add_tsum_nat_add (M + 1)
  have hl := cglLemma62_lseries_eq_head_add_tail χ M s
  calc
    cglLemma62DirichletTail χ M s = LSeries (↗χ) s.1 -
        cglLemma62DirichletHead χ M s.1 := by rw [hl]; ring
    _ = ∑' k : ℕ, LSeries.term (↗χ) s.1 (k + (M + 1)) := by
      unfold LSeries cglLemma62DirichletHead
      rw [← hsplit]
      ring

/-- A CGL tail cutoff at which the elementary integral-tail estimate applies. -/
structure CGLLemma62TailCutoff where
  value : ℕ
  one_le : 1 ≤ value

/-- **CGL Lemma 6.2, far-right Dirichlet-tail estimate.**  On the line dual to
`Re(s)=-2k`, the literal complementary character series is bounded by
`M^{-2k}/(2k)`.  Positivity of depth and cutoff is certified data. -/
theorem cglLemma62_far_dirichletTail_norm_le
    (B : CGLLemma62InducedCharacter) (t : ℝ) (d : CGLLemma62TailContourDepth)
    (J : CGLLemma62TailCutoff) (v : ℝ) :
    ‖cglLemma62DirichletTail B.character⁻¹ J.value (cglLemma62FarRightPointAC t d v)‖ ≤
      (J.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ)) := by
  let s := cglLemma62FarRightPointAC t d v
  have hsre : s.1.re = 1 + 2 * (d.value : ℝ) := by
    unfold s cglLemma62FarRightPointAC cglLemma62FarRightPoint cglLemma62FarLeftPoint
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul,
      add_zero]
    norm_num
  have hdpos : (0 : ℝ) < d.value := by exact_mod_cast d.positive
  let q : ℝ := -2 * (d.value : ℝ)
  have hq : q < 0 := by
    dsimp [q]
    linarith
  have hweight : Summable (fun k : ℕ =>
      ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q - 1)) :=
    GaloisForLFunctions.HTGeometry.summable_shift_rpow hq J.value
  have hterm : Summable (fun n : ℕ =>
      LSeries.term (↗B.character⁻¹) s.1 n) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re B.character⁻¹ s.2
  have htailnorm : Summable (fun k : ℕ =>
      ‖LSeries.term (↗B.character⁻¹) s.1 (k + (J.value + 1))‖) := by
    have hshift := (summable_nat_add_iff (f := fun n : ℕ =>
        ‖LSeries.term (↗B.character⁻¹) s.1 n‖) (J.value + 1)).mpr hterm.norm
    exact hshift
  rw [cglLemma62_dirichletTail_eq_tsum_shift B.character⁻¹ J.value s]
  refine (norm_tsum_le_tsum_norm htailnorm).trans ?_
  refine (htailnorm.tsum_mono hweight ?_).trans ?_
  · intro k
    let n : ℕ := k + (J.value + 1)
    have hn : n ≠ 0 := by
      dsimp [n]
      omega
    have hχ : ‖B.character⁻¹ n‖ ≤ ‖(1 : ℂ)‖ := by
      simpa using (B.character⁻¹).norm_le_one n
    have hle : ‖LSeries.term (↗B.character⁻¹) s.1 n‖ ≤
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ :=
      LSeries.norm_term_le (f := (↗B.character⁻¹)) (g := fun _ : ℕ => (1 : ℂ)) s.1 hχ
    have hnorm : ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ =
        1 / (n : ℝ) ^ s.1.re := by
      rw [LSeries.norm_term_eq, if_neg hn]
      norm_num
    change ‖LSeries.term (↗B.character⁻¹) s.1 n‖ ≤ _
    calc
      ‖LSeries.term (↗B.character⁻¹) s.1 n‖ ≤
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ := hle
      _ = 1 / (n : ℝ) ^ s.1.re := hnorm
      _ = ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q - 1) := by
        rw [hsre]
        have hncast : (n : ℝ) = (J.value : ℝ) + 1 + (k : ℝ) := by
          dsimp [n]
          push_cast
          ring
        rw [hncast, one_div]
        rw [← Real.rpow_neg (by positivity : 0 ≤ (J.value : ℝ) + 1 + (k : ℝ))]
        dsimp [q]
        congr 1
        ring
  · simpa only [q, neg_mul, neg_neg] using
      GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le hq J.one_le

end

end RHTower
