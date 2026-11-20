import GaloisForLFunctions.goldbach.LiLiu.Boundary.KernelRegularity
import GaloisForLFunctions.goldbach.LiLiu.Boundary.ModelKernelBound
import GaloisForLFunctions.goldbach.LiLiu.Mellin.CharacterContour
import GaloisForLFunctions.HTGeometry.DirichletCriticalUpperBoundPoleExclusion

/-! # A square-integrable majorant for the normalized residual -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Set Finset
open scoped ComplexConjugate Classical
noncomputable section

def heightGrowth (t : ℝ) := (1+|t|)^(1/4:ℝ)

private theorem heightGrowth_pos (t : ℝ) : 0 < heightGrowth t := Real.rpow_pos_of_pos (by positivity) _
private theorem one_le_heightGrowth (t : ℝ) : 1 ≤ heightGrowth t :=
  Real.one_le_rpow (by linarith only [abs_nonneg t]) (by norm_num)

theorem characterKernel_strip_bound {n : ℕ} (h : modulusGRH (n+1)) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s z : ℂ, s.re ∈ Icc a (1/8) → z.re ∈ Icc a (1/8) →
      ‖characterKernel (n+1) s z‖ ≤ B * heightGrowth s.im * heightGrowth z.im := by
  obtain ⟨A,hA,hg⟩ := characterFeature_strip_bound h ha
  let X := univ.filter fun χ : DirichletCharacter ℂ (n+1) => χ.Odd
  let c := (2 : ℂ) / (n+1).totient
  refine ⟨‖c‖*X.card*A^2, by positivity, ?_⟩
  intro s z hs hz
  change ‖c * ∑ χ ∈ X, characterFeature χ s * star (characterFeature χ z)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖c‖ * ∑ χ ∈ X, ‖characterFeature χ s * star (characterFeature χ z)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)
    _ ≤ ‖c‖ * ∑ _χ ∈ X, (A*heightGrowth s.im)*(A*heightGrowth z.im) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply sum_le_sum
      intro χ hχ
      have hn := odd_ne_principal (mem_filter.mp hχ).2
      rw [norm_mul,norm_star]
      exact mul_le_mul (hg χ hn s hs.1 (by linarith only [hs.2]))
        (hg χ hn z hz.1 (by linarith only [hz.2])) (norm_nonneg _) (mul_nonneg hA.le (heightGrowth_pos _).le)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem diagonalSeries_halfPlane_bound (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, a ≤ w.re → ‖diagonalSeries N w‖ ≤ D := by
  refine ⟨∑' k, ‖LSeries.term (diagonalCoefficient N) ((1+a : ℝ):ℂ) k‖,
    tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro w hw
  exact HTGeometry.norm_LSeries_le_tsum_term (diagonalSeries_summable N (by simpa using ha))
    (by simpa using hw)

theorem residualKernel_strip_bound {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s z : ℂ, s.re ∈ Icc a (1/8) → z.re ∈ Icc a (1/8) →
      ‖residualKernel (n+1) s z‖ ≤ B * heightGrowth s.im * heightGrowth z.im := by
  obtain ⟨P,hP,hp⟩ := characterKernel_strip_bound h ha
  obtain ⟨D,hD,hd⟩ := diagonalSeries_halfPlane_bound (n+1) (a := 2*a) (by positivity)
  obtain ⟨K,hK,hk⟩ := betaModel_strip_bound hN ha
  refine ⟨P+D+K, by positivity, ?_⟩
  intro s z hs hz
  have hdiag := hd (s+conj z) (by simp; linarith only [hs.1,hz.1])
  have hdiag' : ‖diagonalSeries (n+1) (s+conj z)‖ ≤ D * heightGrowth s.im * heightGrowth z.im :=
    hdiag.trans ((le_mul_of_one_le_right hD (one_le_heightGrowth _)).trans
      (le_mul_of_one_le_right (mul_nonneg hD (heightGrowth_pos _).le) (one_le_heightGrowth _)))
  have hmod := hk s (conj z) hs hz
  simp only [Complex.conj_im, abs_neg] at hmod
  have htri := norm_sub_le (characterKernel (n+1) s z - diagonalSeries (n+1) (s+conj z))
    (betaModel (n+1) s (conj z))
  have htri' := norm_sub_le (characterKernel (n+1) s z) (diagonalSeries (n+1) (s+conj z))
  change ‖_ - betaModel (n+1) s (conj z)‖ ≤ _
  change ‖betaModel (n+1) s (conj z)‖ ≤ K * heightGrowth s.im * heightGrowth z.im at hmod
  linarith only [htri,htri',hp s z hs hz,hdiag',hmod]

private theorem denominator_height {s : ℂ} (hs : 0 ≤ s.re) :
    1+|s.im| ≤ 2*‖1+s‖ := by
  have hr := re_le_norm (1+s)
  have hi := abs_im_le_norm (1+s)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add] at hr hi
  linarith only [hr,hi,hs]

/-- Each height has exponent −3/4 after the Hardy denominators are restored. -/
theorem boundaryKernel_strip_decay {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s z : ℂ, s.re ∈ Icc a (1/8) → z.re ∈ Icc a (1/8) →
      ‖boundaryKernel (n+1) s z‖ ≤ B*(1+|s.im|)^(-(3/4:ℝ))*(1+|z.im|)^(-(3/4:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := residualKernel_strip_bound hN h ha
  refine ⟨4*C, by positivity, ?_⟩
  intro s z hs hz
  have hlow {w : ℂ} (hw : 0 ≤ w.re) : 0 < ‖1+w‖ := by
    have h := denominator_height hw
    linarith only [h,abs_nonneg w.im]
  have hh {w : ℂ} (hw : 0 ≤ w.re) : heightGrowth w.im / ‖1+w‖ ≤ 2*(1+|w.im|)^(-(3/4:ℝ)) := by
    have hv : 0 < 1+|w.im| := by positivity
    have hpow : (1+|w.im|)^(-(3/4:ℝ)) = heightGrowth w.im / (1+|w.im|) := by
      rw [show -(3/4:ℝ) = 1/4-1 by norm_num, Real.rpow_sub hv,Real.rpow_one,heightGrowth]
    rw [hpow, ← mul_div_assoc, div_le_div_iff₀ (hlow hw) hv]
    have H := mul_le_mul_of_nonneg_left (denominator_height hw) (heightGrowth_pos w.im).le
    linarith only [H]
  have h1 := hh (ha.le.trans hs.1)
  have h2 := hh (w := conj z) (ha.le.trans hz.1)
  simp only [Complex.conj_im, abs_neg, heightGrowth] at h2
  rw [boundaryKernel,norm_div,norm_mul]
  calc
    _ ≤ C * heightGrowth s.im * heightGrowth z.im / (‖1+s‖*‖1+conj z‖) :=
      div_le_div_of_nonneg_right (hb s z hs hz) (by positivity)
    _ = C * (heightGrowth s.im / ‖1+s‖) * (heightGrowth z.im / ‖1+conj z‖) := by ring
    _ ≤ C * (2*(1+|s.im|)^(-(3/4:ℝ))) * (2*(1+|z.im|)^(-(3/4:ℝ))) := by
      gcongr
    _ = _ := by ring

#print axioms boundaryKernel_strip_decay
end
end GaloisForLFunctions.Goldbach.LiLiu
