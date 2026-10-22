import GaloisForLFunctions.HTGeometry.DividedDifferenceCauchyProjection
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionInverseSource

/-! # Original-source control of whole Xi divisor blocks

The maximum principle on a padded rectangle controls the entire projector,
including its interior zeros. Only the quotient on the integration contour
enters; no individual residue or zero gap is estimated.
-/

open Complex Set Filter Topology Metric
open HTGeometry GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

def deningerMeyerXiContour (F : ℂ → ℂ) (a b : ℂ) : ℂ → ℂ :=
  entireDividedDifferenceContour xi (fun w => F w/xi w) a b

theorem differentiable_deningerMeyerXiContour {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {a b : ℂ} (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im)
    (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) :
    Differentiable ℂ (deningerMeyerXiContour F a b) :=
  differentiable_entireDividedDifferenceContour deningerMeyerXi_entireRegular.differentiable
    hab hab' (hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz)

private theorem xi_rectangle_padding {a b : ℂ} (ha : a.re = -1) (hb : b.re = 2)
    (hab : a.im ≤ b.im) {T R : ℝ} (hR : 4 ≤ R)
    (haT : -T ≤ a.im) (hbT : b.im ≤ T) {z : ℂ}
    (hz : z.re ≤ -R ∨ R ≤ z.re ∨ z.im ≤ -(T+1) ∨ T+1 ≤ z.im) :
    z ∉ Rectangle a b ∧ ∀ w ∈ RectangleBorder a b, 1 ≤ ‖w-z‖ := by
  have hsep : ∀ w ∈ Rectangle a b, 1 ≤ ‖w-z‖ := by
    intro w hw
    rcases hw with ⟨hre, him⟩
    have hre' : -1 ≤ w.re ∧ w.re ≤ 2 := by
      simpa only [ha, hb, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2), mem_preimage, mem_Icc] using hre
    have him' : a.im ≤ w.im ∧ w.im ≤ b.im := by
      simpa only [uIcc_of_le hab, mem_preimage, mem_Icc] using him
    have hrn := Complex.abs_re_le_norm (w-z)
    have hin := Complex.abs_im_le_norm (w-z)
    simp only [sub_re, sub_im] at hrn hin
    rcases hz with hz | hz | hz | hz
    · linarith [le_abs_self (w.re-z.re)]
    · linarith [neg_le_abs (w.re-z.re)]
    · linarith [le_abs_self (w.im-z.im)]
    · linarith [neg_le_abs (w.im-z.im)]
  refine ⟨fun hz => ?_, fun w hw => hsep w (rectangleBorder_subset_rectangle a b hw)⟩
  have := hsep z hz
  norm_num at this

private theorem xi_cauchy_bound {A : ℂ → ℂ} {a b z : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ w ∈ RectangleBorder a b, ‖A w‖ ≤ M)
    (hsep : ∀ w ∈ RectangleBorder a b, 1 ≤ ‖w-z‖) :
    ‖rectangleCauchyTransform A a b z‖ ≤
      (|b.re-a.re|+|b.im-a.im|)*M/Real.pi := by
  apply norm_rectangleIntegral'_le
  intro w hw
  rw [norm_div]
  simpa using div_le_div₀ hM (hA w hw) zero_lt_one (hsep w hw)

/-- One strip constant works for every rectangular divisor block and every
entire input. Dependence on the block is through its contour quotient alone. -/
theorem deningerMeyerXiContour_weighted_bound (r : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℂ → ℂ), Differentiable ℂ F →
      ∀ (a b : ℂ), a.re = -1 → b.re = 2 → a.im ≤ b.im →
      ∀ (T M : ℝ), 0 ≤ T → -T ≤ a.im → b.im ≤ T → 0 ≤ M →
      (∀ w ∈ RectangleBorder a b, xi w ≠ 0) →
      (∀ w ∈ RectangleBorder a b, ‖F w/xi w‖ ≤ M) →
      ∀ z : ℂ, |z.re| ≤ r →
        ‖deningerMeyerXiContour F a b z‖*(1+z.im^2)^K ≤
          C*(3+|b.im-a.im|)*M*(1+(T+1)^2)^K := by
  let R := max r 3+1
  have hR : 4 ≤ R := by dsimp [R]; linarith [le_max_right r 3]
  have hrR : r ≤ R := by dsimp [R]; linarith [le_max_left r 3]
  obtain ⟨C₀, hC₀⟩ := (deningerMeyerXi_entireRegular (-R-1) (R+1)).decay
    (-R) R (by linarith) (by linarith) K
  have hxi : ∀ z : ℂ, |z.re| ≤ R → ‖xi z‖*(1+z.im^2)^K ≤ |C₀| := by
    intro z hz
    exact ((le_div_iff₀ (by positivity : 0 < (1+z.im^2)^K)).mp
      (hC₀ z (abs_le.mp hz).1 (abs_le.mp hz).2)).trans (le_abs_self _)
  have hxi₀ : ∀ z : ℂ, |z.re| ≤ R → ‖xi z‖ ≤ |C₀| := by
    intro z hz
    have hw : 1 ≤ (1+z.im^2)^K := one_le_pow₀ (by nlinarith [sq_nonneg z.im])
    calc ‖xi z‖ ≤ ‖xi z‖*(1+z.im^2)^K := by nlinarith [norm_nonneg (xi z)]
      _ ≤ |C₀| := hxi z hz
  refine ⟨|C₀|/Real.pi, by positivity, ?_⟩
  intro F hF a b ha hb hab T M hT haT hbT hM hnz hmass z hz
  let L := (3+|b.im-a.im|)*M/Real.pi
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have habre : a.re ≤ b.re := by rw [ha, hb]; norm_num
  have hd := differentiable_deningerMeyerXiContour hF habre hab hnz
  have hext : ∀ u : ℂ,
      u.re ≤ -R ∨ R ≤ u.re ∨ u.im ≤ -(T+1) ∨ T+1 ≤ u.im →
      ‖deningerMeyerXiContour F a b u‖ ≤ ‖xi u‖*L := by
    intro u hu
    obtain ⟨hout, hsep⟩ := xi_rectangle_padding ha hb hab hR haT hbT hu
    have hc := xi_cauchy_bound hM hmass hsep
    have hc' : ‖rectangleCauchyTransform (fun w => F w/xi w) a b u‖ ≤ L := by
      norm_num [ha, hb, L] at hc ⊢
      exact hc
    rw [deningerMeyerXiContour, entireDividedDifferenceContour_outside hF
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz hout,
      norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left hc' (norm_nonneg _)
  have hinside : ∀ u : ℂ, -R ≤ u.re → u.re ≤ R → -(T+1) ≤ u.im → u.im ≤ T+1 →
      ‖deningerMeyerXiContour F a b u‖ ≤ L*|C₀| := by
    apply norm_le_of_rectangle_frontier_bound hd (by linarith : -R < R)
      (by linarith : -(T+1) < T+1)
    intro u hu₁ hu₂ hu₃ hu₄ hboundary
    have hout : u.re ≤ -R ∨ R ≤ u.re ∨ u.im ≤ -(T+1) ∨ T+1 ≤ u.im := by
      rcases hboundary with h | h | h | h
      · exact Or.inl h.le
      · exact Or.inr (Or.inl h.ge)
      · exact Or.inr (Or.inr (Or.inl h.le))
      · exact Or.inr (Or.inr (Or.inr h.ge))
    calc ‖deningerMeyerXiContour F a b u‖ ≤ ‖xi u‖*L := hext u hout
      _ ≤ |C₀| * L := mul_le_mul_of_nonneg_right (hxi₀ u (abs_le.mpr ⟨hu₁, hu₂⟩)) hL
      _ = L*|C₀| := mul_comm _ _
  have hwT : 1 ≤ (1+(T+1)^2)^K := one_le_pow₀ (by nlinarith [sq_nonneg (T+1)])
  have hzR : |z.re| ≤ R := hz.trans hrR
  have hfinal : ‖deningerMeyerXiContour F a b z‖*(1+z.im^2)^K ≤
      L*|C₀| * (1+(T+1)^2)^K := by
    by_cases hzin : -(T+1) ≤ z.im ∧ z.im ≤ T+1
    · have hnorm := hinside z (abs_le.mp hzR).1 (abs_le.mp hzR).2 hzin.1 hzin.2
      have hsq : z.im^2 ≤ (T+1)^2 := by nlinarith [hzin.1, hzin.2]
      exact mul_le_mul hnorm (pow_le_pow_left₀ (by positivity) (by linarith) K)
        (by positivity) (mul_nonneg hL (abs_nonneg _))
    · have hout : z.re ≤ -R ∨ R ≤ z.re ∨ z.im ≤ -(T+1) ∨ T+1 ≤ z.im := by
        by_cases hlow : -(T+1) ≤ z.im
        · exact Or.inr (Or.inr (Or.inr (le_of_not_ge (fun h => hzin ⟨hlow, h⟩))))
        · exact Or.inr (Or.inr (Or.inl (le_of_not_ge hlow)))
      calc
        ‖deningerMeyerXiContour F a b z‖*(1+z.im^2)^K ≤
            (‖xi z‖*L)*(1+z.im^2)^K := mul_le_mul_of_nonneg_right (hext z hout) (by positivity)
        _ = L*(‖xi z‖*(1+z.im^2)^K) := by ring
        _ ≤ L*|C₀| := mul_le_mul_of_nonneg_left (hxi z hzR) hL
        _ ≤ L*|C₀| * (1+(T+1)^2)^K := by
          exact le_mul_of_one_le_right (mul_nonneg hL (abs_nonneg _)) hwT
  calc
    ‖deningerMeyerXiContour F a b z‖*(1+z.im^2)^K ≤
        L*|C₀| * (1+(T+1)^2)^K := hfinal
    _ = _ := by dsimp [L]; ring

end
end RHTower
