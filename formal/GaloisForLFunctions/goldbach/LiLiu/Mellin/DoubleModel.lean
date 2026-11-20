import GaloisForLFunctions.goldbach.LiLiu.Mellin.ModelEvaluation
import GaloisForLFunctions.goldbach.LiLiu.Mellin.SignedBetaMellin
import GaloisForLFunctions.goldbach.LiLiu.Mellin.BetaContinuation
import GaloisForLFunctions.goldbach.LiLiu.Boundary.ModelKernelBound
import GaloisForLFunctions.goldbach.LiLiu.Boundary.KernelRegularity

/-! # Evaluation of the double model integral on the arithmetic strip -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

private theorem product_integral_sub (f : ℝ × ℝ → ℂ) (hm : Measurable f) (hi : Integrable f) :
    (∫ p, f p) = ∫ v : ℝ, ∫ x : ℝ, f (x,x-v) := by
  have h := (integrable_prod_iff hm.aestronglyMeasurable).mp hi
  let g (p : ℝ × ℝ) := f (p.1,p.1-p.2)
  have hg : Measurable g := hm.comp (measurable_fst.prodMk (measurable_fst.sub measurable_snd))
  have hG : Integrable g := (integrable_prod_iff hg.aestronglyMeasurable).mpr ⟨
    h.1.mono (fun x hx => hx.comp_sub_left x), by simpa only [g,integral_sub_left_eq_self] using h.2⟩
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, f (x,y) := integral_prod _ hi
    _ = ∫ x : ℝ, ∫ v : ℝ, f (x,x-v) := integral_congr_ae (Eventually.of_forall
      (fun x => (integral_sub_left_eq_self (fun y : ℝ => f (x,y)) volume x).symm))
    _ = _ := integral_integral_swap hG

def modelTestKernel (N : ℕ) (φ : TestWeight) (σ : ℝ) (p : ℝ × ℝ) : ℂ :=
  let s := mellinLine σ p.1
  let z := mellinLine σ p.2
  (mellinMultiplier N φ s * conj (mellinMultiplier N φ z)) * betaModel N s (conj z)

theorem modelTestKernel_continuous {N : ℕ} (hN : 0 < N) (φ : TestWeight) {σ : ℝ}
    (hs : σ ∈ Ioo (0:ℝ) (3/2)) : Continuous (modelTestKernel N φ σ) := by
  have hc : Continuous (mellinLine σ) := by unfold mellinLine; fun_prop
  have hV := (mellinMultiplier_continuous N hN φ).comp hc
  have hcoords := (hc.comp continuous_fst).prodMk (continuous_conj.comp (hc.comp continuous_snd))
  apply ((hV.comp continuous_fst).mul (continuous_conj.comp (hV.comp continuous_snd))).mul
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (betaModel_differentiableAt hN (p := (mellinLine σ p.1,conj (mellinLine σ p.2)))
    (by simpa [mellinLine] using hs) (by simpa [mellinLine] using hs)).continuousAt.comp hcoords.continuousAt

theorem modelTestKernel_integrable {N : ℕ} (hN : 4 ≤ N) (φ : TestWeight) {σ : ℝ}
    (hσ : 0 < σ) (ht : σ ≤ 1/8) : Integrable (modelTestKernel N φ σ) := by
  have hp : 0 < N := by omega
  have H := mellinMultiplier_quarter_integrable N hp φ σ
  obtain ⟨B,hB,hb⟩ := betaModel_strip_bound hN hσ
  have hm := modelTestKernel_continuous hp φ ⟨hσ,by linarith only [ht]⟩
  apply ((H.mul_prod H).const_mul B).mono' hm.aestronglyMeasurable
  filter_upwards with p
  let s := mellinLine σ p.1
  let z := mellinLine σ p.2
  have hk := hb s (conj z) (by simp [s,mellinLine,ht]) (by simp [z,mellinLine,ht])
  simp only [Complex.conj_im,abs_neg] at hk
  change ‖(_ * conj _) * betaModel N s (conj z)‖ ≤ _
  rw [norm_mul,norm_mul,RCLike.norm_conj]
  calc
    _ ≤ (‖mellinMultiplier N φ s‖ * ‖mellinMultiplier N φ z‖) *
        (B*(1+|s.im|)^(1/4:ℝ)*(1+|z.im|)^(1/4:ℝ)) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by simp only [s,z,mellinLine,add_im,ofReal_im,zero_add,mul_I_im,ofReal_re]; ring

/-- Formula (7.6) in Hermitian coordinates. The shear sends the sum of the
holomorphic Mellin variables to the single density variable. -/
theorem doubleModel_integral {N : ℕ} (hN : 4 ≤ N) (φ : TestWeight) {σ : ℝ}
    (hσ : 0 < σ) (ht : σ ≤ 1/8) :
    (1/(2*Real.pi):ℂ)^2 * (∫ p, modelTestKernel N φ σ p) = -(singularSeries N * φ.mass : ℝ) := by
  let c := (1/(2*Real.pi):ℂ)
  let s := mellinLine σ
  let w := mellinLine (2*σ)
  let M := mellin (companion φ)
  let D (v : ℝ) := (singularSeries N:ℂ) * riemannZeta (w v) * densityEuler N (w v)
  have hp : 0 < N := by omega
  have hhalf : σ < 1/2 := by linarith only [ht]
  have hre (v : ℝ) : (w v).re = 2*σ := by simp [w,mellinLine]
  have he (x v : ℝ) : modelTestKernel N φ σ (x,x-v) =
      D v * (M (s x) * M (w v-s x) * signedBeta (s x) (w v-s x)) := by
    let z := w v - s x
    have hZ : conj (s (x-v)) = z := by apply Complex.ext <;> simp [s,w,z,mellinLine] <;> ring
    have hsz : s x+z = w v := by dsimp [z]; ring
    have hr : (s x).re=σ := by simp [s,mellinLine]
    have hz : z.re=σ := by simp [z,hre,hr]; ring
    have hK := scaled_betaModel hp (s := s x) (z := z) (hr ▸ hσ) (hr ▸ hhalf) (hz ▸ hσ) (hz ▸ hhalf)
    change (mellinMultiplier N φ (s x) * conj (mellinMultiplier N φ (s (x-v)))) * _ = _
    rw [← mellinMultiplier_conj N hp φ, hZ]
    calc
      _ = (N:ℂ)^(s x+z)*betaModel N (s x) z * (M (s x)*M z) := by
        rw [cpow_add _ _ (Nat.cast_ne_zero.mpr hp.ne')]
        dsimp [mellinMultiplier,M]
        ring
      _ = _ := by rw [hK,hsz]; dsimp only [D,z]; ring
  have hs (v : ℝ) : c * (∫ x : ℝ, modelTestKernel N φ σ (x,x-v)) = continuedProfileDensity N φ (w v) := by
    have hne : w v ≠ 1 := by
      intro e
      have hh := hre v
      rw [e,one_re] at hh
      linarith only [hh,ht]
    rw [continuedProfileDensity_eq hne, signedBeta_mellin_identity φ hσ hhalf (hre v)]
    simp only [he,integral_const_mul,D,M,s,c]
    ring
  have hC := (modelTestKernel_continuous hp φ ⟨hσ,by linarith only [ht]⟩).measurable
  rw [product_integral_sub _ hC (modelTestKernel_integrable hN φ hσ ht)]
  change c^2 * _ = _
  rw [pow_two,mul_assoc,← integral_const_mul]
  simp_rw [hs]
  exact singleModel_integral hp.ne' φ (by positivity : 0 < 2*σ) (by linarith only [ht])

#print axioms doubleModel_integral
end
end GaloisForLFunctions.Goldbach.LiLiu
