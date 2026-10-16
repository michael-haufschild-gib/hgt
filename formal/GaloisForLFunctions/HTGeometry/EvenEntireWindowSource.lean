import GaloisForLFunctions.HTGeometry.EvenEntireCompactSource
import Zeta23.ExplicitFormula.Bridge

/-!
# Exact windows for even inverse transforms

Dilation removes the additive type loss in the quadrant/contour construction.
The resulting inverse has the original imaginary-axis support window. This is
the localization step needed to purify mixtures inside a fixed source domain.
-/

open Complex Filter Topology Set MeasureTheory
open scoped FourierTransform ContDiff
noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem SubquadraticType.comp_real_mul {Q : ℂ → ℂ} (hQ : SubquadraticType Q)
    (b : ℝ) : SubquadraticType (fun z => Q ((b : ℂ)*z)) := by
  obtain ⟨p,hp,hp2,A,B,hA,hB,hbound⟩ := hQ
  refine ⟨p,hp,hp2,A,B*|b|^p,hA,by positivity,fun z => ?_⟩
  have h := hbound ((b : ℂ)*z)
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg b) (norm_nonneg z),mul_assoc] using h

theorem angularInverse_comp_pos_mul (Q : ℂ → ℂ) {b : ℝ} (hb : 0<b) (u : ℝ) :
    angularInverse (fun z => Q ((b : ℂ)*z)) (b*u)=b⁻¹ • angularInverse Q u := by
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => Q x*Complex.exp (I*(u : ℂ)*(x : ℂ))) b
  rw [abs_of_pos (inv_pos.mpr hb)] at h
  unfold angularInverse
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  congr 2
  ring

/-- The contour construction retains the exact axis type: the fixed loss
in the existing strip theorem disappears under arbitrary dilation. -/
theorem angularInverse_zero_outside_axis_window {Q : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (he : Function.Even Q) (hs : SubquadraticType Q)
    {M R T : ℝ} (hR : 0≤R)
    (hre : ∀ x : ℝ,‖Q x‖*(1+|x|)^2≤M)
    (him : ∀ y : ℝ,0≤y → ‖Q ((y : ℂ)*I)‖≤R*Real.exp (T*y))
    {u : ℝ} (hu : T<u) : angularInverse Q u=0 := by
  let b : ℝ := max 1 (4/(u-T))
  have hb1 : 1≤b := le_max_left _ _
  have hb : 0<b := lt_of_lt_of_le zero_lt_one hb1
  have hbu : 4≤b*(u-T) := (div_le_iff₀ (sub_pos.mpr hu)).mp (le_max_right _ _)
  let P : ℂ → ℂ := fun z => Q ((b : ℂ)*z)
  have hP : Differentiable ℂ P := hQ.comp (by fun_prop)
  have hPe : Function.Even P := by intro z; dsimp [P]; rw [mul_neg,he]
  have hPre (x : ℝ) : ‖P x‖*(1+|x|)^2≤M := by
    have hh := hre (b*x)
    have hx : |x|≤|b*x| := by
      rw [abs_mul,abs_of_pos hb]
      exact le_mul_of_one_le_left (abs_nonneg x) hb1
    apply hh.trans'
    push_cast
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) (norm_nonneg _)
  have hPim (y : ℝ) (hy : 0≤y) :
      ‖P ((y : ℂ)*I)‖≤R*Real.exp ((T*b)*y) := by
    have hh := him (b*y) (mul_nonneg hb.le hy)
    simpa only [P,Complex.ofReal_mul,mul_assoc] using hh
  -- Keep the explicit type supplied by the quadrant theorem.
  have hupper (z : ℂ) (hz : 0≤z.im) :
      ‖P z‖≤max M R*Real.exp (((T*b)+2)*z.im)*(1+z.re^2)⁻¹ := by
    have hh := upper_weighted_bound_of_axes hP (hs.comp_real_mul b) 2 hR hPre hPim z hz
    have hd : 1+z.re^2≤‖z+I‖^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
        Complex.I_re,Complex.I_im,add_zero]
      nlinarith
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans hh
  have hstrip (z : ℂ) :
      ‖P z‖≤max M R*Real.exp (((T*b)+2)*|z.im|)*(1+z.re^2)⁻¹ := by
    by_cases hz : 0≤z.im
    · simpa only [abs_of_nonneg hz] using hupper z hz
    · have hh := hupper (-z) (by simp only [Complex.neg_im]; linarith)
      rw [hPe z] at hh
      simpa only [Complex.neg_re,Complex.neg_im,neg_sq,
        abs_of_neg (lt_of_not_ge hz)] using hh
  have hz := angularInverse_zero_of_type_lt hP
    (hR.trans (le_max_right M R)) hstrip (show T*b+2<b*u by nlinarith)
  rw [angularInverse_comp_pos_mul Q hb u] at hz
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hb.ne')

theorem compactInverse_tsupport_subset_axis_window {Q : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (he : Function.Even Q) (hs : SubquadraticType Q)
    {M R T : ℝ} (hR : 0≤R)
    (hre : ∀ x : ℝ,‖Q x‖*(1+|x|)^2≤M)
    (him : ∀ y : ℝ,0≤y → ‖Q ((y : ℂ)*I)‖≤R*Real.exp (T*y)) :
    tsupport (compactInverse Q) ⊆ Icc (-T) T := by
  change closure (Function.support (compactInverse Q)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra hh
  have hn : compactInverse Q u≠0 := hu
  simp only [mem_Icc,not_and_or,not_le] at hh
  apply hn
  have hz : angularInverse Q u=0 := by
    rcases hh with hh | hh
    · rw [← angularInverse_even he u]
      exact angularInverse_zero_outside_axis_window hQ he hs hR hre him (by linarith)
    · exact angularInverse_zero_outside_axis_window hQ he hs hR hre him hh
  simp only [compactInverse,hz,smul_zero]

/-- Fourier inversion identifies the localized inverse with any existing
even C² compact source having this entire transform. -/
theorem compactInverse_eq_of_paperFT {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) {Q : ℂ → ℂ} (he : Function.Even Q)
    (hft : ∀ z,Zeta23.paperFT f z=Q z) : compactInverse Q=f := by
  have hV : (fun x : ℝ => Q ((2*Real.pi*x : ℝ) : ℂ))=𝓕 f := by
    funext x
    rw [Zeta23.fourier_eq_paperFT,hft,he]
    push_cast
    rfl
  rw [compactInverse_eq_fourierInv,hV]
  exact hf.continuous.fourierInv_fourier_eq
    (hf.continuous.integrable_of_hasCompactSupport hfs)
    (Zeta23.EF.integrable_fourier_of_contDiff_two hf hfs)

end GaloisForLFunctions.HTGeometry
