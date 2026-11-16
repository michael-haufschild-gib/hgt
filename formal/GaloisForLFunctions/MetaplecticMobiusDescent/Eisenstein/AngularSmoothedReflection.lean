import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularKernelBounds
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularSourceSmoothing

/-!
# Smoothed reflection of the angular cubic source

Absolute Mellin inversion, the actual higher-cusp reflection and a contour shift give an
exact dual sum with opposite angular coefficients. Its conductor scale is unchanged.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

lemma angularPaperKernel_three_halves (k : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    angularPaperKernel k V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        angularMellinEulerData k V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=angularMellinInv_euler_shift k V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change angularPaperKernel k V x=_
  have hl:mellinInv 0 (angularMellinEulerData k V 0) (paperScale*x)=angularPaperKernel k V x:=by
    have hf : angularMellinEulerData k V 0=(fun s:ℂ=>mellin V (-s)*angularCubicReflectionGamma k s) := by
      funext s
      simp only [angularMellinEulerData,pow_zero,one_mul,angularMellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he

lemma angularPaperKernel_three_halves_bound (k : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖angularPaperKernel k V x‖ ≤ C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=angularMellinInv_euler_line_bound k V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=angularMellinInv_euler_shift k V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 (angularMellinEulerData k V 0) (paperScale*x)=angularPaperKernel k V x:=by
    have hf : angularMellinEulerData k V 0=(fun s:ℂ=>mellin V (-s)*angularCubicReflectionGamma k s) := by
      funext s
      simp only [angularMellinEulerData,pow_zero,one_mul,angularMellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)

lemma angularPaperKernel_weighted_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (k : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>a i*angularPaperKernel k V (c*r i)) := by
  obtain ⟨C,hC,hb⟩:=angularPaperKernel_three_halves_bound k V v0 v1 hv0 hVs hV
  apply Summable.of_norm
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _ ≤ ‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

theorem angularPaperKernel_weighted_mellin {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (k : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*angularPaperKernel k V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          angularMellinEulerData k V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    angularMellinEulerData k V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,angularInverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      angularInverseMellinIntegrand_vertical_integrable k V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*angularPaperKernel k V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [angularPaperKernel_three_halves k V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM

theorem angularPaperKernel_weighted_norm_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (k : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*angularPaperKernel k V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=angularPaperKernel_three_halves_bound k V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _ ≤ ‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

/-- Angular twisting preserves absolute summability on the inversion line. -/
lemma angularSourceBar_weighted_summable (k : ℕ) (z : ℂ) :
    Summable (fun h : O => ‖elemPsiSix h ^ k * sourceBarRadialCoefficient z h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
  have hp (h : O) : ‖elemPsiSix h ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one h)
  simpa only [show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num] using
    angular_source_radial_summable (sourceBarRadialCoefficient z) (fun h => elemPsiSix h ^ k)
      hp 2 (sourceBarRadialCoefficient_summable z 2 le_rfl)

lemma angularSourceZ_weighted_summable (k : ℕ) (j : Fin 3) (z : ℂ) :
    Summable (fun h : O => ‖conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient j z h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
  have hp (h : O) : ‖conj (elemPsiSix h) ^ k‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_conj]
    exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one h)
  simpa only [show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num] using
    angular_source_radial_summable (sourceCuspRadialCoefficient j z)
      (fun h => conj (elemPsiSix h) ^ k) hp 2 (sourceCuspRadialCoefficient_summable j z 2 le_rfl)

lemma SourceCuspDatum.angularSmoothing_left_integrable (d : SourceCuspDatum) (k : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => angularSourceSmoothingIntegrand k d.point V X ((-1 : ℂ) + t * Complex.I)) := by
  let M : ℝ → ℂ := fun t =>
    (∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
      (sourceCuspRadialLength h : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) *
      (((paperScale * d.smoothingScale X : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I)) *
        angularMellinEulerData k V 0 ((3 / 2 : ℂ) + t * Complex.I))
  have hK := angularInverseMellinIntegrand_vertical_integrable k V a b ha hVs hV 2 0 (3 / 2)
    (by norm_num) (paperScale * d.smoothingScale X) (mul_pos paperScale_pos (d.smoothingScale_pos X hX))
  have hc : Summable (fun h : O => ‖(conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h)‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    exact angularSourceZ_weighted_summable k d.index d.dualPoint
  have hi : Integrable M := by
    simpa only [M, angularInverseMellinIntegrand, Complex.ofReal_div, Complex.ofReal_ofNat] using
      weighted_vertical_sum_mul_integrable sourceCuspRadialLength sourceCuspRadialLength_pos
        (fun h => conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) (3 / 2)
        hc
        (fun t : ℝ => angularInverseMellinIntegrand k V 0 (paperScale * d.smoothingScale X)
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) hK
  apply ((hi.comp_neg).const_mul (d.angularSmoothingMultiplier k)).congr
  filter_upwards with t
  simpa only [M, Complex.ofReal_neg, neg_neg] using (d.angularSmoothing_reflected_line k V X hX (-t)).symm

theorem SourceCuspDatum.angularSmoothing_left_kernel (d : SourceCuspDatum) (k : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, angularSourceSmoothingIntegrand k d.point V X ((-1 : ℂ) + t * Complex.I)) =
      d.angularSmoothingMultiplier k * ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
        angularPaperKernel k V (d.smoothingScale X * sourceCuspRadialLength h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hc : Summable (fun h : O => ‖(conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h)‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    exact angularSourceZ_weighted_summable k d.index d.dualPoint
  have hk := angularPaperKernel_weighted_mellin sourceCuspRadialLength sourceCuspRadialLength_pos
    (fun h => conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h)
    hc k V a b ha hVs hV
    (d.smoothingScale X) (d.smoothingScale_pos X hX)
  rw [hk]
  rw [← integral_neg_eq_self (fun t : ℝ => angularSourceSmoothingIntegrand k d.point V X ((-1 : ℂ) + t * Complex.I)) volume]
  simp only [Complex.ofReal_neg, d.angularSmoothing_reflected_line k V X hX]
  rw [integral_const_mul]
  ring

/-- Exact smoothed reflection of the actual cubic source at every rational cusp. -/
theorem SourceCuspDatum.angular_smoothed_reflection (d : SourceCuspDatum) (k : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑' h : O, (elemPsiSix h ^ k * sourceBarRadialCoefficient d.point h) * V (sourceCuspRadialLength h / X)) =
      d.angularSmoothingMultiplier k * ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
        angularPaperKernel k V (d.smoothingScale X * sourceCuspRadialLength h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hc : Summable (fun h : O => ‖(elemPsiSix h ^ k * sourceBarRadialCoefficient d.point h)‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    exact angularSourceBar_weighted_summable k d.point
  have hm := weightedMellin_inversion sourceCuspRadialLength sourceCuspRadialLength_pos
    (fun h => elemPsiSix h ^ k * sourceBarRadialCoefficient d.point h) (3 / 2) hc V a b ha hVs hV X hX
  have hmi := compactMellin_vertical_integrable V a b ha hVs hV (3 / 2)
  have hbase := vertical_power_mul_integrable _ hmi X (3 / 2) hX
  have hi := weighted_vertical_sum_mul_integrable sourceCuspRadialLength sourceCuspRadialLength_pos
    (fun h => elemPsiSix h ^ k * sourceBarRadialCoefficient d.point h) (3 / 2) hc
    (fun t : ℝ => (X : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * Complex.I) *
      mellin V (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) hbase
  have hright : Integrable (fun t : ℝ => angularSourceSmoothingIntegrand k d.point V X ((2 : ℂ) + t * Complex.I)) := by
    simp_rw [angularSourceSmoothing_initial_line]
    apply hi.congr
    filter_upwards with t
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hleft' : Integrable (fun t : ℝ => angularSourceSmoothingIntegrand k d.point V X (((-1 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
      d.angularSmoothing_left_integrable k V a b ha hVs hV X hX
  have hright' : Integrable (fun t : ℝ => angularSourceSmoothingIntegrand k d.point V X (((2 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [Complex.ofReal_ofNat] using hright
  have hshift := d.angularSourceSmoothingIntegrand_contour_eq k V a b ha hVs hV X hX (-1) 2 (by norm_num)
    hleft' hright'
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] at hshift
  have hm' : (∑' h : O, (elemPsiSix h ^ k * sourceBarRadialCoefficient d.point h) * V (sourceCuspRadialLength h / X)) =
      (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, angularSourceSmoothingIntegrand k d.point V X ((2 : ℂ) + t * Complex.I)) := by
    simpa only [angularSourceSmoothing_initial_line, Complex.ofReal_div, Complex.ofReal_ofNat] using hm
  rw [hm', ← hshift]
  exact d.angularSmoothing_left_kernel k V a b ha hVs hV X hX


end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
