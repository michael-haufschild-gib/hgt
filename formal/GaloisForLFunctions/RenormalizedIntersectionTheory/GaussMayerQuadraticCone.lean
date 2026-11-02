import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerQuadraticAveraging
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPeriodMellin

/-! Absolute quadratic lattice sums admit a Cauchy averaging transform
into the actual linear Mayer cone. Norm integrals of individual lattice
terms are summable, so the transform uses an actual Bochner integral. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticAveraging
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerQuadraticCone

private def linearWeight (a : ℝ) (p : ℕ × ℕ) : ℝ :=
  ((p.1 : ℝ)+1)*a+((p.2 : ℝ)+1)

/-- The rectangular quadratic form on the strictly positive lattice quadrant. -/
def quadraticWeight (a : ℝ) (p : ℕ × ℕ) : ℝ :=
  (((p.1 : ℝ)+1)*a)^2+((p.2 : ℝ)+1)^2

/-- The actual positive quadrant of the rectangular quadratic lattice. -/
def quadraticCone (w : ℂ) (a : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, (quadraticWeight a p : ℂ)^(-w/2)

private theorem linearWeight_pos {a : ℝ} (ha : 0 < a) (p : ℕ × ℕ) :
    0 < linearWeight a p := by unfold linearWeight; positivity

private theorem quadraticWeight_pos (a : ℝ) (p : ℕ × ℕ) :
    0 < quadraticWeight a p := by unfold quadraticWeight; positivity

private theorem linearWeight_barnes (a : ℝ) (p : ℕ × ℕ) :
    linearWeight a p=(a+1)+barnesLattice a 1 p := by
  unfold linearWeight barnesLattice
  ring

private theorem linear_summable {a σ : ℝ} (ha : 0 < a) (hσ : 2 < σ) :
    Summable (fun p : ℕ × ℕ => linearWeight a p ^ (-σ)) := by
  simpa only [linearWeight_barnes] using
    summable_barnesLattice_rpow (c := a+1) ha zero_lt_one (by linarith only [ha]) hσ

private theorem conePeriod_eq_tsum (w : ℂ) (a : ℝ) :
    MayerPeriodMellin.conePeriod w a=
      ∑' p : ℕ × ℕ, (linearWeight a p : ℂ)^(-w) := by
  unfold MayerPeriodMellin.conePeriod barnesDoubleZeta
  apply tsum_congr
  intro p
  rw [linearWeight_barnes]
  congr 1
  push_cast
  ring

private theorem quadratic_majorant {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (p : ℕ × ℕ) :
    quadraticWeight a p ^ (-σ/2) ≤
      (2 : ℝ)^(σ/2)*linearWeight a p ^ (-σ) := by
  have hl := linearWeight_pos ha p
  have hq := quadraticWeight_pos a p
  have hbound : (linearWeight a p)^2/2 ≤ quadraticWeight a p := by
    unfold linearWeight quadraticWeight
    nlinarith only [sq_nonneg (((p.1 : ℝ)+1)*a-((p.2 : ℝ)+1))]
  have hm := Real.rpow_le_rpow_of_nonpos (div_pos (sq_pos_of_pos hl) (by norm_num))
    hbound (by linarith only [hσ] : -σ/2 ≤ 0)
  have he : ((linearWeight a p)^2/2)^(-σ/2)=
      (2 : ℝ)^(σ/2)*linearWeight a p ^ (-σ) := by
    rw [Real.div_rpow (sq_nonneg _) (by norm_num),← Real.rpow_natCast,
      ← Real.rpow_mul hl.le,Nat.cast_ofNat,show (2 : ℝ)*(-σ/2)= -σ by ring,
      show -σ/2= -(σ/2) by ring,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv,inv_inv]
    ring
  exact hm.trans_eq he

/-- Every positive-period quadratic lattice series is absolutely convergent in the source chamber. -/
theorem summable_quadraticCone {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    Summable (fun p : ℕ × ℕ => ‖(quadraticWeight a p : ℂ)^(-w/2)‖) := by
  refine ((linear_summable ha hw).mul_left ((2 : ℝ)^(w.re/2))).of_nonneg_of_le
    (fun p => norm_nonneg _) (fun p => ?_)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (quadraticWeight_pos a p)]
  have he : (-w/2).re= -w.re/2 := by simp
  rw [he]
  exact quadratic_majorant ha (by linarith only [hw]) p

private def realIntegrand (σ a b t : ℝ) : ℝ :=
  t^σ/((1+t^2)^((σ+2)/2)*(b^2+a^2*t^2)^(σ/2))

private theorem norm_integrand {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (w : ℂ) : ‖quadraticIntegrand w a b t‖=realIntegrand w.re a b t := by
  rw [quadraticIntegrand,norm_div,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 1+t^2),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < b^2+a^2*t^2)]
  have h1 : ((w+2)/2).re=(w.re+2)/2 := by simp
  have h2 : (w/2).re=w.re/2 := by simp
  rw [h1,h2]
  rfl

private theorem real_integrand_eq {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (σ : ℝ) : quadraticIntegrand (σ : ℂ) a b t=(realIntegrand σ a b t : ℂ) := by
  have h1 : ((σ : ℂ)+2)/2=(((σ+2)/2 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (σ : ℂ)/2=((σ/2 : ℝ) : ℂ) := by push_cast; rfl
  rw [quadraticIntegrand,h1,h2,← Complex.ofReal_cpow ht.le,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ 1+t^2),
    ← Complex.ofReal_cpow (by positivity : 0 ≤ b^2+a^2*t^2)]
  simp only [realIntegrand,Complex.ofReal_div,Complex.ofReal_mul]

private theorem integral_norm_integrand {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) :
    (∫ t in Ioi (0 : ℝ), ‖quadraticIntegrand w a b t‖)=
      (MayerScatteringNormalization.archimedeanFactor (((w.re : ℂ)+2)/2)/2).re*
        (a+b)^(-w.re) := by
  have hr : 2 < (w.re : ℂ).re := hw
  have he (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ‖quadraticIntegrand w a b t‖=(quadraticIntegrand (w.re : ℂ) a b t).re := by
    rw [norm_integrand ha hb ht,real_integrand_eq ha hb ht,Complex.ofReal_re]
  rw [setIntegral_congr_fun measurableSet_Ioi he]
  have hi := integral_re (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (quadraticIntegrand_integrable ha hb hr)
  simp only [RCLike.re_to_complex] at hi
  rw [hi,quadratic_integral ha hb hr]
  rw [show -(w.re : ℂ)=((-w.re : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (add_pos ha hb).le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

/-- The exact Cauchy normalization of one quadratic lattice term. -/
def averagingFactor (w : ℂ) : ℂ :=
  MayerScatteringNormalization.archimedeanFactor ((w+2)/2)/2

private def latticeIntegrand (w : ℂ) (a : ℝ) (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  quadraticIntegrand w ((p.2 : ℝ)+1) (((p.1 : ℝ)+1)*a) t

/-- The even Cauchy power in the averaging integral. -/
def cauchyWeight (w : ℂ) (t : ℝ) : ℂ :=
  ((1+t^2 : ℝ) : ℂ)^(-((w+2)/2))

private theorem latticeIntegrand_integrable {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) (p : ℕ × ℕ) :
    IntegrableOn (latticeIntegrand w a p) (Ioi 0) :=
  quadraticIntegrand_integrable (by positivity) (by positivity) hw

private theorem lattice_integral {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) (p : ℕ × ℕ) :
    (∫ t in Ioi (0 : ℝ), latticeIntegrand w a p t)=
      averagingFactor w*(linearWeight a p : ℂ)^(-w) := by
  have h := quadratic_integral (a := (p.2 : ℝ)+1) (b := ((p.1 : ℝ)+1)*a)
    (by positivity) (by positivity) hw
  have he : ((p.2 : ℝ)+1)+((p.1 : ℝ)+1)*a=linearWeight a p := by
    unfold linearWeight
    ring
  rw [he] at h
  exact h

private theorem summable_integral_norm {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) :
    Summable (fun p : ℕ × ℕ => ∫ t in Ioi (0 : ℝ), ‖latticeIntegrand w a p t‖) := by
  have h := (linear_summable ha hw).mul_left (averagingFactor (w.re : ℂ)).re
  refine h.congr fun p => ?_
  have he : ((p.2 : ℝ)+1)+((p.1 : ℝ)+1)*a=linearWeight a p := by
    unfold linearWeight
    ring
  have hi := integral_norm_integrand (a := (p.2 : ℝ)+1) (b := ((p.1 : ℝ)+1)*a)
    (by positivity) (by positivity) hw
  rw [he] at hi
  exact hi.symm

private theorem quadratic_dilation {t : ℝ} (ht : 0 < t) (a : ℝ) (p : ℕ × ℕ) (w : ℂ) :
    cauchyWeight w t*(quadraticWeight (a/t) p : ℂ)^(-w/2)=latticeIntegrand w a p t := by
  have he : quadraticWeight (a/t) p*t^2=
      (((p.1 : ℝ)+1)*a)^2+((p.2 : ℝ)+1)^2*t^2 := by
    unfold quadraticWeight
    field_simp [ht.ne']
  have hpow := congrArg (fun x : ℝ => (x : ℂ)^(w/2)) he
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg
    (quadraticWeight_pos (a/t) p).le (sq_nonneg t)] at hpow
  have hs : ((t^2 : ℝ) : ℂ)^(w/2)=(t : ℂ)^w := by
    have h := Complex.cpow_mul_ofReal_nonneg ht.le (2 : ℝ) (w/2)
    rw [show t^(2 : ℝ)=t^2 from Real.rpow_natCast t 2] at h
    have he : ((2 : ℝ) : ℂ)*(w/2)=w := by push_cast; ring
    simpa only [he] using h.symm
  rw [hs] at hpow
  have hq : (quadraticWeight (a/t) p : ℂ)^(w/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (quadraticWeight_pos (a/t) p).ne'))
  have htP : (t : ℂ)^w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  have huP : ((1+t^2 : ℝ) : ℂ)^((w+2)/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))))
  rw [latticeIntegrand,quadraticIntegrand,← hpow,cauchyWeight,
    show -w/2= -(w/2) by ring]
  simp only [Complex.cpow_neg]
  field_simp [hq,htP,huP]

private theorem tsum_latticeIntegrand {t : ℝ} (ht : 0 < t) (a : ℝ) (w : ℂ) :
    (∑' p : ℕ × ℕ, latticeIntegrand w a p t)=cauchyWeight w t*quadraticCone w (a/t) := by
  rw [quadraticCone,← tsum_mul_left]
  exact tsum_congr fun p => (quadratic_dilation ht a p w).symm

/-- Absolute convergence of the actual quadratic cone's Cauchy average. -/
theorem quadratic_average_integrable {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyWeight w t*quadraticCone w (a/t)) (Ioi 0) := by
  have h := integrable_tsum_of_summable_integral_norm
    (fun p => latticeIntegrand_integrable hw ha p) (summable_integral_norm hw ha)
  exact MeasureTheory.IntegrableOn.congr_fun h
    (fun t ht => tsum_latticeIntegrand ht a w) measurableSet_Ioi

/-- Cauchy averaging of the genuine quadratic lattice equals the actual Mayer cone. -/
theorem quadratic_average_eq_cone {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), cauchyWeight w t*quadraticCone w (a/t))=
      averagingFactor w*MayerPeriodMellin.conePeriod w a := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => (tsum_latticeIntegrand ht a w).symm),
    integral_tsum_eq_tsum_integral_of_summable_integral_norm
      (fun p => latticeIntegrand_integrable hw ha p) (summable_integral_norm hw ha)]
  calc
    _ = ∑' p : ℕ × ℕ, averagingFactor w*(linearWeight a p : ℂ)^(-w) :=
      tsum_congr (lattice_integral hw ha)
    _ = _ := by rw [tsum_mul_left,conePeriod_eq_tsum]

private theorem gamma_ne_zero {s : ℂ} (hs : 0 < s.re) : Complex.Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero (fun n hn => by
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at hr
    linarith only [hr,hs,Nat.cast_nonneg (α := ℝ) n])

/-- The Cauchy normalization is a unit throughout the absolute source chamber. -/
theorem averagingFactor_ne_zero {w : ℂ} (hw : 2 < w.re) : averagingFactor w ≠ 0 := by
  have hs : 0 < ((w+2)/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  have ht : 0 < (((w+2)/2)-1/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  unfold averagingFactor MayerScatteringNormalization.archimedeanFactor
  apply div_ne_zero _ (by norm_num)
  apply div_ne_zero _ (gamma_ne_zero hs)
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (gamma_ne_zero ht)

/-- The normalized Cauchy averaging kernel for multiplicative convolution. -/
def cauchyKernel (w : ℂ) (t : ℝ) : ℂ :=
  (averagingFactor w)⁻¹*(t : ℂ)*cauchyWeight w t

private theorem kernel_integrand {t : ℝ} (ht : 0 < t) (w : ℂ) (a : ℝ) :
    cauchyKernel w t*quadraticCone w (a/t)/(t : ℂ)=
      (averagingFactor w)⁻¹*(cauchyWeight w t*quadraticCone w (a/t)) := by
  unfold cauchyKernel
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

/-- The normalized transform is an absolutely convergent actual convolution integral. -/
theorem cauchyKernel_convolution_integrable {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyKernel w t*quadraticCone w (a/t)/(t : ℂ)) (Ioi 0) := by
  have h := (quadratic_average_integrable hw ha).const_mul (averagingFactor w)⁻¹
  exact MeasureTheory.IntegrableOn.congr_fun h
    (fun t ht => (kernel_integrand ht w a).symm) measurableSet_Ioi

/-- The actual quadratic cone maps to the actual Mayer cone by Cauchy averaging. -/
theorem cauchyKernel_convolution {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (quadraticCone w) a=
      MayerPeriodMellin.conePeriod w a := by
  rw [_root_.RHTower.positiveMellinConvolution,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => kernel_integrand ht w a),
    integral_const_mul,quadratic_average_eq_cone hw ha,
    inv_mul_cancel_left₀ (averagingFactor_ne_zero hw)]

#print axioms summable_quadraticCone
#print axioms integral_norm_integrand
#print axioms summable_integral_norm
#print axioms quadratic_average_integrable
#print axioms quadratic_average_eq_cone
#print axioms averagingFactor_ne_zero
#print axioms cauchyKernel_convolution_integrable
#print axioms cauchyKernel_convolution
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerQuadraticCone
