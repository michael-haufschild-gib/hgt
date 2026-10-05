import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicTransverse
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Partial Poisson summation of every third Fourier lift

The complete physical two-frequency slice is identified with the inverse
Schwartz transform of an affine-line Fourier restriction. Compact-domain
continuity and ordinary Fourier inversion justify the identification.
Shifted Poisson changes the full third-lift series to an exact finite physical
height sum, retaining both tangential frequencies and their full outer lift
sums. The actual unconditional family keeps the original negligible edge
error. No lattice/integral exchange or growing signed saving is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform ContDiff Topology
namespace RHTower.BAGTrace

private def thirdLine (ξ υ t : ℝ) : BAGPhysicalSpace := WithLp.toLp 2 ![ξ,υ,t]

private lemma thirdLine_growth (ξ υ : ℝ) : (thirdLine ξ υ).HasTemperateGrowth := by
  have he : thirdLine ξ υ=fun t : ℝ => WithLp.toLp 2 ![ξ,υ,0] +
      t • (WithLp.toLp 2 ![0,0,1] : BAGPhysicalSpace) := by
    funext t; ext i; fin_cases i <;> simp [thirdLine]
  rw [he]
  fun_prop

private lemma thirdLine_lower (ξ υ t : ℝ) : ‖t‖ ≤ 1+‖thirdLine ξ υ t‖ := by
  have h := PiLp.norm_apply_le (thirdLine ξ υ t) 2
  change ‖t‖ ≤ ‖thirdLine ξ υ t‖ at h
  linarith

def bagThirdFrequencySchwartz (f : SchwartzMap BAGPhysicalSpace ℂ) (ξ υ : ℝ) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℂ (thirdLine_growth ξ υ)
    ⟨1,1,by simpa using thirdLine_lower ξ υ⟩ (𝓕 f)

def bagThirdPhysicalSlice (f : BAGPhysicalSpace → ℂ) (ξ υ r : ℝ) : ℂ :=
  ∫ q : ℝ, ∫ p : ℝ, Complex.exp ((-2*Real.pi*(p*ξ+q*υ) : ℝ)*Complex.I)*
    f (WithLp.toLp 2 ![p,q,r])

private lemma slice_fourier (f : SchwartzMap BAGPhysicalSpace ℂ) (ξ υ ζ : ℝ) :
    (𝓕 (bagThirdPhysicalSlice f ξ υ)) ζ = bagThirdFrequencySchwartz f ξ υ ζ := by
  let w := thirdLine ξ υ ζ
  let K : BAGPhysicalSpace → ℂ := fun v =>
    Complex.exp ((-2*Real.pi*inner ℝ v w : ℝ)*Complex.I)*f v
  have hi : Integrable K := by
    have h := (Real.fourierIntegral_convergent_iff (μ := volume) (f := (f : BAGPhysicalSpace → ℂ)) w).mpr f.integrable
    simpa only [K,Circle.smul_def,Real.fourierChar_apply,smul_eq_mul,mul_neg,neg_mul] using h
  have hh := (Transverse.integral_three K hi).2
  change _ = (𝓕 f) w
  rw [SchwartzMap.fourier_coe]
  conv_rhs => rw [Real.fourier_eq']
  change _ = ∫ v, K v
  rw [hh,Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [bagThirdPhysicalSlice,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp only [K,w,thirdLine]
  simp only [PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,
    add_zero,Matrix.cons_val_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma slice_regular (f : SchwartzMap BAGPhysicalSpace ℂ) (a b : ℝ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) (ξ υ : ℝ) :
    Continuous (bagThirdPhysicalSlice f ξ υ) ∧ HasCompactSupport (bagThirdPhysicalSlice f ξ υ) := by
  let K : ℝ → ℝ → ℝ → ℂ := fun r q p =>
    Complex.exp ((-2*Real.pi*(p*ξ+q*υ) : ℝ)*Complex.I)*f (WithLp.toLp 2 ![p,q,r])
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => K z.1.1 z.1.2 z.2) := by
    dsimp only [K]
    apply Continuous.mul
    · fun_prop
    · apply f.continuous.comp
      exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.continuous.comp (by fun_prop)
  have hp (r q : ℝ) : (∫ p in Icc a b, K r q p)=∫ p : ℝ, K r q p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    dsimp only [K]
    rw [hs _ 0 (by simpa using hp),mul_zero]
  have hq (r q : ℝ) (hq : q ∉ Icc a b) : (∫ p in Icc a b, K r q p)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with p
    dsimp only [K]
    simp only [hs (WithLp.toLp 2 ![p,q,r]) 1 hq,mul_zero,Pi.zero_apply]
  have he (r : ℝ) : (∫ q in Icc a b, ∫ p in Icc a b, K r q p)=bagThirdPhysicalSlice f ξ υ r := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hq r)]
    simp only [hp,bagThirdPhysicalSlice,K]
  have hinner := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun z : ℝ × ℝ => fun p : ℝ => K z.1 z.2 p) hc (s := Icc a b) isCompact_Icc
  have houter := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun r q : ℝ => ∫ p in Icc a b, K r q p) hinner (s := Icc a b) isCompact_Icc
  constructor
  · simpa only [he] using houter
  · apply HasCompactSupport.intro (show IsCompact (Icc a b) from isCompact_Icc)
    intro r hr
    unfold bagThirdPhysicalSlice
    apply integral_eq_zero_of_ae
    filter_upwards [] with q
    apply integral_eq_zero_of_ae
    filter_upwards [] with p
    simp only [hs (WithLp.toLp 2 ![p,q,r]) 2 hr,mul_zero,Pi.zero_apply]

theorem bagThirdPhysicalSlice_eq_inverse (f : SchwartzMap BAGPhysicalSpace ℂ) (a b : ℝ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) (ξ υ : ℝ) :
    bagThirdPhysicalSlice f ξ υ = (𝓕⁻ (bagThirdFrequencySchwartz f ξ υ) : SchwartzMap ℝ ℂ) := by
  have hr := slice_regular f a b hs ξ υ
  have hi : Integrable (bagThirdPhysicalSlice f ξ υ) := hr.1.integrable_of_hasCompactSupport hr.2
  have hF : 𝓕 (bagThirdPhysicalSlice f ξ υ)=(bagThirdFrequencySchwartz f ξ υ : ℝ → ℂ) :=
    funext (slice_fourier f ξ υ)
  have he := hr.1.fourierInv_fourier_eq hi (by rw [hF]; exact (bagThirdFrequencySchwartz f ξ υ).integrable)
  rw [hF] at he
  simpa only [SchwartzMap.fourierInv_coe] using he.symm

theorem bagThirdPhysicalSlice_zero (f : BAGPhysicalSpace → ℂ) (a b : ℝ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0)
    (ξ υ r : ℝ) (hr : r ∉ Icc a b) : bagThirdPhysicalSlice f ξ υ r=0 := by
  unfold bagThirdPhysicalSlice
  apply integral_eq_zero_of_ae
  filter_upwards [] with q
  apply integral_eq_zero_of_ae
  filter_upwards [] with p
  simp only [hs (WithLp.toLp 2 ![p,q,r]) 2 hr,mul_zero,Pi.zero_apply]

theorem bagThirdLift_poisson (f : SchwartzMap BAGPhysicalSpace ℂ) (a b : ℝ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) (ξ υ z : ℝ) :
    (∑' k : ℤ, (𝓕 f) (WithLp.toLp 2 ![ξ,υ,(k : ℝ)-z])) =
      ∑' n : ℤ, Complex.exp ((2*Real.pi*(n : ℝ)*z : ℝ)*Complex.I)*
        bagThirdPhysicalSlice f ξ υ n := by
  let h := bagThirdFrequencySchwartz f ξ υ
  have hInv (n : ℤ) : (𝓕 h) (-(n : ℝ))=bagThirdPhysicalSlice f ξ υ n := by
    rw [bagThirdPhysicalSlice_eq_inverse f a b hs ξ υ]
    have he := Real.fourierInv_eq_fourier_neg (h : ℝ → ℂ) (n : ℝ)
    simpa only [SchwartzMap.fourierInv_coe,SchwartzMap.fourier_coe] using he.symm
  calc
    _ = ∑' k : ℤ, h (-z+(k : ℝ)) := by
      apply tsum_congr
      intro k
      change (𝓕 f) (thirdLine ξ υ ((k : ℝ)-z))=(𝓕 f) (thirdLine ξ υ (-z+(k : ℝ)))
      rw [sub_eq_add_neg,add_comm (k : ℝ)]
    _ = ∑' n : ℤ, (𝓕 h) n * fourier n ((-z : ℝ) : UnitAddCircle) := h.tsum_eq_tsum_fourier (-z)
    _ = ∑' n : ℤ, (𝓕 h) (-(n : ℝ)) * fourier (-n) ((-z : ℝ) : UnitAddCircle) := by
      have he := ((Equiv.neg ℤ).tsum_eq
        (fun n : ℤ => (𝓕 h) (n : ℝ) * fourier n ((-z : ℝ) : UnitAddCircle))).symm
      simp only [Equiv.neg_apply] at he
      simpa only [Int.cast_neg] using he
    _ = _ := by
      apply tsum_congr
      intro n
      rw [hInv,fourier_coe_apply]
      have he : Complex.exp (2*Real.pi*Complex.I*((-n : ℤ) : ℂ)*((-z : ℝ) : ℂ)/(1 : ℂ))=
          Complex.exp ((2*Real.pi*(n : ℝ)*z : ℝ)*Complex.I) := by
        congr 1
        push_cast
        ring
      simpa only [Complex.ofReal_one,he] using
        mul_comm (bagThirdPhysicalSlice f ξ υ n)
          (Complex.exp ((2*Real.pi*(n : ℝ)*z : ℝ)*Complex.I))

theorem bagThirdLift_poisson_finite (f : SchwartzMap BAGPhysicalSpace ℂ) (a b : ℝ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) (ξ υ z : ℝ) :
    (∑' k : ℤ, (𝓕 f) (WithLp.toLp 2 ![ξ,υ,(k : ℝ)-z])) =
      ∑ n ∈ Finset.Icc (⌈a⌉ : ℤ) ⌊b⌋,
        Complex.exp ((2*Real.pi*(n : ℝ)*z : ℝ)*Complex.I)*bagThirdPhysicalSlice f ξ υ n := by
  rw [bagThirdLift_poisson f a b hs ξ υ z]
  apply tsum_eq_sum
  intro n hn
  have hr : (n : ℝ) ∉ Icc a b := by
    simpa only [Finset.mem_Icc,Int.ceil_le,Int.le_floor,Set.mem_Icc] using hn
  rw [bagThirdPhysicalSlice_zero f a b hs ξ υ n hr,mul_zero]

/-- The third-lift series is absolutely convergent at every real tangential frequency. -/
theorem summable_norm_bagThirdLift (f : SchwartzMap BAGPhysicalSpace ℂ) (ξ υ z : ℝ) :
    Summable (fun k : ℤ => ‖(𝓕 f) (WithLp.toLp 2 ![ξ,υ,(k : ℝ)-z])‖) := by
  have hi : Function.Injective (fun k : ℤ => ((0 : ℤ),(0 : ℤ),k)) := by
    intro k l h
    exact congrArg (fun v : ℤ × ℤ × ℤ => v.2.2) h
  have h := (summable_norm_bagFourierIntegerTriple f (WithLp.toLp 2 ![ξ,υ,-z])).comp_injective hi
  apply h.congr
  intro k
  dsimp only [Function.comp_apply]
  have he : bagIntegerTriple (0,0,k)+WithLp.toLp 2 ![ξ,υ,-z]=
      WithLp.toLp 2 ![ξ,υ,(k : ℝ)-z] := by
    ext i
    fin_cases i <;> simp [bagIntegerTriple,sub_eq_add_neg]
  rw [he]

/-- Every original lift remains; only the third coordinate is transformed to physical height. -/
theorem bagLiftedFourierTest_eq_partialPoisson (f : SchwartzMap BAGPhysicalSpace ℂ) (a b : ℝ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) (x : ℝ × ℝ × ℝ) :
    bagLiftedFourierTest f x =
      ∑' k : ℤ, ∑' l : ℤ, ∑ n ∈ Finset.Icc (⌈a⌉ : ℤ) ⌊b⌋,
        Complex.exp ((2*Real.pi*(n : ℝ)*x.2.2 : ℝ)*Complex.I)*
          bagThirdPhysicalSlice f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) n := by
  let H : ℤ × ℤ × ℤ → ℂ := fun k =>
    (𝓕 f) (bagIntegerTriple k-WithLp.toLp 2 ![x.1,x.2.1,x.2.2])
  have hh : Summable H := by
    simpa only [H,sub_eq_add_neg] using
      (summable_norm_bagFourierIntegerTriple f (-WithLp.toLp 2 ![x.1,x.2.1,x.2.2])).of_norm
  change (∑' k, H k) = _
  rw [hh.tsum_prod]
  apply tsum_congr
  intro k
  rw [(hh.prod_factor k).tsum_prod]
  apply tsum_congr
  intro l
  have he (n : ℤ) : H (k,l,n)=(𝓕 f)
      (WithLp.toLp 2 ![(k : ℝ)-x.1,(l : ℝ)-x.2.1,(n : ℝ)-x.2.2]) := by
    exact congrArg (fun v : BAGPhysicalSpace => (𝓕 f) v) (by
      ext i
      fin_cases i <;> rfl)
  simp_rw [he]
  exact bagThirdLift_poisson_finite f a b hs _ _ _

private lemma actual_box {N : ℝ} {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → A v=0 := by
  intro v i hi
  have hz0 : η (v i)=0 := hz _ (fun h => hi ⟨h.1.le,h.2.le⟩)
  rw [hA]
  fin_cases i <;> simp_all [bagCubicPhysicalAmplitude,bagCubicMellinSliceValue]

/-- Unconditional actual family with the full third-lift finite-height identity
and the original negligible sharp/smooth error. -/
theorem exists_bagThirdLiftPoissonFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        (∀ ξ υ z : ℝ, Summable (fun k : ℤ =>
          ‖(𝓕 (A N)) (WithLp.toLp 2 ![ξ,υ,(k : ℝ)-z])‖)) ∧
        (∀ x : ℝ × ℝ × ℝ, bagLiftedFourierTest (A N) x =
          ∑' k : ℤ, ∑' l : ℤ, ∑ n ∈ Finset.Icc (⌈(N : ℝ)⌉ : ℤ) ⌊2*(N : ℝ)⌋,
            Complex.exp ((2*Real.pi*(n : ℝ)*x.2.2 : ℝ)*Complex.I)*
              bagThirdPhysicalSlice (A N) ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) n)) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal N-primeGaussianCubicSmoothedOffDiagonal N (η N)‖)
          atTop (𝓝 0) := by
  obtain ⟨η,A,hA,herr⟩ := exists_bagCubicPhysicalFourierFamily
  refine ⟨η,A,?_,herr⟩
  filter_upwards [hA] with N hreg
  refine ⟨hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1,hreg.2.2.2.2.1,
    hreg.2.2.2.2.2.1,summable_norm_bagThirdLift (A N),?_⟩
  exact bagLiftedFourierTest_eq_partialPoisson (A N) N (2*N)
    (actual_box hreg.2.2.2.1 (A N) hreg.2.2.2.2.2.1)

end RHTower.BAGTrace
