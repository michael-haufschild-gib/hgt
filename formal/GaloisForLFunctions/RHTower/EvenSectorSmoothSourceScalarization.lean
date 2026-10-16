import GaloisForLFunctions.RHTower.EvenSectorHermitianScalarization
import GaloisForLFunctions.HTGeometry.EvenEntireCompactSource
import GaloisForLFunctions.HTGeometry.CompactTestTransformOrder

/-!
# Exact scalarization of smooth even pole-free mixtures

The global factor is realized by an actual smooth compact even pole-free
source. Its whole autocorrelation is the original positive finite mixture.
-/

open Complex Filter Topology Set MeasureTheory Finsupp Zeta23
open scoped ComplexConjugate NNReal ContDiff FourierTransform
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.EvenHermitianFactor

noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

def SmoothEvenPolarTestFn : Type :=
  {f : WeilEvenPolarTestFn // ContDiff ℝ ∞ f.1.1}

def smoothPolarCoefficients (c : SmoothEvenPolarTestFn →₀ ℝ≥0) : WeilEvenPolarTestFn →₀ ℝ≥0 :=
  c.mapDomain Subtype.val

theorem smoothPolarCoefficients_smooth (c : SmoothEvenPolarTestFn →₀ ℝ≥0)
    (f : WeilEvenPolarTestFn) (hf : f ∈ (smoothPolarCoefficients c).support) :
    ContDiff ℝ ∞ f.1.1 := by
  classical
  let e : SmoothEvenPolarTestFn ↪ WeilEvenPolarTestFn := ⟨Subtype.val,Subtype.val_injective⟩
  change f ∈ (c.mapDomain e).support at hf
  rw [Finsupp.support_mapDomain_embedding] at hf
  obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hf
  exact g.2

theorem factor_axis_norm_sq (c : WeilEvenPolarTestFn →₀ ℝ≥0) {q : ℂ → ℂ}
    (he : Function.Even q) (hi : ∀ z,evenPolarMixtureSpectrum c z=q z*conj (q (conj z)))
    (z : ℂ) (hz : z.re=0 ∨ z.im=0) :
    ‖q z‖^2=c.sum (fun f t => (t : ℝ)*‖paperFT f.1.1 z‖^2) := by
  have hc : q (conj z)=q z := by
    rcases hz with hz | hz
    · rw [show conj z=-z by apply Complex.ext <;> simp [hz],he z]
    · rw [show conj z=z by apply Complex.ext <;> simp [hz]]
  have hh := hi z
  rw [evenPolarMixtureSpectrum_axis c z hz,hc,Complex.mul_conj,Complex.normSq_eq_norm_sq] at hh
  exact_mod_cast hh.symm

theorem factor_real_decay (c : WeilEvenPolarTestFn →₀ ℝ≥0)
    (hc : ∀ f ∈ c.support,ContDiff ℝ ∞ f.1.1) {q : ℂ → ℂ}
    (he : Function.Even q) (hi : ∀ z,evenPolarMixtureSpectrum c z=q z*conj (q (conj z)))
    (n : ℕ) : ∃ M : ℝ,∀ x : ℝ,‖q x‖*(1+|x|)^n≤M := by
  classical
  have hex (f : WeilEvenPolarTestFn) : ∃ K : ℝ,0≤K ∧
      ∀ (_ : f ∈ c.support) (x : ℝ),‖paperFT f.1.1 x‖*(1+|x|)^n≤K := by
    by_cases hf : f ∈ c.support
    · obtain ⟨K,hK,hb⟩ := exists_testTransform_decay_order (hc f hf) f.1.2.2 0 0 n
      refine ⟨K,hK,fun _ x => ?_⟩
      have hh := hb (x : ℂ) (by simp)
      rw [le_div_iff₀ (by positivity)] at hh
      simpa only [testTransform,Zeta23.paperFT,Complex.norm_real,Real.norm_eq_abs] using hh
    · exact ⟨0,le_rfl,fun hh => False.elim (hf hh)⟩
  choose K hK hKb using hex
  let D := c.sum (fun f t => (t : ℝ)*(K f)^2)
  refine ⟨D+1,fun x => ?_⟩
  have hsq : (‖q x‖*(1+|x|)^n)^2≤D := by
    rw [mul_pow,factor_axis_norm_sq c he hi (x : ℂ) (Or.inr (by simp))]
    dsimp only [D,Finsupp.sum]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro f hf
    calc
      ((c f : ℝ)*‖paperFT f.1.1 x‖^2)*((1+|x|)^n)^2 =
          (c f : ℝ)*(‖paperFT f.1.1 x‖*(1+|x|)^n)^2 := by ring
      _ ≤ (c f : ℝ)*(K f)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (hKb f hf x) 2) (c f).coe_nonneg
  nlinarith [sq_nonneg (‖q x‖*(1+|x|)^n-1/2)]

theorem factor_imaginary_type (c : WeilEvenPolarTestFn →₀ ℝ≥0) {q : ℂ → ℂ}
    (he : Function.Even q) (hi : ∀ z,evenPolarMixtureSpectrum c z=q z*conj (q (conj z))) :
    ∃ R T : ℝ,0≤R ∧ 0≤T ∧ ∀ y : ℝ,0≤y →
      ‖q ((y : ℂ)*I)‖≤R*Real.exp (T*y) := by
  obtain ⟨M,A,hM,hA,hb⟩ := evenPolarMixtureSpectrum_exponential c
  refine ⟨M+1,A,by linarith,hA,fun y hy => ?_⟩
  have hc : conj ((y : ℂ)*I)=-((y : ℂ)*I) := by simp
  have hh := hb ((y : ℂ)*I)
  rw [hi,hc,he ((y : ℂ)*I),norm_mul,Complex.norm_conj,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy] at hh
  have he1 : 1≤Real.exp (A*y) := Real.one_le_exp (mul_nonneg hA hy)
  have hh' : ‖q ((y : ℂ)*I)‖≤M*Real.exp (A*y)+1 := by
    nlinarith [sq_nonneg (‖q ((y : ℂ)*I)‖-1/2)]
  nlinarith

/-- Every smooth positive finite even-polar mixture spectrum is produced by
one actual smooth compact even-polar source. -/
theorem exists_smoothPolar_spectral_scalarization (c : SmoothEvenPolarTestFn →₀ ℝ≥0) :
    ∃ f : SmoothEvenPolarTestFn,∀ z,
      evenPolarMixtureSpectrum (smoothPolarCoefficients c) z=
        paperFT f.1.1.1 z*conj (paperFT f.1.1.1 (conj z)) := by
  let d := smoothPolarCoefficients c
  obtain ⟨q,hq,he,hp,_,hi,hs⟩ := exists_evenPolarMixture_entire_factor_subquadratic d
  have hdec := factor_real_decay d (smoothPolarCoefficients_smooth c) he hi
  obtain ⟨R,T,hR,hT,him⟩ := factor_imaginary_type d he hi
  obtain ⟨f,hf,hfs,hfe,hft⟩ := exists_smooth_compact_source hq he hs hdec hR hT him
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))
  let g : SmoothEvenPolarTestFn := ⟨⟨⟨f,hf2,hfs⟩,hfe,by rw [hft,hp]⟩,hf⟩
  refine ⟨g,fun z => ?_⟩
  change evenPolarMixtureSpectrum d z=paperFT f z*conj (paperFT f (conj z))
  rw [hft,hft]
  exact hi z

/-- The whole autocorrelation profile of a finite positive mixture. -/
def polarMixtureProfile (c : WeilEvenPolarTestFn →₀ ℝ≥0) (u : ℝ) : ℂ :=
  c.sum fun f t => (t : ℂ)*EF.weilTest f.1.1 f.1.1 u

theorem polarMixtureProfile_contDiff (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    ContDiff ℝ 2 (polarMixtureProfile c) := by
  classical
  change ContDiff ℝ 2 (fun u => ∑ f ∈ c.support,(c f : ℂ)*EF.weilTest f.1.1 f.1.1 u)
  apply ContDiff.sum
  intro f _
  exact contDiff_const.mul (EF.weilTest_contDiff f.1.2.1 f.1.2.1.continuous f.1.2.2)

theorem polarMixtureProfile_hasCompactSupport (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    HasCompactSupport (polarMixtureProfile c) := by
  classical
  change HasCompactSupport (fun u => ∑ f ∈ c.support,(c f : ℂ)*EF.weilTest f.1.1 f.1.1 u)
  convert! (HasCompactSupport.finset_sum (s := c.support)
    (f := fun f u => (c f : ℂ)*EF.weilTest f.1.1 f.1.1 u)
    (fun f _ => (EF.weilTest_hasCompactSupport f.1.2.2 f.1.2.2).mul_left)) using 1
  funext u
  simp

theorem polarMixtureProfile_transform (c : WeilEvenPolarTestFn →₀ ℝ≥0) (z : ℂ) :
    paperFT (polarMixtureProfile c) z=evenPolarMixtureSpectrum c z := by
  classical
  unfold paperFT polarMixtureProfile evenPolarMixtureSpectrum Finsupp.sum
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro f _
    simp_rw [mul_assoc]
    rw [Zeta23.integral_const_mul_C]
    simp_rw [← mul_assoc I z]
    change (c f : ℂ)*paperFT (EF.weilTest f.1.1 f.1.1) z=_
    rw [EF.paperFT_weilTest f.1.2.1.continuous f.1.2.1.continuous f.1.2.2 f.1.2.2]
  · intro f _
    have hc := (EF.weilTest_contDiff f.1.2.1 f.1.2.1.continuous f.1.2.2).continuous
    have hs := EF.weilTest_hasCompactSupport f.1.2.2 f.1.2.2
    have hh := (integrable_mul_cexp_of_hasCompactSupport hc hs (I*z)).const_mul (c f : ℂ)
    convert hh using 1
    funext u
    ring

private theorem eq_of_paperFT_eq {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g)
    (he : ∀ z,paperFT f z=paperFT g z) : f=g := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfs
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgs
  have hF : 𝓕 f=𝓕 g := by
    funext x
    rw [Zeta23.fourier_eq_paperFT,Zeta23.fourier_eq_paperFT,he]
  calc
    f = 𝓕⁻ (𝓕 f) := (hf.continuous.fourierInv_fourier_eq hfi (EF.integrable_fourier_of_contDiff_two hf hfs)).symm
    _ = 𝓕⁻ (𝓕 g) := by rw [hF]
    _ = g := hg.continuous.fourierInv_fourier_eq hgi (EF.integrable_fourier_of_contDiff_two hg hgs)

/-- **Exact source scalarization.** Positive finite mixtures of smooth even
pole-free autocorrelations are single smooth even pole-free autocorrelations.
The complete profile is preserved, with no approximation or energy tolerance. -/
theorem exists_smoothPolar_exact_autocorrelation (c : SmoothEvenPolarTestFn →₀ ℝ≥0) :
    ∃ f : SmoothEvenPolarTestFn,
      EF.weilTest f.1.1.1 f.1.1.1=polarMixtureProfile (smoothPolarCoefficients c) := by
  obtain ⟨f,hf⟩ := exists_smoothPolar_spectral_scalarization c
  refine ⟨f,eq_of_paperFT_eq
    (EF.weilTest_contDiff f.1.1.2.1 f.1.1.2.1.continuous f.1.1.2.2)
    (polarMixtureProfile_contDiff _) (EF.weilTest_hasCompactSupport f.1.1.2.2 f.1.1.2.2)
    (polarMixtureProfile_hasCompactSupport _) (fun z => ?_)⟩
  rw [EF.paperFT_weilTest f.1.1.2.1.continuous f.1.1.2.1.continuous f.1.1.2.2 f.1.1.2.2,
    polarMixtureProfile_transform,hf]

end RHTower.EvenSector
