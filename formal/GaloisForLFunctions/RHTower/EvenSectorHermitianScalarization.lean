import GaloisForLFunctions.HTGeometry.EvenHermitianSpectralFactor
import GaloisForLFunctions.HTGeometry.CompactTestTransform
import GaloisForLFunctions.RHTower.PrimitiveHyperplaneBlindPositivity
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# Global even scalarization of actual EWU mixture spectra

Every positive finite mixture of actual even pole-free sources has a single
entire even Hermitian factor. The identity holds on the whole complex plane,
and the factor has literal zeros at both poles. No RH, positivity of the Weil
functional, divisor parity, or spectral-factor premise is used.
-/

open Complex Filter Topology Set MeasureTheory Finsupp Zeta23
open scoped ComplexConjugate NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.EvenHermitianFactor

noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

/-- The entire autocorrelation spectrum of a positive finite even polar mixture. -/
def evenPolarMixtureSpectrum (c : WeilEvenPolarTestFn →₀ ℝ≥0) (z : ℂ) : ℂ :=
  c.sum fun f t => (t : ℂ)*paperFT f.1.1 z*conj (paperFT f.1.1 (conj z))

theorem evenPolarMixtureSpectrum_entire (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    Differentiable ℂ (evenPolarMixtureSpectrum c) := by
  classical
  change Differentiable ℂ (fun z => ∑ f ∈ c.support,
    (c f : ℂ)*paperFT f.1.1 z*conj (paperFT f.1.1 (conj z)))
  apply Differentiable.fun_sum
  intro f _
  have h := differentiable_paperFT_of_compact f.1.2.1.continuous f.1.2.2
  exact ((differentiable_const _).mul h).mul (RHTower.differentiable_conj_reflect h)

theorem evenPolarMixtureSpectrum_even (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    Function.Even (evenPolarMixtureSpectrum c) := by
  intro z
  unfold evenPolarMixtureSpectrum Finsupp.sum
  apply Finset.sum_congr rfl
  intro f _
  dsimp only
  rw [map_neg,paperFT_neg_of_even f.2.1,paperFT_neg_of_even f.2.1]

theorem evenPolarMixtureSpectrum_axis (c : WeilEvenPolarTestFn →₀ ℝ≥0)
    (z : ℂ) (hz : z.re=0 ∨ z.im=0) :
    evenPolarMixtureSpectrum c z=
      ((c.sum fun f t => (t : ℝ)*‖paperFT f.1.1 z‖^2 : ℝ) : ℂ) := by
  classical
  unfold evenPolarMixtureSpectrum Finsupp.sum
  push_cast
  apply Finset.sum_congr rfl
  intro f _
  have he : paperFT f.1.1 (conj z)=paperFT f.1.1 z := by
    rcases hz with hz | hz
    · rw [show conj z=-z by apply Complex.ext <;> simp [hz],paperFT_neg_of_even f.2.1]
    · rw [show conj z=z by apply Complex.ext <;> simp [hz]]
  rw [he,mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_pow]

theorem evenPolarMixtureSpectrum_axisNonnegative (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    AxisNonnegative (evenPolarMixtureSpectrum c) := by
  intro z hz
  rw [evenPolarMixtureSpectrum_axis c z hz]
  constructor
  · rfl
  · simp only [Complex.ofReal_re,Finsupp.sum]
    exact Finset.sum_nonneg fun f _ => mul_nonneg (c f).coe_nonneg (sq_nonneg _)

private theorem paperFT_linear_exponential (f : WeilTestFn) :
    ∃ M A : ℝ,0≤M ∧ 0≤A ∧ ∀ z,‖paperFT f.1 z‖≤M*Real.exp (A*‖z‖) := by
  obtain ⟨R,hR⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  let M := ∫ u : ℝ,‖f.1 u‖
  refine ⟨M,|R|,integral_nonneg (fun _ => norm_nonneg _),abs_nonneg _,fun z => ?_⟩
  have hs (u : ℝ) (hu : |R| < |u|) : f.1 u=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := hR hm
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    linarith [le_abs_self R]
  have hh := norm_testTransform_le_exp f.2.1.continuous f.2.2 (abs_nonneg R) hs z
    (Complex.abs_im_le_norm z)
  simpa only [testTransform,Zeta23.paperFT,mul_comm,M] using hh

theorem evenPolarMixtureSpectrum_exponential (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    ∃ M A : ℝ,0≤M ∧ 0≤A ∧ ∀ z,
      ‖evenPolarMixtureSpectrum c z‖≤M*Real.exp (A*‖z‖) := by
  classical
  choose M A hM hA hb using fun f : WeilEvenPolarTestFn => paperFT_linear_exponential f.1
  let B := ∑ f ∈ c.support,2*A f
  let D := ∑ f ∈ c.support,(c f : ℝ)*(M f)^2
  have hB : 0≤B := Finset.sum_nonneg fun f _ => mul_nonneg (by norm_num) (hA f)
  have hD : 0≤D := Finset.sum_nonneg fun f _ => mul_nonneg (c f).coe_nonneg (sq_nonneg _)
  refine ⟨D,B,hD,hB,fun z => ?_⟩
  change ‖∑ f ∈ c.support,((c f : ℂ)*paperFT f.1.1 z*conj (paperFT f.1.1 (conj z)))‖≤_
  apply (norm_sum_le _ _).trans
  rw [show D*Real.exp (B*‖z‖)=∑ f ∈ c.support,((c f : ℝ)*(M f)^2)*Real.exp (B*‖z‖) by
    rw [Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro f hfc
  have hAB : 2*A f≤B := Finset.single_le_sum
    (fun f _ => mul_nonneg (by norm_num) (hA f)) hfc
  have hpair : ‖paperFT f.1.1 z‖*‖paperFT f.1.1 (conj z)‖≤
      (M f)^2*Real.exp ((2*A f)*‖z‖) := by
    calc
      _ ≤ (M f*Real.exp (A f*‖z‖))*(M f*Real.exp (A f*‖conj z‖)) :=
        mul_le_mul (hb f z) (hb f (conj z)) (norm_nonneg _)
          (mul_nonneg (hM f) (Real.exp_nonneg _))
      _ = _ := by rw [Complex.norm_conj]; rw [show (2*A f)*‖z‖=A f*‖z‖+A f*‖z‖ by ring,Real.exp_add]; ring
  rw [norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (c f).coe_nonneg,mul_assoc]
  calc
    _ ≤ (c f : ℝ)*((M f)^2*Real.exp ((2*A f)*‖z‖)) :=
      mul_le_mul_of_nonneg_left hpair (c f).coe_nonneg
    _ ≤ ((c f : ℝ)*(M f)^2)*Real.exp (B*‖z‖) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAB (norm_nonneg z)))
        (mul_nonneg (c f).coe_nonneg (sq_nonneg _))

private theorem orderOne_of_linear_exponential {f : ℂ → ℂ} {M A : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hb : ∀ z,‖f z‖≤M*Real.exp (A*‖z‖)) :
    ∃ C : ℝ,0≤C ∧ ∀ z,‖f z‖≤Real.exp (C*(1+‖z‖)*Real.log (2+‖z‖)) := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(M+A)/Real.log 2,by positivity,fun z => ?_⟩
  have hl : Real.log 2≤Real.log (2+‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have he : M≤Real.exp M := by linarith [Real.add_one_le_exp M]
  apply (hb z).trans
  calc
    M*Real.exp (A*‖z‖) ≤ Real.exp M*Real.exp (A*‖z‖) :=
      mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
    _ = Real.exp (M+A*‖z‖) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hl (div_nonneg (add_nonneg hM hA) hl2.le)
      rw [div_mul_cancel₀ _ hl2.ne'] at hh
      have hx := mul_le_mul_of_nonneg_left hh (show 0≤1+‖z‖ by positivity)
      nlinarith [mul_nonneg hM (norm_nonneg z)]

/-- **Unconditional EWU analytic scalarization.** One even entire factor
represents the complete spectrum of every actual positive finite polar
mixture and retains the literal pole zeros. -/
theorem exists_evenPolarMixture_entire_factor_subquadratic (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    ∃ q : ℂ → ℂ,Differentiable ℂ q ∧ Function.Even q ∧
      q (I/2)=0 ∧ q (-(I/2))=0 ∧
      (∀ z,evenPolarMixtureSpectrum c z=q z*conj (q (conj z))) ∧ SubquadraticType q := by
  obtain ⟨M,A,hM,hA,hb⟩ := evenPolarMixtureSpectrum_exponential c
  obtain ⟨C,hC,hgrowth⟩ := orderOne_of_linear_exponential hM hA hb
  obtain ⟨q,hq,hqe,hidentity,hqs⟩ := exists_even_entire_factor_subquadratic hC
    (evenPolarMixtureSpectrum_entire c) (evenPolarMixtureSpectrum_even c)
    (evenPolarMixtureSpectrum_axisNonnegative c) hgrowth
  have hp : evenPolarMixtureSpectrum c (I/2)=0 := by
    unfold evenPolarMixtureSpectrum Finsupp.sum
    apply Finset.sum_eq_zero
    intro f _
    dsimp only
    rw [f.2.2,mul_zero,zero_mul]
  have hc : conj (I/2)=-(I/2) := by simp only [map_div₀,Complex.conj_I,map_ofNat,neg_div]
  have hq0 : q (I/2)=0 := by
    rw [hidentity,hc,hqe,Complex.mul_conj,Complex.normSq_eq_norm_sq] at hp
    have hh : ‖q (I/2)‖^2=0 := by exact_mod_cast hp
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  exact ⟨q,hq,hqe,hq0,by rw [hqe,hq0],hidentity,hqs⟩

theorem exists_evenPolarMixture_entire_factor (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    ∃ q : ℂ → ℂ,Differentiable ℂ q ∧ Function.Even q ∧
      q (I/2)=0 ∧ q (-(I/2))=0 ∧
      ∀ z,evenPolarMixtureSpectrum c z=q z*conj (q (conj z)) := by
  obtain ⟨q,hq,he,hp,hm,hi,_⟩ := exists_evenPolarMixture_entire_factor_subquadratic c
  exact ⟨q,hq,he,hp,hm,hi⟩

end RHTower.EvenSector
