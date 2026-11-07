/-
Cusp lattice periodization adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinNearestPoint
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# The actual cubic cusp period lattice

The basis `3,3ω` has covolume `9√3/2`, independently of the complex
embedding's orientation. Integral Eisenstein coordinates identify this
lattice with the actual translation subgroup. Its fundamental domain
unfolds absolutely integrable periodizations over the complex plane.
-/
noncomputable section
open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein Eisenstein.Coordinates

lemma ringComplex_ne_zero {n : O} (hn : n≠0) : ringComplex n≠0 := by
  simpa only [map_zero] using ringComplex_injective.ne hn

lemma complex_omega_im_ne_zero : (ringComplex omega).im≠0 := by
  intro h
  have hh := complex_omega_coordinates.2
  rw [h] at hh
  norm_num at hh

lemma complex_omega_im_abs : |(ringComplex omega).im|=Real.sqrt 3/2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  nlinarith only [complex_omega_coordinates.2,hs,sq_abs (ringComplex omega).im,
    abs_nonneg (ringComplex omega).im,Real.sqrt_nonneg 3]

/-- Real coordinates in the scaled integral cusp basis. -/
def cubicPeriodCoordinates : ℂ ≃ₗ[ℝ] (Fin 2→ℝ) where
  toFun z := ![(z.re-z.im*(ringComplex omega).re/(ringComplex omega).im)/3,
    z.im/(3*(ringComplex omega).im)]
  invFun v := 3*((v 0:ℂ)+(v 1:ℂ)*ringComplex omega)
  left_inv z := by
    apply Complex.ext <;>
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
        Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
        zero_mul,sub_zero,add_zero,zero_add] <;>
      field_simp [complex_omega_im_ne_zero]
    ring
  right_inv v := by
    ext j
    fin_cases j <;>
      simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
        zero_mul,sub_zero,add_zero,zero_add] <;>
      field_simp [complex_omega_im_ne_zero] <;> ring_nf <;> rfl
  map_add' z w := by
    ext j
    fin_cases j <;> simp [Complex.add_re,Complex.add_im] <;> ring
  map_smul' c z := by
    ext j
    fin_cases j <;> simp [Complex.real_smul] <;> ring

def periodBasis : Basis (Fin 2) ℝ ℂ := Basis.ofEquivFun cubicPeriodCoordinates
lemma periodBasis_zero : periodBasis 0=3 := by
  simp [periodBasis,Basis.coe_ofEquivFun,cubicPeriodCoordinates]
lemma periodBasis_one : periodBasis 1=3*ringComplex omega := by
  simp [periodBasis,Basis.coe_ofEquivFun,cubicPeriodCoordinates]

lemma ringComplex_eval (a b : ℤ) : ringComplex (eval a b)=(a:ℂ)+(b:ℂ)*ringComplex omega := by
  simp only [eval,map_add,map_mul,map_intCast]

def periodLattice : Submodule ℤ ℂ := Submodule.span ℤ (Set.range periodBasis)
def periodDomain : Set ℂ := ZSpan.fundamentalDomain periodBasis

instance cubicPeriodLatticeCountable : Countable periodLattice := by unfold periodLattice; infer_instance
instance cubicPeriodLatticeVolumeInvariant : VAddInvariantMeasure periodLattice ℂ volume :=
  inferInstanceAs (VAddInvariantMeasure periodLattice.toAddSubgroup ℂ volume)

lemma periodDomain_fundamental : IsAddFundamentalDomain periodLattice periodDomain volume :=
  ZSpan.isAddFundamentalDomain periodBasis volume
lemma periodDomain_measurable : MeasurableSet periodDomain :=
  ZSpan.fundamentalDomain_measurableSet periodBasis

lemma three_embedding_mem (n : O) : 3*ringComplex n ∈ periodLattice := by
  have hzero : periodBasis 0 ∈ periodLattice := Submodule.subset_span ⟨0,rfl⟩
  have hone : periodBasis 1 ∈ periodLattice := Submodule.subset_span ⟨1,rfl⟩
  have h := periodLattice.add_mem
    (periodLattice.smul_mem (Coordinates.coords n).1 hzero)
    (periodLattice.smul_mem (Coordinates.coords n).2 hone)
  rw [periodBasis_zero,periodBasis_one] at h
  convert h using 1
  conv_lhs => rw [← Coordinates.eval_coords n,ringComplex_eval]
  simp only [zsmul_eq_mul]
  ring

def periodPoint (n : O) : periodLattice := ⟨3*ringComplex n,three_embedding_mem n⟩
lemma periodPoint_val (n : O) : (periodPoint n : ℂ)=3*ringComplex n := rfl
lemma periodPoint_bijective : Function.Bijective periodPoint := by
  constructor
  · intro n m h
    apply ringComplex_injective
    exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) (congrArg Subtype.val h)
  · intro p
    have h := (periodBasis.mem_span_iff_repr_mem ℤ p.1).mp p.2
    obtain ⟨a,ha⟩ := h 0
    obtain ⟨b,hb⟩ := h 1
    change (a:ℝ)=_ at ha
    change (b:ℝ)=_ at hb
    refine ⟨Coordinates.eval a b, ?_⟩
    apply Subtype.ext
    change 3*ringComplex (Coordinates.eval a b)=p.1
    rw [← periodBasis.sum_repr p.1,Fin.sum_univ_two,← ha,← hb,
      periodBasis_zero,periodBasis_one,ringComplex_eval]
    simp only [Complex.real_smul,Complex.ofReal_intCast]
    ring

def periodEquiv : O ≃ periodLattice := Equiv.ofBijective _ periodPoint_bijective

theorem integral_eq_period_integrals (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z : ℂ, f z)=∑' n : O,∫ z in periodDomain,f (z+3*ringComplex n) := by
  rw [periodDomain_fundamental.integral_eq_tsum'' f hf]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*ringComplex n+z)=f (z+3*ringComplex n)
  rw [add_comm]

theorem lintegral_eq_period_lintegrals (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : ℂ, f z)=∑' n : O,∫⁻ z in periodDomain,f (z+3*ringComplex n) := by
  rw [periodDomain_fundamental.lintegral_eq_tsum'' f]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setLIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*ringComplex n+z)=f (z+3*ringComplex n)
  rw [add_comm]

lemma periodDomain_volume : volume periodDomain=ENNReal.ofReal (9*Real.sqrt 3/2) := by
  have hunit : volume (ZSpan.fundamentalDomain Complex.basisOneI)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]
    exact Complex.orthonormalBasisOneI.volume_parallelepiped
  rw [periodDomain,ZSpan.measure_fundamentalDomain periodBasis volume Complex.basisOneI,hunit,mul_one]
  congr 1
  rw [Basis.det_apply,Matrix.det_fin_two]
  norm_num only [Basis.toMatrix_apply,periodBasis_zero,periodBasis_one,
    Complex.coe_basisOneI_repr,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Complex.mul_re,Complex.mul_im,Complex.re_ofNat,
    Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero]
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤3),abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ)≤3),complex_omega_im_abs]
  ring

lemma norm_mem_periodDomain (z : ℂ) (hz : z∈periodDomain) :
    ‖z‖≤∑i : Fin 2,‖periodBasis i‖ := by
  have heq := (ZSpan.fract_eq_self (b := periodBasis)).mpr hz
  simpa only [heq] using ZSpan.norm_fract_le periodBasis z

lemma periodization_lintegral_norm_ne_top (f : ℂ → ℂ) (hf : Integrable f) :
    (∑' n : O,∫⁻ z in periodDomain,‖f (z+3*ringComplex n)‖ₑ) ≠ ⊤ := by
  rw [← lintegral_eq_period_lintegrals (fun z => ‖f z‖ₑ)]
  exact hf.hasFiniteIntegral.ne

theorem integral_periodization (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z in periodDomain,∑' n : O,f (z+3*ringComplex n))=∫ z : ℂ,f z := by
  let : Countable O := Coordinates.coordinateEquiv.injective.countable
  rw [integral_tsum]
  · exact (integral_eq_period_integrals f hf).symm
  · intro n
    exact (hf.comp_add_right (3*ringComplex n)).aestronglyMeasurable.restrict
  · exact periodization_lintegral_norm_ne_top f hf

#print axioms periodDomain_volume
#print axioms periodPoint_bijective
#print axioms integral_periodization
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
