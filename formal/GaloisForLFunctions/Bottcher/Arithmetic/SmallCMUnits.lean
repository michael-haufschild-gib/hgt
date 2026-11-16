import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Bounded CM units are sums of two roots of unity

A unit determines the integral phase `u / conjugate(u)`. The roots of its
phase quadratic are integral and, under the conjugate bound two, have modulus
one in every embedding. Kronecker's theorem makes both roots torsion.
This proves the characterization in Sano, arXiv:2611.16354, Theorem 1.5.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Bottcher.Arithmetic

/-- A real reciprocal quadratic with trace in `[-2,2]` has unit-modulus roots. -/
private theorem norm_root_reciprocal_quadratic (v : ℝ) (z : ℂ)
    (hv : |v| ≤ 2) (hz : z ^ 2 - (v : ℂ) * z + 1 = 0) : ‖z‖ = 1 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re,
    Complex.zero_re] at hr
  simp only [pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.one_im,
    Complex.zero_im] at hi
  have hv2 : v ^ 2 ≤ 4 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hv
    have hp := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)
    nlinarith only [hp]
  have hlinear : 2 * z.re - v = 0 := by
    by_cases hzi : z.im = 0
    · rw [hzi] at hr
      have hs : (2 * z.re - v) ^ 2 ≤ 0 := by nlinarith only [hr, hv2]
      exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
    · have hp : z.im * (2 * z.re - v) = 0 := by linear_combination hi
      exact (mul_eq_zero.mp hp).resolve_left hzi
  have hv' : v = 2 * z.re := by linarith only [hlinear]
  rw [hv'] at hr
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by nlinarith only [hr]
  have hn' : ‖z‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith only [hn]
  nlinarith only [hn', norm_nonneg z]

/-- The phase determined by a nonzero complex number makes its bounded
quadratic roots lie on the unit circle. -/
private theorem norm_root_phase_quadratic (u z : ℂ) (hu : u ≠ 0)
    (hb : ‖u‖ ≤ 2) (hz : z ^ 2 - u * z + u / conj u = 0) : ‖z‖ = 1 := by
  obtain ⟨ε, he2⟩ := IsAlgClosed.exists_pow_nat_eq (u / conj u) (by norm_num : 0 < (2 : ℕ))
  have hen : ‖ε‖ = 1 := by
    have hn := congrArg norm he2
    rw [norm_pow, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hu)] at hn
    nlinarith only [hn, norm_nonneg ε]
  have he0 : ε ≠ 0 := by
    intro h
    rw [h, norm_zero] at hen
    norm_num at hen
  have hc : conj u ≠ 0 := by simpa only [map_ne_zero] using hu
  have hurel : u = conj u * ε ^ 2 := by
    have hh := (div_eq_iff hc).mp he2.symm
    simpa only [mul_comm] using hh
  have hv : u / ε = conj u * ε := by
    apply (div_eq_iff he0).mpr
    calc
      u = conj u * ε ^ 2 := hurel
      _ = _ := by ring
  have hreal : conj (u / ε) = u / ε := by
    rw [map_div₀, ← Complex.inv_eq_conj hen, div_inv_eq_mul, hv]
  have him : (u / ε).im = 0 := by
    have hi := congrArg Complex.im hreal
    simp only [Complex.conj_im] at hi
    linarith only [hi]
  have hre : (((u / ε).re : ℝ) : ℂ) = u / ε := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him.symm
  have hbound : |(u / ε).re| ≤ 2 := by
    calc
      _ = ‖(((u / ε).re : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖u‖ := by rw [hre, norm_div, hen, div_one]
      _ ≤ 2 := hb
  have hroot : (z / ε) ^ 2 - (((u / ε).re : ℝ) : ℂ) * (z / ε) + 1 = 0 := by
    rw [hre]
    calc
      _ = (z ^ 2 - u * z + ε ^ 2) / ε ^ 2 := by field_simp
      _ = 0 := by rw [he2, hz, zero_div]
  have hn := norm_root_reciprocal_quadratic (u / ε).re (z / ε) hbound hroot
  simpa only [norm_div, hen, div_one] using hn

end Bottcher.Arithmetic

open Polynomial NumberField NumberField.IsCMField

namespace Bottcher.Arithmetic

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

/-- The integral phase of a CM unit. -/
private def cmUnitPhase (u : (𝓞 K)ˣ) : 𝓞 K :=
  ((unitsMulComplexConjInv K u : (𝓞 K)ˣ) : 𝓞 K)

private theorem cmUnitPhase_embedding (u : (𝓞 K)ˣ) (φ : K →+* ℂ) :
    φ (cmUnitPhase u : K) = φ (u : K) / conj (φ (u : K)) := by
  simp [cmUnitPhase, unitsMulComplexConjInv_apply, div_eq_mul_inv,
    complexEmbedding_complexConj]

/-- The quadratic whose two roots give the desired root-of-unity sum. -/
private def cmUnitPolynomial (u : (𝓞 K)ˣ) : K[X] :=
  X ^ 2 + C (-(u : K)) * X + C (cmUnitPhase u : K)

private theorem phase_quadratic_root_integral {L : Type*} [Field L] [Algebra K L]
    (u : (𝓞 K)ˣ) (z : L)
    (hz : z ^ 2 - algebraMap K L (u : K) * z + algebraMap K L (cmUnitPhase u : K) = 0) :
    IsIntegral ℤ z := by
  letI : IsScalarTower ℤ (𝓞 K) L := IsScalarTower.of_algebraMap_eq fun x => by simp
  apply isIntegral_trans (A := 𝓞 K) z
  refine ⟨X ^ 2 + C (-(u : 𝓞 K)) * X + C (cmUnitPhase u),
    (isMonicOfDegree_add_add_two _ _).monic, ?_⟩
  simpa only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C, map_neg,
    IsScalarTower.algebraMap_apply (𝓞 K) K L, neg_mul, ← sub_eq_add_neg] using hz

private theorem phase_quadratic_root_finiteOrder {L : Type*} [Field L] [NumberField L]
    [Algebra K L] (u : (𝓞 K)ˣ)
    (hu : ∀ φ : K →+* ℂ, ‖φ (u : K)‖ ≤ 2) (z : L)
    (hz : z ^ 2 - algebraMap K L (u : K) * z + algebraMap K L (cmUnitPhase u : K) = 0) :
    IsOfFinOrder z := by
  have hnorm (φ : L →+* ℂ) : ‖φ z‖ = 1 := by
    have he := congrArg φ hz
    simp only [map_add, map_sub, map_pow, map_mul, map_zero] at he
    have hp := cmUnitPhase_embedding u (φ.comp (algebraMap K L))
    change φ (algebraMap K L (cmUnitPhase u : K)) =
      φ (algebraMap K L (u : K)) / conj (φ (algebraMap K L (u : K))) at hp
    rw [hp] at he
    have huK : (u : K) ≠ 0 :=
      Units.ne_zero (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
    exact norm_root_phase_quadratic _ _
      ((map_ne_zero (φ.comp (algebraMap K L))).mpr huK)
      (hu (φ.comp (algebraMap K L))) he
  obtain ⟨n, hn, hp⟩ := Embeddings.pow_eq_one_of_norm_eq_one L ℂ
    (phase_quadratic_root_integral u z hz) hnorm
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hp⟩

/-- A CM unit has all conjugates bounded by two exactly when each complex
embedding is a sum of two roots of unity. -/
theorem small_cm_unit_iff_sum_two_roots (u : (𝓞 K)ˣ) :
    (∀ φ : K →+* ℂ, ‖φ (u : K)‖ ≤ 2) ↔
      ∀ φ : K →+* ℂ, ∃ ξ η : ℂ, IsOfFinOrder ξ ∧ IsOfFinOrder η ∧
        φ (u : K) = ξ + η := by
  constructor
  · intro hu φ
    let L := (cmUnitPolynomial u).SplittingField
    haveI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
    letI : NumberField L := ⟨⟩
    have hd : IsMonicOfDegree ((cmUnitPolynomial u).map (algebraMap K L)) 2 := by
      simpa only [cmUnitPolynomial, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C] using
        isMonicOfDegree_add_add_two (algebraMap K L (-(u : K)))
          (algebraMap K L (cmUnitPhase u : K))
    obtain ⟨z, hz⟩ := (Polynomial.SplittingField.splits (cmUnitPolynomial u)).exists_eval_eq_zero
      (by rw [degree_eq_natDegree hd.monic.ne_zero, hd.natDegree_eq]; norm_num)
    have hze : z ^ 2 - algebraMap K L (u : K) * z +
        algebraMap K L (cmUnitPhase u : K) = 0 := by
      rw [← eval₂_eq_eval_map] at hz
      change eval₂ (algebraMap K L) z
        (X ^ 2 + C (-(u : K)) * X + C (cmUnitPhase u : K)) = 0 at hz
      simp only [eval₂_add, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C] at hz
      rw [map_neg] at hz
      linear_combination hz
    have hwe : (algebraMap K L (u : K) - z) ^ 2 -
        algebraMap K L (u : K) * (algebraMap K L (u : K) - z) +
          algebraMap K L (cmUnitPhase u : K) = 0 := by
      linear_combination hze
    have hzf := phase_quadratic_root_finiteOrder u hu z hze
    have hwf := phase_quadratic_root_finiteOrder u hu _ hwe
    letI : Algebra K ℂ := φ.toAlgebra
    let e : L →ₐ[K] ℂ := IsAlgClosed.lift
    refine ⟨e z, e (algebraMap K L (u : K) - z),
      e.toMonoidHom.isOfFinOrder hzf, e.toMonoidHom.isOfFinOrder hwf, ?_⟩
    calc
      φ (u : K) = e (algebraMap K L (u : K)) := (e.commutes _).symm
      _ = e z + e (algebraMap K L (u : K) - z) := by
        rw [← map_add]
        congr 1
        ring
  · intro h φ
    obtain ⟨ξ, η, hξ, hη, he⟩ := h φ
    rw [he]
    calc
      ‖ξ + η‖ ≤ ‖ξ‖ + ‖η‖ := norm_add_le _ _
      _ = 2 := by rw [hξ.norm_eq_one, hη.norm_eq_one]; norm_num

end Bottcher.Arithmetic
