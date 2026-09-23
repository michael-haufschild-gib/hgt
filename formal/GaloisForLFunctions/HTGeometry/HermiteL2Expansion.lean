import GaloisForLFunctions.HTGeometry.HermiteL2Completeness
import GaloisForLFunctions.HTGeometry.HermiteExpansionSummable

/-!
# The Hermite expansion of a Schwartz function converges in `L²`

The coefficients of a Schwartz function are absolutely summable, and the normalized Hermite
functions are unit vectors, so the Hermite series converges absolutely in `L²`.  Its sum has the
same coefficients as the function, because the inner product against a Hermite function is
continuous; the difference is therefore orthogonal to every Hermite function, hence zero by
completeness of the Hermite system.

Consequently the `L²` norm of a Schwartz function is bounded by the sum of the absolute values of
its coefficients — the estimate opposite to the coefficient bound, and the one that makes the
coefficient map a topological embedding.

* `norm_toLp_hermiteUnit` : the normalized Hermite functions are unit vectors.
* `summable_norm_hermiteCoeff` : **the coefficients are absolutely summable.**
* `hasSum_hermiteExpansion_toLp` : **the Hermite expansion converges to the function in `L²`.**
* `norm_toLp_le_tsum_hermiteCoeff` : **`‖f‖₂ ≤ ∑ |cⱼ(f)|`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Unit vectors and absolute summability -/

theorem norm_toLp_hermiteUnit (j : ℕ) :
    ‖(hermiteUnit j).toLp 2 (volume : Measure ℝ)‖ = 1 := by
  have h := norm_toLp_hermiteUnit_shifted 0 j
  rw [Function.iterate_zero_apply, pow_zero] at h
  exact h

theorem summable_norm_hermiteCoeff (f : 𝓢(ℝ, ℂ)) :
    Summable fun j : ℕ => ‖hermiteCoeff f j‖ := by
  obtain ⟨C, hC, hbound⟩ := hermiteCoeff_decay_shift 2 f
  have hle : ∀ j : ℕ, ‖hermiteCoeff f j‖
      ≤ (C * ((4 * π) ^ (2 : ℕ))⁻¹) * (1 / ((((j + 1 : ℕ)) : ℝ) ^ (2 : ℕ))) := by
    intro j
    have hpos := four_pi_mul_pos j
    have hj := hbound j
    have hstep : ‖hermiteCoeff f j‖ ≤ C * ((4 * π * ((j : ℝ) + 1)) ^ (2 : ℕ))⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      linarith [hj]
    refine le_trans hstep (le_of_eq ?_)
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle ?_
  have h1 : Summable fun j : ℕ => 1 / ((j : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h2 : Summable fun j : ℕ => 1 / ((((j + 1 : ℕ)) : ℝ) ^ (2 : ℕ)) := (summable_nat_add_iff 1).mpr h1
  exact h2.mul_left _

theorem summable_hermiteExpansion_toLp (f : 𝓢(ℝ, ℂ)) :
    Summable fun j : ℕ => hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ) := by
  refine Summable.of_norm ?_
  have hfun : (fun j : ℕ => ‖hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ)‖)
      = fun j : ℕ => ‖hermiteCoeff f j‖ := by
    funext j
    rw [norm_smul, norm_toLp_hermiteUnit, mul_one]
  rw [hfun]
  exact summable_norm_hermiteCoeff f

/-! ## The coefficients of the sum -/

theorem inner_hermiteSchwartz_hermiteUnit (n j : ℕ) :
    inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ))
        ((hermiteUnit j).toLp 2 (volume : Measure ℝ))
      = if j = n then ((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) else 0 := by
  have hpos := hermiteNorm_pos j
  have hunit : (hermiteUnit j).toLp 2 (volume : Measure ℝ)
      = ((‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ)⁻¹ •
        (hermiteSchwartz j).toLp 2 (volume : Measure ℝ) := by
    rw [hermiteUnit, toLp_smul]
  rw [hunit, inner_smul_right]
  by_cases hjn : j = n
  · subst hjn
    have hne : ((‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    have hself : inner ℂ ((hermiteSchwartz j).toLp 2 (volume : Measure ℝ))
        ((hermiteSchwartz j).toLp 2 (volume : Measure ℝ))
        = ((‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ)
          * ((‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, sq]
      norm_cast
    rw [if_pos rfl, hself, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [if_neg hjn, inner_hermiteSchwartz_toLp_eq_zero (fun h => hjn h.symm), mul_zero]

theorem inner_hermiteSchwartz_toLp_eq (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) (f.toLp 2 (volume : Measure ℝ))
      = ((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) * hermiteCoeff f n := by
  have hne : ((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hermiteNorm_pos n).ne'
  rw [hermiteCoeff, ← schwartzPair_eq_inner_toLp]
  field_simp

/-- **The Hermite expansion of a Schwartz function converges to it in `L²`.**  The series
converges absolutely, its sum has the same coefficients as the function, and the Hermite system is
complete. -/
theorem hasSum_hermiteExpansion_toLp (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun j : ℕ => hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ))
      (f.toLp 2 (volume : Measure ℝ)) := by
  obtain ⟨S, hS⟩ := summable_hermiteExpansion_toLp f
  have hcoeff : ∀ n : ℕ,
      inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) S
        = ((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) * hermiteCoeff f n := by
    intro n
    have hmap := hS.mapL (innerSL ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)))
    have hfun : (fun j : ℕ =>
        (innerSL ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)))
          (hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ)))
        = fun j : ℕ => if j = n then
            ((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) * hermiteCoeff f n
          else 0 := by
      funext j
      show inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ))
          (hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ)) = _
      rw [inner_smul_right, inner_hermiteSchwartz_hermiteUnit]
      by_cases hjn : j = n
      · subst hjn
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hjn, if_neg hjn, mul_zero]
    rw [hfun] at hmap
    have hunique := (hasSum_ite_eq n
      (((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℝ) : ℂ) * hermiteCoeff f n))
    exact hmap.unique hunique
  have hdiff : ∀ n : ℕ,
      inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ))
        (S - f.toLp 2 (volume : Measure ℝ)) = 0 := by
    intro n
    rw [inner_sub_right, hcoeff n, inner_hermiteSchwartz_toLp_eq f n, sub_self]
  have hzero : S - f.toLp 2 (volume : Measure ℝ) = 0 := hermite_l2_complete hdiff
  have hSf : S = f.toLp 2 (volume : Measure ℝ) := by
    rw [sub_eq_zero] at hzero
    exact hzero
  rwa [hSf] at hS

/-- **The `L²` norm is bounded by the sum of the absolute values of the coefficients.** -/
theorem norm_toLp_le_tsum_hermiteCoeff (f : 𝓢(ℝ, ℂ)) :
    ‖f.toLp 2 (volume : Measure ℝ)‖ ≤ ∑' j : ℕ, ‖hermiteCoeff f j‖ := by
  have hsum := hasSum_hermiteExpansion_toLp f
  have hnorm : ‖f.toLp 2 (volume : Measure ℝ)‖
      ≤ ∑' j : ℕ, ‖hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ)‖ := by
    rw [← hsum.tsum_eq]
    exact norm_tsum_le_tsum_norm (by
      have hfun : (fun j : ℕ => ‖hermiteCoeff f j • (hermiteUnit j).toLp 2 (volume : Measure ℝ)‖)
          = fun j : ℕ => ‖hermiteCoeff f j‖ := by
        funext j
        rw [norm_smul, norm_toLp_hermiteUnit, mul_one]
      rw [hfun]
      exact summable_norm_hermiteCoeff f)
  refine le_trans hnorm (le_of_eq ?_)
  refine tsum_congr fun j => ?_
  rw [norm_smul, norm_toLp_hermiteUnit, mul_one]

end GaloisForLFunctions

end
