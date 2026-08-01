import GaloisForLFunctions.RHTower.DeningerBoundarySpace

/-!
# The boundary space is a Hilbert space

The coefficient families of finite boundary norm form a submodule of all families, because the
weight is nonnegative and the squared norm satisfies the parallelogram bound.  Dividing by the
square root of the weight identifies that submodule linearly with the square-summable sequences and
carries the boundary norm to the `ℓ²` norm; completeness of `ℓ²` therefore transports to the
boundary norm.

* `deningerBoundarySubmodule` : the boundary data of finite boundary norm.
* `deningerBoundaryEquiv` : the isometric parametrization by `ℓ²`.
* `deningerBoundary_complete` : the boundary norm is complete.
-/

namespace RHTower

open scoped ENNReal

section BoundaryComplete

variable {ι : Type*}

/-- Square summability of the coefficients of a member of `ℓ²`. -/
theorem deningerLp_summable (ψ : lp (fun _ : ι => ℂ) 2) :
    Summable fun a : ι => ‖(ψ : ι → ℂ) a‖ ^ 2 := by
  have h := (lp.memℓp ψ).summable (by norm_num)
  simpa using h

/-- The squared `ℓ²` norm is the sum of the squared coefficients. -/
theorem deningerLp_normSq (ψ : lp (fun _ : ι => ℂ) 2) :
    ‖ψ‖ ^ 2 = ∑' a : ι, ‖(ψ : ι → ℂ) a‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ψ
  simpa using h

/-- The parallelogram bound for the squared norm. -/
theorem deningerNormSq_add_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]

/-- **The boundary data of finite boundary norm.**  This is the linear core of the boundary space:
the weight is nonnegative, so the parallelogram bound makes the condition additive, and the weight
of a scalar multiple is a constant multiple. -/
def deningerBoundarySubmodule (ℓ : ι → ℝ) : Submodule ℂ (ι → ℂ) where
  carrier := {φ | Summable fun a : ι => |ℓ a| * ‖φ a‖ ^ 2}
  add_mem' := by
    intro φ ψ hφ hψ
    have hφ' : Summable fun a : ι => |ℓ a| * ‖φ a‖ ^ 2 := hφ
    have hψ' : Summable fun a : ι => |ℓ a| * ‖ψ a‖ ^ 2 := hψ
    have hsum : Summable fun a : ι =>
        2 * (|ℓ a| * ‖φ a‖ ^ 2) + 2 * (|ℓ a| * ‖ψ a‖ ^ 2) :=
      (hφ'.mul_left 2).add (hψ'.mul_left 2)
    refine Summable.of_norm_bounded hsum fun a => ?_
    have hnonneg : (0 : ℝ) ≤ |ℓ a| * ‖(φ + ψ) a‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc |ℓ a| * ‖(φ + ψ) a‖ ^ 2 ≤ |ℓ a| * (2 * ‖φ a‖ ^ 2 + 2 * ‖ψ a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (deningerNormSq_add_le (φ a) (ψ a)) (abs_nonneg _)
      _ = 2 * (|ℓ a| * ‖φ a‖ ^ 2) + 2 * (|ℓ a| * ‖ψ a‖ ^ 2) := by ring
  zero_mem' := by
    show Summable fun a : ι => |ℓ a| * ‖(0 : ι → ℂ) a‖ ^ 2
    simp
  smul_mem' := by
    intro c φ hφ
    have hφ' : Summable fun a : ι => |ℓ a| * ‖φ a‖ ^ 2 := hφ
    have hfun : (fun a : ι => |ℓ a| * ‖(c • φ) a‖ ^ 2)
        = fun a : ι => ‖c‖ ^ 2 * (|ℓ a| * ‖φ a‖ ^ 2) := by
      funext a
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
      ring
    show Summable fun a : ι => |ℓ a| * ‖(c • φ) a‖ ^ 2
    rw [hfun]
    exact hφ'.mul_left _

theorem deningerMem_boundarySubmodule_iff (ℓ : ι → ℝ) (φ : ι → ℂ) :
    φ ∈ deningerBoundarySubmodule ℓ ↔ Summable fun a : ι => |ℓ a| * ‖φ a‖ ^ 2 :=
  Iff.rfl

/-- The boundary datum of a square-summable sequence has finite boundary norm. -/
theorem deningerBoundaryDatum_mem (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (ψ : lp (fun _ : ι => ℂ) 2) :
    deningerBoundaryDatum ℓ ψ ∈ deningerBoundarySubmodule ℓ := by
  have hfun : (fun a : ι => |ℓ a| * ‖deningerBoundaryDatum ℓ ψ a‖ ^ 2)
      = fun a : ι => ‖(ψ : ι → ℂ) a‖ ^ 2 :=
    funext fun a => deningerBoundary_term ℓ hℓ ψ a
  show Summable fun a : ι => |ℓ a| * ‖deningerBoundaryDatum ℓ ψ a‖ ^ 2
  rw [hfun]
  exact deningerLp_summable ψ

/-- Multiplying a boundary datum by the square root of its weight. -/
noncomputable def deningerBoundaryCoeff (ℓ : ι → ℝ) (φ : ι → ℂ) (a : ι) : ℂ :=
  ((Real.sqrt |ℓ a| : ℝ) : ℂ) * φ a

theorem deningerBoundaryCoeff_normSq (ℓ : ι → ℝ) (φ : ι → ℂ) (a : ι) :
    ‖deningerBoundaryCoeff ℓ φ a‖ ^ 2 = |ℓ a| * ‖φ a‖ ^ 2 := by
  rw [deningerBoundaryCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (abs_nonneg (ℓ a))]

/-- A boundary datum of finite boundary norm has square-summable weighted coefficients. -/
theorem deningerBoundaryCoeff_memℓp (ℓ : ι → ℝ) {φ : ι → ℂ}
    (hφ : φ ∈ deningerBoundarySubmodule ℓ) : Memℓp (deningerBoundaryCoeff ℓ φ) 2 := by
  have hφ' : Summable fun a : ι => |ℓ a| * ‖φ a‖ ^ 2 := hφ
  have hsum : Summable fun a : ι => ‖deningerBoundaryCoeff ℓ φ a‖ ^ 2 := by
    have hfun : (fun a : ι => ‖deningerBoundaryCoeff ℓ φ a‖ ^ 2)
        = fun a : ι => |ℓ a| * ‖φ a‖ ^ 2 :=
      funext fun a => deningerBoundaryCoeff_normSq ℓ φ a
    rw [hfun]
    exact hφ'
  apply memℓp_gen
  simpa using hsum

/-- **The boundary space is parametrized by `ℓ²`.**  Dividing by the square root of the weight is a
linear bijection from the square-summable sequences onto the boundary data of finite boundary
norm. -/
noncomputable def deningerBoundaryEquiv (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0) :
    lp (fun _ : ι => ℂ) 2 ≃ₗ[ℂ] deningerBoundarySubmodule ℓ where
  toFun ψ := ⟨deningerBoundaryDatum ℓ ψ, deningerBoundaryDatum_mem ℓ hℓ ψ⟩
  map_add' ψ₁ ψ₂ := by
    refine Subtype.ext (funext fun a => ?_)
    simp only [deningerBoundaryDatum, Submodule.coe_add, Pi.add_apply, lp.coeFn_add]
    rw [add_div]
  map_smul' c ψ := by
    refine Subtype.ext (funext fun a => ?_)
    simp only [deningerBoundaryDatum, SetLike.mk_smul_mk, Pi.smul_apply, lp.coeFn_smul,
      smul_eq_mul, RingHom.id_apply]
    rw [mul_div_assoc]
  invFun φ := ⟨deningerBoundaryCoeff ℓ (φ : ι → ℂ), deningerBoundaryCoeff_memℓp ℓ φ.2⟩
  left_inv ψ := by
    refine lp.ext (funext fun a => ?_)
    exact deningerBoundaryDatum_leftInverse ℓ hℓ ψ a
  right_inv φ := by
    refine Subtype.ext (funext fun a => ?_)
    have hw : ((Real.sqrt |ℓ a| : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast deningerBoundaryWeight_ne_zero (hℓ a)
    show deningerBoundaryCoeff ℓ (φ : ι → ℂ) a / ((Real.sqrt |ℓ a| : ℝ) : ℂ) = (φ : ι → ℂ) a
    rw [deningerBoundaryCoeff, mul_comm, mul_div_assoc, div_self hw, mul_one]

theorem deningerBoundaryEquiv_apply (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (ψ : lp (fun _ : ι => ℂ) 2) :
    ((deningerBoundaryEquiv ℓ hℓ ψ : deningerBoundarySubmodule ℓ) : ι → ℂ)
      = deningerBoundaryDatum ℓ ψ := rfl

/-- **The parametrization is isometric.** -/
theorem deningerBoundaryEquiv_normSq (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (ψ : lp (fun _ : ι => ℂ) 2) :
    deningerBoundaryNormSq ℓ ((deningerBoundaryEquiv ℓ hℓ ψ : deningerBoundarySubmodule ℓ) : ι → ℂ)
      = ‖ψ‖ ^ 2 := by
  rw [deningerBoundaryEquiv_apply, deningerLp_normSq]
  exact deningerBoundary_normSq_datum ℓ hℓ ψ

/-- The boundary norm. -/
noncomputable def deningerBoundaryNorm (ℓ : ι → ℝ) (φ : ι → ℂ) : ℝ :=
  Real.sqrt (deningerBoundaryNormSq ℓ φ)

theorem deningerBoundaryNorm_symm (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (φ : deningerBoundarySubmodule ℓ) :
    deningerBoundaryNorm ℓ (φ : ι → ℂ) = ‖(deningerBoundaryEquiv ℓ hℓ).symm φ‖ := by
  have h := deningerBoundaryEquiv_normSq ℓ hℓ ((deningerBoundaryEquiv ℓ hℓ).symm φ)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [deningerBoundaryNorm, h, Real.sqrt_sq (norm_nonneg _)]

/-- **The boundary norm is complete.**  A boundary-norm Cauchy sequence corresponds under the
parametrization to an `ℓ²`-Cauchy sequence, and `ℓ²` is complete; transporting the limit back gives
a boundary datum approached in boundary norm. -/
theorem deningerBoundary_complete (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (φ : ℕ → deningerBoundarySubmodule ℓ)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      deningerBoundaryNorm ℓ ((φ m : ι → ℂ) - (φ n : ι → ℂ)) < ε) :
    ∃ ω : deningerBoundarySubmodule ℓ,
      Filter.Tendsto (fun n => deningerBoundaryNorm ℓ ((φ n : ι → ℂ) - (ω : ι → ℂ)))
        Filter.atTop (nhds 0) := by
  set e := deningerBoundaryEquiv ℓ hℓ with he
  set ψ : ℕ → lp (fun _ : ι => ℂ) 2 := fun n => e.symm (φ n) with hψ
  have hdiff : ∀ m n : ℕ,
      deningerBoundaryNorm ℓ ((φ m : ι → ℂ) - (φ n : ι → ℂ)) = ‖ψ m - ψ n‖ := by
    intro m n
    have hcoe : ((φ m : ι → ℂ) - (φ n : ι → ℂ))
        = ((φ m - φ n : deningerBoundarySubmodule ℓ) : ι → ℂ) := by
      rw [Submodule.coe_sub]
    rw [hcoe, deningerBoundaryNorm_symm ℓ hℓ, map_sub]
  have hcauchySeq : CauchySeq ψ := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, ← hdiff m n]
    exact hN m hm n hn
  obtain ⟨psiLim, hpsiLim⟩ := cauchySeq_tendsto_of_complete hcauchySeq
  refine ⟨e psiLim, ?_⟩
  have hnorm : ∀ n : ℕ,
      deningerBoundaryNorm ℓ ((φ n : ι → ℂ) - ((e psiLim : deningerBoundarySubmodule ℓ) : ι → ℂ))
        = dist (ψ n) psiLim := by
    intro n
    have hcoe : ((φ n : ι → ℂ) - ((e psiLim : deningerBoundarySubmodule ℓ) : ι → ℂ))
        = ((φ n - e psiLim : deningerBoundarySubmodule ℓ) : ι → ℂ) := by
      rw [Submodule.coe_sub]
    rw [hcoe, deningerBoundaryNorm_symm ℓ hℓ, map_sub, LinearEquiv.symm_apply_apply,
      dist_eq_norm]
  have hdist : Filter.Tendsto (fun n => dist (ψ n) psiLim) Filter.atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hpsiLim
  exact (Filter.tendsto_congr hnorm).mpr hdist

end BoundaryComplete

end RHTower
