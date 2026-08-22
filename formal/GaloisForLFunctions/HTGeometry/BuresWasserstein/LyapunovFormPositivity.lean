import GaloisForLFunctions.HTGeometry.HilbertSchmidtSandwichPositivity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtSandwichBounds
import GaloisForLFunctions.HTGeometry.OperatorLoewnerVectorBounds
import GaloisForLFunctions.HTGeometry.BuresWasserstein.KantorovichConverse
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNormBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positivity of the Lyapunov-solved quadratic form

The derivative of the Wasserstein vector field is built from solutions of Lyapunov equations
`u y + y u = u² q u²`.  Solving for `q` gives `q = u⁻¹ y u⁻² + u⁻² y u⁻¹`, and the Hilbert–Schmidt
pairing of `q` against `y` is a sum of two squared Hilbert–Schmidt norms:

`Re ⟨q, y⟩_HS = ‖u^{-1/2} y u⁻¹‖²_HS + ‖u⁻¹ y u^{-1/2}‖²_HS ≥ 0`.

This is the positivity underlying Kim–Mer–Pálfia (arXiv:2607.29142), Lemma 3.11, obtained without
the semigroup integral representation of the paper.
-/

open scoped Ring BigOperators InnerProductSpace
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

omit [CompleteSpace E] [StarOrderedRing (E →L[ℂ] E)] in
/-- Solving the Lyapunov equation `u y + y u = u² q u²`. -/
theorem lyapunov_solution {u y : E →L[ℂ] E} (hu : IsStrictlyPositive u) :
    (u * u) * (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ) * (u * u)
      = u * y + y * u := by
  have hL : ∀ z : (E →L[ℂ] E), u * (u⁻¹ʳ * z) = z := fun z =>
    Ring.mul_inverse_cancel_left u z hu.isUnit
  have hR : ∀ z : (E →L[ℂ] E), u⁻¹ʳ * (u * z) = z := fun z =>
    Ring.inverse_mul_cancel_left u z hu.isUnit
  have hRr : u⁻¹ʳ * u = 1 := Ring.inverse_mul_cancel u hu.isUnit
  simp only [add_mul, mul_add, mul_assoc, hL, hR, hRr, mul_one]

/-- The pairing of the Lyapunov solution against `y` is a sum of two squared Hilbert–Schmidt
norms. -/
theorem re_hsInner_lyapunovSolution {u y : E →L[ℂ] E} (hu : IsStrictlyPositive u)
    (hy : IsHilbertSchmidt y) :
    RCLike.re (hsInner (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ) y)
      = hsNormSq ((u ^ (-(1/2) : ℝ)) ∘L y ∘L u⁻¹ʳ)
        + hsNormSq (u⁻¹ʳ ∘L y ∘L (u ^ (-(1/2) : ℝ))) := by
  have hhalf : IsSelfAdjoint (u ^ (-(1/2) : ℝ)) :=
    (CFC.rpow_nonneg (a := u) (y := (-(1/2) : ℝ))).isSelfAdjoint
  have hinvsa : IsSelfAdjoint (u⁻¹ʳ : E →L[ℂ] E) := hu.ringInverse.isSelfAdjoint
  have hsq : (u ^ (-(1/2) : ℝ)) * (u ^ (-(1/2) : ℝ)) = (u⁻¹ʳ : E →L[ℂ] E) := by
    rw [← CFC.rpow_add hu.isUnit, CFC.inverse_eq_rpow_neg_one hu]
    norm_num
  have hHS1 : IsHilbertSchmidt (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E) :=
    (hy.comp_left _).comp_right _
  have hHS2 : IsHilbertSchmidt ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E) :=
    (hy.comp_left _).comp_right _
  have hterm1 : RCLike.re (hsInner (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E) y)
      = hsNormSq ((u ^ (-(1/2) : ℝ)) ∘L y ∘L u⁻¹ʳ) := by
    have h := re_hsInner_sandwich_eq_hsNormSq (s := u ^ (-(1/2) : ℝ)) (t := (u⁻¹ʳ : E →L[ℂ] E)) hy
    rwa [show (adjoint (u ^ (-(1/2) : ℝ)) ∘L (u ^ (-(1/2) : ℝ)) : E →L[ℂ] E) = u⁻¹ʳ by
      rw [show adjoint (u ^ (-(1/2) : ℝ)) = (u ^ (-(1/2) : ℝ) : E →L[ℂ] E) from hhalf.star_eq]
      exact hsq,
      show ((u⁻¹ʳ : E →L[ℂ] E) ∘L adjoint (u⁻¹ʳ : E →L[ℂ] E)) = u⁻¹ʳ * u⁻¹ʳ by
      rw [show adjoint (u⁻¹ʳ : E →L[ℂ] E) = u⁻¹ʳ from hinvsa.star_eq]; rfl] at h
  have hterm2 : RCLike.re (hsInner ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E) y)
      = hsNormSq (u⁻¹ʳ ∘L y ∘L (u ^ (-(1/2) : ℝ))) := by
    have h := re_hsInner_sandwich_eq_hsNormSq (s := (u⁻¹ʳ : E →L[ℂ] E))
      (t := u ^ (-(1/2) : ℝ)) hy
    rwa [show (adjoint (u⁻¹ʳ : E →L[ℂ] E) ∘L (u⁻¹ʳ : E →L[ℂ] E)) = u⁻¹ʳ * u⁻¹ʳ by
      rw [show adjoint (u⁻¹ʳ : E →L[ℂ] E) = u⁻¹ʳ from hinvsa.star_eq]; rfl,
      show ((u ^ (-(1/2) : ℝ)) ∘L adjoint (u ^ (-(1/2) : ℝ)) : E →L[ℂ] E) = u⁻¹ʳ by
      rw [show adjoint (u ^ (-(1/2) : ℝ)) = (u ^ (-(1/2) : ℝ) : E →L[ℂ] E) from hhalf.star_eq]
      exact hsq] at h
  rw [hsInner_add_left hHS1 hHS2 hy, map_add, hterm1, hterm2]

/-- **Nonnegativity of the Lyapunov-solved quadratic form.** -/
theorem re_hsInner_lyapunovSolution_nonneg {u y : E →L[ℂ] E} (hu : IsStrictlyPositive u)
    (hy : IsHilbertSchmidt y) :
    0 ≤ RCLike.re (hsInner (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ) y) := by
  rw [re_hsInner_lyapunovSolution hu hy]
  exact add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)

/-! ### The quantitative lower bound -/

/-- A Loewner upper bound on `u` gives a Loewner lower bound on `u^{-1/2}`. -/
theorem smul_one_le_rpow_neg_half {u : E →L[ℂ] E} (hu : IsStrictlyPositive u) {β : ℝ}
    (hβ : 0 < β) (hub : u ≤ β • (1 : E →L[ℂ] E)) :
    (Real.sqrt β⁻¹) • (1 : E →L[ℂ] E) ≤ u ^ (-(1/2) : ℝ) := by
  have hinv : β⁻¹ • (1 : E →L[ℂ] E) ≤ u⁻¹ʳ :=
    smul_one_le_ringInverse_of_le_smul_one hu hβ hub
  have hmono := CFC.sqrt_le_sqrt _ _ hinv
  rwa [cfcSqrt_smul (inv_pos.mpr hβ).le (zero_le_one (α := E →L[ℂ] E)), CFC.sqrt_one,
    CFC.sqrt_eq_rpow, rpow_half_ringInverse hu] at hmono

/-- **Quantitative lower bound for the Lyapunov-solved quadratic form.** -/
theorem re_hsInner_lyapunovSolution_lower {u y : E →L[ℂ] E} (hu : IsStrictlyPositive u)
    (hy : IsHilbertSchmidt y) {β : ℝ} (hβ : 0 < β) (hub : u ≤ β • (1 : E →L[ℂ] E)) :
    (2 * (β⁻¹ * (β⁻¹ * β⁻¹))) * hsNormSq y
      ≤ RCLike.re (hsInner (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ) y) := by
  have hinvsa : IsSelfAdjoint (u⁻¹ʳ : E →L[ℂ] E) := hu.ringInverse.isSelfAdjoint
  have hhalfsa : IsSelfAdjoint (u ^ (-(1/2) : ℝ) : E →L[ℂ] E) :=
    (CFC.rpow_nonneg (a := u) (y := (-(1/2) : ℝ))).isSelfAdjoint
  have hlowinv : β⁻¹ • (1 : E →L[ℂ] E) ≤ u⁻¹ʳ :=
    smul_one_le_ringInverse_of_le_smul_one hu hβ hub
  have hlowhalf : (Real.sqrt β⁻¹) • (1 : E →L[ℂ] E) ≤ u ^ (-(1/2) : ℝ) :=
    smul_one_le_rpow_neg_half hu hβ hub
  have hsqβ : Real.sqrt β⁻¹ * Real.sqrt β⁻¹ = β⁻¹ :=
    Real.mul_self_sqrt (inv_pos.mpr hβ).le
  have hvinv : ∀ v : E, (β⁻¹ * β⁻¹) * ‖v‖ ^ 2 ≤ ‖(u⁻¹ʳ : E →L[ℂ] E) v‖ ^ 2 := fun v =>
    sq_mul_norm_sq_le_norm_apply_sq (inv_pos.mpr hβ).le hlowinv v
  have hvhalf : ∀ v : E, β⁻¹ * ‖v‖ ^ 2 ≤ ‖(u ^ (-(1/2) : ℝ) : E →L[ℂ] E) v‖ ^ 2 := fun v => by
    have h := sq_mul_norm_sq_le_norm_apply_sq (Real.sqrt_nonneg β⁻¹) hlowhalf v
    rwa [hsqβ] at h
  have hterm1 : (β⁻¹ * (β⁻¹ * β⁻¹)) * hsNormSq y
      ≤ hsNormSq ((u ^ (-(1/2) : ℝ)) ∘L (y ∘L u⁻¹ʳ)) := by
    refine le_hsNormSq_sandwich hy (inv_pos.mpr hβ).le hvhalf ?_
    intro v
    rw [show adjoint (u⁻¹ʳ : E →L[ℂ] E) = u⁻¹ʳ from hinvsa.star_eq]
    exact hvinv v
  have hterm2 : ((β⁻¹ * β⁻¹) * β⁻¹) * hsNormSq y
      ≤ hsNormSq ((u⁻¹ʳ : E →L[ℂ] E) ∘L (y ∘L (u ^ (-(1/2) : ℝ)))) := by
    refine le_hsNormSq_sandwich hy (by positivity) hvinv ?_
    intro v
    rw [show adjoint (u ^ (-(1/2) : ℝ) : E →L[ℂ] E) = u ^ (-(1/2) : ℝ) from hhalfsa.star_eq]
    exact hvhalf v
  rw [re_hsInner_lyapunovSolution hu hy]
  have hassoc1 : ((u ^ (-(1/2) : ℝ)) ∘L y ∘L u⁻¹ʳ : E →L[ℂ] E)
      = (u ^ (-(1/2) : ℝ)) ∘L (y ∘L u⁻¹ʳ) := rfl
  have hassoc2 : ((u⁻¹ʳ : E →L[ℂ] E) ∘L y ∘L (u ^ (-(1/2) : ℝ)))
      = (u⁻¹ʳ : E →L[ℂ] E) ∘L (y ∘L (u ^ (-(1/2) : ℝ))) := rfl
  rw [hassoc1, hassoc2]
  have hsum : (2 * (β⁻¹ * (β⁻¹ * β⁻¹))) * hsNormSq y
      = (β⁻¹ * (β⁻¹ * β⁻¹)) * hsNormSq y + ((β⁻¹ * β⁻¹) * β⁻¹) * hsNormSq y := by ring
  rw [hsum]
  exact add_le_add hterm1 hterm2

/-! ### The sharp coercivity bound -/

omit [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
open ContinuousLinearMap in
/-- `hsNorm` squares back to `hsNormSq`. -/
lemma hsNorm_sq (T : E →L[ℂ] E) : (hsNorm T) ^ 2 = hsNormSq T :=
  Real.sq_sqrt (hsNormSq_nonneg T)

open ContinuousLinearMap in
/-- Loewner bounds on `u` bound the operator norms of `u⁻¹` and `u^{-1/2}`. -/
lemma norm_ringInverse_le {u : E →L[ℂ] E} (hu : IsStrictlyPositive u) {β : ℝ} (hβ : 0 < β)
    (hlb : β⁻¹ • (1 : E →L[ℂ] E) ≤ u) :
    ‖(u⁻¹ʳ : E →L[ℂ] E)‖ ≤ β ∧ ‖(u ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ≤ Real.sqrt β := by
  have hupper : (u⁻¹ʳ : E →L[ℂ] E) ≤ β • (1 : E →L[ℂ] E) := by
    have h := ringInverse_le_of_smul_one_le (inv_pos.mpr hβ) hlb
    rwa [inv_inv] at h
  have h1 : ‖(u⁻¹ʳ : E →L[ℂ] E)‖ ≤ β :=
    norm_le_of_le_smul_one hu.ringInverse.nonneg hβ.le hupper
  refine ⟨h1, ?_⟩
  have h2 : (u ^ (-(1/2) : ℝ) : E →L[ℂ] E) ≤ (Real.sqrt β) • (1 : E →L[ℂ] E) := by
    have hm := CFC.sqrt_le_sqrt _ _ hupper
    rwa [CFC.sqrt_eq_rpow, rpow_half_ringInverse hu,
      cfcSqrt_smul hβ.le (zero_le_one (α := E →L[ℂ] E)), CFC.sqrt_one] at hm
  exact norm_le_of_le_smul_one CFC.rpow_nonneg (Real.sqrt_nonneg β) h2

open ContinuousLinearMap in
/-- **Sharp coercivity of the Lyapunov-solved form**: `‖q‖²_HS ≤ 2β³ · Re⟨q, y⟩_HS`. -/
theorem hsNormSq_le_re_hsInner_lyapunovSolution {u y : E →L[ℂ] E} (hu : IsStrictlyPositive u)
    (hy : IsHilbertSchmidt y) {β : ℝ} (hβ : 0 < β) (hlb : β⁻¹ • (1 : E →L[ℂ] E) ≤ u) :
    hsNormSq (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ)
      ≤ (2 * (β * (β * β)))
        * RCLike.re (hsInner (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ) y) := by
  obtain ⟨hn1, hn2⟩ := norm_ringInverse_le hu hβ hlb
  set A : E →L[ℂ] E := (u ^ (-(1/2) : ℝ)) ∘L (y ∘L u⁻¹ʳ) with hA
  set B : E →L[ℂ] E := (u⁻¹ʳ : E →L[ℂ] E) ∘L (y ∘L (u ^ (-(1/2) : ℝ))) with hB
  have hAHS : IsHilbertSchmidt A := (hy.comp_right _).comp_left _
  have hBHS : IsHilbertSchmidt B := (hy.comp_right _).comp_left _
  have hsqβ : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ.le
  have hq1 : (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E)
      = (u ^ (-(1/2) : ℝ)) ∘L (A ∘L u⁻¹ʳ) := by
    have hsq : (u ^ (-(1/2) : ℝ)) * (u ^ (-(1/2) : ℝ)) = (u⁻¹ʳ : E →L[ℂ] E) := by
      rw [← CFC.rpow_add hu.isUnit, CFC.inverse_eq_rpow_neg_one hu]; norm_num
    calc (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E)
        = ((u ^ (-(1/2) : ℝ)) * (u ^ (-(1/2) : ℝ))) * (y * (u⁻¹ʳ * u⁻¹ʳ)) := by
          rw [hsq]; noncomm_ring
      _ = (u ^ (-(1/2) : ℝ)) ∘L (A ∘L u⁻¹ʳ) := by
          show _ = (u ^ (-(1/2) : ℝ)) * ((u ^ (-(1/2) : ℝ)) * (y * u⁻¹ʳ) * u⁻¹ʳ)
          noncomm_ring
  have hq2 : ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
      = (u⁻¹ʳ : E →L[ℂ] E) ∘L (B ∘L (u ^ (-(1/2) : ℝ))) := by
    have hsq : (u ^ (-(1/2) : ℝ)) * (u ^ (-(1/2) : ℝ)) = (u⁻¹ʳ : E →L[ℂ] E) := by
      rw [← CFC.rpow_add hu.isUnit, CFC.inverse_eq_rpow_neg_one hu]; norm_num
    calc ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
        = (u⁻¹ʳ * u⁻¹ʳ) * (y * ((u ^ (-(1/2) : ℝ)) * (u ^ (-(1/2) : ℝ)))) := by
          rw [hsq]; noncomm_ring
      _ = (u⁻¹ʳ : E →L[ℂ] E) ∘L (B ∘L (u ^ (-(1/2) : ℝ))) := by
          show _ = u⁻¹ʳ * (u⁻¹ʳ * (y * (u ^ (-(1/2) : ℝ))) * (u ^ (-(1/2) : ℝ)))
          noncomm_ring
  have hbound1 : hsNormSq (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E)
      ≤ (β * (β * β)) * hsNormSq A := by
    rw [hq1]
    refine (hsNormSq_sandwich_le hAHS).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonneg A)
    calc ‖(u ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ^ 2 * ‖(u⁻¹ʳ : E →L[ℂ] E)‖ ^ 2
        ≤ (Real.sqrt β) ^ 2 * β ^ 2 := by
          gcongr
      _ = β * (β * β) := by rw [sq, hsqβ]; ring
  have hbound2 : hsNormSq ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
      ≤ (β * (β * β)) * hsNormSq B := by
    rw [hq2]
    refine (hsNormSq_sandwich_le hBHS).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonneg B)
    calc ‖(u⁻¹ʳ : E →L[ℂ] E)‖ ^ 2 * ‖(u ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ^ 2
        ≤ β ^ 2 * (Real.sqrt β) ^ 2 := by
          gcongr
      _ = β * (β * β) := by rw [sq (Real.sqrt β), hsqβ]; ring
  have hHS1 : IsHilbertSchmidt (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E) :=
    (hy.comp_left _).comp_right _
  have hHS2 : IsHilbertSchmidt ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E) :=
    (hy.comp_left _).comp_right _
  have htri : hsNorm (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
      ≤ Real.sqrt (β * (β * β)) * (hsNorm A + hsNorm B) := by
    refine (hsNorm_add_le hHS1 hHS2).trans ?_
    have e1 : hsNorm (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) : E →L[ℂ] E)
        ≤ Real.sqrt (β * (β * β)) * hsNorm A := by
      have h := Real.sqrt_le_sqrt hbound1
      rwa [Real.sqrt_mul (by positivity)] at h
    have e2 : hsNorm ((u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
        ≤ Real.sqrt (β * (β * β)) * hsNorm B := by
      have h := Real.sqrt_le_sqrt hbound2
      rwa [Real.sqrt_mul (by positivity)] at h
    linarith
  have hkey : hsNormSq (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
      ≤ (β * (β * β)) * (hsNorm A + hsNorm B) ^ 2 := by
    rw [← hsNorm_sq]
    have hnn : 0 ≤ hsNorm (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E) :=
      hsNorm_nonneg _
    have hsq := mul_self_le_mul_self hnn htri
    have hb : Real.sqrt (β * (β * β)) * Real.sqrt (β * (β * β)) = β * (β * β) :=
      Real.mul_self_sqrt (by positivity)
    calc hsNorm (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E) ^ 2
        = hsNorm (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E)
            * hsNorm (u⁻¹ʳ * y * (u⁻¹ʳ * u⁻¹ʳ) + (u⁻¹ʳ * u⁻¹ʳ) * y * u⁻¹ʳ : E →L[ℂ] E) := sq _
      _ ≤ (Real.sqrt (β * (β * β)) * (hsNorm A + hsNorm B))
            * (Real.sqrt (β * (β * β)) * (hsNorm A + hsNorm B)) := hsq
      _ = (Real.sqrt (β * (β * β)) * Real.sqrt (β * (β * β)))
            * ((hsNorm A + hsNorm B) * (hsNorm A + hsNorm B)) := by ring
      _ = (β * (β * β)) * (hsNorm A + hsNorm B) ^ 2 := by rw [hb, sq]
  refine hkey.trans ?_
  rw [re_hsInner_lyapunovSolution hu hy, ← hA, ← hB, ← hsNorm_sq A, ← hsNorm_sq B]
  have hsum : (hsNorm A + hsNorm B) ^ 2 ≤ 2 * (hsNorm A ^ 2 + hsNorm B ^ 2) := by
    nlinarith [sq_nonneg (hsNorm A - hsNorm B)]
  calc (β * (β * β)) * (hsNorm A + hsNorm B) ^ 2
      ≤ (β * (β * β)) * (2 * (hsNorm A ^ 2 + hsNorm B ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 * (β * (β * β))) * (hsNorm A ^ 2 + hsNorm B ^ 2) := by ring

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
