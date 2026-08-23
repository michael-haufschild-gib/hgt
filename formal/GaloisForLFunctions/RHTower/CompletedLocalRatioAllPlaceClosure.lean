import GaloisForLFunctions.RHTower.CompletedLocalRatioAllPlaceCollapse
import GaloisForLFunctions.RHTower.FiniteEulerLocalRatioAbsoluteDivergence

/-!
# Complete all-place local-ratio closure

This module joins the two unconditional halves of the all-place no-go:

* the ordinary prime product has no nonempty open domain of absolute convergence;
* completion-compatible meromorphic regularization is the constant unit symbol.

The latter statement is then transported through an arbitrary idempotent linear polarization.  Its
off-diagonal corner is literally zero and its diagonal corner is the polarization itself, hence the
identity on the polarized range.  This is the exact functorial window/Fredholm collapse used by the
paper theorem, without selecting a particular Hardy-space model.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Multiplication by the globally regularized completed local-ratio symbol on complex-valued
functions. -/
def regularizedCompletedLocalRatioMultiplication :
    (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f s := regularizedCompletedLocalRatio s * f s
  map_add' f g := by
    funext s
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The regularized multiplication operator is exactly the identity. -/
theorem regularizedCompletedLocalRatioMultiplication_eq_id :
    regularizedCompletedLocalRatioMultiplication = LinearMap.id := by
  ext f s
  simp [regularizedCompletedLocalRatioMultiplication,
    regularizedCompletedLocalRatio_eq_one]

/-- Off-diagonal corner of regularized multiplication relative to a linear polarization. -/
def regularizedCompletedLocalRatioOffDiagonal
    (P : Module.End ℂ (ℂ → ℂ)) : Module.End ℂ (ℂ → ℂ) :=
  (LinearMap.id - P).comp (regularizedCompletedLocalRatioMultiplication.comp P)

/-- Diagonal corner of regularized multiplication relative to a linear polarization. -/
def regularizedCompletedLocalRatioDiagonal
    (P : Module.End ℂ (ℂ → ℂ)) : Module.End ℂ (ℂ → ℂ) :=
  P.comp (regularizedCompletedLocalRatioMultiplication.comp P)

/-- **Universal off-diagonal collapse.** Every idempotent polarization has zero completed
local-ratio off-diagonal corner. -/
theorem regularizedCompletedLocalRatioOffDiagonal_eq_zero
    (P : Module.End ℂ (ℂ → ℂ)) (hP : P.comp P = P) :
    regularizedCompletedLocalRatioOffDiagonal P = 0 := by
  rw [regularizedCompletedLocalRatioOffDiagonal,
    regularizedCompletedLocalRatioMultiplication_eq_id]
  ext f s
  have hPf := LinearMap.congr_fun hP f
  change P (P f) = P f at hPf
  simp [LinearMap.comp_apply, hPf]

/-- **Universal diagonal collapse.** The completed local-ratio diagonal corner is the
polarization, hence the identity on its range. -/
theorem regularizedCompletedLocalRatioDiagonal_eq
    (P : Module.End ℂ (ℂ → ℂ)) (hP : P.comp P = P) :
    regularizedCompletedLocalRatioDiagonal P = P := by
  rw [regularizedCompletedLocalRatioDiagonal,
    regularizedCompletedLocalRatioMultiplication_eq_id]
  apply LinearMap.ext
  intro f
  change P (P f) = P f
  exact LinearMap.congr_fun hP f

/-- Pointwise range form: the diagonal corner fixes every polarized vector. -/
theorem regularizedCompletedLocalRatioDiagonal_apply_of_mem_range
    (P : Module.End ℂ (ℂ → ℂ)) (hP : P.comp P = P)
    {f : ℂ → ℂ} (hf : P f = f) :
    regularizedCompletedLocalRatioDiagonal P f = f := by
  rw [regularizedCompletedLocalRatioDiagonal_eq P hP, hf]

/-- The regularized diagonal corner has trivial kernel on the polarized range. -/
theorem regularizedCompletedLocalRatioDiagonal_injectiveOn_range
    (P : Module.End ℂ (ℂ → ℂ)) (hP : P.comp P = P) :
    Set.InjOn (regularizedCompletedLocalRatioDiagonal P) (LinearMap.range P) := by
  intro f hf g hg hfg
  have hf_fixed : P f = f := by
    obtain ⟨f0, rfl⟩ := hf
    exact LinearMap.congr_fun hP f0
  have hg_fixed : P g = g := by
    obtain ⟨g0, rfl⟩ := hg
    exact LinearMap.congr_fun hP g0
  rw [regularizedCompletedLocalRatioDiagonal_eq P hP] at hfg
  exact hf_fixed.symm.trans (hfg.trans hg_fixed)

/-- The ordinary and regularized alternatives close simultaneously: no open absolute-product
domain exists, while every regularized polarized window is the trivial identity window. -/
theorem completedLocalRatio_allPlace_noGo :
    (¬ ∃ U : Set ℂ, U.Nonempty ∧ IsOpen U ∧
      ∀ s ∈ U, GaloisForLFunctions.RHTower.FiniteEulerLocalRatioAbsolutelySummableAt s) ∧
    regularizedCompletedLocalRatio = (fun _ => 1) ∧
    ∀ (P : Module.End ℂ (ℂ → ℂ)), P.comp P = P →
      regularizedCompletedLocalRatioOffDiagonal P = 0 ∧
      regularizedCompletedLocalRatioDiagonal P = P := by
  refine ⟨GaloisForLFunctions.RHTower.not_exists_nonempty_open_finiteEulerLocalRatio_absoluteConvergenceDomain,
    regularizedCompletedLocalRatio_eq_const_one, ?_⟩
  intro P hP
  exact ⟨regularizedCompletedLocalRatioOffDiagonal_eq_zero P hP,
    regularizedCompletedLocalRatioDiagonal_eq P hP⟩

end GaloisForLFunctions.RHTower

end
