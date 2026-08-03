import GaloisForLFunctions.RHTower.CCMRationalWeightedShiftLOneIsometry
import GaloisForLFunctions.RHTower.CCMRationalAdelicBruhatSimpleTensorTraceClass
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Rational adelic orbit coefficients in genuine `ℓ1`

This file packages every fixed-base rational adelic Bruhat orbit as an actual point of
`ℓ1(ℚˣ)`, identifies the pre-existing trace-class weighted shift with the canonical
`ℓ1` isometric representation, and proves a reusable local dominated-convergence criterion for
`ℓ1`-valued families.

The remaining class-space landing problem is thereby isolated exactly: establish local summable
domination and coordinate continuity for the canonical section parameters.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions
namespace RHTower

/-- A pure-tensor rational adelic orbit as a genuine `ℓ1(ℚˣ)` coefficient. -/
def ccmRationalAdelicBruhatPureTensorOrbitLOne
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    CCMRationalMoritaLOneCoefficient :=
  ⟨(ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b :
      PreLp (fun _ : CCMRationalUnit => ℂ)), by
    change Memℓp
      (ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b) 1
    rw [memℓp_gen_iff (by norm_num)]
    simpa using
      ccmRationalAdelicBruhatPureTensorOrbitCoefficient_summable
        f φ hbInf b⟩

@[simp]
theorem ccmRationalAdelicBruhatPureTensorOrbitLOne_apply
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatPureTensorOrbitLOne f φ hbInf b q =
      ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b q :=
  rfl

/-- An arbitrary algebraic Bruhat-tensor orbit as a genuine `ℓ1(ℚˣ)` coefficient. -/
def ccmRationalAdelicBruhatTensorOrbitLOne
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    CCMRationalMoritaLOneCoefficient :=
  ⟨(ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b :
      PreLp (fun _ : CCMRationalUnit => ℂ)), by
    change Memℓp (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b) 1
    rw [memℓp_gen_iff (by norm_num)]
    simpa using
      ccmRationalAdelicBruhatTensorOrbitCoefficient_summable t hbInf b⟩

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitLOne_apply
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbitLOne t hbInf b q =
      ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q :=
  rfl

/-- The old fixed-base adelic weighted shift is exactly the canonical `ℓ1` isometric image;
its auxiliary uniform-bound certificate carries no analytic information. -/
theorem ccmRationalAdelicBruhatTensorWeightedShift_eq_lOne
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorWeightedShift t hbInf b k =
      ccmRationalMoritaLOneWeightedShiftOperator k
        (ccmRationalAdelicBruhatTensorOrbitLOne t hbInf b) := by
  apply ccmRationalMoritaWeightedShift_congr_bound

/-- Exact trace norm of every fixed-base adelic Bruhat monomial. -/
theorem ccmRationalAdelicBruhatTensorWeightedShift_traceNorm
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : CCMRationalUnit) :
    _root_.RHTower.traceNorm CCMRationalMoritaHilbert
        (ccmRationalAdelicBruhatTensorWeightedShift t hbInf b k) =
      ‖ccmRationalAdelicBruhatTensorOrbitLOne t hbInf b‖ := by
  rw [ccmRationalAdelicBruhatTensorWeightedShift_eq_lOne]
  exact ccmRationalMoritaLOneWeightedShift_norm k
    (ccmRationalAdelicBruhatTensorOrbitLOne t hbInf b)

/-- **Local `ℓ1` dominated-convergence law.**  Coordinatewise continuity plus one locally
summable majorant implies genuine `ℓ1` continuity. -/
theorem continuousAt_ccmRationalMoritaLOneCoefficient_of_dominated
    {X : Type*} [TopologicalSpace X]
    (F : X → CCMRationalMoritaLOneCoefficient) (x₀ : X)
    (u : CCMRationalUnit → ℝ) (hu : Summable u)
    (hcoord : ∀ q, ContinuousAt (fun x => F x q) x₀)
    (hbound : ∀ᶠ x in 𝓝 x₀, ∀ q, ‖F x q‖ ≤ u q) :
    ContinuousAt F x₀ := by
  have hbound₀ : ∀ q, ‖F x₀ q‖ ≤ u q := hbound.self_of_nhds
  have hdom : ∀ᶠ x in 𝓝 x₀, ∀ q,
      ‖(‖F x q - F x₀ q‖ : ℝ)‖ ≤ u q + u q := by
    filter_upwards [hbound] with x hx
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le (F x q) (F x₀ q)).trans
      (add_le_add (hx q) (hbound₀ q))
  have hterm : ∀ q, Tendsto (fun x => ‖F x q - F x₀ q‖)
      (𝓝 x₀) (𝓝 0) := by
    intro q
    have hc : ContinuousAt (fun _ : X => F x₀ q) x₀ := continuousAt_const
    have ht := ((hcoord q).sub hc).norm
    rw [ContinuousAt] at ht
    simpa using ht
  have htsum : Tendsto
      (fun x => ∑' q, ‖F x q - F x₀ q‖)
      (𝓝 x₀) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence
      (hu.add hu) hterm hdom
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  convert htsum using 1
  funext x
  rw [ccmRationalMoritaLOneCoefficient_norm_eq_tsum]
  rfl

/-- Isometric weighted-shift transport preserves and reflects continuity at every parameter. -/
theorem continuousAt_ccmRationalMoritaLOneWeightedShift_iff
    {X : Type*} [TopologicalSpace X]
    (k : CCMRationalUnit)
    (F : X → CCMRationalMoritaLOneCoefficient) (x₀ : X) :
    ContinuousAt (fun x => ccmRationalMoritaLOneWeightedShift k (F x)) x₀ ↔
      ContinuousAt F x₀ := by
  constructor
  · intro h
    rw [ContinuousAt, Metric.tendsto_nhds] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with y hy
    · rw [← ccmRationalMoritaLOneWeightedShift_dist k]
      exact hy
  · intro h
    exact (ccmRationalMoritaLOneWeightedShiftLinearIsometry k).continuous.continuousAt.comp h

end RHTower
end GaloisForLFunctions
