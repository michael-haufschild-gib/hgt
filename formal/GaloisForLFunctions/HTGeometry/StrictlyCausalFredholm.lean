import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator
import GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers

/-!
# Strict causality removes the entire regularized determinant

Every closed kernel path contains a forbidden causal edge. This proves all
trace powers vanish, and hence the global entire determinant is identically 1.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

namespace SchurKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

def SquareIntegrable (k : SchurKernel μ) : Prop :=
  (∫⁻ t, ∫⁻ a, ‖k.toFun t a‖ₑ ^ 2 ∂μ ∂μ) < ∞

theorem SquareIntegrable.comp {k l : SchurKernel μ}
    (hk : k.SquareIntegrable) (hl : l.SquareIntegrable) : (k.comp l).SquareIntegrable := by
  let k' : SqIntKernel μ μ := ⟨k.toFun, k.measurable, hk⟩
  let l' : SqIntKernel μ μ := ⟨l.toFun, l.measurable, hl⟩
  exact (k'.comp l').energy_lt_top

/-- The index `n` represents the positive power `n+1`. -/
def positivePower (k : SchurKernel μ) : ℕ → SchurKernel μ
  | 0 => k
  | n + 1 => k.comp (k.positivePower n)

theorem positivePower_op (k : SchurKernel μ) (n : ℕ) :
    (k.positivePower n).op = k.op ^ (n + 1) := by
  induction n with
  | zero => simp [positivePower]
  | succ n ih =>
    rw [positivePower, comp_op, ih, pow_succ' k.op (n + 1)]
    rfl

theorem SquareIntegrable.positivePower {k : SchurKernel μ}
    (hk : k.SquareIntegrable) (n : ℕ) : (k.positivePower n).SquareIntegrable := by
  induction n with
  | zero => exact hk
  | succ n ih => exact hk.comp ih

variable [LinearOrder α]

def StrictlyCausal (k : SchurKernel μ) : Prop :=
  ∀ t a, t ≤ a → k.toFun t a = 0

theorem StrictlyCausal.comp {k l : SchurKernel μ}
    (hk : k.StrictlyCausal) (hl : l.StrictlyCausal) : (k.comp l).StrictlyCausal := by
  intro t a hta
  rw [comp_toFun]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change k.toFun t y * l.toFun y a = 0
  by_cases hty : t ≤ y
  · rw [hk t y hty, zero_mul]
  · rw [hl y a ((le_of_not_ge hty).trans hta), mul_zero]

theorem StrictlyCausal.positivePower {k : SchurKernel μ}
    (hk : k.StrictlyCausal) (n : ℕ) : (k.positivePower n).StrictlyCausal := by
  induction n with
  | zero => exact hk
  | succ n ih => exact hk.comp ih

theorem opTrace_comp_eq_zero_of_strictlyCausal
    [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)] {k l : SchurKernel μ}
    (hk : k.StrictlyCausal) (hl : l.StrictlyCausal)
    (hk2 : k.SquareIntegrable) (hl2 : l.SquareIntegrable) :
    ContinuousLinearMap.opTrace (k.op ∘L l.op) = 0 := by
  rw [opTrace_comp_op k l hk2 hl2]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  apply integral_eq_zero_of_ae
  filter_upwards with z
  change k.toFun z y * l.toFun y z = 0
  rcases le_total z y with h | h
  · rw [hk z y h, zero_mul]
  · rw [hl y z h, mul_zero]

theorem opTrace_pow_eq_zero_of_strictlyCausal
    [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)] {k : SchurKernel μ}
    (hk : k.StrictlyCausal) (hk2 : k.SquareIntegrable) (n : ℕ) :
    ContinuousLinearMap.opTrace (k.op ^ (n + 2)) = 0 := by
  have hpow : k.op ^ (n + 2) = k.op ∘L (k.positivePower n).op := by
    rw [positivePower_op, pow_succ' k.op (n + 1)]
    rfl
  rw [hpow]
  exact opTrace_comp_eq_zero_of_strictlyCausal hk (hk.positivePower n)
    hk2 (hk2.positivePower n)

end SchurKernel

open HilbertSchmidt _root_.RHTower

theorem entireDet2_coordMatrix_eq_one_of_tracePowers_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : ContinuousLinearMap.IsHilbertSchmidt T)
    (htr : ∀ n : ℕ, ContinuousLinearMap.opTrace (T ^ (n + 2)) = 0) :
    entireDet2 (coordMatrix b T) = fun _ => 1 := by
  refine (isRegularizedDet_entireDet2 (isHS_coordMatrix b hT)).unique ?_
  refine ⟨differentiable_const 1, detRadius (coordMatrix b T), detRadius_pos _,
    detRadius_mul_hsNorm_lt _, fun z _ => ?_⟩
  rw [fredholmDet, fredholmExp_coordMatrix b hT]
  simp [traceExponent, htr]

theorem SchurKernel.entireDet2_eq_one_of_strictlyCausal
    {α : Type*} [MeasurableSpace α] [LinearOrder α] {μ : Measure α} [SFinite μ]
    [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)]
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    {k : SchurKernel μ} (hk : k.StrictlyCausal) (hk2 : k.SquareIntegrable) :
    entireDet2 (coordMatrix b k.op) = fun _ => 1 :=
  entireDet2_coordMatrix_eq_one_of_tracePowers_zero b (k.isHilbertSchmidt_op hk2)
    (SchurKernel.opTrace_pow_eq_zero_of_strictlyCausal hk hk2)

end GaloisForLFunctions.HTGeometry
