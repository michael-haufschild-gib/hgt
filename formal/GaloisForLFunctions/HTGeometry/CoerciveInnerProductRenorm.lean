import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator

/-!
# Coercive inner-product renorming

A bounded self-adjoint metric operator whose quadratic form controls the original norm equips the
same vector space with a complete Hilbert norm.  Both identity directions are quantitative.  This
is the completion step needed when a closed form is used as the ambient Hilbert inner product.
-/

open Complex Filter Topology
open scoped InnerProduct

noncomputable section

namespace CoerciveInnerProductRenorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded metric operator with coercivity constant one. -/
structure Datum (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →L[ℂ] H
  selfAdjoint : IsSelfAdjoint op
  coercive : ∀ x : H, ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (op x) x)

/-- Same vector space equipped with `⟪D.op x,y⟫`. -/
def Carrier (_D : Datum H) := H

instance (_D : Datum H) : AddCommGroup (Carrier _D) :=
  inferInstanceAs (AddCommGroup H)

instance (_D : Datum H) : Module ℂ (Carrier _D) :=
  inferInstanceAs (Module ℂ H)

/-- Algebraic identity from the renormed carrier to the original Hilbert space. -/
def toOld (D : Datum H) : Carrier D ≃ₗ[ℂ] H := LinearEquiv.refl ℂ H

variable (D : Datum H)

instance core : InnerProductSpace.Core ℂ (Carrier D) where
  inner x y := inner ℂ (D.op (toOld D x)) (toOld D y)
  conj_inner_symm x y := by
    rw [inner_conj_symm]
    exact D.selfAdjoint.isSymmetric (toOld D x) (toOld D y) |>.symm
  re_inner_nonneg x := le_trans (sq_nonneg ‖toOld D x‖) (D.coercive (toOld D x))
  add_left x y z := by
    simp [toOld]
  smul_left x y c := by
    simp [toOld, mul_comm]
  definite x hx := by
    have hle := D.coercive (toOld D x)
    rw [hx] at hle
    have hle0 : ‖toOld D x‖ ^ 2 ≤ 0 := by simpa using hle
    apply (toOld D).injective
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hle0 (sq_nonneg _)))

instance instNormedAddCommGroup : NormedAddCommGroup (Carrier D) :=
  (core D).toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace ℂ (Carrier D) :=
  InnerProductSpace.ofCore _

theorem inner_def (x y : Carrier D) :
    inner ℂ x y = inner ℂ (D.op (toOld D x)) (toOld D y) := rfl

/-- Renormed norm dominates the original norm. -/
theorem old_norm_le (x : Carrier D) : ‖toOld D x‖ ≤ ‖x‖ := by
  have hsq : ‖toOld D x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      ‖toOld D x‖ ^ 2 ≤
          RCLike.re (inner ℂ (D.op (toOld D x)) (toOld D x)) := D.coercive _
      _ = RCLike.re (inner ℂ x x) := by rw [inner_def]
      _ = ‖x‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  nlinarith [norm_nonneg (toOld D x), norm_nonneg x]

/-- Original norm controls the renormed norm with an explicit bounded-operator constant. -/
theorem norm_le (x : Carrier D) :
    ‖x‖ ≤ (‖D.op‖ + 1) * ‖toOld D x‖ := by
  have hsq : ‖x‖ ^ 2 =
      RCLike.re (inner ℂ (D.op (toOld D x)) (toOld D x)) := by
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x).trans
      (congrArg RCLike.re (inner_def D x x))
  have hre : RCLike.re (inner ℂ (D.op (toOld D x)) (toOld D x)) ≤
      ‖D.op‖ * ‖toOld D x‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ (D.op (toOld D x)) (toOld D x)‖ := RCLike.re_le_norm _
      _ ≤ ‖D.op (toOld D x)‖ * ‖toOld D x‖ := norm_inner_le_norm _ _
      _ ≤ (‖D.op‖ * ‖toOld D x‖) * ‖toOld D x‖ :=
        mul_le_mul_of_nonneg_right (D.op.le_opNorm _) (norm_nonneg _)
      _ = ‖D.op‖ * ‖toOld D x‖ ^ 2 := by ring
  have hsqbound : ‖x‖ ^ 2 ≤ ‖D.op‖ * ‖toOld D x‖ ^ 2 := hsq.le.trans hre
  have hrle : ‖D.op‖ ≤ (‖D.op‖ + 1) ^ 2 := by
    nlinarith [sq_nonneg ‖D.op‖]
  have hmul := mul_le_mul_of_nonneg_right hrle (sq_nonneg ‖toOld D x‖)
  have htargetSq : ‖x‖ ^ 2 ≤ ((‖D.op‖ + 1) * ‖toOld D x‖) ^ 2 := by
    calc
      ‖x‖ ^ 2 ≤ ‖D.op‖ * ‖toOld D x‖ ^ 2 := hsqbound
      _ ≤ (‖D.op‖ + 1) ^ 2 * ‖toOld D x‖ ^ 2 := hmul
      _ = ((‖D.op‖ + 1) * ‖toOld D x‖) ^ 2 := by ring
  have hx0 : 0 ≤ ‖toOld D x‖ := norm_nonneg _
  have hnew0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hright0 : 0 ≤ (‖D.op‖ + 1) * ‖toOld D x‖ := mul_nonneg (by positivity) hx0
  nlinarith

/-- Coercive metric renorming preserves completeness. -/
instance instCompleteSpace : CompleteSpace (Carrier D) := by
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  have hold : CauchySeq (fun n => toOld D (u n)) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hle := old_norm_le D (u m - u n)
    have hlt := hN m hm n hn
    simpa [dist_eq_norm, ← map_sub] using hle.trans_lt (by simpa [dist_eq_norm] using hlt)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hold
  let xnew : Carrier D := (toOld D).symm x
  refine ⟨xnew, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  let C : ℝ := ‖D.op‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (ε / C) (div_pos hε hC)
  refine ⟨N, fun n hn => ?_⟩
  have hbound := norm_le D (u n - xnew)
  have holdlt : ‖toOld D (u n - xnew)‖ < ε / C := by
    simpa [dist_eq_norm, xnew] using hN n hn
  have hlt := mul_lt_mul_of_pos_left holdlt hC
  have hlt' : C * ‖toOld D (u n - xnew)‖ < ε := by
    calc
      C * ‖toOld D (u n - xnew)‖ < C * (ε / C) := hlt
      _ = ε := by field_simp
  simpa [dist_eq_norm, C] using hbound.trans_lt hlt'

end CoerciveInnerProductRenorm
