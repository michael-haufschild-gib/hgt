import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionConjugacy

/-!
# The rigid constant sector of polynomial connection conjugacy

Transporting the constant eigenvector detects a constant coefficient exactly.
Unlike the nonconstant degree classes, two constant connections are linearly
conjugate only when their coefficients are identical.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Identity is a connection intertwiner. -/
def gomesPolynomialConnectionIntertwinerRefl (A : ℝ[X]) :
    GomesPolynomialConnectionIntertwiner A A :=
  ⟨LinearEquiv.refl ℝ ℝ[X], by apply LinearMap.ext; intro Q; rfl⟩

/-- The inverse of an invertible connection intertwiner intertwines in reverse. -/
def gomesPolynomialConnectionIntertwinerSymm (A B : ℝ[X])
    (E : GomesPolynomialConnectionIntertwiner A B) :
    GomesPolynomialConnectionIntertwiner B A := by
  refine ⟨E.val.symm, ?_⟩
  apply LinearMap.ext
  intro Q
  change E.val.symm (gomesPolynomialFirstOrderLinearMap B Q) =
    gomesPolynomialFirstOrderLinearMap A (E.val.symm Q)
  apply E.val.injective
  have h := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f (E.val.symm Q)) E.property
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h.symm

/-- Invertible connection intertwiners compose. -/
def gomesPolynomialConnectionIntertwinerTrans (A B D : ℝ[X])
    (E : GomesPolynomialConnectionIntertwiner A B)
    (F : GomesPolynomialConnectionIntertwiner B D) :
    GomesPolynomialConnectionIntertwiner A D := by
  refine ⟨E.val.trans F.val, ?_⟩
  apply LinearMap.ext
  intro Q
  have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f Q) E.property
  have hf := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f (E.val Q)) F.property
  change E.val (gomesPolynomialFirstOrderLinearMap A Q) =
    gomesPolynomialFirstOrderLinearMap B (E.val Q) at he
  change F.val (gomesPolynomialFirstOrderLinearMap B (E.val Q)) =
    gomesPolynomialFirstOrderLinearMap D (F.val (E.val Q)) at hf
  change F.val (E.val (gomesPolynomialFirstOrderLinearMap A Q)) =
    gomesPolynomialFirstOrderLinearMap D (F.val (E.val Q))
  rw [he, hf]

/-- A connection conjugate to a constant coefficient has that identical coefficient. -/
theorem gomesPolynomialConnectionIntertwiner_constant_source
    (a : ℝ) (B : ℝ[X]) (E : GomesPolynomialConnectionIntertwiner (C a) B) :
    B = C a := by
  have h := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f 1) E.property
  change E.val (gomesPolynomialFirstOrderOperator (C a) 1) =
    gomesPolynomialFirstOrderOperator B (E.val 1) at h
  have hc : gomesPolynomialFirstOrderOperator (C a) 1 = (-a) • (1 : ℝ[X]) := by
    simp [gomesPolynomialFirstOrderOperator, smul_eq_C_mul]
  rw [hc, map_smul] at h
  have hn : E.val (1 : ℝ[X]) ≠ 0 := by
    intro hz
    have he : E.val (1 : ℝ[X]) = E.val 0 := by simpa only [map_zero] using hz
    exact one_ne_zero (E.val.injective he)
  have hz := (gomesPolynomialFirstOrderEigenvalues_mem_iff B (-a)).mp ⟨E.val 1, hn, h.symm⟩
  simpa only [map_neg, neg_neg] using eq_neg_of_add_eq_zero_left hz

/-- Constant-source conjugacy has no hidden nonconstant or different-constant targets. -/
theorem gomesPolynomialConnection_constant_source_intertwiner_iff (a : ℝ) (B : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner (C a) B) ↔ B = C a := by
  constructor
  · rintro ⟨E⟩
    exact gomesPolynomialConnectionIntertwiner_constant_source a B E
  · rintro rfl
    exact ⟨gomesPolynomialConnectionIntertwinerRefl _⟩

/-- Constant-target conjugacy is equally rigid. -/
theorem gomesPolynomialConnection_constant_target_intertwiner_iff (A : ℝ[X]) (b : ℝ) :
    Nonempty (GomesPolynomialConnectionIntertwiner A (C b)) ↔ A = C b := by
  constructor
  · rintro ⟨E⟩
    exact gomesPolynomialConnectionIntertwiner_constant_source b A
      (gomesPolynomialConnectionIntertwinerSymm _ _ E)
  · rintro rfl
    exact ⟨gomesPolynomialConnectionIntertwinerRefl _⟩

/-- Two constant connections are conjugate exactly when their real coefficients agree. -/
theorem gomesPolynomialConnection_constant_intertwiner_iff (a b : ℝ) :
    Nonempty (GomesPolynomialConnectionIntertwiner (C a) (C b)) ↔ a = b := by
  rw [gomesPolynomialConnection_constant_source_intertwiner_iff, C_inj]
  exact eq_comm

/-- Invertible linear intertwining is a symmetric relation. -/
theorem gomesPolynomialConnection_intertwiner_symm_iff (A B : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner A B) ↔
      Nonempty (GomesPolynomialConnectionIntertwiner B A) := by
  constructor <;> rintro ⟨E⟩
  · exact ⟨gomesPolynomialConnectionIntertwinerSymm _ _ E⟩
  · exact ⟨gomesPolynomialConnectionIntertwinerSymm _ _ E⟩

end GaloisForLFunctions.HTGeometry
