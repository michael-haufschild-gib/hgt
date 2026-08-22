import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# Two-sided Hilbert–Schmidt bounds for a sandwich `Y ↦ S Y T`

Kim–Mer–Pálfia (arXiv:2607.29142), Lemma 3.10, bound the Hilbert–Schmidt norm of a sandwiched
Hilbert–Schmidt operator from both sides by the extreme eigenvalues of `S⋆S` and `T T⋆`.  Written
basis-wise the statement needs no trace: for every vector `y`,

`c ‖y‖² ≤ ‖S y‖² ≤ C ‖y‖²`

transfers termwise to `∑ᵢ ‖S (Y eᵢ)‖²`, giving `c ‖Y‖²_HS ≤ ‖S Y‖²_HS ≤ C ‖Y‖²_HS`; the right
factor is handled by the same estimate applied to the adjoints, since the Hilbert–Schmidt norm is
adjoint-invariant.
-/

open scoped BigOperators InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Upper bound for a left composition.** -/
theorem hsNormSq_comp_left_le {S : F →L[𝕜] G} {Y : E →L[𝕜] F} (hY : IsHilbertSchmidt Y)
    {C : ℝ} (hC : ∀ y : F, ‖S y‖ ^ 2 ≤ C * ‖y‖ ^ 2) :
    hsNormSq (S ∘L Y) ≤ C * hsNormSq Y := by
  have hsum1 : Summable (fun i => ‖(S ∘L Y) (hsBasis 𝕜 E i)‖ ^ 2) := hY.comp_left S
  have hsum2 : Summable (fun i => C * ‖Y (hsBasis 𝕜 E i)‖ ^ 2) := hY.mul_left C
  have hle : ∀ i, ‖(S ∘L Y) (hsBasis 𝕜 E i)‖ ^ 2 ≤ C * ‖Y (hsBasis 𝕜 E i)‖ ^ 2 := fun i => by
    rw [comp_apply]; exact hC _
  calc hsNormSq (S ∘L Y) = ∑' i, ‖(S ∘L Y) (hsBasis 𝕜 E i)‖ ^ 2 := rfl
    _ ≤ ∑' i, C * ‖Y (hsBasis 𝕜 E i)‖ ^ 2 := Summable.tsum_mono hsum1 hsum2 hle
    _ = C * hsNormSq Y := (tsum_mul_left).trans rfl

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Lower bound for a left composition.** -/
theorem le_hsNormSq_comp_left {S : F →L[𝕜] G} {Y : E →L[𝕜] F} (hY : IsHilbertSchmidt Y)
    {c : ℝ} (hc : ∀ y : F, c * ‖y‖ ^ 2 ≤ ‖S y‖ ^ 2) :
    c * hsNormSq Y ≤ hsNormSq (S ∘L Y) := by
  have hsum1 : Summable (fun i => ‖(S ∘L Y) (hsBasis 𝕜 E i)‖ ^ 2) := hY.comp_left S
  have hsum2 : Summable (fun i => c * ‖Y (hsBasis 𝕜 E i)‖ ^ 2) := hY.mul_left c
  have hle : ∀ i, c * ‖Y (hsBasis 𝕜 E i)‖ ^ 2 ≤ ‖(S ∘L Y) (hsBasis 𝕜 E i)‖ ^ 2 := fun i => by
    rw [comp_apply]; exact hc _
  calc c * hsNormSq Y = ∑' i, c * ‖Y (hsBasis 𝕜 E i)‖ ^ 2 := (tsum_mul_left).symm
    _ ≤ ∑' i, ‖(S ∘L Y) (hsBasis 𝕜 E i)‖ ^ 2 := Summable.tsum_mono hsum2 hsum1 hle
    _ = hsNormSq (S ∘L Y) := rfl

/-- **Upper bound for a right composition**, via adjoints. -/
theorem hsNormSq_comp_right_le {Y : F →L[𝕜] G} {T : E →L[𝕜] F} (hY : IsHilbertSchmidt Y)
    {C : ℝ} (hC : ∀ y : F, ‖adjoint T y‖ ^ 2 ≤ C * ‖y‖ ^ 2) :
    hsNormSq (Y ∘L T) ≤ C * hsNormSq Y := by
  have hYT : IsHilbertSchmidt (Y ∘L T) := hY.comp_right T
  have hadj : hsNormSq (Y ∘L T) = hsNormSq (adjoint T ∘L adjoint Y) := by
    rw [← hYT.hsNormSq_adjoint, adjoint_comp]
  rw [hadj, ← hY.hsNormSq_adjoint]
  exact hsNormSq_comp_left_le hY.adjoint hC

/-- **Lower bound for a right composition**, via adjoints. -/
theorem le_hsNormSq_comp_right {Y : F →L[𝕜] G} {T : E →L[𝕜] F} (hY : IsHilbertSchmidt Y)
    {c : ℝ} (hc : ∀ y : F, c * ‖y‖ ^ 2 ≤ ‖adjoint T y‖ ^ 2) :
    c * hsNormSq Y ≤ hsNormSq (Y ∘L T) := by
  have hYT : IsHilbertSchmidt (Y ∘L T) := hY.comp_right T
  have hadj : hsNormSq (Y ∘L T) = hsNormSq (adjoint T ∘L adjoint Y) := by
    rw [← hYT.hsNormSq_adjoint, adjoint_comp]
  rw [hadj, ← hY.hsNormSq_adjoint]
  exact le_hsNormSq_comp_left hY.adjoint hc

/-- **Operator-norm upper bound for a sandwich.** -/
theorem hsNormSq_sandwich_le {S T Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y) :
    hsNormSq (S ∘L (Y ∘L T)) ≤ (‖S‖ ^ 2 * ‖T‖ ^ 2) * hsNormSq Y := by
  have hYT : IsHilbertSchmidt (Y ∘L T) := hY.comp_right T
  have h1 : hsNormSq (S ∘L (Y ∘L T)) ≤ ‖S‖ ^ 2 * hsNormSq (Y ∘L T) :=
    hsNormSq_comp_left_le hYT (fun v => by
      calc ‖S v‖ ^ 2 ≤ (‖S‖ * ‖v‖) ^ 2 := by
            gcongr; exact S.le_opNorm v
        _ = ‖S‖ ^ 2 * ‖v‖ ^ 2 := by ring)
  have h2 : hsNormSq (Y ∘L T) ≤ ‖T‖ ^ 2 * hsNormSq Y :=
    hsNormSq_comp_right_le hY (fun v => by
      calc ‖adjoint T v‖ ^ 2 ≤ (‖adjoint T‖ * ‖v‖) ^ 2 := by
            gcongr; exact (adjoint T).le_opNorm v
        _ = ‖T‖ ^ 2 * ‖v‖ ^ 2 := by rw [adjoint.norm_map]; ring)
  calc hsNormSq (S ∘L (Y ∘L T)) ≤ ‖S‖ ^ 2 * hsNormSq (Y ∘L T) := h1
    _ ≤ ‖S‖ ^ 2 * (‖T‖ ^ 2 * hsNormSq Y) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (‖S‖ ^ 2 * ‖T‖ ^ 2) * hsNormSq Y := by ring

/-- **Lower Hilbert–Schmidt bound for a sandwich.** -/
theorem le_hsNormSq_sandwich {S T Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y)
    {c d : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y : E, c * ‖y‖ ^ 2 ≤ ‖S y‖ ^ 2)
    (hd : ∀ y : E, d * ‖y‖ ^ 2 ≤ ‖adjoint T y‖ ^ 2) :
    (c * d) * hsNormSq Y ≤ hsNormSq (S ∘L (Y ∘L T)) := by
  have hYT : IsHilbertSchmidt (Y ∘L T) := hY.comp_right T
  calc (c * d) * hsNormSq Y = c * (d * hsNormSq Y) := by ring
    _ ≤ c * hsNormSq (Y ∘L T) :=
        mul_le_mul_of_nonneg_left (le_hsNormSq_comp_right hY hd) hc0
    _ ≤ hsNormSq (S ∘L (Y ∘L T)) := le_hsNormSq_comp_left hYT hc

/-- **Two-sided Hilbert–Schmidt bounds for a sandwich** (Kim–Mer–Pálfia, Lemma 3.10). -/
theorem hsNormSq_sandwich_bounds {S T Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y)
    {c C d D : ℝ} (hc0 : 0 ≤ c) (hC0 : 0 ≤ C)
    (hc : ∀ y : E, c * ‖y‖ ^ 2 ≤ ‖S y‖ ^ 2) (hC : ∀ y : E, ‖S y‖ ^ 2 ≤ C * ‖y‖ ^ 2)
    (hd : ∀ y : E, d * ‖y‖ ^ 2 ≤ ‖adjoint T y‖ ^ 2)
    (hD : ∀ y : E, ‖adjoint T y‖ ^ 2 ≤ D * ‖y‖ ^ 2) :
    (c * d) * hsNormSq Y ≤ hsNormSq (S ∘L (Y ∘L T))
      ∧ hsNormSq (S ∘L (Y ∘L T)) ≤ (C * D) * hsNormSq Y := by
  have hYT : IsHilbertSchmidt (Y ∘L T) := hY.comp_right T
  constructor
  · calc (c * d) * hsNormSq Y = c * (d * hsNormSq Y) := by ring
      _ ≤ c * hsNormSq (Y ∘L T) :=
          mul_le_mul_of_nonneg_left (le_hsNormSq_comp_right hY hd) hc0
      _ ≤ hsNormSq (S ∘L (Y ∘L T)) := le_hsNormSq_comp_left hYT hc
  · calc hsNormSq (S ∘L (Y ∘L T)) ≤ C * hsNormSq (Y ∘L T) := hsNormSq_comp_left_le hYT hC
      _ ≤ C * (D * hsNormSq Y) :=
          mul_le_mul_of_nonneg_left (hsNormSq_comp_right_le hY hD) hC0
      _ = (C * D) * hsNormSq Y := by ring

end ContinuousLinearMap
