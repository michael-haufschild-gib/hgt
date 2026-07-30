import GaloisForLFunctions.HTGeometry.LocalExtensionMatrixChart

/-!
# Real Hermitian slice of the local-extension chart

Real onsite shifts and real-symmetric new-edge controls form a physical
slice of the complex local-extension chart.  The slice is real analytic,
contains every selected exchange direction, and preserves Hermiticity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix.Norms.Elementwise

/-- Complexification of the symmetric part of a real matrix. -/
def realSymmetricEdge
    {ρ : Type*} (edge : Matrix ρ ρ ℝ) :
    Matrix ρ ρ ℂ :=
  fun r s => ((edge r s + edge s r) / 2 : ℝ)

theorem realSymmetricEdge_isHermitian
    {ρ : Type*} (edge : Matrix ρ ρ ℝ) :
    (realSymmetricEdge edge).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext r s
  simp [Matrix.conjTranspose_apply, realSymmetricEdge, add_comm]

/-- Tensor products of Hermitian transition and edge matrices are
Hermitian. -/
theorem layerMatrixCoupling_isHermitian
    {α ρ : Type*}
    {transition : Matrix α α ℂ} {edge : Matrix ρ ρ ℂ}
    (htransition : transition.IsHermitian)
    (hedge : edge.IsHermitian) :
    (layerMatrixCoupling transition edge).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  have ht :=
    congrFun (congrFun htransition x.1) y.1
  have he :=
    congrFun (congrFun hedge x.2) y.2
  simpa [Matrix.conjTranspose_apply, layerMatrixCoupling,
    map_mul] using congrArg₂ (· * ·) ht he

/-- Real parameterization of the physical Hermitian slice. -/
def realLocalExtensionParameter
    {ρ : Type*}
    (p : (ρ → ℝ) × Matrix ρ ρ ℝ) :
    (ρ → ℂ) × Matrix ρ ρ ℂ :=
  (fun r => (p.1 r : ℂ), realSymmetricEdge p.2)

theorem realLocalExtensionParameter_analyticAt
    {ρ : Type*} [Fintype ρ]
    (p₀ : (ρ → ℝ) × Matrix ρ ρ ℝ) :
    AnalyticAt ℝ
      (realLocalExtensionParameter :
        ((ρ → ℝ) × Matrix ρ ρ ℝ) →
          (ρ → ℂ) × Matrix ρ ρ ℂ) p₀ := by
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro r
    let coord : (ρ → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) r
    exact
      (Complex.ofRealCLM.analyticAt _).comp
        ((coord.analyticAt p₀.1).comp analyticAt_fst)
  · apply AnalyticAt.pi
    intro r
    apply AnalyticAt.pi
    intro s
    let rowR : Matrix ρ ρ ℝ →L[ℝ] (ρ → ℝ) :=
      ContinuousLinearMap.proj (R := ℝ) r
    let colS : (ρ → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) s
    let entryRS : Matrix ρ ρ ℝ →L[ℝ] ℝ :=
      colS.comp rowR
    let rowS : Matrix ρ ρ ℝ →L[ℝ] (ρ → ℝ) :=
      ContinuousLinearMap.proj (R := ℝ) s
    let colR : (ρ → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) r
    let entrySR : Matrix ρ ρ ℝ →L[ℝ] ℝ :=
      colR.comp rowS
    have hrs :
        AnalyticAt ℝ
          (fun p : (ρ → ℝ) × Matrix ρ ρ ℝ =>
            p.2 r s) p₀ :=
      (entryRS.analyticAt p₀.2).comp analyticAt_snd
    have hsr :
        AnalyticAt ℝ
          (fun p : (ρ → ℝ) × Matrix ρ ρ ℝ =>
            p.2 s r) p₀ :=
      (entrySR.analyticAt p₀.2).comp analyticAt_snd
    exact
      (Complex.ofRealCLM.analyticAt _).comp
        ((hrs.add hsr).div_const)

@[simp] theorem realLocalExtensionParameter_center
    {ρ : Type*}
    (shift₀ : ρ → ℝ) :
    realLocalExtensionParameter
        (shift₀, (0 : Matrix ρ ρ ℝ)) =
      ((fun r => (shift₀ r : ℂ)), 0) := by
  ext <;> simp [realLocalExtensionParameter, realSymmetricEdge]

/-- The real-symmetric slice contains every real selected exchange
direction exactly. -/
theorem realSymmetricEdge_selectedLayerExchange
    {ρ : Type*} [DecidableEq ρ]
    (r s : ρ) (g : ℝ) :
    realSymmetricEdge
        (g • fun u v =>
          if (u = r ∧ v = s) ∨ (u = s ∧ v = r)
          then (1 : ℝ) else 0) =
      (g : ℂ) • selectedLayerExchangeMatrix r s := by
  ext u v
  let b : ρ → ρ → ℝ :=
    fun x y =>
      if (x = r ∧ y = s) ∨ (x = s ∧ y = r)
      then 1 else 0
  have hsymm : b v u = b u v := by
    simp only [b]
    congr 1
    aesop
  change (((g * b u v + g * b v u) / 2 : ℝ) : ℂ) =
    (g : ℂ) *
      (if (u = r ∧ v = s) ∨ (u = s ∧ v = r)
        then 1 else 0)
  rw [hsymm]
  by_cases h :
      (u = r ∧ v = s) ∨ (u = s ∧ v = r)
  · simp [b, h]
  · simp [b, h]

/-- Every real point of the physical slice is a Hermitian local
Hamiltonian whenever the old transition channel is Hermitian. -/
theorem localExtensionMatrix_realParameter_isHermitian
    {α ρ : Type*}
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (p : (ρ → ℝ) × Matrix ρ ρ ℝ) :
    (localExtensionMatrix
      (fun a => (energy a : ℂ))
      (realLocalExtensionParameter p).1
      transition
      (realLocalExtensionParameter p).2).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff]
    simp [realLocalExtensionParameter, layeredEnergy]
  · exact layerMatrixCoupling_isHermitian
      htransition (realSymmetricEdge_isHermitian p.2)

end

end GaloisForLFunctions.HTGeometry
