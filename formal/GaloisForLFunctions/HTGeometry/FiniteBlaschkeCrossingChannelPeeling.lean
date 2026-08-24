import GaloisForLFunctions.HTGeometry.FiniteBlaschkeProduct
import GaloisForLFunctions.HTGeometry.AdjointGramChannelPeeling

open Complex Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Crossing channel `B₀ K_(B₁)` inside product model space. -/
def finiteBlaschkeCrossingChannel (B₀ B₁ : FiniteBlaschke) :
    Submodule ℂ HardyDisk :=
  (finiteBlaschkeModelSpace B₁).map
    ((finiteBlaschkeMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk)

noncomputable instance (B₀ B₁ : FiniteBlaschke) :
    FiniteDimensional ℂ (finiteBlaschkeCrossingChannel B₀ B₁) := by
  unfold finiteBlaschkeCrossingChannel
  infer_instance

noncomputable instance (B₀ B₁ : FiniteBlaschke) :
    (finiteBlaschkeCrossingChannel B₀ B₁).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Crossing-channel dimension is exactly the disappearing denominator multiplicity. -/
theorem finrank_finiteBlaschkeCrossingChannel (B₀ B₁ : FiniteBlaschke) :
    Module.finrank ℂ (finiteBlaschkeCrossingChannel B₀ B₁) = B₁.deg := by
  have hinj : Function.Injective
      ((finiteBlaschkeMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk) := by
    intro x y hxy
    have hzero : finiteBlaschkeMul B₀ (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hnorm : ‖x - y‖ = 0 := by
      rw [← norm_finiteBlaschkeMul B₀ (x - y), hzero, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  let e := Submodule.equivMapOfInjective
    ((finiteBlaschkeMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk) hinj (finiteBlaschkeModelSpace B₁)
  calc
    Module.finrank ℂ (finiteBlaschkeCrossingChannel B₀ B₁) =
        Module.finrank ℂ (finiteBlaschkeModelSpace B₁) := by
      exact (LinearEquiv.finrank_eq e).symm
    _ = B₁.deg := finrank_finiteBlaschkeModelSpace B₁

/-- The crossing channel is a literal subspace of the full product model space. -/
theorem finiteBlaschkeCrossingChannel_le_modelSpace_append (B₀ B₁ : FiniteBlaschke) :
    finiteBlaschkeCrossingChannel B₀ B₁ ≤
      finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁) := by
  rw [FiniteBlaschke.finiteBlaschkeModelSpace_append_eq_sup]
  exact le_sup_right

/-- Causal compression of a finite inner quotient is contractive. -/
theorem norm_finiteBlaschkeCausalCore_le_one (A B : FiniteBlaschke) :
    ‖finiteBlaschkeCausalCore A B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  have hsplit := norm_sq_finiteBlaschkeLeakageCore A B x
  have hle : ‖finiteBlaschkeCausalCore A B x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    change ‖(finiteBlaschkeMul B).adjoint (finiteBlaschkeMul A x)‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith [sq_nonneg ‖finiteBlaschkeLeakageCore A B x‖]
  nlinarith [norm_nonneg (finiteBlaschkeCausalCore A B x), norm_nonneg x]

/-- Exact theorem-C `(11)` identity at finite scale: crossing-channel leakage Gram defect equals
the square of causal compression on that channel. -/
theorem norm_finiteBlaschkeCrossingGramDefect_eq_sq
    (A B₀ B₁ : FiniteBlaschke) :
    ‖channelGramDefect (finiteBlaschkeCrossingChannel B₀ B₁)
        (finiteBlaschkeLeakageCore A (FiniteBlaschke.append B₀ B₁))‖ =
      ‖(finiteBlaschkeCausalCore A (FiniteBlaschke.append B₀ B₁)).comp
          (finiteBlaschkeCrossingChannel B₀ B₁).starProjection‖ *
        ‖(finiteBlaschkeCausalCore A (FiniteBlaschke.append B₀ B₁)).comp
          (finiteBlaschkeCrossingChannel B₀ B₁).starProjection‖ :=
  norm_channelGramDefect_eq_sq _ _ _
    (adjoint_comp_finiteBlaschkeLeakageCore_add_causalCore A
      (FiniteBlaschke.append B₀ B₁))

/-- Exact theorem-C `(12)` estimate at finite scale: off-diagonal leakage is controlled by causal
compression on the crossing channel. -/
theorem norm_finiteBlaschkeCrossingOffDiagonalGram_le
    (A B₀ B₁ : FiniteBlaschke) :
    ‖channelOffDiagonalGram (finiteBlaschkeCrossingChannel B₀ B₁)
        (finiteBlaschkeLeakageCore A (FiniteBlaschke.append B₀ B₁))‖ ≤
      ‖(finiteBlaschkeCausalCore A (FiniteBlaschke.append B₀ B₁)).comp
        (finiteBlaschkeCrossingChannel B₀ B₁).starProjection‖ :=
  norm_channelOffDiagonalGram_le _ _ _
    (adjoint_comp_finiteBlaschkeLeakageCore_add_causalCore A
      (FiniteBlaschke.append B₀ B₁))
    (norm_finiteBlaschkeCausalCore_le_one A (FiniteBlaschke.append B₀ B₁))

/-- The boundary-scaling causal-channel limit implies theorem-C `(11)` exactly. -/
theorem tendsto_norm_finiteBlaschkeCrossingGramDefect_zero
    {ι : Type*} {l : Filter ι} (A B₀ B₁ : ι → FiniteBlaschke)
    (hcausal : Tendsto (fun i =>
      ‖(finiteBlaschkeCausalCore (A i) (FiniteBlaschke.append (B₀ i) (B₁ i))).comp
        (finiteBlaschkeCrossingChannel (B₀ i) (B₁ i)).starProjection‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖channelGramDefect (finiteBlaschkeCrossingChannel (B₀ i) (B₁ i))
        (finiteBlaschkeLeakageCore (A i)
          (FiniteBlaschke.append (B₀ i) (B₁ i)))‖) l (𝓝 0) := by
  convert hcausal.mul hcausal using 1
  · funext i
    exact norm_finiteBlaschkeCrossingGramDefect_eq_sq (A i) (B₀ i) (B₁ i)
  · simp

/-- The same boundary-scaling limit implies theorem-C `(12)` exactly. -/
theorem tendsto_norm_finiteBlaschkeCrossingOffDiagonalGram_zero
    {ι : Type*} {l : Filter ι} (A B₀ B₁ : ι → FiniteBlaschke)
    (hcausal : Tendsto (fun i =>
      ‖(finiteBlaschkeCausalCore (A i) (FiniteBlaschke.append (B₀ i) (B₁ i))).comp
        (finiteBlaschkeCrossingChannel (B₀ i) (B₁ i)).starProjection‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖channelOffDiagonalGram (finiteBlaschkeCrossingChannel (B₀ i) (B₁ i))
        (finiteBlaschkeLeakageCore (A i)
          (FiniteBlaschke.append (B₀ i) (B₁ i)))‖) l (𝓝 0) := by
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_finiteBlaschkeCrossingOffDiagonalGram_le (A i) (B₀ i) (B₁ i))
    hcausal

end GaloisForLFunctions.HTGeometry
