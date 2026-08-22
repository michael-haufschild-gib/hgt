import GaloisForLFunctions.HTGeometry.QuasiAbelianPositiveFactorJetAmple
import GaloisForLFunctions.HTGeometry.QuasiAbelianFiniteJetPeeling

/-!
# Convergent damped subgroup extensions preserve all-order jet ampleness

The determinant argument of Abe's subgroup-rank induction uses only the
convergence to zero of the literal complement jet sums. It does not require a
uniform exponential rate. This file records that exact weaker interface, so a
future period-matrix construction can be connected to all-order interpolation
through a proved convergence statement rather than the false global-gap
majorant.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Packet-specific output of an analytic damped construction. The finite evaluation matrix of
actual upper-factor columns converges to that of the prescribed lower columns. -/
structure AbeConvergentJetPacketLift
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ)
    {I : Type u} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → MultivariateEntire d) where
  upperColumn : ℝ → FiniteJetPacketIndex d I m → upper.forms
  remainder : ℝ → FiniteJetPacketIndex d I m → FiniteJetPacketIndex d I m → ℂ
  jet_decomposition : ∀ (B : ℝ) (i j : FiniteJetPacketIndex d I m),
    multiIndexJetEvalCLM (w i.1) i.2.1 (upperColumn B j).1 =
      multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j) + remainder B i j
  remainder_tendsto_zero : ∀ (i j : FiniteJetPacketIndex d I m),
    Tendsto (fun B => remainder B i j) Filter.atTop (nhds 0)

/-- One subgroup-rank extension that constructs convergent packet lifts. -/
structure AbeConvergentDampedFactorExtension
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ) where
  subgroup_le : ΓH ≤ Γ
  liftPacket : ∀ (I : Type u) [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → lower.forms),
    AbeConvergentJetPacketLift upper w m (fun j ↦ (lowerColumn j).1)

/-- **Convergent Abe subgroup-rank induction.** Literal convergence of the complement jet sums
is sufficient to transport every finite jet packet from the lower to the upper factor. -/
theorem AbeConvergentDampedFactorExtension.jetAmpleEveryFiniteOrder
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (E : AbeConvergentDampedFactorExtension.{u} lower upper)
    (hlower : AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} lower) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} upper := by
  intro I _ _ w m hdistinct hm
  classical
  let Q := FiniteJetPacketIndex d I m
  let basisTarget : Q → Q → ℂ := fun j i ↦ if i = j then 1 else 0
  have hlowerDistinct : PairwiseDistinctModulo ΓH w := by
    intro i j hij hmem
    exact hdistinct hij (E.subgroup_le hmem)
  have hexact (j : Q) : ∃ f : lower.forms,
      lower.jetPacketLinearMap w m f = basisTarget j :=
    hlower I w m hlowerDistinct hm (basisTarget j)
  let lowerColumn : Q → lower.forms := fun j ↦ Classical.choose (hexact j)
  have hlowerColumn (j : Q) :
      lower.jetPacketLinearMap w m (lowerColumn j) = basisTarget j :=
    Classical.choose_spec (hexact j)
  let L := E.liftPacket I w m lowerColumn
  let M : ℝ → Matrix Q Q ℂ := fun B ↦ Matrix.of fun i j ↦
    multiIndexJetEvalCLM (w i.1) i.2.1 (L.upperColumn B j).1
  have hmatrix : Tendsto M Filter.atTop (nhds (1 : Matrix Q Q ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have herr := L.remainder_tendsto_zero i j
    have hentry : Tendsto
        (fun B : ℝ ↦
          multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 + L.remainder B i j)
        Filter.atTop
        (nhds (multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 + 0)) :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ ↦ multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1)
        Filter.atTop
        (nhds (multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1))).add herr
    have hlowerEntry :
        multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 =
          (1 : Matrix Q Q ℂ) i j := by
      have hij := congrFun (hlowerColumn j) i
      simpa [basisTarget, Matrix.one_apply] using hij
    rw [← hlowerEntry]
    simpa only [M, Matrix.of_apply, L.jet_decomposition, add_zero] using hentry
  have hdet : Tendsto (fun B ↦ (M B).det) Filter.atTop (nhds 1) := by
    change Tendsto ((fun X : Matrix Q Q ℂ ↦ X.det) ∘ M)
      Filter.atTop (nhds 1)
    simpa [Function.comp_def] using
      continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have heventually : ∀ᶠ B in Filter.atTop, (M B).det ≠ 0 :=
    hdet.eventually (eventually_ne_nhds one_ne_zero)
  obtain ⟨B, hB⟩ := heventually.exists
  letI : AddCommGroup upper.forms := Module.addCommMonoidToAddCommGroup ℂ
  exact linearMap_surjective_of_evaluationMatrix_det_ne_zero
    (upper.jetPacketLinearMap w m) (L.upperColumn B) (by
      simpa only [M, AutomorphicFactor.jetPacketLinearMap_apply] using hB)

end

end GaloisForLFunctions.HTGeometry
