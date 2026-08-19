import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedFactorExtension

/-!
# The damped extension step, required only on jet-basis columns

`AbeDampedFactorExtension.liftPacket` asks for a damped lift of *every* lower column.  Abe's
Proposition 8.2 does not supply that: the multiplier used in the damping must be `ΓH`-invariant, and
a lift preserving all packet jets of an arbitrary column at once is a stronger demand than the
construction meets.

Inspecting the proof of `AbeDampedFactorExtension.jetAmpleEveryFiniteOrder` shows it only ever uses
columns that realize the standard jet basis of the packet — those produced by the lower factor's own
ampleness.  Restricting `liftPacket` to those columns therefore costs nothing downstream and makes
the interface reachable.  The strong interface implies the restricted one, so every prior instance
survives.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- One damped extension step, required only for columns realizing the standard jet basis. -/
structure AbeDampedFactorExtensionBasis
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ) where
  subgroup_le : ΓH ≤ Γ
  liftPacket : ∀ (I : Type u) [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → lower.forms),
    (∀ j, lower.jetPacketLinearMap w m (lowerColumn j)
      = fun i => if i = j then (1 : ℂ) else 0) →
    AbeDampedJetPacketLift upper w m (fun j ↦ (lowerColumn j).1)

/-- The strong interface implies the restricted one. -/
def AbeDampedFactorExtension.toBasis
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (E : AbeDampedFactorExtension.{u} lower upper) :
    AbeDampedFactorExtensionBasis.{u} lower upper where
  subgroup_le := E.subgroup_le
  liftPacket := fun I _ _ w m lowerColumn _ => E.liftPacket I w m lowerColumn

theorem AbeDampedFactorExtensionBasis.jetAmpleEveryFiniteOrder
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (E : AbeDampedFactorExtensionBasis.{u} lower upper)
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
  let L := E.liftPacket I w m lowerColumn hlowerColumn
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
          multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 +
            ∑' z, L.remainderTerm B z i j)
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


/-- The tower built from restricted extension steps. -/
inductive AbePositiveFactorTowerBasis (d : ℕ) :
    {Γ : AddSubgroup (Fin d → ℂ)} → AutomorphicFactor d Γ → Type (u + 1)
  | base (P : AbePositiveFactorPresentation.{u} d) :
      AbePositiveFactorTowerBasis d P.factor
  | extension
      {ΓH Γ : AddSubgroup (Fin d → ℂ)}
      {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
      (previous : AbePositiveFactorTowerBasis d lower)
      (step : AbeDampedFactorExtensionBasis.{u} lower upper) :
      AbePositiveFactorTowerBasis d upper

theorem AbePositiveFactorTowerBasis.jetAmpleEveryFiniteOrder
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {ψ : AutomorphicFactor d Γ} (T : AbePositiveFactorTowerBasis.{u} d ψ) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} ψ := by
  induction T with
  | base P => exact P.jetAmpleEveryFiniteOrder
  | extension previous step ih =>
      exact step.jetAmpleEveryFiniteOrder ih

/-- Positivity in the restricted sense: reachable from an Abe presentation by restricted steps. -/
def AutomorphicFactor.IsAbePositiveToruslessBasis
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) : Prop :=
  Nonempty (AbePositiveFactorTowerBasis.{u} d ψ)

/-- **Torusless fixed-factor all-order jet ampleness, restricted interface.** -/
theorem AutomorphicFactor.jetAmpleEveryFiniteOrder_of_isAbePositiveToruslessBasis
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ)
    (hpositive : AutomorphicFactor.IsAbePositiveToruslessBasis.{u} ψ) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} ψ :=
  hpositive.some.jetAmpleEveryFiniteOrder

/-- Every strong tower is a restricted tower. -/
def AbePositiveFactorTower.toBasis {d : ℕ} :
    ∀ {Γ : AddSubgroup (Fin d → ℂ)} {ψ : AutomorphicFactor d Γ},
      AbePositiveFactorTower.{u} d ψ → AbePositiveFactorTowerBasis.{u} d ψ
  | _, _, AbePositiveFactorTower.base P => AbePositiveFactorTowerBasis.base P
  | _, _, AbePositiveFactorTower.extension previous step =>
      AbePositiveFactorTowerBasis.extension previous.toBasis step.toBasis

theorem isAbePositiveToruslessBasis_of_isAbePositiveTorusless
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)} {ψ : AutomorphicFactor d Γ}
    (h : AutomorphicFactor.IsAbePositiveTorusless.{u} ψ) :
    AutomorphicFactor.IsAbePositiveToruslessBasis.{u} ψ :=
  ⟨h.some.toBasis⟩

end

end GaloisForLFunctions.HTGeometry
