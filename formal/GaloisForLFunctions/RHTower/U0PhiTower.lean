import GaloisForLFunctions.RHTower.CoherentTower
import GaloisForLFunctions.U0.U0CurveSectors
import GaloisForLFunctions.U0.U0PhiKummerLayers

/-!
# The sharp U0/Bottcher window tower as an RHTower coherent tower

The large-parameter window branch supplies an explicit dyadic Kummer tower
`phiBRoot k b`.  This file connects that tower to the generic RHTower
`CoherentTower` API and keeps the per-level `u₀` independence certificates.
-/

namespace RHTower

open Complex Filter Set Metric Bottcher
open U0 U0NaturalBoundary U0MeroCarrier
open U0MStepBranch U0PhiMStep
open U0PhiLargeWindow U0PhiLargeCarrier U0PhiKummerLayers

/-- Adjacent large-window Kummer layers square to the previous layer. -/
theorem phiBRoot_succ_sq (k : ℕ) (b z : ℂ) :
    phiBRoot (k + 1) b z ^ 2 = phiBRoot k b z := by
  unfold phiBRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hpow : ((2 : ℂ) ^ (k + 2)) = ((2 : ℂ) ^ (k + 1)) * 2 := by
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
  rw [hpow]
  field_simp [pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)]
  ring

/-- For every sharp large parameter, the explicit Böttcher window roots form an
RHTower coherent dyadic Kummer tower over the whole window disk. -/
theorem phiB_coherentTower_large_norm {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    Nonempty (CoherentTower (phiB b) (ball (0 : ℂ) (rB b))) := by
  refine ⟨{
    level := fun k z => phiBRoot k b z
    level_zero := ?_
    analytic := ?_
    sq := ?_ }⟩
  · intro z _hz
    exact phiBRoot_zero b z
  · intro k
    exact phiBRoot_analytic hb k
  · intro k z _hz
    exact phiBRoot_succ_sq k b z

/-- The sharp large-window Böttcher tower is a coherent RHTower tower, and every
level remains algebraically independent from `u₀` over the meromorphic annulus carrier. -/
theorem phiB_coherentTower_with_noRelation_large_norm {b : ℂ}
    (hb : 2 + Real.sqrt 2 < ‖b‖) :
    ∃ T : CoherentTower (phiB b) (ball (0 : ℂ) (rB b)),
      (∀ k z, T.level k z = phiBRoot k b z) ∧
      (∀ k z, T.level k z ≠ 0) ∧
      (∀ k,
        letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
          (annWB_nonempty hb)
        letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
          (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
            (annWB_nonempty hb) (annWB_infinite hb)).toAlgebra
        NoRelation (RatFunc ℂ)
          (algebraMap (analyticSubring (annWB b)) (meroField (annWB b))
            ⟨Germ.coeRingHom (𝓟 (annWB b)) (T.level k),
              ⟨T.level k, (T.analytic k).mono annWB_subset_ball, rfl⟩⟩)
          (algebraMap (analyticSubring (annWB b)) (meroField (annWB b))
            (u0AnSub annWB_subset_Ext))) := by
  let T : CoherentTower (phiB b) (ball (0 : ℂ) (rB b)) :=
    { level := fun k z => phiBRoot k b z
      level_zero := by
        intro z _hz
        exact phiBRoot_zero b z
      analytic := by
        intro k
        exact phiBRoot_analytic hb k
      sq := by
        intro k z _hz
        exact phiBRoot_succ_sq k b z }
  refine ⟨T, ?_, ?_, ?_⟩
  · intro k z
    rfl
  · intro k z
    exact phiBRoot_ne_zero k b z
  · intro k
    simpa [T, phiBRootAn] using u0_phiBRoot_independence (b := b) hb k

/-- At the sharp U0/Böttcher threshold, the concrete U0 `psiN` Kummer tower is
available as an RHTower coherent tower with levelwise `NoRelation` certificates.
The U0 curve-sector theorem discharges the former filled-Julia viability input. -/
theorem u0_coherentTower_with_noRelation_of_gt_sharp {b : ℂ}
    (hb : 2 + Real.sqrt 2 < ‖b‖) :
    ∃ (r : ℝ) (N : ℕ) (hr : 1 < r) (T : CoherentTower (psiN b N) (ball (0 : ℂ) r)),
      (∀ k z, T.level k z ≠ 0) ∧
      (∀ k,
        letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
          (annMB_nonempty hr)
        letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
          (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
            (annMB_infinite hr)).toAlgebra
        NoRelation (RatFunc ℂ)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            ⟨Germ.coeRingHom (𝓟 (annMB r)) (T.level k),
              ⟨T.level k, (T.analytic k).mono inter_subset_left, rfl⟩⟩)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            (u0AnSub annMB_subset_Ext))) := by
  exact u0_coherentTower_with_noRelation_of_viable (U0CurveSectors.viable_of_gt_sharp hb)

/-- For every `‖b‖ ≥ 4`, the concrete U0 `psiN` Kummer tower is available as an
RHTower coherent tower with levelwise `NoRelation` certificates.  The large-parameter
Böttcher exterior estimate discharges the viability input. -/
theorem u0_coherentTower_with_noRelation_of_norm_ge_four {b : ℂ} (hb : 4 ≤ ‖b‖) :
    ∃ (r : ℝ) (N : ℕ) (hr : 1 < r) (T : CoherentTower (psiN b N) (ball (0 : ℂ) r)),
      (∀ k z, T.level k z ≠ 0) ∧
      (∀ k,
        letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
          (annMB_nonempty hr)
        letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
          (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
            (annMB_infinite hr)).toAlgebra
        NoRelation (RatFunc ℂ)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            ⟨Germ.coeRingHom (𝓟 (annMB r)) (T.level k),
              ⟨T.level k, (T.analytic k).mono inter_subset_left, rfl⟩⟩)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            (u0AnSub annMB_subset_Ext))) := by
  refine u0_coherentTower_with_noRelation_of_viable ?_
  intro z hz hfilled
  have hgt : 1 < ‖z‖ := filledJulia_exterior hb hfilled
  linarith

end RHTower
