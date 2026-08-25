import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity

/-!
# Cubic Xi diagonal-Rees transversality

Canonical coefficient-generated Stokes cuts contain one positive pendant singleton cut for every
Puiseux branch.  Hence every nonzero orbit charge has strictly positive threshold block coarea.
Applied to the negative cubic wall--Xi Malgrange landing, unit Rees activation moves the Witt value
strictly above its completely contracted value.  Therefore no fixed charge can land at the cubic Xi
residual at both scales.

This kills the previously surviving Rees-rigid branch and replaces it with an exact positive drift
law.  It neither assumes nor proves existence of a contracted landing, and it does not prove RH.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

/-- Every completely contracted cubic Xi landing has strictly positive total canonical threshold
block coarea.  Pendant-cut faithfulness upgrades local nonnegativity to strict positivity. -/
theorem routePPrimitiveGammaJuliaStokesCubicContractedLanding_totalBlockEnergy_pos
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0)) :
    0 < ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
  have hxne :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero x
  have hlocal : ∃ a, x.1.1 a ≠ 0 := by
    by_contra h
    push Not at h
    apply hxne
    apply Subtype.ext
    funext a i
    exact congrFun (h a) i
  obtain ⟨a, ha⟩ := hlocal
  have hlift :
      (d a).toOrbitCoareaDatum.liftCharge (x.1.1 a) ≠ 0 := by
    intro hlift
    apply ha
    funext i
    obtain ⟨branch, hbranch⟩ :=
      (d a).toOrbitCoareaDatum.orbit_surjective i
    have hzero := congrFun hlift branch
    simpa [OrbitCoareaDatum.liftCharge, hbranch] using hzero
  have hblockpos :
      0 < (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
    simpa [OrbitCoareaDatum.blockEnergy] using
      (d a).toOrbitCoareaDatum.cuts.toPositivePendantCutFamily.positive_edge_energy hlift
  apply Finset.sum_pos'
  · intro b _
    exact (d b).toOrbitCoareaDatum.blockEnergy_nonneg (x.1.1 b)
  · exact ⟨a, Finset.mem_univ _, hblockpos⟩

/-- Exact diagonal-Rees drift: unit value minus the contracted Xi target is total threshold block
coarea. -/
theorem routePPrimitiveGammaJuliaStokesCubicContractedLanding_unit_sub_target_eq_totalBlockEnergy
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0)) :
    globalReesWittForm genus d (fun _ _ => 1) x.1 -
        (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) =
      ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
  have hzero := x.2
  have hdecompZero := globalReesWittForm_eq_positive_add_oneRank
    genus d (fun _ _ => 0) x.1
  have hdecompOne := globalReesWittForm_eq_positive_add_oneRank
    genus d (fun _ _ => 1) x.1
  have hpositive :
      globalReesPositiveForm d (fun _ _ => 1) x.1 =
        globalReesPositiveForm d (fun _ _ => 0) x.1 +
          ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
    simp [globalReesPositiveForm, localReesPositiveForm_apply,
      OrbitCoareaDatum.reesBlockEnergy, OrbitCoareaDatum.blockEnergy,
      OrbitCoareaDatum.cutCharge, Finset.sum_add_distrib]
  linarith

/-- Unit Rees activation moves every contracted cubic Xi landing strictly above its target. -/
theorem routePPrimitiveGammaJuliaStokesCubicContractedLanding_unit_gt_target
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0)) :
    normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4 <
      globalReesWittForm genus d (fun _ _ => 1) x.1 := by
  have hblock :=
    routePPrimitiveGammaJuliaStokesCubicContractedLanding_totalBlockEnergy_pos x
  have hdiff :=
    routePPrimitiveGammaJuliaStokesCubicContractedLanding_unit_sub_target_eq_totalBlockEnergy x
  linarith

/-- No fixed coefficient-generated charge can land at the cubic Xi residual at both complete
threshold contraction and unit Rees scale. -/
theorem not_nonempty_routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} :
    ¬ Nonempty
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d) := by
  rintro ⟨x⟩
  let y : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0) := ⟨x.1, x.2.1⟩
  have hgt :=
    routePPrimitiveGammaJuliaStokesCubicContractedLanding_unit_gt_target y
  linarith [x.2.2]

/-- Adding canonical raw Euler/Gamma--Wold rank debt cannot revive the empty Rees-rigid fiber. -/
theorem not_nonempty_routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} :
    ¬ Nonempty
      (routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber
        genus d) := by
  rintro ⟨x⟩
  exact
    not_nonempty_routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber
      ⟨x.1⟩

end

end RHTower
